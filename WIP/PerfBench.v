(* Performance benchmark for egraph_reducing_equal' under vm_compute. *)
#[local] Set Warnings "-native-compiler-disabled".
From Stdlib Require Import Lists.List Strings.String BinNums PArith.BinPos.
Import ListNotations.
Open Scope string.
Open Scope list.

From coqutil Require Import Map.Interface.
From Utils Require Import Utils Monad.
Import StateMonad.
From Utils Require Import TrieMap FullPosTrie FullPosTrieConv.
From coqutil Require Import Datatypes.Result.
From Utils.EGraph Require Import Defs.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
Import PositiveInstantiation.

(* depth analysis instance, mirroring Automation.v *)
Instance bench_analysis : analysis string string (option positive) :=
  weighted_depth_analysis (fun _ => Some xH).

Definition filter_rules :=
  (fun pat : string * Rule.rule string =>
     match pat with
     | (_, Rule.term_rule _ _ _) => false
     | (_, Rule.sort_rule _ _) => false
     | _ => true
     end).

Definition all_reversible : string * Rule.rule string -> bool := fun _ => true.
Definition no_inj : list (string * list string) := [].

(* Monoid with an associativity equation. *)
Definition monoid : lang string :=
  {[l
  [s|
      -----------------------------------------------
      #"S" srt
  ];
  [:|  "a": #"S", "b" : #"S"
       -----------------------------------------------
       #"*" "a" "b" : #"S"
  ];
  [:=  "a": #"S", "b" : #"S", "c" : #"S"
       ----------------------------------------------- ("assoc")
       #"*" (#"*" "a" "b") "c"
       = #"*" "a" (#"*" "b" "c")
       : #"S"
  ];
  [:=  "a": #"S", "b" : #"S"
       ----------------------------------------------- ("comm")
       #"*" "a" "b"
       = #"*" "b" "a"
       : #"S"
  ]
  ]}.

(* Build a context of n variables x0..x(n-1) of sort S. *)
Fixpoint nat_name (i : nat) : string :=
  match i with O => "" | S j => String.append "z" (nat_name j) end.
Definition var_name (i : nat) : string := String.append "x" (nat_name i).
Definition Ssort : sort string := scon "S" [].

Fixpoint bench_ctx_n (n : nat) : ctx string :=
  match n with
  | 0 => []
  | S i => (var_name i, Ssort) :: bench_ctx_n i
  end.

(* left-assoc: (((x0 * x1) * x2) * ... ) *)
Fixpoint e_left_n (n : nat) : term string :=
  match n with
  | 0 => var (var_name 0)
  | S i => con "*" [ var (var_name (S i)); e_left_n i ]
  end.

(* right-assoc: (x0 * (x1 * (x2 * ...))) over the same n+1 variables,
   listed so the leaves match e_left_n. *)
Fixpoint e_right_n' (lo n : nat) : term string :=
  match n with
  | 0 => var (var_name lo)
  | S i => con "*" [ e_right_n' (S lo) i; var (var_name lo) ]
  end.

(* ====================================================================
   POSITIVE instantiation benchmark (the realistic fast path).
   We rename the string language/terms to positive via PosRenaming
   exactly as egraph_equal' does internally, then drive the positive
   engine (PositiveInstantiation.egraph_equal / compat_intersect).

   FINDINGS (monoid assoc+comm, positive keys; vm_compute):
   - Positive is ~15x faster than the string instantiation; the string
     numbers were dominated by slow string `eqb` and are MISLEADING.
   - Saturation reaches fixpoint by iteration 3 (s3..s6 plateau ~0.17s);
     the cost is concentrated in the one expensive iteration.
   - Per expensive iteration: build_tries ~0.01s, REBUILD is in the noise
     (oneiter ~= oneiter_nr), and the join+writes (process_erule) phase
     dominates (~0.3s). So on positive, rebuild/worklist are NOT the
     bottleneck (on string they looked like it purely due to eqb cost).
   - worklist_dedup is O(n^2) and removes ZERO entries in these saturating
     workloads: depth 4/6/8 -> 270/773/1369 entries -> 0.011/0.12/0.273s.
     2.9x size => ~11x time: a latent quadratic that will dominate at
     scale (bigger languages / deeper terms). Its soundness contract is
     only `worklist_dedup_preserves_all` (output is a sublist of input),
     so it can be replaced by an O(n) idx_map-backed exact-dup pass that
     keeps the identical e-graph result (re-union/re-analyze is idempotent).

   process_erule split (n=6 expensive iteration, `jc` measurement):
     build_tries 0.017s | JOIN/intersection 0.013s (1089 matches!) |
     WRITES (exec_write) ~0.38s. The intersection algorithm is NOT the
     bottleneck; the write-application phase is ~92% of the iteration.
     exec_write runs once per match: rebuilds `map.of_list (combine
     query_vars assignment)`, inserts each write-clause atom (preallocating
     even when the node already exists -- see exec_write TODO), and unions.
     Levers (all in verified code): (a) cut redundant matches -- the
     semi-naive frontier uses TOTAL for every non-frontier clause, so a
     match with k new clauses is found k times (classic double-count; a
     proper delta split OLD<i / NEW=i / TOTAL>i finds each once); (b) avoid
     exec_write's per-match map rebuild / redundant preallocation.
     MEASURED redundancy (jc vs jcd): 1089 total matches but only 299
     DISTINCT -> ~73% of exec_write calls are redundant (3.6x). Since
     writes are ~92% of the iteration, deduping matches before exec_write
     (or a proper delta decomposition) could cut iteration cost by ~70%.
     exec_write is idempotent on a repeated match, so dedup is result-
     preserving; the cheapest form is to collect+dedup assignments across
     all frontiers in process_erule and exec_write each once.

   DEDUP RESULT (process_erule now aggregates per-frontier keys into one
   idx_trie and exec_writes each unique assignment once; runtime-only change,
   src/Utils/EGraph/Defs.v).  Before -> after, monoid n=6, fpt engine:
     - sat_eq full solve (s3..s6): ~0.130s -> ~0.030s  (~4.3x faster)
     - expensive iter oneiter_nr:  0.244s -> 0.118s
     - post-join worklist n=4/6/8: 270/773/1369 -> 52/108/168 (~7x fewer
       redundant union entries; the O(n^2) worklist_dedup concern evaporates)
     - worklist_dedup @ n=8:       0.21s  -> 0.003s
   Correctness preserved: s_check/sat_eq/easy_check still true/Success.
   (jc=1089 total vs jcd=299 distinct are computed by THIS file's own
   per-frontier logic, so they are unchanged -- they measure the redundancy
   the runtime change now collapses.)
   ==================================================================== *)
Import PosListMap.

(* Rename (lang, e_left, e_right, sort, eqn-rules) to positive together,
   so they share one renaming. Mirrors egraph_equal''s rename_and_run. *)
Definition pos_bundle (n : nat)
  : lang positive * term positive * term positive * sort positive * lang positive :=
  let c := bench_ctx_n (S n) in
  let m : state (PosRenaming.renaming string) _ :=
    @! let l'  <- PosRenaming.rename_lang (ctx_to_rules c ++ monoid) in
       let e1' <- PosRenaming.rename_term (var_to_con (e_left_n n)) in
       let e2' <- PosRenaming.rename_term (var_to_con (e_right_n' 0 n)) in
       let t'  <- PosRenaming.rename_sort (sort_var_to_con Ssort) in
       let pr  <- PosRenaming.rename_lang
                    (ctx_to_rules c ++ PositiveInstantiation.filter_eqn_rules monoid) in
       ret (l', e1', e2', t', pr)
  in
  fst (m {| PosRenaming.p_to_v := map.empty;
            PosRenaming.v_to_p := [];
            PosRenaming.next_id := xO xH |}).

(* Fixed bundle at n=6 (term depth 6), shared by the micro-benchmarks. *)
Definition bnd6 := Eval vm_compute in pos_bundle 6.
Definition l6   := Eval vm_compute in let '(l,_,_,_,_) := bnd6 in l.
Definition e1_6 := Eval vm_compute in let '(_,e,_,_,_) := bnd6 in e.
Definition e2_6 := Eval vm_compute in let '(_,_,e,_,_) := bnd6 in e.
Definition t6   := Eval vm_compute in let '(_,_,_,t,_) := bnd6 in t.
Definition pr6  := Eval vm_compute in let '(_,_,_,_,p) := bnd6 in p.
(* build_rule_set now returns a [result]; unwrap (monoid always succeeds). *)
Definition rs_dummy : rule_set positive positive trie_map trie_map :=
  @Defs.Build_rule_set positive positive trie_map trie_map map.empty [] [].
Definition rs_ac := Eval vm_compute in
  match PositiveInstantiation.build_rule_set 100 pr6 l6 with
  | Success rs => rs | Failure _ => rs_dummy end.

(* saturation: schedule weight = fuel (#run1iter), Defs fuel = 1, as in the
   string wrapper; mirrors that semantics on positive keys. *)
Definition sat_eq (fuel : nat) : bool :=
  let '(res, _, _) :=
    fst (PositiveInstantiation.egraph_equal l6 [(fuel, rs_ac)] 100 1 e1_6 e2_6 t6) in
  res.

Definition s_check := Eval vm_compute in sat_eq 6.
Print s_check.
Time Definition s1  := Eval vm_compute in sat_eq 1.
Time Definition s2  := Eval vm_compute in sat_eq 2.
Time Definition s3  := Eval vm_compute in sat_eq 3.
Time Definition s4  := Eval vm_compute in sat_eq 4.
Time Definition s5  := Eval vm_compute in sat_eq 5.
Time Definition s6  := Eval vm_compute in sat_eq 6.

(* ---- profiling a single (expensive) iteration ---- *)
(* pin the (option positive) depth analysis used by the positive engine,
   so run1iter doesn't default to the generic unit_analysis instance. *)
Definition an_pos : analysis positive positive (option positive) :=
  weighted_depth_analysis (fun _ => Some xH).

Arguments Defs.run1iter {idx}%_type_scope {Eqb_idx} idx_succ%_function_scope
  idx_zero {symbol}%_type_scope {symbol_map}%_function_scope symbol_map_plus
  {idx_map}%_function_scope idx_map_plus idx_trie%_function_scope {analysis_result}%_type_scope
  {H} spaced_list_intersect%_function_scope rebuild_fuel%_nat_scope rs _.

(* graph after 2 saturation iterations; the 3rd iteration is the expensive one *)
Definition g_pre :=
  Eval vm_compute in
    snd (PositiveInstantiation.egraph_equal l6 [(2%nat, rs_ac)] 100 1 e1_6 e2_6 t6).

(* DB size characterization: number of (symbol -> rows) and total rows *)
Definition db_nsyms := Eval vm_compute in List.length (map.tuples g_pre.(db)).
Print db_nsyms.
Definition db_nrows :=
  Eval vm_compute in
    List.fold_left (fun acc p => Nat.add acc (List.length (map.tuples (snd p))))
      (map.tuples g_pre.(db)) O.
Print db_nrows.

(* one full iteration (build_tries + join + writes + rebuild) *)
Time Definition oneiter :=
  Eval vm_compute in
    (Defs.run1iter Pos.succ xH ptree_map_plus ptree_map_plus
       (@FullPosTrie.full_pos_trie_map) (@fpt_spaced_intersect) (H:=an_pos) 100 rs_ac g_pre).

(* same but rebuild_fuel = 0 : build_tries + join + writes, NO rebuild *)
Time Definition oneiter_nr :=
  Eval vm_compute in
    (Defs.run1iter Pos.succ xH ptree_map_plus ptree_map_plus
       (@FullPosTrie.full_pos_trie_map) (@fpt_spaced_intersect) (H:=an_pos) 0 rs_ac g_pre).

(* build_tries alone *)
Time Definition bt :=
  Eval vm_compute in fst (Defs.build_tries _ _ _ _ _ _ _ _ _ rs_ac g_pre).

(* ---- isolate join vs rebuild ---- *)
(* state after the join phase (rebuild_fuel=0), before any rebuild *)
Definition g_join :=
  Eval vm_compute in
    snd (Defs.run1iter Pos.succ xH ptree_map_plus ptree_map_plus
           (@FullPosTrie.full_pos_trie_map) (@fpt_spaced_intersect) (H:=an_pos) 0 rs_ac g_pre).
Definition wl_len := Eval vm_compute in List.length g_join.(worklist).
Print wl_len.
Definition rows_after_join :=
  Eval vm_compute in
    List.fold_left (fun acc p => Nat.add acc (List.length (map.tuples (snd p))))
      (map.tuples g_join.(db)) O.
Print rows_after_join.
(* rebuild alone, applied to the post-join state *)
Time Definition rb :=
  Eval vm_compute in snd (Defs.rebuild (H:=an_pos) 100 g_join).

(* cost of one worklist_dedup pass over the worklist *)
Time Definition wd :=
  Eval vm_compute in List.length (@Defs.worklist_dedup _ _ g_join.(worklist)).
Print wd.

(* ---- split process_erule: JOIN (intersection) vs WRITES ---- *)
(* db_tries for g_pre is precomputed, so `jc` times only the intersection
   work across all rules/frontiers (no exec_write). Then
   writes ~= oneiter_nr - build_tries - jc. *)
Definition db_tries6 :=
  Eval vm_compute in fst (Defs.build_tries _ _ _ _ _ _ _ _ _ rs_ac g_pre).

Definition join_count : nat :=
  List.fold_left
    (fun (acc : nat) (r : Defs.erule positive positive) =>
       let qptrs := @Defs.query_clause_ptrs positive positive r in
       let qv := @Defs.query_vars positive positive r in
       let nclauses := List.length (uncurry cons qptrs) in
       List.fold_left
         (fun acc2 fn =>
            let fr := @Defs.idx_of_nat positive Pos.succ xH fn in
            let tries :=
              ne_map (@Defs.trie_of_clause positive _ positive trie_map trie_map
                        (@FullPosTrie.full_pos_trie_map) qv db_tries6 fr) qptrs in
            Nat.add acc2
              (List.length (@Defs.intersection_keys positive (@FullPosTrie.full_pos_trie_map)
                              (@fpt_spaced_intersect) tries)))
         (seq 0 nclauses) acc)
    (@Defs.compiled_rules positive positive trie_map trie_map rs_ac) O.

Time Definition jc := Eval vm_compute in join_count.
Print jc.

(* DISTINCT matches per rule (dedup assignments across all frontier choices).
   jc (total) >> jcd (distinct) would confirm semi-naive double-counting:
   the same match re-found (and re-written) once per new clause it contains. *)
Fixpoint dedup_assigns (l : list (list positive)) : list (list positive) :=
  match l with
  | [] => []
  | x :: xs =>
      let r := dedup_assigns xs in
      if List.existsb (eqb x) r then r else x :: r
  end.

Definition join_distinct : nat :=
  List.fold_left
    (fun (acc : nat) (r : Defs.erule positive positive) =>
       let qptrs := @Defs.query_clause_ptrs positive positive r in
       let qv := @Defs.query_vars positive positive r in
       let nclauses := List.length (uncurry cons qptrs) in
       let all_assigns :=
         List.flat_map
           (fun fn =>
              let fr := @Defs.idx_of_nat positive Pos.succ xH fn in
              let tries :=
                ne_map (@Defs.trie_of_clause positive _ positive trie_map trie_map
                          (@FullPosTrie.full_pos_trie_map) qv db_tries6 fr) qptrs in
              @Defs.intersection_keys positive (@FullPosTrie.full_pos_trie_map) (@fpt_spaced_intersect) tries)
           (seq 0 nclauses) in
       Nat.add acc (List.length (dedup_assigns all_assigns)))
    (@Defs.compiled_rules positive positive trie_map trie_map rs_ac) O.

Definition jcd := Eval vm_compute in join_distinct.
Print jcd.

(* ---- worklist_dedup scaling: confirm O(n^2) on positive keys ---- *)
(* post-join worklist for a given term depth n (the expensive 3rd iteration). *)
Definition gjoin_wl (n : nat) : list (Defs.worklist_entry positive) :=
  let '(l, e1, e2, t, pr) := pos_bundle n in
  let rs := match PositiveInstantiation.build_rule_set 100 pr l with
            | Success rs => rs | Failure _ => rs_dummy end in
  let gp := snd (PositiveInstantiation.egraph_equal l [(2%nat, rs)] 100 1 e1 e2 t) in
  (snd (Defs.run1iter Pos.succ xH ptree_map_plus ptree_map_plus
          (@FullPosTrie.full_pos_trie_map) (@fpt_spaced_intersect) (H:=an_pos) 0 rs gp)).(worklist).

Definition wl4 := Eval vm_compute in gjoin_wl 4.
Definition wl6 := Eval vm_compute in gjoin_wl 6.
Definition wl8 := Eval vm_compute in gjoin_wl 8.
Definition n4 := Eval vm_compute in List.length wl4. Print n4.
Definition n6 := Eval vm_compute in List.length wl6. Print n6.
Definition n8 := Eval vm_compute in List.length wl8. Print n8.
Time Definition wd4 := Eval vm_compute in List.length (@Defs.worklist_dedup _ _ wl4).
Time Definition wd6 := Eval vm_compute in List.length (@Defs.worklist_dedup _ _ wl6).
Time Definition wd8 := Eval vm_compute in List.length (@Defs.worklist_dedup _ _ wl8).

(* ---- build_rule_set scaling (per-call SETUP cost) ---- *)
Import Rule.
Definition opname (i : nat) : string := String.append "*" (nat_name i).
(* NB: lists are parenthesized as (con op ([...])) to avoid clashing with an
   `id [ _ ]` indexing notation brought in by the map imports. *)
Definition op_term_rule (i : nat) : string * rule string :=
  (opname i, term_rule [("b",Ssort);("a",Ssort)] ["a";"b"] Ssort).
Definition op_assoc_rule (i : nat) : string * rule string :=
  let op := opname i in
  (String.append "assoc" (nat_name i),
   term_eq_rule [("c",Ssort);("b",Ssort);("a",Ssort)]
     (con op ([con op ([var "a"; var "b"]); var "c"]))
     (con op ([var "a"; con op ([var "b"; var "c"])])) Ssort).
Definition op_comm_rule (i : nat) : string * rule string :=
  let op := opname i in
  (String.append "comm" (nat_name i),
   term_eq_rule [("b",Ssort);("a",Ssort)]
     (con op ([var "a"; var "b"])) (con op ([var "b"; var "a"])) Ssort).

Definition big_lang (n : nat) : lang string :=
  List.flat_map (fun i => [op_comm_rule i; op_assoc_rule i; op_term_rule i])
    (List.rev (seq 0 n))
  ++ [("S", sort_rule [] [])].

(* An EASY goal (a = a) on a realistic-sized language: should be setup-bound. *)
Definition easy (n : nat) : Result.result unit :=
  fst (egraph_reducing_equal' (big_lang n) filter_rules all_reversible no_inj
         100 100 100 100 [("a", Ssort)] (var "a") (var "a")).
Definition easy_check := Eval vm_compute in easy 20.
Print easy_check.
Time Definition e20 := Eval vm_compute in easy 20.
Time Definition e40 := Eval vm_compute in easy 40.

(* decompose setup: rename vs (positive) build_rule_set *)
From Pyrosome.Tools Require Import PosRenaming.
Definition l_str (n : nat) : lang string :=
  Defs.ctx_to_rules [("a", Ssort)] ++ big_lang n.
Definition rstate0 : PosRenaming.renaming string :=
  {| PosRenaming.p_to_v := map.empty;
     PosRenaming.v_to_p := [];
     PosRenaming.next_id := xO xH |}.
Definition lp40 := Eval vm_compute in fst (PosRenaming.rename_lang (l_str 40) rstate0).
Time Definition t_rename40 :=
  Eval vm_compute in fst (PosRenaming.rename_lang (l_str 40) rstate0).
Time Definition t_pbuild40 :=
  Eval vm_compute in
    PositiveInstantiation.build_rule_set 100
      (PositiveInstantiation.filter_eqn_rules lp40) lp40.
