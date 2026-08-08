(* Phase-0 measurement gate for INCREMENTAL TRIES.

   Question: is build_tries a MATERIAL fraction of an EXPENSIVE saturation
   iteration on a REAL Pyrosome /Lang language?

   Finding so far: assoc-only on value_subst is inherently O(n^2) (confluent, no
   blow-up) so it is never an expensive iteration.  Real expensive iterations
   come from substitution-pushing / e-class cross-product blow-up.  So here we
   drive a real SUBSTITUTION-HEAVY goal: the CPS `pm_pair` reduction
     pm_pair (pair v1 v2) e  =  blk_subst (snoc (snoc id v1) v2) e
   on the real CPS target language (cps_lang ++ block_subst ++ value_subst),
   whose RHS triggers the subst-pushing equations.  We run the SAME two-rule-set
   reducing schedule egraph_equal' uses, capture the e-graph after k forward
   rounds, and isolate build_tries (`bt`) vs a full iteration (`oneiter`).

   Decision rule: build_tries < ~15-20% of oneiter on the heaviest round => STOP.

   ============================ FINDINGS (GATE FAILED) ============================
   Full fix_cps stack (48 query clauses), cmp-chain workload, positive, vm_compute.
   build_tries amplified x200 (window-varied) to clear the 1ms timer floor.

     N    rows   build_tries/call   oneiter   oneiter_nr(no rebuild)   bt fraction
     30    271      0.41 ms           50 ms          45 ms               ~0.8%
     50    451      1.10 ms          113 ms          87 ms               ~1.0%

   build_tries is ~1% of an iteration at every real-language scale tested, and
   its fraction grows only ~0.8%->1.0% as rows go 271->451.  The dominant costs:
     - process_erule (join + exec_write):  ~75-85% of each iteration
     - rebuild (congruence repair):        ~14-23% (grows with the worklist)
     - build_tries (the recomputed tries): ~1%
   => Incrementally maintaining the tries can save at most ~1%, nowhere near the
      "substantial speedup" bar.  Phase 1-3 NOT worth doing.  The real levers are
      exec_write per-match cost (Defs.v exec_write TODO: redundant prealloc +
      per-match map.of_list rebuild) and rebuild, plus end-to-end setup
      (build_rule_set is computed twice per goal).  See WIP/incremental_tries_design.md.

   NOTE: s_check prints false here only because this harness uses egraph_equal
   (whose eq_proven needs sort_of, but sort rules are filtered out); the real
   compiler uses egraph_reducing_equal (extraction-based).  The captured g3/g5
   ARE real forward-saturation states (the cmp/assoc rules fire; rows grow), so
   the build_tries-vs-oneiter ratio measured on them is valid.
   ================================================================================ *)
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
From Pyrosome.Tools Require Import PosRenaming.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS.
Import PosListMap.
Open Scope nat_scope.

Instance bench_analysis : analysis string string (option positive) :=
  weighted_size_analysis (fun _ => Some xH).

(* FULL fix_cps target stack (the real DiagFixCPSReal target language). *)
Definition L : lang :=
  fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst.

(* Large cmp-chain goal in value_subst (cmp/id form a monoid): saturates to
   O(N^2) rows, giving a big DB for reliable timing, while L's 43 clauses give a
   realistic build_tries inner-loop width. *)
Definition N := 30%nat.
Fixpoint nat_name (i : nat) : string :=
  match i with O => "" | S j => String.append "z" (nat_name j) end.
Definition envname (i : nat) : string := String.append "G" (nat_name i).
Definition subname (i : nat) : string := String.append "f" (nat_name i).
Fixpoint env_ctx (n : nat) : ctx :=
  match n with
  | 0 => [(envname 0, {{s #"env"}})]
  | S i => (envname (S i), {{s #"env"}}) :: env_ctx i
  end.
Fixpoint sub_ctx (n : nat) : ctx :=
  match n with
  | 0 => []
  | S i => (subname (S i), {{s #"sub" {var (envname i)} {var (envname (S i))} }}) :: sub_ctx i
  end.
Definition c_goal : ctx := sub_ctx N ++ env_ctx N.
Fixpoint left_chain (n : nat) : term :=
  match n with
  | 0 => var (subname 1)
  | 1 => var (subname 1)
  | S i => {{e #"cmp" {left_chain i} {var (subname (S i))} }}
  end.
Fixpoint right_chain (lo n : nat) : term :=
  match n with
  | 0 => var (subname lo)
  | 1 => var (subname lo)
  | S i => {{e #"cmp" {var (subname lo)} {right_chain (S lo) i} }}
  end.
Definition e1_goal : term := left_chain N.
Definition e2_goal : term := right_chain 1 N.
Definition t_goal  : sort := {{s #"sub" {var (envname 0)} {var (envname N)} }}.

Definition filter_rules : string * Rule.rule string -> bool :=
  (fun '(_, r) => match r with
                  | Rule.term_rule _ _ _ | Rule.sort_rule _ _ => false
                  | _ => true end).
Definition all_reversible : string * Rule.rule string -> bool := fun _ => true.

Definition pos_bundle :=
  let c := c_goal in
  let rev_rules := named_map rev_rule
                     (filter (fun p => all_reversible p && filter_rules p) L) in
  let m : state (PosRenaming.renaming string) _ :=
    @! let l'  <- PosRenaming.rename_lang (ctx_to_rules c ++ L) in
       let e1' <- PosRenaming.rename_term (var_to_con e1_goal) in
       let e2' <- PosRenaming.rename_term (var_to_con e2_goal) in
       let t'  <- PosRenaming.rename_sort (sort_var_to_con t_goal) in
       let fwd <- PosRenaming.rename_lang (ctx_to_rules c ++ filter filter_rules L) in
       let rev <- PosRenaming.rename_lang (ctx_to_rules c ++ rev_rules) in
       ret (l', e1', e2', t', fwd, rev)
  in
  fst (m {| PosRenaming.p_to_v := map.empty;
            PosRenaming.v_to_p := [];
            PosRenaming.next_id := xO xH |}).

Definition rs_dummy : rule_set positive positive trie_map trie_map :=
  @Defs.Build_rule_set positive positive trie_map trie_map map.empty [] [].
Definition unwrap_rs (r : Result.result (rule_set positive positive trie_map trie_map)) :=
  match r with Success rs => rs | Failure _ => rs_dummy end.

Definition pack := Eval vm_compute in pos_bundle.
Definition lP   := Eval vm_compute in let '(l,_,_,_,_,_) := pack in l.
Definition e1P  := Eval vm_compute in let '(_,e,_,_,_,_) := pack in e.
Definition e2P  := Eval vm_compute in let '(_,_,e,_,_,_) := pack in e.
Definition tP   := Eval vm_compute in let '(_,_,_,t,_,_) := pack in t.
Definition fwdP := Eval vm_compute in let '(_,_,_,_,f,_) := pack in f.
Definition revP := Eval vm_compute in let '(_,_,_,_,_,r) := pack in r.
Definition rsR  := Eval vm_compute in unwrap_rs (PositiveInstantiation.build_rule_set 100 fwdP lP).
Definition rsRR := Eval vm_compute in unwrap_rs (PositiveInstantiation.build_rule_set 100 revP lP).
Definition schedP := [(10%nat, rsR); (1%nat, rsRR)].

(* clause count of the forward rule_set (build_tries inner-loop multiplier). *)
Definition n_clauses :=
  Eval vm_compute in
    List.fold_left
      (fun acc p => Nat.add acc (List.length (map.tuples (snd p))))
      (map.tuples (@Defs.query_clauses positive positive trie_map trie_map rsR)) O.
Print n_clauses.

(* sanity: does the reducing schedule solve this goal? *)
Definition s_check :=
  Eval vm_compute in
    let '(res, _, _) := fst (PositiveInstantiation.egraph_equal lP schedP 100 1 e1P e2P tP) in res.
Print s_check.

Definition an_pos : analysis positive positive (option positive) :=
  weighted_size_analysis (fun _ => Some xH).

Arguments Defs.run1iter {idx}%_type_scope {Eqb_idx} idx_succ%_function_scope
  idx_zero idx_leb%_function_scope {symbol}%_type_scope {symbol_map}%_function_scope symbol_map_plus
  {idx_map}%_function_scope idx_map_plus idx_trie%_function_scope {analysis_result}%_type_scope
  {H} spaced_list_intersect%_function_scope rebuild_fuel%_nat_scope window%_nat_scope rs _.
Arguments Defs.build_tries {idx}%_type_scope {Eqb_idx} idx_succ%_function_scope
  idx_leb%_function_scope {symbol}%_type_scope {symbol_map}%_function_scope symbol_map_plus
  {idx_map}%_function_scope idx_map_plus idx_trie%_function_scope {analysis_result}%_type_scope
  window%_nat_scope q _.

(* state after k forward rounds *)
Definition g_at (k : nat) :=
  snd (PositiveInstantiation.egraph_equal lP [(k, rsR)] 100 1 e1P e2P tP).

Definition g3 := Eval vm_compute in g_at 3.
Definition g5 := Eval vm_compute in g_at 5.
Definition rows3 := Eval vm_compute in
  List.fold_left (fun acc p => Nat.add acc (List.length (map.tuples (snd p))))
    (map.tuples g3.(db)) O. Print rows3.
Definition rows5 := Eval vm_compute in
  List.fold_left (fun acc p => Nat.add acc (List.length (map.tuples (snd p))))
    (map.tuples g5.(db)) O. Print rows5.


(* ===== RELIABLE decomposition: the REAL run1iter only (no external build_tries
   replication; an isolated build_tries call mis-wires the map instances and
   yields empty tries -- the run1iter path uses the correct internal wiring). ===== *)

Definition g1 := Eval vm_compute in g_at 1.
Definition g2 := Eval vm_compute in g_at 2.
Definition rows_of (g : instance positive positive trie_map trie_map
                         (@FullPosTrie.full_pos_trie_map) (option positive)) : nat :=
  List.fold_left (fun acc p => Nat.add acc (List.length (map.tuples (snd p))))
    (map.tuples g.(db)) O.
Definition rows1 := Eval vm_compute in rows_of g1. Print rows1.
Definition rows2 := Eval vm_compute in rows_of g2. Print rows2.

(* run1iter, rebuild OFF, parameterized by window + rule_set. *)
Definition run1nr (w : nat) (rs : rule_set positive positive trie_map trie_map)
  (g : instance positive positive trie_map trie_map
         (@FullPosTrie.full_pos_trie_map) (option positive)) :=
  Defs.run1iter Pos.succ xH Pos.leb ptree_map_plus ptree_map_plus
    (@FullPosTrie.full_pos_trie_map) (@fpt_spaced_intersect) (H:=an_pos) 0 w rs g.

(* rsR with NO rules: build_tries runs in full, process_erule does nothing. *)
Definition rsR_nb : rule_set positive positive trie_map trie_map :=
  @Defs.Build_rule_set positive positive trie_map trie_map
    (@Defs.query_clauses positive positive trie_map trie_map rsR)
    []
    (@Defs.compiled_const_rules positive positive trie_map trie_map rsR).

(* amplify x40, varying window (defeats CSE, same scan cost); sum row counts to
   force full evaluation of run1iter (incl. its internal build_tries). *)
Definition amp (rs : rule_set positive positive trie_map trie_map)
  (g : instance positive positive trie_map trie_map
         (@FullPosTrie.full_pos_trie_map) (option positive)) (k : nat) : nat :=
  List.fold_left
    (fun acc w => Nat.add acc (rows_of (snd (run1nr w rs g)))) (seq 0 k) O.

(* per-state: build_tries-only (rsR_nb) vs build_tries+process_erule (rsR), x40 *)
Time Definition bt_g1 := Eval vm_compute in amp rsR_nb g1 40.
Time Definition pe_g1 := Eval vm_compute in amp rsR    g1 40.
Time Definition bt_g2 := Eval vm_compute in amp rsR_nb g2 40.
Time Definition pe_g2 := Eval vm_compute in amp rsR    g2 40.
Time Definition bt_g3 := Eval vm_compute in amp rsR_nb g3 40.
Time Definition pe_g3 := Eval vm_compute in amp rsR    g3 40.
Time Definition bt_g5 := Eval vm_compute in amp rsR_nb g5 40.
Time Definition pe_g5 := Eval vm_compute in amp rsR    g5 40.

(* =================== MEASUREMENT POSTMORTEM (read this) ===================
   vm_compute Eval-timing CANNOT reliably decompose run1iter into
   build_tries / process_erule / rebuild here.  Two artifacts corrupt it:

   1. Dead-code elimination: when build_tries' output (the tries) is discarded
      (e.g. run1iter with compiled_rules = []), or when a result feeds only into
      a discarded position, vm_compute does NOT evaluate the work -> times look
      ~0 (the bogus "build_tries = 0.4ms / 1%" figure came from this: an
      isolated build_tries call whose output was an empty/DCE'd structure).

   2. Output normalization: when the run1iter result IS forced
      (Eval vm_compute in oneiter g), the ~45ms measured is dominated by
      vm_compute NORMALIZING the ~271-row output instance (its db tries), NOT by
      the computation of interest.  Proof: oneiter with REAL query_clauses
      (full build_tries scan) ~= oneiter with EMPTY query_clauses (no scan) ~=
      45ms.  If the scan cost 45ms the empty version would be ~0.  It isn't.

   The ONLY trustworthy vm_compute number is END-TO-END with a small (discarded-
   instance) result:  fst (egraph_equal ...) -> the whole solve of this goal is
   ~14ms, and it is FLAT across schedule weights 2..12 (egraph_equal short-
   circuits at fixpoint).  This synthetic cmp-chain goal is simply too cheap --
   and its reduction rules do not even fire here (s_check=false; rows never grow
   past the 271 of the initial terms) -- to exhibit ANY phase as a bottleneck.

   CONCLUSION: neither the "build_tries ~1%" gate nor the "process_erule
   75-85%" breakdown is trustworthy.  Per-phase cost on a REAL slow workload
   must be measured with SOURCE-LEVEL timers in run1iter (or OCaml-extraction
   profiling), not vm_compute Eval-timing.  See WIP/incremental_tries_design.md.
   ========================================================================= *)
