Set Implicit Arguments.

(* ==========================================================================
   Injectivity-rule GENERATOR.

   Goal: automatically discover every *sound* rule of the shape

       f x1..xn = f y1..yn  ->  xi = yi  (for i in some subset S of positions)

   ("f is injective in the positions S").  Finding all such sound rules is
   undecidable, so we approximate with a bounded, e-graph-based counterexample
   search:

     1. Seed an e-graph with a generic instance of every constructor and with
        both sides of every equation of the language (context variables become
        fresh opaque generators).
     2. Saturate the *whole* language's equational theory for [X] iterations.
        This merges terms the theory proves equal -- in particular the two
        sides of associativity/unit laws, which is exactly where injectivity
        fails.
     3. Scan the resulting database.  Two atoms [f a1..an] and [f b1..bn] that
        landed in the *same* e-class (same canonical [atom_ret]) are equal
        terms.  If they disagree at position [i] (ai, bi in different classes)
        then [f]'s injectivity at [i] has a counterexample: position [i] is
        REFUTED.  A position never refuted (within [X] iterations) is a
        candidate injective position.

   The output is a [list (string * list string)] -- exactly the schema format
   consumed by [TypeInference.build_injection_rules].  A caller who likes the
   results can feed them straight into inference.

   NOTE ON SOUNDNESS: this is a heuristic.  A position reported injective might
   have a counterexample only beyond [X] iterations.  Per the design, using a
   too-strong injectivity rule never yields falsehood -- it can only make
   inference fail -- so the bounded approximation is safe to try.
   ========================================================================== *)

From coqutil Require Import Datatypes.String Map.Interface Datatypes.Result.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils EGraph.Defs Monad Lens UnionFind.
From Pyrosome Require Import Theory.Core
  Tools.Matches Tools.EGraph.Defs
  Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.PosRenaming.
From Utils.EGraph Require Import Semantics QueryOpt.
From Utils Require Import TrieMap PosListMap FullPosTrie FullPosTrieConv.
Import PArith.
Import Ascii.AsciiSyntax.
Import StringInstantiation.
Import StateMonad.

Local Notation named_list := (@named_list string).
Local Notation term := (@term string).
Local Notation ctx := (@ctx string).
Local Notation sort := (@sort string).
Local Notation rule := (@rule string).
Local Notation lang := (@lang string).

(* -------------------------------------------------------------------------
   The positive-index engine layer, paralleling [TypeInference.WithWeight].
   ------------------------------------------------------------------------- *)
Section WithWeight.
  Local Open Scope positive.

  Local Notation atom := (atom positive positive).
  Local Notation instance := (Defs.instance positive positive trie_map trie_map
                                (@FullPosTrie.full_pos_trie_map) (option positive)).
  Local Notation sequent := (sequent positive positive).
  Local Notation term := (@Term.term positive).
  Local Notation sort := (@Term.sort positive).
  Local Notation ctx := (@Term.ctx positive).
  Local Notation lang := (@Rule.lang positive).
  Local Notation sort_of := PosListMap.sort_of.

  Context (weight : atom -> option positive).

  Definition empty_egraph : instance :=
    Defs.empty_egraph (idx:=positive) (default:positive) (symbol:=positive)
      (symbol_map:=trie_map) (idx_map:=trie_map)
      (idx_trie:=(@FullPosTrie.full_pos_trie_map)) (option positive).

  (* with_sorts fixed to [true]; leaves [with_ctx_sorts], [sub], [e] open. *)
  Definition add_open_term (l : lang) :=
    Defs.add_open_term (V:=positive) (V_map:=trie_map) Pos.succ sort_of l
      (H:=weighted_size_analysis weight) true.

  Definition add_open_sort (l : lang) :=
    Defs.add_open_sort (V:=positive) (V_map:=trie_map) Pos.succ sort_of l
      (H:=weighted_size_analysis weight) true.

  (* Allocate a fresh opaque generator for each ctx var, returning the sub.
     [false false] = with_sorts / with_ctx_sorts, matching the query-side
     compilation in [rule_to_log_rule]. *)
  Definition add_ctx (l : lang) :=
    Defs.add_ctx (V:=positive) (V_map:=trie_map) Pos.succ sort_of l
      (H:=weighted_size_analysis weight) false false.

  (* Compile the rules in [rs] to sequents, using the FULL language [l] for
     lookups (so a filtered rule set still resolves sorts correctly). *)
  Definition compile_seqs (l rs : lang) : list sequent :=
    flat_map (fun '(n,r) =>
                match rule_to_log_rule trie_map _ Pos.succ sort_of l
                        (analysis_result:=unit) 1000%nat n r with
                | Result.Success s => [s]
                | Result.Failure _ => []
                end) rs.

  (* Only the EQUATIONS ([sort_eq_rule]/[term_eq_rule]).  The generative
     [sort_rule]/[term_rule] introduction rules are what make saturation explode
     -- they add [con n <every well-sorted arg tuple>], building terms without
     bound.  The equations, by contrast, only fire where their LHS pattern
     already occurs, so they PROPAGATE declared equalities (e.g. [conc emp G = G]
     at every occurrence of [conc emp _], including inside other rules' seeded
     terms) without generating fresh constructor applications.  This is the
     middle ground between full saturation and congruence-only. *)
  Definition is_eq_rule (r : Rule.rule positive) : bool :=
    match r with
    | sort_eq_rule _ _ _ => true
    | term_eq_rule _ _ _ _ => true
    | _ => false
    end.

  Definition eq_seqs (l : lang) : list sequent :=
    compile_seqs l (filter (fun '(_,r) => is_eq_rule r) l).

  (* [TypeInference.state_operation] with the iteration fuel exposed as [X] and
     the whole compiled rule set passed in. *)
  Definition saturate_gen (fuel : nat) (seqs : list sequent)
    : state instance bool :=
    @saturate_until positive Pos.eqb Pos.succ (default (A:=positive))
      Pos.leb
      positive trie_map ptree_map_plus trie_map ptree_map_plus
      (@FullPosTrie.full_pos_trie_map) (option positive)
      (weighted_size_analysis weight) (@fpt_spaced_intersect)
      1000%nat
      0%nat (* window *)
      (@QueryOpt.build_rule_set positive Pos.eqb Pos.succ (default (A:=positive))
         positive trie_map ptree_map_plus trie_map
         (@FullPosTrie.full_pos_trie_map) 1000%nat
         seqs)
      (Mret false) fuel.

  (* ---- seeding ---- *)

  (* One generic instance of each constructor, plus both sides of each equation,
     with the rule's context variables opened as fresh generators. *)
  Definition seed_rule (l : lang) (nr : positive * Rule.rule positive)
    : state instance unit :=
    let '(n,r) := nr in
    match r with
    | sort_rule c _ =>
        @! let sub <- add_ctx l c in
          let _ <- add_open_sort l false sub (scon n (id_args c)) in
          ret tt
    | term_rule c _ _ =>
        @! let sub <- add_ctx l c in
          let _ <- add_open_term l false sub (con n (id_args c)) in
          ret tt
    | sort_eq_rule c t1 t2 =>
        @! let sub <- add_ctx l c in
          let _ <- add_open_sort l false sub t1 in
          let _ <- add_open_sort l false sub t2 in
          ret tt
    | term_eq_rule c e1 e2 _ =>
        @! let sub <- add_ctx l c in
          let _ <- add_open_term l false sub e1 in
          let _ <- add_open_term l false sub e2 in
          ret tt
    end.

  Definition seed (l : lang) : state instance unit :=
    list_Miter (seed_rule l) l.

  (* Seed, then saturate for [fuel] iterations using the EQUATIONS ONLY.  No
     generative intro rules, so terms stay bounded by what the seed and the
     equations' RHSs reach; meanwhile every declared equality is instantiated
     wherever its LHS occurs, which reconciles argument terms with their normal
     forms.  Converges quickly (linear calc is stable by fuel 2). *)
  Definition run_eq (fuel : nat) (l : lang) : instance :=
    snd ((@! let _ <- seed l in
             let _ <- saturate_gen fuel (eq_seqs l) in
             ret tt) empty_egraph).

  (* ---- scanning the database for counterexamples ---- *)

  (* All atoms in the db as (fn, args, ret). *)
  Definition atom_triples (i : instance)
    : list (positive * list positive * positive) :=
    map.fold (fun acc fn tbl =>
                map.fold (fun acc2 args e =>
                            (fn, args, match e with {| entry_value := v |} => v end)
                              :: acc2)
                  acc tbl)
      [] i.(db).

  Definition canon (i : instance) (x : positive) : positive :=
    snd (UnionFind.find i.(equiv) x).

  (* Atoms with every id replaced by its canonical e-class rep. *)
  Definition catoms (i : instance)
    : list (positive * list positive * positive) :=
    map (fun '(fn,args,r) => (fn, map (canon i) args, canon i r))
      (atom_triples i).

End WithWeight.

(* -------------------------------------------------------------------------
   Pure counterexample analysis over canonicalized atoms.
   ------------------------------------------------------------------------- *)

(* Positions where two equal-length arg lists disagree (0-indexed). *)
Fixpoint diff_positions (refargs cargs : list positive) (pos : nat) : list nat :=
  match refargs, cargs with
  | r::refargs', c::cargs' =>
      if Pos.eqb r c then diff_positions refargs' cargs' (S pos)
      else pos :: diff_positions refargs' cargs' (S pos)
  | _, _ => []
  end.

Definition nat_inb (x : nat) (l : list nat) : bool := existsb (Nat.eqb x) l.

Definition nat_union (a b : list nat) : list nat :=
  fold_right (fun x acc => if nat_inb x acc then acc else x::acc) b a.

Definition key_eqb (k1 k2 : positive * positive) : bool :=
  let '(a,b) := k1 in let '(c,d) := k2 in andb (Pos.eqb a c) (Pos.eqb b d).

Fixpoint assoc_get {K V} (keyb : K -> K -> bool) (l : list (K*V)) (k : K)
  : option V :=
  match l with
  | [] => None
  | (k',v)::l' => if keyb k k' then Some v else assoc_get keyb l' k
  end.

(* Add refuted positions [dp] to fn's entry (union). *)
Fixpoint add_refuted (fn : positive) (dp : list nat)
  (refuted : list (positive * list nat)) : list (positive * list nat) :=
  match refuted with
  | [] => [(fn,dp)]
  | (fn',ps)::rest =>
      if Pos.eqb fn fn' then (fn', nat_union dp ps)::rest
      else (fn',ps)::add_refuted fn dp rest
  end.

(* Single pass: for each atom, compare against the first atom seen in its
   (fn,ret) group and record disagreements as refuted positions. *)
Fixpoint scan_pass (atoms : list (positive * list positive * positive))
  (seen : list ((positive*positive) * list positive))
  (refuted : list (positive * list nat)) : list (positive * list nat) :=
  match atoms with
  | [] => refuted
  | (fn,args,r)::rest =>
      let k := (fn,r) in
      match assoc_get key_eqb seen k with
      | None => scan_pass rest ((k,args)::seen) refuted
      | Some refargs =>
          scan_pass rest seen (add_refuted fn (diff_positions refargs args 0) refuted)
      end
  end.

(* Arity of each fn (from its first atom). *)
Fixpoint arities (atoms : list (positive * list positive * positive))
  (acc : list (positive * nat)) : list (positive * nat) :=
  match atoms with
  | [] => acc
  | (fn,args,_)::rest =>
      if existsb (fun '(f,_) => Pos.eqb f fn) acc
      then arities rest acc
      else arities rest ((fn, length args)::acc)
  end.

Fixpoint assoc_getp (l : list (positive * list nat)) (k : positive)
  : list nat :=
  match l with
  | [] => []
  | (k',v)::l' => if Pos.eqb k k' then v else assoc_getp l' k
  end.

(* -------------------------------------------------------------------------
   Functional-dependency discovery (generalizes the injectivity scan above).

   [scan_pass] answers one question per position: "do all same-class [f]-atoms
   agree at position [j]?" -- i.e. is [j] *unconditionally* determined by the
   e-class (injectivity).  That is the [S = []] case of the general question:

     for which sets [S] of argument positions is [j] determined *given* that the
     two atoms already agree on [S]?

   Formally, [j] functionally depends on [S] for [f] when no two [f]-atoms land
   in the same e-class (same [ret]) and agree on every position in [S] yet
   disagree at [j].  [S = []] is injectivity.  For a NON-injective operator this
   still finds the cancellation laws: [conc] is not injective (associativity
   [conc (conc A B) C = conc A (conc B C)] merges two [conc] atoms disagreeing in
   both args), but position [1] IS determined given agreement on position [0]
   ([conc Z A = conc Z B -> A = B], left cancellation) and symmetrically position
   [0] given [1] (right cancellation).  No operator is named or special-cased:
   cancellation drops out of the same search that yields injectivity.

   [fd_scan] is [scan_pass] with the shared positions [S] folded into the group
   key: atoms are keyed by [(ret, project args S)], so only atoms already
   agreeing on [S] are compared, and [j] is checked for constancy within each
   group.  Atoms MUST be pre-filtered to one head [f] (the key omits [f], and
   distinct heads may share e-class ids via cross-constructor equations). *)

(* project [args] onto the positions in [S] (0-indexed). *)
Definition proj_args (args : list positive) (S : list nat) : list positive :=
  map (fun i => nth i args 1%positive) S.

Fixpoint poslist_eqb (l1 l2 : list positive) : bool :=
  match l1, l2 with
  | [], [] => true
  | x::l1', y::l2' => andb (Pos.eqb x y) (poslist_eqb l1' l2')
  | _, _ => false
  end.

Definition fdkey_eqb (k1 k2 : positive * list positive) : bool :=
  andb (Pos.eqb (fst k1) (fst k2)) (poslist_eqb (snd k1) (snd k2)).

(* [true] iff position [j] is determined by shared positions [S] (no
   counterexample), scanning atoms of a single head. *)
Fixpoint fd_scan (As : list (list positive * positive)) (sh : list nat) (j : nat)
  (seen : list ((positive * list positive) * positive)) : bool :=
  match As with
  | [] => true
  | (args,r)::rest =>
      let k := (r, proj_args args sh) in
      let v := nth j args 1%positive in
      match assoc_get fdkey_eqb seen k with
      | None => fd_scan rest sh j ((k,v)::seen)
      | Some v' => if Pos.eqb v v' then fd_scan rest sh j seen else false
      end
  end.

Definition fd_holds (As : list (list positive * positive)) (sh : list nat) (j : nat)
  : bool := fd_scan As sh j [].

(* All subsets of [l], smallest-first is NOT guaranteed; we filter by size. *)
Fixpoint powerset (l : list nat) : list (list nat) :=
  match l with
  | [] => [ [] ]
  | x::l' => let ps := powerset l' in map (cons x) ps ++ ps
  end.

Fixpoint natlist_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x::l1', y::l2' => andb (Nat.eqb x y) (natlist_eqb l1' l2')
  | _, _ => false
  end.

(* Working shared-sets of MINIMAL size determining [j].  Smallest [S] first: an
   injective [j] yields [[[]]] (S=[], injectivity); a cancellative-only [j]
   yields the singleton(s) it is cancelled by.  Minimality keeps the emitted
   premise as weak as possible and drops the always-true "agree on everything
   else" tautologies. *)
Fixpoint first_working (sizes : list nat) (ps : list (list nat))
  (As : list (list positive * positive)) (j : nat) : list (list nat) :=
  match sizes with
  | [] => []
  | k::rest =>
      match filter (fun s => andb (Nat.eqb (length s) k) (fd_holds As s j)) ps with
      | [] => first_working rest ps As j
      | w => w
      end
  end.

Definition min_fd (As : list (list positive * positive)) (universe : list nat)
  (j : nat) : list (list nat) :=
  first_working (seq 0 (S (length universe))) (powerset universe) As j.

(* Group conclusion positions by their determining shared-set, so all positions
   sharing one premise become one multi-conclusion rule (matching the classic
   injectivity rule's shape when [S=[]]). *)
Fixpoint add_concl (sh : list nat) (j : nat) (acc : list (list nat * list nat))
  : list (list nat * list nat) :=
  match acc with
  | [] => [(sh, [j])]
  | (sh',js)::rest =>
      if natlist_eqb sh sh' then (sh', j::js)::rest
      else (sh',js)::add_concl sh j rest
  end.

(* All (shared-set, conclusion-positions) functional dependencies of one head of
   arity [n]. *)
Definition fdeps_of_fn (As : list (list positive * positive)) (n : nat)
  : list (list nat * list nat) :=
  fold_right
    (fun j acc =>
       let universe := filter (fun i => negb (Nat.eqb i j)) (seq 0 n) in
       fold_right (fun sh acc' => add_concl sh j acc') acc (min_fd As universe j))
    [] (seq 0 n).

(* Atoms of a single head, as (args, ret) pairs. *)
Definition fn_atoms (atoms : list (positive * list positive * positive))
  (fn : positive) : list (list positive * positive) :=
  fold_right (fun '(f,args,r) acc => if Pos.eqb f fn then (args,r)::acc else acc)
    [] atoms.

(* -------------------------------------------------------------------------
   String-facing driver.
   ------------------------------------------------------------------------- *)

(* trivial weight: extraction weight is irrelevant to the scan (we read the raw
   db, not extracted terms), so give every atom weight 1. *)
Definition triv_weight : atom positive positive -> option positive :=
  mk_weight (fun _ => false).

(* One constructor's finding: name, injective arg names, refuted arg names. *)
Record inj_finding := {
    if_name : string;
    if_injective : list string;
    if_refuted : list string
  }.

(* Look up a constructor by name and return its full context arg names, in order. *)
Definition ctx_arg_names (L : lang) (name : string) : option (list string) :=
  match Find_x name L with
  | Some r => Some (map fst (get_ctx r))
  | None => None
  end.

Definition nth_names (names : list string) (positions : list nat) : list string :=
  map (fun p => nth p names "?") positions.

(* Core analysis given a saturated/closed graph and the renaming. *)
Definition findings_of (g : Defs.instance positive positive trie_map trie_map
                              (@FullPosTrie.full_pos_trie_map) (option positive))
  (rn : renaming string) (L : lang) : list inj_finding :=
  let atoms := catoms g in
  let refuted := scan_pass atoms [] [] in
  let ars := arities atoms [] in
  flat_map
    (fun '(fn, ar) =>
       if Pos.eqb fn 1%positive (* sort_of *) then []
       else
         let name := of_p rn fn in
         match ctx_arg_names L name with
         | None => []
         | Some names =>
             let ref_ps := assoc_getp refuted fn in
             let all_ps := seq 0 ar in
             let inj_ps := filter (fun p => negb (nat_inb p ref_ps)) all_ps in
             [ {| if_name := name;
                  if_injective := nth_names names inj_ps;
                  if_refuted := nth_names names (filter (fun p => nat_inb p ref_ps) all_ps) |} ]
         end)
    ars.

(* ---- entry point ----

   [findings X] / [gen_schemas X]: saturate the EQUATIONS for [X] iterations (no
   generative intro rules), then scan.  Bounded (terms don't grow without limit)
   yet propagates declared equalities to every occurrence, so argument terms get
   identified with their normal forms.  [X = 2] suffices for the linear calculus
   (stable at higher [X]). *)

Definition findings (X : nat) (L : lang) : list inj_finding :=
  let '(l_pos, rn) := rename_lang L init_renaming in
  findings_of (run_eq triv_weight X l_pos) rn L.

(* Keep only constructors with at least one injective argument, as a schema
   list ready for [TypeInference.build_injection_rules]. *)
Definition schemas_of (fs : list inj_finding) : list (string * list string) :=
  map (fun f => (f.(if_name), f.(if_injective)))
    (filter (fun f => match f.(if_injective) with [] => false | _ => true end) fs).

Definition gen_schemas (X : nat) (L : lang) : list (string * list string) :=
  schemas_of (findings X L).

(* ---- general functional-dependency schema generator ----

   The full generalization of [gen_schemas].  Instead of a single injective-arg
   list per constructor, each schema is [(name, (shared, concl))]: two [name]
   atoms in the same e-class that agree on the [shared] args are forced to agree
   on the [concl] args.  [shared = []] is injectivity (exactly what [gen_schemas]
   produced); [shared <> []] is cancellation.  Both come out of the one
   [fdeps_of_fn] search -- no operator is special-cased, and no cancellation
   template is hand-written.  For the linear calculus this yields the injectivity
   rules AND [conc]'s cancellation laws automatically.

   These feed [build_general_injection_rules] (below).  Sound to try, for the
   same reason as the injectivity schemas: a spuriously-discovered dependency can
   only over-merge during inference and make it fail (which [compute_wf_lang]
   then catches), never produce a false theorem. *)
Definition fundep_schemas_of
  (g : Defs.instance positive positive trie_map trie_map
         (@FullPosTrie.full_pos_trie_map) (option positive))
  (rn : renaming string) (L : lang)
  : list (string * (list string * list string)) :=
  let atoms := catoms g in
  let ars := arities atoms [] in
  flat_map
    (fun '(fn, ar) =>
       if Pos.eqb fn 1%positive (* sort_of *) then []
       else
         let name := of_p rn fn in
         match ctx_arg_names L name with
         | None => []
         | Some names =>
             let As := fn_atoms atoms fn in
             map (fun '(sh, js) => (name, (nth_names names sh, nth_names names js)))
               (fdeps_of_fn As ar)
         end)
    ars.

Definition gen_fundep_schemas (X : nat) (L : lang)
  : list (string * (list string * list string)) :=
  let '(l_pos, rn) := rename_lang L init_renaming in
  fundep_schemas_of (run_eq triv_weight X l_pos) rn L.

(* ---- general injection/cancellation rule builder ----

   The functional-dependency generalization of
   [TypeInference.injection_rule_from_name_and_rule].  A schema names a set of
   [shared] argument positions (identified across the two atoms) and a set of
   [concl] positions (equalized in the conclusion):

     f a[shared],x1.. = r,  f a[shared],y1.. = r  |-  x_j = y_j  (j in concl)

   [shared = []] gives the ordinary injectivity/congruence rule (its output then
   coincides with [injection_rule_from_name_and_rule]).  [shared] nonempty gives
   a cancellation rule: [shared=["G"]], [concl=["H"]] on [conc] yields
   [conc G H1 = conc G H2 -> H1 = H2] (left cancellation).  A shared argument
   keeps its bare name in both atoms (forcing them equal in the pattern); a
   non-shared argument is suffixed [1]/[2].  [shared] and [concl] are disjoint by
   construction. *)
Definition injection_side (context : ctx) (shared : list string) (suffix : string)
  : list string :=
  map (fun x => if inb (fst x) shared then fst x else (fst x ++ suffix)%string) context.

Definition general_injection_rule (name : string) (shared concl : list string)
  (r : rule) : sequent string string :=
  let ret_name := (name ++ " cong_ret")%string in
  let context := get_ctx r in
  {|
    seq_assumptions :=
      [atom_clause (Build_atom name (injection_side context shared "1") ret_name);
       atom_clause (Build_atom name (injection_side context shared "2") ret_name)];
    seq_conclusions := map (fun nm => eq_clause (nm ++ "1")%string (nm ++ "2")%string) concl
  |}.

Definition build_general_injection_rule (L : lang)
  (schema : string * (list string * list string)) : sequent string string :=
  let '(name, (shared, concl)) := schema in
  match Find_x name L with
  | Some r => general_injection_rule name shared concl r
  | None => Build_sequent _ _ default default
  end.

Definition build_general_injection_rules
  (schemas : list (string * (list string * list string))) (L : lang)
  : list (sequent string string) :=
  map (build_general_injection_rule L) schemas.

(* debug: canonical (args, ret) e-class ids of every atom whose head prints as
   [nm], from the equation-saturated graph.  Two rows with the same [ret] but
   different [args] are a merge; where they differ is a refuted position. *)
Definition dump_head (X : nat) (nm : string) (L : lang) : list (list nat * nat) :=
  let '(l_pos, rn) := rename_lang L init_renaming in
  let g := run_eq triv_weight X l_pos in
  map (fun '(_,args,r) => (map Pos.to_nat args, Pos.to_nat r))
    (filter (fun '(fn,_,_) => String.eqb (of_p rn fn) nm) (catoms g)).
