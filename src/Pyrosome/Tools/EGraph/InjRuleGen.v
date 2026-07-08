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
From Pyrosome Require Import Theory.Core Elab.PreRule
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

  (* [TypeInference.state_operation] with the iteration fuel exposed as [X], the
     semi-naive look-back [window] exposed, and the whole compiled rule set passed
     in.  [window] is used only by the FIRST saturation iteration (the cross-phase
     catch-up): it re-matches every db row whose epoch is within [window] ticks of
     the current epoch.  For a FRESH graph (everything seeded at one epoch)
     [window = 0] suffices; for an INCREMENTAL resume on an already-saturated graph
     (new atoms at the current epoch, old atoms many epochs back) a [window] large
     enough to reach back over all prior epochs re-matches the equations against
     the whole graph, exactly as a from-scratch saturation would. *)
  Definition saturate_gen_win (window fuel : nat) (seqs : list sequent)
    : state instance bool :=
    @saturate_until positive Pos.eqb Pos.succ (default (A:=positive))
      Pos.leb
      positive trie_map ptree_map_plus trie_map ptree_map_plus
      (@FullPosTrie.full_pos_trie_map) (option positive)
      (weighted_size_analysis weight) (@fpt_spaced_intersect)
      1000%nat
      window
      (@QueryOpt.build_rule_set positive Pos.eqb Pos.succ (default (A:=positive))
         positive trie_map ptree_map_plus trie_map
         (@FullPosTrie.full_pos_trie_map) 1000%nat
         seqs)
      (Mret false) fuel.

  Definition saturate_gen (fuel : nat) (seqs : list sequent)
    : state instance bool := saturate_gen_win 0 fuel seqs.

  (* ---- seeding ---- *)

  (* Variables occurring in the sorts of a context.  A position is FREE if its
     variable occurs in NO context sort -- i.e. nothing else's type depends on
     it.  Only free positions are safe to vary independently (below): varying a
     DEPENDENT index (e.g. [cmp]'s object [G1], which [f : arr G1 G2] fixes)
     would build an ill-typed variant, whose e-graph collapse the scan misreads
     as a counterexample and SPURIOUSLY refutes the index's injectivity. *)
  Fixpoint term_fvs (e : term) : list positive :=
    match e with var x => [x] | con _ s => flat_map term_fvs s end.
  Definition sort_fvs (t : sort) : list positive :=
    match t with scon _ s => flat_map term_fvs s end.
  Definition free_positions (c : ctx) : ctx :=
    let fvs := flat_map (fun '(_,t) => sort_fvs t) c in
    filter (fun '(p,_) => negb (existsb (Pos.eqb p) fvs)) c.

  (* Fresh-name offset for the same-sort duplicate of each context variable.
     Duplicates go FIRST: [add_ctx] is a right fold ([list_Mfoldr]), so it runs
     tail-first; putting the originals LAST means they are processed BEFORE the
     duplicates, so each duplicate's sort (which references the ORIGINAL vars)
     resolves against an already-populated substitution.  With the originals
     first, the duplicates would be processed before their referenced originals
     exist and get the [default] sort -- seeding an ill-sorted term that merges
     unsoundly and drops valid injectivity laws. *)
  Definition seed_BIG : positive := 1000000.
  Definition dup_ctx (c : ctx) : ctx :=
    map (fun '(p,t) => ((p + seed_BIG)%positive, t)) c ++ c.

  (* Seed both sides of an equation under the base instance PLUS, for each FREE
     position, a variant sharing every generator with the base except that one,
     which it swaps to the position's (same-sort) duplicate.  Two applications
     of a head differing only in an argument the head DROPS then collapse to one
     e-class, so the scan refutes that position -- the counterexample generic
     single-instance seeding never builds (e.g. [.1 (pair g v1) = .1 (pair g
     v2) = g], projection).  Restricting to free positions keeps every variant
     well-typed, so sort-index injectivity (which inference relies on) is
     preserved. *)
  Definition seed_eq {T} (l : lang) (c : ctx)
    (add : bool -> list (positive * positive) -> T -> state instance positive)
    (e1 e2 : T) : state instance unit :=
    @! let subA <- add_ctx l (dup_ctx c) in
       let _ <- add false subA e1 in
       let _ <- add false subA e2 in
       let _ <- list_Miter (fun '(pi,_) =>
                  let gdup := named_list_lookup default subA (pi + seed_BIG)%positive in
                  let subi := map (fun '(k,v) =>
                                if Pos.eqb k pi then (k, gdup) else (k,v)) subA in
                  @! let _ <- add false subi e1 in
                     let _ <- add false subi e2 in
                     ret tt)
                  (free_positions c) in
       ret tt.

  (* One generic instance of each constructor; for each equation, a base
     instance plus same-sort free-position variants (see [seed_eq]). *)
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
        seed_eq l c (add_open_sort l) t1 t2
    | term_eq_rule c e1 e2 _ =>
        seed_eq l c (add_open_term l) e1 e2
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
   Structural recoverability filter.

   The counterexample search below declares an argument injective when no
   equation MERGES two differently-shaped applications of a head within the fuel
   bound.  That is a completeness heuristic, and it MISSES purely extensional
   non-injectivity.  The motivating case is a closure

     #"closure" "B" "e" "v" : #"val" "G" (#"neg" "B")      "v" : #"val" "G" "A"

   which captures an environment [v] whose type [A] is EXISTENTIALLY HIDDEN from
   the result sort [#"val" "G" (#"neg" "B")].  Two closures with different
   environments but a CONSTANT body (a body that ignores its environment) are
   equal, so [closure] is not injective in [v] -- nor in the body [e], whose
   sort [#"blk" (#"ext" #"emp" (#"prod" "A" "B"))] also mentions [A].  But no
   single declared equation merges two differently-environmented closures (the
   collapse is extensional / eta-driven), so the saturation search never refutes
   these positions and wrongly reports [closure] fully injective.

   The fix is structural and language-agnostic: the injectivity/congruence rule

     f x1..xn = f y1..yn  ->  xi = yi

   is only WELL-FORMED when its conclusion is well-sorted, i.e. when the sort of
   argument [i] is pinned down by what the two (equal) applications already
   share.  Equal applications share their result sort, so its free variables are
   determined; a cancellation premise additionally holds the [shared] arguments
   equal, determining their sorts' free variables too.  If [xi]'s sort mentions
   a variable determined by NONE of these, then [xi] and [yi] need not inhabit a
   common sort and the equation [xi = yi] cannot even be stated -- so position
   [i] is dropped.  This refutes [closure]'s environment/body injectivity from
   the rule structure alone (matching, and for [jmp] reproducing, the
   hand-written injectivity lists), and it can never drop a genuinely-formable
   law: a dropped position provably has no well-sorted injectivity conclusion.
   Sound to apply for the same reason as the search: it only ever REMOVES
   candidate injective positions, so a downstream congruence decomposition stays
   sound (fewer decompositions) and elaboration stays conservative. *)

Fixpoint sterm_fvs (e : term) : list string :=
  match e with
  | var x => [x]
  | con _ s => flat_map sterm_fvs s
  end.
Definition ssort_fvs (t : sort) : list string :=
  match t with scon _ s => flat_map sterm_fvs s end.

Definition name_inb (x : string) (l : list string) : bool :=
  existsb (String.eqb x) l.

(* Free variables whose value is DETERMINED when two equal applications of
   [name] additionally hold the [shared] arguments equal: the free vars of the
   (shared) result sort, plus the free vars of each shared argument's sort. *)
Definition determined_vars (c : ctx) (res : sort) (shared : list string)
  : list string :=
  ssort_fvs res
    ++ flat_map (fun '(x,t) => if name_inb x shared then ssort_fvs t else []) c.

(* Keep only those [concl] argument names whose injectivity conclusion
   [x1 = x2] is well-sorted: every free variable of the argument's sort is
   determined.  Sort constructors (no term-level result sort) and unknown heads
   are left untouched. *)
Definition filter_recoverable (L : lang) (name : string)
  (shared concl : list string) : list string :=
  match Find_x name L with
  | Some (term_rule c _ res) =>
      let det := determined_vars c res shared in
      filter (fun nm =>
                match Find_x nm c with
                | Some t => forallb (fun v => name_inb v det) (ssort_fvs t)
                | None => true
                end) concl
  | _ => concl
  end.

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
             (* search-injective positions, further restricted to those whose
                injectivity conclusion is well-sorted (structural recoverability;
                see [filter_recoverable]) -- this drops e.g. a closure's captured
                environment, whose type is hidden from the result sort *)
             let inj_names :=
               filter_recoverable L name [] (nth_names names inj_ps) in
             [ {| if_name := name;
                  if_injective := inj_names;
                  if_refuted :=
                    filter (fun nm => negb (name_inb nm inj_names)) names |} ]
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

(* ---- reduction-engine schema table ----

   The REDUCTION engine ([Automation.by_reduction'] -> [Defs.egraph_reducing_cong]
   -> [Defs.cong_subgoals]) consumes a flat [list (string * list (list string))]:
   per operator, a LIST of alternative recursed-arg sets.  [gen_fundep_schemas]
   already yields (name,(shared,concl)) dependencies; for the reduction engine
   only the [concl] positions matter -- [cong_subgoals] forces every non-recursed
   arg syntactically equal, which subsumes the [shared] premise (all >= shared).
   So we drop [shared], drop empty conclusions (they decompose nothing), and
   group the conclusion-sets by operator name.  This is the reduction-engine
   analogue of [build_general_injection_rules] for the elaboration engine. *)
Fixpoint group_concls (fds : list (string * (list string * list string)))
  : list (string * list (list string)) :=
  match fds with
  | [] => []
  | (n,(_shared,concl)) :: rest =>
      let g := group_concls rest in
      match concl with
      | [] => g  (* empty conclusion carries no decomposition *)
      | _ =>
          let fix ins g :=
            match g with
            | [] => [(n,[concl])]
            | (n',alts)::g' =>
                if eqb n n'
                then (n', if existsb (eqb concl) alts then alts else alts ++ [concl]) :: g'
                else (n',alts) :: ins g'
            end in
          ins g
      end
  end.

(* Generate the reduction-engine injectivity/cancellation table from a language:
   saturate the equations for [X] iterations, read off the functional
   dependencies, keep the conclusion-sets grouped by operator. *)
Definition gen_reduce_inj_rules (X : nat) (L : lang)
  : list (string * list (list string)) :=
  group_concls
    (map (fun '(name, (shared, concl)) =>
            (name, (shared, filter_recoverable L name shared concl)))
       (gen_fundep_schemas X L)).

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

(* -------------------------------------------------------------------------
   Incremental generation FUSED with type inference.

   The separated pipeline ([gen_fundep_schemas] on an elaborated language, then
   [infer_lang_ext_simple_gen] using the schemas) has a chicken-and-egg gap: the
   generator needs an ELABORATED language, but the schemas are what let us
   ELABORATE it -- so a language's own rules cannot contribute to the injectivity
   facts used to elaborate itself.  Here we close the loop by threading the
   injectivity e-graph THROUGH inference: as each rule is elaborated, its
   injectivity/cancellation schemas are read off the current injectivity e-graph
   (base + everything elaborated so far), then the freshly elaborated rule is
   seeded into that e-graph and it is re-saturated, so later rules see it.

   This is strictly more expressive than the separated version AND better-scoped:
   rule [k] is elaborated using exactly the equational theory of the rules in
   scope for [k] (base + rules 1..k-1), never a later rule's equation.

   The threaded state is [(g, rn, lp)]: the positive injectivity e-graph [g], the
   string<->positive renaming [rn] (grown as new constructors appear), and the
   accumulated positive elaborated language [lp] (needed to seed new atoms and to
   recompile the equation rule-set).  Everything else reuses the existing pieces:
   [fundep_schemas_of] reads schemas off [g]; [infer_rule_gen] elaborates one
   rule; [seed_rule]+[saturate_gen_win] add the elaborated rule and re-saturate. *)

Local Notation pos_instance :=
  (Defs.instance positive positive trie_map trie_map
     (@FullPosTrie.full_pos_trie_map) (option positive)).
Local Notation pos_lang := (@Rule.lang positive).
Local Notation prelang := (@prelang string).

Section Incremental.
  (* [fuel]: saturation iterations per (re-)saturation.  [window]: semi-naive
     look-back for the incremental resume -- large enough to re-match the
     equations over every prior epoch (see [saturate_gen_win]). *)
  Context (fuel window : nat).

  (* Seed the freshly elaborated (positive) rule [nr] into [g] and re-saturate,
     using the accumulated language [lp] (which must already contain [nr]) for
     sort lookups and the equation rule-set. *)
  Definition incr_add (nr : positive * Rule.rule positive) (lp : pos_lang)
    (g : pos_instance) : pos_instance :=
    snd ((@! let _ <- seed_rule triv_weight lp nr in
             let _ <- saturate_gen_win triv_weight window fuel (eq_seqs lp) in
             ret tt) g).

  Fixpoint infer_lang_incr (l_base : lang) (l : prelang)
    (st : pos_instance * renaming string * pos_lang)
    : lang * (pos_instance * renaming string * pos_lang) :=
    match l with
    | [] => ([], st)
    | (n,r)::l' =>
        (* elaborate the tail first (dependency order: base-most rules first),
           threading the injectivity e-graph forward *)
        let '(el', st1) := infer_lang_incr l_base l' st in
        let '(g1, rn1, lp1) := st1 in
        let L_str := el' ++ l_base in
        (* schemas for constructors currently in scope, read off the e-graph *)
        let schemas := fundep_schemas_of g1 rn1 L_str in
        let r' := infer_rule_gen L_str (build_general_injection_rules schemas) r in
        (* add the elaborated rule to the e-graph and re-saturate *)
        let '(nr_pos_l, rn2) := rename_lang [(n,r')] rn1 in
        let lp2 := nr_pos_l ++ lp1 in
        let g2 := match nr_pos_l with
                  | nr_pos :: _ => incr_add nr_pos lp2 g1
                  | [] => g1
                  end in
        ((n,r')::el', (g2, rn2, lp2))
    end.

  (* Elaborate [l] against [l_base], generating injectivity/cancellation rules
     incrementally.  Mirrors [infer_lang_ext_simple_gen] but with the injectivity
     e-graph threaded through, so [l]'s own rules inform its elaboration. *)
  Definition infer_lang_ext_simple_incr (l_base l : lang) : lang :=
    let '(lp0, rn0) := rename_lang l_base init_renaming in
    let g0 := run_eq triv_weight fuel lp0 in
    fst (infer_lang_incr l_base (of_lang l) (g0, rn0, lp0)).

  (* Prelang variant, drop-in for [TypeInference.infer_lang_ext]. *)
  Definition infer_lang_ext_incr (l_base : lang) (l : prelang) : lang :=
    let '(lp0, rn0) := rename_lang l_base init_renaming in
    let g0 := run_eq triv_weight fuel lp0 in
    fst (infer_lang_incr l_base l (g0, rn0, lp0)).

End Incremental.

(* -------------------------------------------------------------------------
   Compiler-case elaboration with AUTO-GENERATED injectivity rules.

   A compiler elaborates each source rule into a FIXED target language, and the
   injectivity/cancellation facts inference needs are those of the TARGET.  Since
   the target does not change as cases are elaborated, there is NOTHING to thread
   (unlike [infer_lang_ext_simple_incr]): the target's schemas are generated ONCE
   up front by running the functional-dependency search over [tgt], and the same
   [build_general_injection_rules] closure is reused for every case.  Drop-in for
   [infer_compiler_simple], replacing its hand-written schema list with the
   generated one.  (Compiler analogue of [infer_lang_ext_simple_incr], but with
   no e-graph threading -- hence [autoinj], not [incr].) *)
Definition infer_compiler_simple_autoinj (fuel : nat) (tgt : lang)
  cmp_pre cmp (src : lang) :=
  infer_compiler_simple_gen tgt cmp_pre cmp src
    (build_general_injection_rules (gen_fundep_schemas fuel tgt)).

(* debug: canonical (args, ret) e-class ids of every atom whose head prints as
   [nm], from the equation-saturated graph.  Two rows with the same [ret] but
   different [args] are a merge; where they differ is a refuted position. *)
Definition dump_head (X : nat) (nm : string) (L : lang) : list (list nat * nat) :=
  let '(l_pos, rn) := rename_lang L init_renaming in
  let g := run_eq triv_weight X l_pos in
  map (fun '(_,args,r) => (map Pos.to_nat args, Pos.to_nat r))
    (filter (fun '(fn,_,_) => String.eqb (of_p rn fn) nm) (catoms g)).

(* ---- reduction with GENERATED inj_rules ----

   Wires [gen_reduce_inj_rules] into [Automation.by_reduction'] (addressing the
   Automation.v TODO "plug inj_rules into tactics"): read the goal's language,
   generate the per-op injectivity/cancellation alternatives at fuel [X], and
   thread them into the reduction engine's congruence decomposition
   ([Defs.cong_subgoals]).  Reduction-engine analogue of
   [infer_compiler_simple_autoinj].

   OPT-IN, not the default [Automation.by_reduction]: generation [vm_compute]s
   [gen_fundep_schemas X l] over the WHOLE goal language, which is expensive (and
   can OOM) on large targets.  For a fixed target, prefer precomputing the table
   once --
     Definition my_inj_rules := Eval vm_compute in gen_reduce_inj_rules X my_lang.
   -- and passing it directly to [Automation.by_reduction' reversible my_inj_rules]. *)
Ltac by_reduction_gen X :=
  lazymatch goal with
  | |- eq_term ?l _ _ _ _ =>
      let rules := eval vm_compute in (gen_reduce_inj_rules X l) in
      Automation.by_reduction' (fun _ : string * Rule.rule string => true) rules
  end.
