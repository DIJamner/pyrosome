(* TODO: separate semantics and theorems
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps Relations UnionFind.
From Utils.EGraph Require Import Defs.
From Utils Require TrieMap.
Import Sets.
Import StateMonad.

(*TODO: move to Utils.v*)
(*redefine with ::= to change cleanup *)
Ltac cleanup_procedure := eauto with utils.
Ltac cleanup_context :=
  repeat multimatch goal with
    | H : ?P |- _ =>
        clear H; assert P as H by cleanup_procedure; clear H
    end.

Definition If_Some_satisfying {A} (P : A -> Prop) x :=
  match x with
  | Some x => P x
  | None => True
  end.
Notation "x <?> P" :=
  (If_Some_satisfying P x)
    (at level 56,left associativity).


(*TODO: move to Utils.v*)
Ltac inversions := autorewrite with inversion in *; break; subst.

(*TODO: move to utils*)
Ltac get_head e :=
  lazymatch e with
  | ?f _ => get_head f
  | _ => e
  end.

Ltac match_some_satisfying :=
  lazymatch goal with
  | H : ?e <$> ?f |- _ =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  | |- context ctx [?e <$> ?f] =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  | H : ?e <?> ?f |- _ =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  | |- context ctx [?e <?> ?f] =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  end.

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)

      (*TODO: just extend to Natlike?*)
      (idx_succ : idx -> idx)
      (idx_zero : WithDefault idx)
      (*TODO: any reason to have separate from idx?*)
      (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol).

  Existing Instance idx_zero.

  Notation atom := (atom idx symbol).

  (*TODO: really should just assign a name to eq.
    Long term, eq shouldn't be special.
   *)
  Variant clause := eq_clause (x y : idx) | atom_clause (a:atom).

  Definition clause_vars c :=
    match c with
    | eq_clause x y => [x;y]
    | atom_clause a =>
        a.(atom_ret)::a.(atom_args)
    end.

  (* Represents a logical sequent of the form
     x1,...,xn, P1, ... , Pn |- y1,...,yn, Q1, ... , Qn
     or alternately
     forall x1...xn, P1 /\ ... /\ Pn -> exists y1...yn, Q1 /\ ... /\ Qn

     TODO: leave vars as components or infer?
   *)
  Record sequent : Type :=
    {
      (*forall_vars : list idx;*)
      seq_assumptions : list clause;
      (* exist_vars : list idx *)
      seq_conclusions : list clause;
    }.

  Definition forall_vars (s : sequent) := flat_map clause_vars s.(seq_assumptions).
  Definition exists_vars (s : sequent) :=
    filter (fun x => negb (inb x (forall_vars s)))
      (flat_map clause_vars s.(seq_conclusions)).

  Definition sequent_vars s :=
    (flat_map clause_vars (s.(seq_assumptions)++s.(seq_conclusions))).
    

  Definition atom_subst (sub : named_list idx idx) (a : atom) :=
    Build_atom
      a.(atom_fn)
      (map (fun x => named_list_lookup x sub x) a.(atom_args))
      (named_list_lookup a.(atom_ret) sub a.(atom_ret)).

  (*
    TODO: is there a straightforward SMT encoding of these logical expressions?

    Preamble:
    declare an unknown type T
    declare each function symbol as an uninterpreted function of the approriate arity,
    from Ts to T

    translate clauses to expressions as follows:
    (= x y) ~> (= x y)
    (f x1...xn -> y) ~> (= (f x1 ... xn) y)

    for each sequent, generate:
    (assert (forall x1...xn, (and |P1| ... |Pn|) => exist y1...yn, (and |Q1|..|Qn|)))


    Should be able to do type checking, inference, equations, etc.

    Issue: is this correct? SMT might assume decidable equality

   *)

  
  (* clause lists are isomorphic to DBs/egraphs,
     up to some egraph state

   *)
  Section AsInstance.

  Context (symbol_map : forall A, map.map symbol A)
        (symbol_map_plus : map_plus symbol_map).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_plus : map_plus idx_trie)
        (analysis_result : Type)
        `{analysis idx symbol analysis_result}.

    
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie analysis_result).

  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).

  
  Notation alloc :=
    (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result).
  
  Definition rename_lookup (x : idx) : stateT (named_list idx idx) (state instance) idx :=
    fun sub =>
      match named_list_lookup_err sub x with
      | Some y => Mret (y, sub)
      | None => @! let y <- alloc in
                  ret (y, (x,y)::sub)
      end.

  Definition rename_atom (a : atom) : stateT (named_list idx idx) (state instance) atom :=
    let (f, args, out) := a in
    @! let args' <- list_Mmap rename_lookup args in
      let out' <- rename_lookup out in
      ret Build_atom f args' out'.

  (*TODO: output type? should be unit, but doesn't really matter *)
  Definition add_clause_to_instance c
    : stateT (named_list idx idx) (state instance) unit :=
    match c with
    | eq_clause x y =>
        @! let x' <- rename_lookup x in
          let y' <- rename_lookup y in
          (Mseq (lift (Defs.union x' y')) (Mret tt))
    | atom_clause a =>
        @! let a' <- rename_atom a in
        (lift (update_entry a'))
    end.

  Definition clauses_to_instance := list_Miter add_clause_to_instance.

  Definition uf_to_clauses (u : union_find) :=
    map (uncurry eq_clause) (map.tuples u.(parent _ _ _)).


  Definition row_to_atom f (p : list idx * db_entry idx analysis_result) : atom :=
    let '(k,e) := p in
    Build_atom f k e.(entry_value _ _).
  
  Definition table_atoms '(f,tbl) : list atom :=
    map (row_to_atom f) (map.tuples tbl).
  
  Definition db_to_atoms (d : db_map idx symbol symbol_map idx_trie analysis_result) :=
    (flat_map table_atoms (map.tuples d)).
  
  Definition instance_to_clauses i :=
    (uf_to_clauses i.(equiv)) ++ (map atom_clause (db_to_atoms i.(db))).

  (* Note: instance_to_clauses and clauses_to_instance
     are intended to be isomorphic up to egraph bookkeeping
   *)
  
  End AsInstance.

(* Alternate approach: consider the initial model of the theory.
   Terms added at the start form a no-premise rule, so can be ignored.
   TODO: make a class?
 *)
  Record model : Type :=
    {
      domain : Type;
      (* included to support setoids *)
      domain_eq : domain -> domain -> Prop;
      domain_wf x := domain_eq x x;
      (*constants : idx -> domain; TODO: do I have any constants? *)
      interpretation : symbol -> list domain -> option domain;
      interprets_to f args d := exists d', interpretation f args = Some d' /\ domain_eq d' d;
    }.

  Class model_ok (m : model) : Prop :=
    {
      interpretation_preserving
      : forall f args1 args2,
        all2 m.(domain_eq) args1 args2 ->
        option_relation m.(domain_eq) (m.(interpretation) f args1) (m.(interpretation) f args2)
    }.
  
  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_plus : map_plus symbol_map)
    (symbol_map_ok : forall A, map.ok (symbol_map A)).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: check that we don't need weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_ok : forall A, map.ok (idx_trie A))
        (idx_trie_plus : map_plus idx_trie).

  
  Section ForModel.

    Context m (idx_interpretation : idx_map m.(domain)).

    Definition atom_sound_for_model a :=
      (list_Mmap (map.get idx_interpretation) a.(atom_args)) <$> (fun args =>
      (map.get idx_interpretation a.(atom_ret)) <$> (fun out =>      
      m.(interprets_to) a.(atom_fn) args out)).
  
  Definition eq_sound_for_model x y : Prop :=
    map.get idx_interpretation x <$> (fun x' =>
    (map.get idx_interpretation y) <$>
      (m.(domain_eq) x')).

   Definition clause_sound_for_model (c : clause) : Prop :=
    match c with
    | eq_clause x y => eq_sound_for_model x y
    | atom_clause a => atom_sound_for_model a
    end.

  End ForModel.

  Definition model_satisfies_rule m r :=
    forall query_assignment,
      set_eq (map.keys query_assignment) (forall_vars r) ->
      all (clause_sound_for_model m query_assignment) r.(seq_assumptions) ->
      exists out_assignment,
        map.extends out_assignment query_assignment
        /\ all (clause_sound_for_model m out_assignment)
          r.(seq_conclusions).  

  Notation match_clause := (match_clause idx _).
  Notation match_clause' := (match_clause' idx _).

  (*TODO: duplicate. find other def and move to better location*)
  Fixpoint nat_to_idx n :=
    match n with
    | 0 => idx_zero
    | S n => idx_succ (nat_to_idx n)
    end.

  Definition assign_sub (assignment : list idx) :=
    combine (seq 0 (List.length assignment)) assignment.

  Fixpoint compatible_assignment pa a :=
    match pa, a with
    | [], _ => True
    | None::pa', _::a' => compatible_assignment pa' a'
    | (Some x)::pa', y::a' => x = (y : idx) /\ compatible_assignment pa' a'
    | _, _ => False
    end.
  
  (*TODO: how to describe a as smallest list?*)
  Definition assignment_correct l1 l2 a :=
      forall default,
      map (fun x => named_list_lookup default (assign_sub a) x) l1 = l2.
  
  (*TODO: how to describe as smallest list?*)
  Definition passignment_ex l1 l2 pa :=
    exists assignment,
      assignment_correct l1 l2 assignment
      /\ compatible_assignment pa assignment.
  
  Definition passignment_forall l1 l2 pa :=
    forall assignment,
      assignment_correct l1 l2 assignment ->
      compatible_assignment pa assignment.
  
  Lemma empty_passignment a
    : compatible_assignment [] a.
  Proof. exact I. Qed.

  
  Lemma match_clause'_complete cargs cv args v acc a
    : match_clause' cargs cv args v acc = None ->
      passignment_forall (cv::cargs) (v::args) acc ->
      forall default,
      map (fun x => named_list_lookup default (assign_sub a) x) (cv::cargs) <> (v::args).
  Proof.
    (*
    revert args acc a.induction cargs;
      destruct args;
      unfold passignment_forall,
      assignment_correct;
      basic_goal_prep;
      basic_utils_crush.
     *)
    Abort.
    
  (*TODO: too strong a statement.
    The passignment doesn't have to stay compatible in the case where there are no compatible assignments
   *)
  Lemma match_clause'_compat_preserving cargs cv args v acc passignment
    : match_clause' cargs cv args v acc = Some passignment ->
      passignment_ex (cv::cargs) (v::args) acc ->
      passignment_ex (cv::cargs) (v::args) passignment.
  Proof.
    revert args; induction cargs;
      destruct args;
      unfold passignment_forall,
      assignment_correct;
      basic_goal_prep;
      basic_utils_crush.
    { (*TODO: insert correctness *) shelve. }
    {
      revert H; case_match; try congruence.
      intros.

      (*
      Lemma insert_correct
        : Some l = insert idx Eqb_idx acc a i ->
          passignment_forall l1 l2 acc ->
          passignment_forall l1 l2 acc ->
          
    
  Lemma match_clause_correct default cargs cv args v assignment
    : let sub := assign_sub assignment in
      match_clause (cargs, cv) args v = Some assignment
      -> map (fun x => named_list_lookup default sub x) (cv::cargs)
         = v::args.
  Proof.*)
      Abort.
  
  Lemma match_clause_correct default cargs cv args v assignment
    : let sub := assign_sub assignment in
      match_clause (cargs, cv) args v = Some assignment
      -> map (fun x => named_list_lookup default sub x) (cv::cargs)
         = v::args.
  Proof.
    cbn -[map].
    case_match; cbn -[map]; try congruence.
    remember [] as acc.
    
    revert dependent l.
    revert args.
    (*
    symmetry in HeqH.
    eapply match_clause'_correct in HeqH.
    rewrite <- HeqH.
    intros.
    autorewrite with utils in *.
    subst.
    eapply map_ext.
    clear HeqH.
    intros.
    (*TODO: need assumption that r is dense
    cbn.
     *)
     *)
Abort.


  
  Context (analysis_result : Type).

  Notation instance :=
    (instance idx symbol symbol_map idx_map idx_trie analysis_result).
  (*TODO: many of these relations can be functions. what's the best way to define them?*)
  
  Definition atom_in_egraph a (i : instance) :=
    (map.get i.(db) a.(atom_fn)) <$>
      (fun tbl => (map.get tbl a.(atom_args)) <$>
                    (fun r => r.(entry_value _ _) = a.(atom_ret))).

  (*
  (*Defined separately for proof convenience.
    Equivalent to a term using ~ atom_in_egraph
   *)
  Definition not_key_in_egraph a (i : instance) :=
    (map.get i.(db _ _ _ _ _) a.(atom_fn)) <?>
      (fun tbl => (map.get tbl a.(atom_args)) <?>
                    (fun r => False)).
  *)

  Definition SomeRel {A B} (R : A -> B -> Prop) ma mb :=
    ma <$> (fun x => mb <$> (R x)).
  
  Inductive le (n : idx) : idx -> Prop :=
    le_n : le n n | le_S : forall m, le n m -> le n (idx_succ m).

  Section ForModel.

    Context m (idx_interpretation : idx_map m.(domain)).

    Local Notation atom_sound_for_model :=
      (atom_sound_for_model m idx_interpretation).

    Definition worklist_entry_sound e :=
      match e with
      | union_repair _ old_idx new_idx improved_new_analysis =>
          eq_sound_for_model m idx_interpretation old_idx new_idx
      | analysis_repair _ i => True (* these don't affect soundness of the egraph *)
      end.
    
    (*TODO: move to defining file*)
    Arguments parent {idx}%type_scope {idx_map rank_map} u.
    
    Record egraph_sound_for_interpretation e : Prop :=
      {
        idx_interpretation_wf : forall i d, map.get idx_interpretation i = Some d -> m.(domain_wf) d;
        interpretation_exact : forall x,
          Is_Some (map.get idx_interpretation x) -> Sep.has_key x (parent (equiv e));
        (* inferrable
        interpretation_bounded : forall i, le e.(equiv).(next _ _ _) i ->
                                           map.get idx_interpretation i = None;
         *)
        atom_interpretation : forall a, atom_in_egraph a e -> atom_sound_for_model a;
        rel_interpretation :
        forall i1 i2,
          (* TODO: should every index be required to map to a domain value?
             (e.g. to allow flexibility when initially allocating them)
           *)
          uf_rel_PER _ _ _ e.(equiv) i1 i2 ->
          eq_sound_for_model m idx_interpretation i1 i2;
        parents_interpretation :
        (* Parents do not have to exist in the egraph (and may not, during rebuilding)
           but they must be valid in the model or rebuilding is unsound.
         *)
        forall i l, map.get e.(parents) i = Some l -> all atom_sound_for_model l;
        worklist_sound : all worklist_entry_sound e.(worklist)
      }.

  End ForModel.

  (* TODO: is exists right?
     Possibly: f is probably sufficiently unique up to equivalence
   *)
  Definition egraph_sound_for_model m e : Prop :=
    exists f, egraph_sound_for_interpretation m f e.

  (* TODO: is this record needed? other fields may not be necessary *)
  Record egraph_ok (e : instance) : Prop :=
    {
      egraph_equiv_ok : exists roots, union_find_ok e.(equiv) roots;
      (* TODO: not an invariant that parents exist?
           Can be broken in many places.
           What is the invariant?
           - that the parent could exist
       *)
    }.

  Record egraph_sound e m : Prop :=
    {
      sound_egraph_ok :> egraph_ok e;
      sound_egraph_for_model : egraph_sound_for_model m e;
    }.

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).


  Hint Rewrite @map.get_empty : utils.

  (*
  Lemma PER_empty (j k : idx)
    : reachable_plus map.empty j k <-> False.
  Proof.
    unfold reachable_plus.
    intuition (subst; eauto with utils).
    induction H;
      basic_goal_prep;
      basic_utils_crush.
    all: 
      basic_utils_crush.
  Qed.
  Hint Rewrite reachable_empty : utils.
   *)
  
  Lemma PER_empty A (a b : A) R 
    : (forall a b, ~ R a b) -> ~ PER_closure R a b.
  Proof.
    intros ? ?.
    induction H0;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  
  Theorem empty_sound_for_interpretation m
    (*: egraph_sound (empty_egraph idx_zero analysis_result) m.*)
    : egraph_sound_for_interpretation m map.empty (empty_egraph idx_zero _).
  Proof.
    constructor; cbn; try tauto;
      unfold atom_in_egraph;
      basic_goal_prep;
      rewrite ? map.get_empty in *;
      basic_goal_prep;
      try tauto;
      try congruence.
    {
      exfalso; eapply PER_empty; try eassumption.
      basic_goal_prep;
        basic_utils_crush.
    }
  Qed.

  Theorem empty_sound m : egraph_sound (empty_egraph idx_zero analysis_result) m.
  Proof.
    unfold empty_egraph.
    constructor.
    { cbn; do 3 econstructor; basic_goal_prep; basic_utils_crush.
      { apply empty_forest_rooted. }
    }
    intros; exists map.empty.
    apply empty_sound_for_interpretation.
  Qed.
  
  Notation saturate_until' := (saturate_until' idx_succ idx_zero spaced_list_intersect).
  Notation saturate_until := (saturate_until idx_succ idx_zero spaced_list_intersect).

  Notation run1iter :=
    (run1iter idx Eqb_idx idx_succ idx_zero symbol Eqb_symbol symbol_map symbol_map_plus
       idx_map idx_map_plus idx_trie spaced_list_intersect).
  (*
  Notation rebuild := (rebuild idx Eqb_idx symbol Eqb_symbol symbol_map idx_map idx_trie).
  *)
    
  (*TODO: move *)
  Lemma get_update_diff K V (mp : map.map K V) {H : map.ok mp} `{WithDefault V} (m : mp) k k' f
    : k <> k' -> map.get (map_update m k f) k'
                 = (map.get m k').
  Proof.
    unfold map_update.
    intro.
    case_match; cbn; eauto.
    all:rewrite map.get_put_diff; eauto.
  Qed.
  
  (*TODO: move *)
  Lemma get_update_same K V (mp : map.map K V) {H : map.ok mp} `{WithDefault V} (m : mp) k f
    : map.get (map_update m k f) k
      = Some match map.get m k with
          | Some x => f x
          | None => f default
          end.
  Proof.
    unfold map_update.
    case_match; cbn; eauto.
    all:rewrite map.get_put_same; eauto.
  Qed.


  Lemma atoms_functional a1 a2 e
    :  atom_in_egraph a1 e ->
       atom_in_egraph a2 e ->
       a1.(atom_fn) = a2.(atom_fn) ->
       a1.(atom_args) = a2.(atom_args) ->
       a1 = a2.
  Proof.
    clear idx_succ.
    unfold atom_in_egraph;
      destruct a1, a2;
      basic_goal_prep;
      subst.
    f_equal.
    repeat (match_some_satisfying; cbn; try tauto;[]).
    basic_goal_prep;
      subst.
    reflexivity.
  Qed.

  Lemma atom_in_egraph_excluded a e
    : atom_in_egraph a e \/ ~ atom_in_egraph a e.
  Proof.
    clear idx_succ.
    unfold atom_in_egraph.
    repeat (match_some_satisfying; cbn;[]).
    basic_goal_prep.
    destruct d; cbn.
    eqb_case entry_value (atom_ret a); intuition eauto.
  Qed.

  (*TODO: move to Defs*)
  Instance atom_eqb : Eqb atom :=
    fun a b =>
      (eqb a.(atom_fn) b.(atom_fn))
      && (eqb a.(atom_args) b.(atom_args))
      && (eqb a.(atom_ret) b.(atom_ret)).

  Instance atom_eqb_ok : Eqb_ok atom_eqb.
  Proof.
    intros [f a o] [f' a' o']; unfold eqb, atom_eqb; cbn.
    eqb_case f f'; cbn; try congruence.
    eqb_case a a'; cbn; try congruence.
    eqb_case o o'; cbn; try congruence.
  Qed.

  Lemma all2_iff2 A B (R1 R2 : A -> B -> Prop) l1 l2
    : iff2 R1 R2 ->
      all2 R1 l1 l2 ->
      all2 R2 l1 l2.
  Proof using.
    clear.
    unfold iff2;
      intro Hr.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
    firstorder.
  Qed.

  (*TODO: move*)
  Lemma all2_impl A B (R S : A -> B -> Prop) l1 l2
    : (forall a b, R a b -> S a b) -> all2 R l1 l2 -> all2 S l1 l2.
  Proof using.
    clear.
    intro.
    revert l2; induction l1; destruct l2;
      basic_goal_prep; basic_utils_crush.
  Qed.

  Lemma all2_Is_Some_satisfying_l A B (R : A -> B -> Prop) l1 l2
      : all2 (fun x y => x <$> (fun x' => R x' y)) l1 l2
        <-> option_all l1 <$> (fun l1' => all2 R l1' l2).
  Proof.
    clear idx_succ idx_zero.
    revert l2; induction l1; destruct l2;
      basic_goal_prep; (repeat case_match; basic_goal_prep); basic_utils_crush.
    { eapply IHl1; eauto. }
    { eapply IHl1; eauto. } 
    { eapply IHl1; eauto. }
  Qed.
  
  Lemma all2_Is_Some_satisfying_r A B (R : A -> B -> Prop) l1 l2
      : all2 (fun x y => y <$> (fun y' => R x y')) l1 l2
        <-> option_all l2 <$> (fun l2' => all2 R l1 l2').
  Proof.
    clear idx_succ idx_zero.
    revert l1; induction l2; destruct l1;
      basic_goal_prep; (repeat case_match; basic_goal_prep); basic_utils_crush.
    { eapply IHl2; eauto. }
    { eapply IHl2; eauto. } 
    { eapply IHl2; eauto. }
  Qed.

  Lemma args_rel_interpretation m interp e
    : egraph_sound_for_interpretation m interp e ->
      forall args1 args2,
        all2 (uf_rel_PER _ _ _ e.(equiv)) args1 args2 ->
        option_relation (all2 m.(domain_eq)) (list_Mmap (map.get interp) args1)
          (list_Mmap (map.get interp) args2).
  Proof.
    destruct e,1; cbn in *.
    clear atom_interpretation0 parents_interpretation0.
    unfold SomeRel.
    induction args1;
      destruct args2;
      basic_goal_prep;
      try tauto.
    specialize (IHargs1 args2).
    break.
    eapply rel_interpretation0 in H.
    unfold eq_sound_for_model in H.
    case_match; destruct (map.get interp i) eqn:Hi.
    all:cbn in H; try tauto.
    rewrite !TrieMap.Mmap_option_all.
    eapply all2_impl in H0; try eapply rel_interpretation0.
    unfold eq_sound_for_model in H0.
    change
      (all2
         (fun x y =>
            (fun x y =>
               (fun x y => x <$> (fun x' => y <$> domain_eq m x')) x (map.get interp y))
              (map.get interp x) y)
        args1 args2)
      in H0.
    rewrite <- TrieMap.all2_map_l in H0.
    change
      (all2 (fun x y =>
               (fun x y => x <$> (fun x' => y <$> domain_eq m x')) x (map.get interp y))
         (map (map.get interp) args1) args2)
      in H0.
    rewrite <- TrieMap.all2_map_r in H0.
    rewrite all2_Is_Some_satisfying_l in H0.
    case_match; cbn in *; try tauto.
    rewrite all2_Is_Some_satisfying_r in H0.
    case_match; cbn in *; tauto.
  Qed.
  
  Definition atom_rel (equiv : union_find idx (idx_map idx) (idx_map nat)) (a1 a2 : atom) : Prop :=
    a1.(atom_fn) = a2.(atom_fn)
    /\ all2 (uf_rel _ _ _ equiv) a1.(atom_args) a2.(atom_args)
    /\ uf_rel _ _ _ equiv a1.(atom_ret) a2.(atom_ret).

  Lemma atom_rel_refl equiv : Reflexive (atom_rel equiv).
  Proof using.
    clear idx_succ idx_zero.
    unfold atom_rel.
    intro a; destruct a; cbn; intuition eauto.
    1:eapply all2_refl.
    all: apply reachable_rel_Reflexive.
  Qed.
  
  Lemma atom_rel_sym equiv : Symmetric (atom_rel equiv).
  Proof using.
    clear idx_succ idx_zero.
    unfold atom_rel.
    intros a b; destruct a, b; cbn; intuition eauto.
    1:eapply all2_Symmetric.
    all: try apply reachable_rel_Symmetric; eauto.
  Qed.

  (*TODO: just use nat?*)
  Lemma le_trans a b c : le a b -> le b c -> le a c.
  Proof.
    intros H1 H2; revert a H1; induction H2;
      basic_goal_prep; try constructor; eauto.
  Qed.
  
  Lemma iff2_atom_rel equiv equiv'
    : iff2 (uf_rel idx (idx_map idx) (idx_map nat) equiv)
        (uf_rel idx (idx_map idx) (idx_map nat) equiv') ->
      iff2 (atom_rel equiv) (atom_rel equiv').
  Proof.
    clear idx_zero idx_succ.
    unfold atom_rel.
    intros Huf [] [];
      basic_goal_prep;
      intuition eauto.
    all: try eapply all2_iff2; try eassumption.
    all: try eapply Huf; eauto.
    unfold iff2 in *; firstorder.
  Qed.
  
  Lemma state_triple_list_Mfoldl A B f l P acc
    : (forall (acc : B) (l1 : list A) (a : A) (l2 : list A),
          l = l1 ++ a :: l2 ->
          state_triple
            (fun e : instance => P (a :: l2) acc e)
            (f acc a)
            (fun p => P l2 (fst p) (snd p))) ->
      state_triple (fun e => P l acc e) (list_Mfoldl f l acc)
        (fun p => P [] (fst p) (snd p)).
  Proof.
    revert acc.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_utils_crush.
    }
    {
      cbn [all list_Mfoldl]; intros; break.
      eapply state_triple_bind.
      { eapply H with (l1:=[]); eauto. }
      unfold curry.
      intro b.
      cbn.
      eapply IHl;
        basic_goal_prep.
      eapply H with (l1:= a::l1).
      basic_utils_crush.
    }
  Qed.

  Context `{analysis idx symbol analysis_result}.
    

  Definition monotone {A} P : Prop :=
    (forall i i' : idx_map A, map.extends i i' -> P i' -> P i).

  Definition monotone1 {A B} (P : _ -> B -> _) : Prop :=
    (forall a (i i' : idx_map A), map.extends i i' -> P i' a -> P i a).

  Definition monotone2 {A B C} (P : _ -> B -> C -> _) : Prop :=
    (forall a b (i i' : idx_map A), map.extends i i' -> P i' a b -> P i a b).
  
  Lemma monotone2_fix_l {A B C} (P : idx_map A -> B -> C -> _) x
    : monotone2 P ->
      monotone1 (fun i => P i x).
  Proof.
    unfold monotone2, monotone1.
    basic_goal_prep.
    eapply H0; eauto.
  Qed.

  
  Definition state_sound_for_model {A} (m : model) i
    (s : state instance A) Post :=
    state_triple (Sep.and1 egraph_ok (egraph_sound_for_interpretation m i)) s
      (*TODO: make sure that i' can depend on x *)
      (fun x => exists i', (Post i' (fst x))
                           /\ egraph_ok (snd x)
                           /\ egraph_sound_for_interpretation m i' (snd x)
                           /\ map.extends i' i).

  Hint Resolve Properties.map.extends_refl : utils.
  
  Lemma worklist_entry_sound_mono m
    : monotone1 (worklist_entry_sound m).
  Proof.
    intros x ? ?.
    destruct x; basic_goal_prep; auto.
    revert H1.
    unfold eq_sound_for_model, Is_Some_satisfying in *; case_match; try tauto.
    case_match; try tauto.
    eapply H0 in case_match_eqn, case_match_eqn0.
    rewrite case_match_eqn, case_match_eqn0.
    auto.
  Qed.
        
  Lemma pull_worklist_sound m i
    : state_sound_for_model m i
        (pull_worklist idx symbol symbol_map idx_map idx_trie analysis_result) 
        (fun i' wl => i = i' /\ all (worklist_entry_sound m i) wl).
  Proof.
    cbv -[map.rep domain map.get all worklist_entry_sound map.extends];
      intros; break.
    {
      eexists; intuition eauto; destruct e; cbn in *.
      { destruct H1; basic_utils_crush. }
      { destruct H0; constructor; cbn in *; eauto with utils. }
      { destruct H1; constructor; cbn in *; intuition (cbn; eauto). }
      { basic_utils_crush. }
    } 
  Qed.

  Lemma map_extends_trans {key value : Type} {map : map.map key value} (m1 m2 m3 : map)
    : map.extends m1 m2 -> map.extends m2 m3 -> map.extends m1 m3.
  Proof using. clear; unfold map.extends; intuition eauto. Qed.

  Lemma state_sound_for_model_bind A B m i c P Q (f : A -> _ B)
    : state_sound_for_model m i c P ->
      (forall (a:A) i', map.extends i' i ->
                        P i' a ->
                        state_sound_for_model m i' (f a) Q) ->
      state_sound_for_model m i (@! let p <- c in (f p)) Q.
  Proof.
    clear idx_succ idx_zero.
    basic_goal_prep.
    intros; auto.
    intros e He.
    specialize (H0 e He).
    repeat basic_goal_prep.
    destruct (c e) eqn:Hce.
    repeat basic_goal_prep.
    clear c Hce.
    eapply H1 in H0; eauto with utils; clear H1.
    
    specialize (H0 i0).
    unfold Sep.and1 in *; intuition break.
    eexists; intuition eauto using map_extends_trans.
  Qed.

  Lemma monotone1_all A m (Pmono : _ -> A -> _)
    : monotone1 Pmono ->
      monotone1 (fun i' : idx_map (domain m) => all (Pmono i')).
  Proof.
    clear.
    intros; intros l.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Resolve monotone1_all : utils.
  
  Lemma state_sound_for_model_Mmap A B m i P_const P_elt l (f : A -> _ B) 
    : (forall (a:A) i', In a l ->
                        map.extends i' i ->
                        P_const i' ->
                        state_sound_for_model m i' (f a)
                          (fun i' a => P_const i' /\ P_elt i' a)) ->
      P_const i ->
      monotone1 P_elt ->
      state_sound_for_model m i (list_Mmap f l)
        (fun i' l => P_const i' /\ all (P_elt i') l).
  Proof.
    cleanup_context.
    revert i.
    induction l.
    {
      intros.
      eapply state_triple_wkn_ret;
        unfold Sep.and1 in *;
        basic_goal_prep; subst;
        eexists; cbn; intuition eauto with utils.
    }
    {
      intros.
      cbn [list_Mmap].
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        basic_goal_prep;
          basic_utils_crush.
      }
      intros.
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        eapply IHl; auto.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply H0.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply map_extends_trans; eauto.
      }
      {
        intros.
        eapply state_triple_wkn_ret;
          unfold Sep.and1 in *;
          basic_goal_prep; subst;
          eexists; intuition eauto using Properties.map.extends_refl.
        basic_goal_prep;
          basic_utils_crush.
      }
    }
  Qed.
  

  
  Lemma ret_sound_for_model A m i (x:A)
    : state_sound_for_model m i (Mret x) (fun i' a => i = i' /\ a = x).
  Proof.
    unfold state_sound_for_model, Sep.and1; basic_goal_prep; basic_utils_crush.
    intros ? ?.
    eexists; basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma ret_sound_for_model' A m i (x:A) P
    : P i x ->
      state_sound_for_model m i (Mret x) P.
  Proof.
    clear idx_succ idx_zero.
    unfold state_sound_for_model, monotone1, Sep.and1; basic_goal_prep; basic_utils_crush.
    intros ? ?.
    eexists; basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma state_sound_for_model_Mmap_dep A B m i P_const P_elt l (f : A -> _ B) 
    : (forall (a:A) i', In a l ->
                        map.extends i' i ->
                        P_const i' ->
                        state_sound_for_model m i' (f a)
                          (fun i' a' => P_const i' /\ P_elt a i' a')) ->
      P_const i ->
      (forall a, monotone1 (P_elt a)) ->
      state_sound_for_model m i (list_Mmap f l)
        (fun i' l' => P_const i' /\ all2 (fun a => P_elt a i') l l').
  Proof.
    cleanup_context.
    revert i.
    induction l.
    {
      intros.
      eapply state_triple_wkn_ret;
        unfold Sep.and1 in *;
        basic_goal_prep; subst;
        eexists; cbn; intuition eauto with utils.
    }
    {
      intros.
      cbn [list_Mmap].
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        basic_goal_prep;
          basic_utils_crush.
      }
      intros.
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        eapply IHl; auto.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply H0.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply map_extends_trans; eauto.
      }
      {
        intros.
        eapply ret_sound_for_model'; eauto with utils.
        {
          basic_goal_prep; intuition eauto.
          eapply H2; eauto.
        }
      }
    }
  Qed.
  
  Lemma const_monotone1 A B
    : monotone1 (fun (_ : idx_map A) (_ : B) => True).
  Proof. repeat intro; auto. Qed.
  Hint Resolve const_monotone1 : utils.
  
  Lemma state_sound_for_model_Miter A m i P
    l (f : A -> state instance unit) 
    : (forall (a:A) i', In a l ->
                        map.extends i' i ->
                        P i' tt ->
                        state_sound_for_model m i' (f a) P) ->
      P i tt ->
      state_sound_for_model m i (list_Miter f l) P.
  Proof.
    clear idx_succ idx_zero.
    revert i.
    induction l.
    { intros; eapply ret_sound_for_model'; eauto with utils. }
    {
      intros.
      cbn [list_Miter].
      eapply state_sound_for_model_bind.
      2:{
        intros.
        eapply IHl; eauto.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply H0.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply map_extends_trans; eauto.
      }
      {
        basic_goal_prep;
          basic_utils_crush.
      }
    }
  Qed.

  Lemma eq_sound_monotone m
    : monotone2 (eq_sound_for_model m).
  Proof using.
    clear.
    unfold monotone2, eq_sound_for_model.
    intros.
    destruct (map.get i' a) eqn:Hi';
      basic_goal_prep; try tauto.
    eapply H in Hi'.
    rewrite Hi' in *.
    cbn.
    destruct (map.get i' b) eqn:Hb;
      basic_goal_prep; try tauto.
    eapply H in Hb.
    rewrite Hb in *.
    cbn; auto.
  Qed.

  
  Lemma find_next_const x u u' i0
    : UnionFind.find u x = (u', i0) ->
      (next idx (idx_map idx) (idx_map nat) u)
      = (next idx (idx_map idx) (idx_map nat) u').
  Proof.
    unfold UnionFind.find.
    destruct u.
    cbn.
    case_match; cbn; try congruence.
    {
      eqb_case i x.
      { basic_goal_prep; basic_utils_crush. }
      {
        case_match; cbn; try congruence.
        basic_goal_prep.
        basic_utils_crush.
      }
    }
    {
      basic_goal_prep; basic_utils_crush.
    }
  Qed.

  (*TODO: move to UnionFind.v *)

  (*TODO: move to originating file*)
  Hint Constructors PER_closure transitive_closure : utils.
  Lemma subrelation_PER_closure A (R1 R2 : A -> A -> Prop)
    : subrelation R1 R2 ->
      subrelation (PER_closure R1) (PER_closure R2).
  Proof using.
    clear.
    unfold subrelation.
    intros ? ?; induction 1; basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma PER_closure_of_trans A (R : A -> A -> Prop)
    :  iff2 (PER_closure (transitive_closure R)) (PER_closure R).
  Proof using.
    clear.
    unfold iff2; split;
      induction 1; basic_goal_prep;
      basic_utils_crush.
    eapply trans_PER_subrel; eauto.
  Qed.
  
  Instance subrelation_Proper {A}
    : Proper (iff2 ==> iff2 ==> iff) (subrelation (A:=A)).
  Proof using.
    clear.
    unfold subrelation.
    repeat intro; unfold iff2 in *; split; intros.
    { rewrite <- H, <- H0 in *; eauto. }
    { rewrite H, H0 in *; eauto. }
  Qed.

  (*TODO: move to originating file *)
  Existing Instance iff2_rel.
  
  Lemma trans_to_PER_natural u u'
    : subrelation (parent_rel idx (idx_map idx) (parent u))
        (parent_rel idx (idx_map idx) (parent u')) ->
      subrelation (uf_rel_PER idx (idx_map idx) (idx_map nat) u)
        (uf_rel_PER idx (idx_map idx) (idx_map nat) u').
  Proof.
    clear.
    intro H; eapply subrelation_PER_closure in H.
    unfold parent_rel in H.
    rewrite !PER_closure_of_trans in H.
    exact H.
  Qed.
  
  Lemma find_sound m i x
    : Sep.has_key x i ->
      state_sound_for_model m i (find x) (fun i' a => i = i' /\ eq_sound_for_model m i x a).
  Proof.
    cleanup_context.
    unfold find.
    {
      intros ? ? ?.
      case_match; cbn.
      unfold Sep.and1 in *; break.
      destruct H1; break.
      pose proof case_match_eqn.
      eapply find_spec in case_match_eqn;
        try Lia.lia; eauto.
      2:{ eapply interpretation_exact; eauto. }
      break.
      eexists; intuition eauto with utils.
      {
        eapply rel_interpretation; eauto.
        eapply H7 in H6.
        eapply trans_PER_subrel; eauto.
      }
      { constructor; eauto. }
      {
        destruct H2; constructor; basic_goal_prep; intuition eauto.
        {
          eapply interpretation_exact0 in H2.
          eapply find_preserves_domain in H3; eauto.
          eapply H3; eauto.
        }
        {
          eapply rel_interpretation0; eauto.
          eapply trans_to_PER_natural; eauto.
        }
      }
    }
  Qed.

  Context m (m_PER : PER (domain_eq m)).
  
  Lemma eq_sound_for_model_trans i x y z
    : eq_sound_for_model m i x y ->
      eq_sound_for_model m i y z ->
      eq_sound_for_model m i x z.
  Proof using m_PER.
    clear idx_succ.
    unfold  eq_sound_for_model, Is_Some_satisfying.
    repeat case_match; basic_goal_prep; auto.
    all: try tauto.
    all: etransitivity; eassumption.
  Qed.

  Lemma eq_sound_has_key_r i old_idx new_idx
          : eq_sound_for_model m i old_idx new_idx ->
            Sep.has_key new_idx i.
  Proof using.
    clear idx_succ idx_zero.
    unfold eq_sound_for_model, Sep.has_key, Is_Some_satisfying.
    repeat case_match; tauto.
  Qed.
  Hint Resolve eq_sound_has_key_r : utils.
  
  Lemma canonicalize_worklist_entry_sound i a
    : (worklist_entry_sound m i a) ->
      state_sound_for_model m i
        (canonicalize_worklist_entry idx Eqb_idx symbol
           symbol_map idx_map idx_trie
           analysis_result a)
        (fun i' a => i = i' /\ worklist_entry_sound m i' a).
  Proof.
    intro.
    destruct a; cbn -[Mbind].
    2:{ eapply ret_sound_for_model'; eauto using worklist_entry_sound_mono. }
    {
      eapply state_sound_for_model_bind; eauto using worklist_entry_sound_mono.
      { eapply find_sound; eauto with utils. }
      basic_goal_prep; subst.
      eapply ret_sound_for_model'; eauto using worklist_entry_sound_mono.
      cbn.
      intuition subst.
      eapply eq_sound_for_model_trans; eauto.
    }
  Qed.
  

  Arguments repair {idx}%type_scope {Eqb_idx} idx_zero {symbol}%type_scope {Eqb_symbol}
    {symbol_map idx_map idx_trie}%function_scope {analysis_result}%type_scope 
    {H} e _.
  
  Arguments get_parents {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
    {analysis_result}%type_scope x _.

  Lemma atom_sound_monotone
    : monotone1 (atom_sound_for_model m).
  Proof using.
    clear.
    unfold atom_sound_for_model.
    repeat intro.
    unfold Is_Some_satisfying in H0.
    repeat case_match; try tauto.
    rewrite !TrieMap.Mmap_option_all in *.
    eapply Properties.map.getmany_of_list_extends in case_match_eqn; eauto.
    unfold map.getmany_of_list in case_match_eqn;
      rewrite case_match_eqn.
    eapply H in case_match_eqn0; rewrite case_match_eqn0.
    cbn.
    auto.
  Qed.
  Hint Resolve atom_sound_monotone : utils.
  Hint Resolve monotone1_all : utils.

  
  (*TODO: lift upwards, use as needed *)
  Ltac open_ssm' :=
    cleanup_context;
    lazymatch goal with
    | |- state_sound_for_model _ _ ?e _ =>
        let h := get_head e in
        unfold h; unfold state_sound_for_model, Sep.and1; repeat intro;
        eexists; eauto with utils;
        break; cbn[fst snd]
    end.
  
  Ltac open_ssm :=
    open_ssm';
    intuition eauto with utils;
    break; cbn[fst snd];
    try lazymatch goal with
      | H : egraph_ok _ |- egraph_ok _ =>
          destruct H; constructor; eauto with utils
      | H : egraph_sound_for_interpretation _ _ _
        |- egraph_sound_for_interpretation _ _ _ =>
          destruct H; constructor; eauto with utils
    end.
  
  Lemma get_parents_sound i old_idx
    : state_sound_for_model m i (get_parents old_idx)
         (fun i' a => i = i' /\ all (atom_sound_for_model m i) a).
  Proof.
    open_ssm.
    unfold unwrap_with_default; case_match; [| exact I].
    eapply parents_interpretation in case_match_eqn; eauto.
  Qed.

  Hint Rewrite @map.get_remove_same: utils.
  (*Hint Rewrite @map.get_remove_diff using tauto: utils.*)
  
  Lemma remove_parents_sound i old_idx
    : state_sound_for_model m i
        (remove_parents idx symbol symbol_map idx_map idx_trie analysis_result old_idx) 
        (fun i' _ => i' = i).
  Proof.
    open_ssm.
    basic_goal_prep.
    eqb_case i0 old_idx;
      basic_utils_crush.
    rewrite map.get_remove_diff in H0; try tauto.
    eauto.
  Qed.
  
  Ltac iss_case :=
    lazymatch goal with
    | H : ?ma <$> _ |- _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn in H;[| tauto]
    | |- ?ma <?> _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn;[| tauto]
    end.
  
  Lemma db_remove_sound i a1
    : state_sound_for_model m i
        (db_remove idx symbol symbol_map idx_map idx_trie analysis_result a1)
        (fun i' _ => i' = i).
  Proof.
    open_ssm.
    basic_goal_prep.
    eapply atom_interpretation0.
    unfold atom_in_egraph in *.
    basic_goal_prep.
    basic_utils_crush.
    repeat iss_case.
    eqb_case (atom_fn a1) (atom_fn a).
    {
      rewrite H1 in *.
      rewrite get_update_same in Hma; eauto.
      autorewrite with inversion in *.
      unfold Basics.flip in *.
      case_match.
      2:{
        change (map.remove map.empty (atom_args a1) = r) in Hma.
        rewrite Properties.map.remove_empty in *.
        basic_utils_crush.
      }
      cbn; subst.        
      eqb_case (atom_args a1) (atom_args a).
      {
        rewrite H2 in *.
        basic_utils_crush.
      }
      {
        rewrite map.get_remove_diff in Hma0; eauto.
        rewrite Hma0; cbn; eauto.
      }
    }
    {
      rewrite get_update_diff in Hma; eauto.
      rewrite Hma; cbn; eauto.
      rewrite Hma0; cbn; eauto.
    }
  Qed.

  Definition eq_atom_in_interpretation i (a1 a2 : atom) :=
    atom_fn a1 = atom_fn a2 /\
      all2 (eq_sound_for_model m i) (atom_args a1) (atom_args a2) /\
      eq_sound_for_model m i (atom_ret a1) (atom_ret a2).

  
  Lemma all2_flip A B (R : A -> B -> Prop) l1 l2
    : all2 R l1 l2 = all2 (fun a b => R b a) l2 l1.
  Proof using.
    clear.
    revert l2; induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Instance eq_sound_for_model_Symmetric i : Symmetric (eq_sound_for_model m i).
  Proof using m_PER .
    clear idx_succ idx_zero.
    unfold eq_sound_for_model.
    repeat intro.
    repeat iss_case.
    cbn.
    symmetry; auto.
  Qed.

  Lemma eq_atom_monotone
    : monotone2 eq_atom_in_interpretation.
  Proof using.
    clear.
    unfold eq_atom_in_interpretation.
    repeat intro.
      basic_goal_prep;
        basic_utils_crush.
      1: eapply all2_impl; try eassumption.
      all:intros; eapply eq_sound_monotone; eauto.
  Qed.


  Lemma canonicalize_sound i a1
    : atom_sound_for_model m i a1 ->
      state_sound_for_model m i (canonicalize a1)
        (fun i' a => i = i' /\ eq_atom_in_interpretation i a a1).
  Proof.
    cleanup_context.
    unfold canonicalize.
    destruct a1.
    intros.
    eapply state_sound_for_model_bind; eauto with utils.
    {
      eapply state_sound_for_model_Mmap_dep with (P_const:= eq i); auto.
      {
        cbn beta;intros; subst.
        eapply find_sound.
        unfold atom_sound_for_model in *.
        repeat iss_case.
        basic_goal_prep.
        rewrite TrieMap.Mmap_option_all in *.
        
        eapply In_option_all in Hma; eauto.
        2: eapply in_map; eauto.
        break.
        unfold Sep.has_key; rewrite H3; auto.
      }
      {
        repeat intro; 
        eapply eq_sound_monotone; eauto with utils.
      }
    }
    {
      cbn beta;intros; subst.
      eapply state_sound_for_model_bind; eauto with utils.
      {
        eapply find_sound.
        unfold atom_sound_for_model in *.
        repeat iss_case.
        basic_goal_prep.
        rewrite TrieMap.Mmap_option_all in *.
        subst.
        unfold Sep.has_key; rewrite Hma0; auto.
      }
      {
        cbn beta;intros; subst.
        eapply ret_sound_for_model'; eauto with utils.
        {
          unfold eq_atom_in_interpretation;
            basic_goal_prep;
            intuition subst; eauto.
          {
            eapply all2_Symmetric; eauto.
            apply eq_sound_for_model_Symmetric.
          }
          { apply eq_sound_for_model_Symmetric; auto. }
        }      
      }
    }
  Qed.
  
  Arguments db_lookup {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
    {analysis_result}%type_scope f args%list_scope _.

  
  (*TODO: preconditions?*)
  Lemma db_lookup_sound i f args
    : state_sound_for_model m i
        (db_lookup f args)
        (fun i' mx => i = i'
                      /\ mx <?> (fun x => atom_sound_for_model m i (Build_atom f args x))).
  Proof.
    open_ssm.
    basic_goal_prep;
      basic_utils_crush.
    case_match; cbn; try tauto.
    case_match; cbn; try tauto.
    unfold atom_sound_for_model; cbn.
    assert (atom_in_egraph (Build_atom f args (entry_value idx analysis_result d)) e).
    {
      unfold atom_in_egraph; cbn.
      rewrite case_match_eqn; cbn;
        rewrite case_match_eqn0; cbn.
      reflexivity.
    }
    eapply atom_interpretation in H0; eauto.
  Qed.

  Lemma state_sound_for_model_Mseq A B (i : idx_map (domain m)) (c1 : state instance A)
    P Q (c2 : state instance B)
    : state_sound_for_model m i c1 P ->
      (forall a (i' : idx_map (domain m)),
          map.extends i' i -> P i' a -> state_sound_for_model m i' c2 Q) ->
      state_sound_for_model m i (@! c1; c2) Q.
  Proof.
    intros.
    change (@! c1; c2) with (@! let _ <- c1 in c2).
    eapply state_sound_for_model_bind; eauto.
  Qed.
  
  Lemma same_domain_has_key A (m1 m2 : idx_map A)
    : map.same_domain m1 m2 <->
        (forall x : idx, Sep.has_key x m1 <-> Sep.has_key x m2).
  Proof using.
    clear idx_succ idx_zero.
    unfold map.same_domain, map.sub_domain,  Sep.has_key.
    intuition repeat case_match; eauto;
      try eapply H2 in case_match_eqn0; try eapply H1 in case_match_eqn;
      try eapply H1 in case_match_eqn0; try eapply H2 in case_match_eqn;
      try specialize (H0 k);
      rewrite ? H1, ?H2 in *;
      repeat case_match;
      break; try eexists; intuition eauto; try congruence.
    Unshelve.
    all: auto.
  Qed.
  
  (*TODO: move to UnionFind.v*)
  Lemma union_same_domain u u' x y i0 l
    : union_find_ok u l ->
      Sep.has_key x u.(parent) ->
      Sep.has_key y u.(parent) ->
      UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) u x y
      = (u', i0) ->
      map.same_domain u.(parent) u'.(parent).
  Proof using idx_map_ok Eqb_idx_ok.
    clear idx_succ idx_zero.
    unfold UnionFind.union.
    intros.
    eapply same_domain_has_key.
    intro k.
    do 2 case_match.
    pose proof case_match_eqn.
    pose proof case_match_eqn0.
    eapply find_spec in H4; eauto; break; try Lia.lia.
    eapply find_spec in H5; eauto; break; try Lia.lia.
    2:{ eapply H10; eauto. }
    eapply find_preserves_domain with (x:=k) in case_match_eqn, case_match_eqn0;
      eauto.
    2:{ eapply H10; eauto. }
    rewrite H10.
    case_match; autorewrite with inversion in *; break; subst; eauto.
    
    assert (Sep.has_key i (parent u)).
    {
      unfold Sep.has_key.      
      eapply forest_root_iff with (m:= parent u) in H6; eauto using uf_forest.
      rewrite H6; eauto.
    }
    assert (Sep.has_key i1 (parent u)).
    {
      unfold Sep.has_key.      
      eapply forest_root_iff with (m:= parent u) in H11; eauto using uf_forest.
      rewrite H11; eauto.
    }
    case_match; cbn in *; autorewrite with inversion in *; break; subst; cbn in *; eauto.
    all: rewrite H15.
    all: rewrite has_key_put.
    all: intuition subst; eauto.
  Qed.

  
  Lemma union_closure_implies_PER A R `{PER A R} R1 R2
    : (impl2 R1 R) -> (impl2 R2 R) -> impl2 (union_closure_PER R1 R2) R.
  Proof using.
    clear idx_succ idx_zero.
    unfold impl2;
      induction 3;
      basic_goal_prep;
      basic_utils_crush.
    { etransitivity; eassumption. }
    { symmetry; auto. }
  Qed.

  Instance eq_sound_for_model_PER i
    : PER (eq_sound_for_model m i).
  Proof using m_PER.
    clear idx_succ idx_zero.
    unfold eq_sound_for_model.
    constructor; repeat intro; repeat iss_case; cbn.
    { symmetry; auto. }
    { etransitivity; eassumption. }
  Qed.

  (*TODO: move to UnionFInd.v *)
  Arguments parent_rel [idx]%type_scope [idx_map] m _ _.
  
  (*TODO: move to UnionFind.v*)
  Lemma union_output l uf x y uf' z
    :  union_find_ok uf l ->
       Sep.has_key x (parent uf) ->
       Sep.has_key y (parent uf) ->
       UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) uf x y = (uf', z) ->
       parent_rel uf'.(parent) x z
       /\ parent_rel uf'.(parent) y z.
  Proof using idx_map_ok Eqb_idx_ok.
    clear idx_succ idx_zero.
    unfold UnionFind.union.
    intros.
    do 2 case_match.
    eapply find_spec in case_match_eqn; eauto; break; try Lia.lia.
    eapply find_spec in case_match_eqn0; eauto; break; try Lia.lia.
    2:{ eapply H9; eauto. }
    eqb_case i i0.
    {
      autorewrite with inversion in *; break; subst.
      intuition eauto.
      eapply H14.
      eapply union_find_limit; eauto.
      Lia.lia.
    }
    case_match.
    all: autorewrite with inversion in *; break; subst.
    all: basic_goal_prep.
    all: intuition eauto.
    all:lazymatch goal with
      |- parent_rel (map.put _ ?i0 _) ?x _ =>
        eqb_case x i0; [ eapply parent_rel_put_same; now eauto |]
    end.
    all: try now (eapply unloop_parent; eauto using uf_forest;
                  eapply H14; eapply union_find_limit; eauto; Lia.lia).
    all: eapply transitive_closure_transitive;
      [now (eapply unloop_parent; eauto using uf_forest;
            eapply H14; eapply union_find_limit; eauto; Lia.lia)|].
    all: eapply parent_rel_put_same; now eauto.
  Qed.
    
  Lemma union_sound i x y
    : eq_sound_for_model m i x y ->
      state_sound_for_model m i (Defs.union x y)
        (fun i' a => i = i' /\ eq_sound_for_model m i' x a).
  Proof.
    intros; open_ssm'.
    basic_goal_prep.
    eqb_case x y.
    { basic_goal_prep; intuition eauto with utils. }
    case_match.
    destruct (egraph_equiv_ok _ e0).
    pose proof case_match_eqn as Hdom.
    eapply union_spec in case_match_eqn; try Lia.lia; eauto.
    2:{
      eapply interpretation_exact; eauto.
      eapply eq_sound_has_key_r; symmetry; eauto.
    }
    2:{
      eapply interpretation_exact; eauto.
      eapply eq_sound_has_key_r; eauto.
    }
    break.
    eqb_case x i0; basic_goal_prep.
    {
      intuition eauto with utils.
      { eapply eq_sound_for_model_trans; try eassumption; symmetry; now eauto. }
      {
        constructor; cbn.
        eexists; eauto.
      }
      {
        destruct e1; constructor; cbn; eauto.
        {
          intros x H'; apply interpretation_exact0 in H'.
          eapply union_same_domain in Hdom; eauto.
          { eapply same_domain_has_key in Hdom; eapply Hdom; eauto. }
          {
            symmetry in H0; eapply eq_sound_has_key_r in H0.
            eapply interpretation_exact0; eauto.
          }
          {
            eapply eq_sound_has_key_r in H0.
            eapply interpretation_exact0; eauto.
          }
        }
        {
          intros.
          eapply H6 in H7.
          revert H7; eapply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
          unfold singleton_rel, impl2; basic_goal_prep; subst; eauto.
        }
        { split; auto; symmetry; auto. }
      }
    }
    intuition try constructor; basic_goal_prep; intuition eauto with utils.    
    { eapply union_output in Hdom; eauto.
      2:{
        symmetry in H0; eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      2:{
        eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      break.
      eapply trans_PER_subrel in H8; eapply H6 in H8.
      revert H8; apply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
      {
        repeat intro.
        eapply rel_interpretation; eauto.
      }
      { unfold singleton_rel, impl2; basic_goal_prep; subst; auto. }
    }
    { eapply idx_interpretation_wf; eauto. }
    {
      eapply interpretation_exact in H8; eauto.
      eapply union_same_domain in Hdom; eauto.
      { eapply same_domain_has_key in Hdom; eapply Hdom; eauto. }
      {
        symmetry in H0; eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      {
        eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
    }
    { eapply atom_interpretation in e1; eauto. }
    {
      eapply H6 in H8.
      revert H8; apply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
      {
        repeat intro.
        eapply rel_interpretation; eauto.
      }
      { unfold singleton_rel, impl2; basic_goal_prep; subst; auto. }
    }
    { eapply parents_interpretation; eauto. }
    2:{ eapply worklist_sound; eauto. }    
    { eapply union_output in Hdom; eauto.
      2:{
        symmetry in H0; eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      2:{
        eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      break.
      eapply trans_PER_subrel in H8; eapply H6 in H8.
      revert H8; apply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
      {
        repeat intro.
        eapply rel_interpretation; eauto.
      }
      { unfold singleton_rel, impl2; basic_goal_prep; subst; auto. }
    }
  Qed.

  
  Lemma interprets_to_functional f args d d'
    : interprets_to m f args d ->
      interprets_to m f args d' ->
      m.(domain_eq) d d'.
  Proof.
    unfold interprets_to.
    basic_goal_prep.
    replace x0 with x in * by congruence.
    etransitivity; eauto; symmetry; eauto.
  Qed.

  Lemma get_analyses_sound i args
    : state_sound_for_model m i
         (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result args) 
         (fun i' _ => i = i').
  Proof.
    open_ssm'.
    split; eauto.
    case_match; basic_goal_prep; intuition eauto with utils.
  Qed.

  Lemma update_analyses_sound i o a
    : state_sound_for_model m i
        (update_analyses idx symbol symbol_map idx_map idx_trie analysis_result o a)
         (fun i' _ => i = i').
  Proof.
    open_ssm.
  Qed.
  
  Lemma set_eq_empty_l A (l : list A) : set_eq [] l <-> l = [].
  Proof using.
    clear.
    unfold set_eq, incl; 
      basic_goal_prep;
      basic_utils_crush.
    destruct l; auto.
    basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite set_eq_empty_l : utils.

  Lemma all_incl A (l1 l2 : list A) P
    : incl l1 l2 -> all P l2 -> all P l1.
  Proof using.
    clear.
    revert l2; induction l1;
      basic_goal_prep;
      basic_utils_crush.
    eapply in_all; eauto.
  Qed.
      
  Lemma db_set_sound i a
    : atom_sound_for_model m i a ->
      state_sound_for_model m i
        (db_set idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result a)
        (fun i' _ => i = i').
  Proof.
    cleanup_context.
    unfold db_set.
    intros.
    eapply state_sound_for_model_bind; eauto using get_analyses_sound with utils.
    cbn beta; intros; subst.
    eapply state_sound_for_model_bind; eauto using update_analyses_sound with utils.
    cbn beta; intros; subst.
    unfold db_set'.
    unfold state_sound_for_model, Sep.and1.
    repeat intro; eexists; split; cbn; intuition eauto.
    { destruct H4; constructor; basic_goal_prep; intuition eauto. }
    {
      destruct H5; constructor; basic_goal_prep; intuition eauto.
      {
        unfold atom_in_egraph in H3; cbn in H3.
        eqb_case (atom_fn a) (atom_fn a2);
          [ rewrite H5 in *; rewrite get_update_same in *
          | rewrite get_update_diff in * ]; eauto.
        basic_goal_prep.
        case_match.
        {
          eqb_case (atom_args a) (atom_args a2);
          [ rewrite H6 in *; rewrite map.get_put_same in *
          | rewrite map.get_put_diff in * ]; repeat iss_case;
            autorewrite with inversion in *; break; subst; cbn in *; eauto.
          { replace a2 with a in * by (destruct a, a2; cbn in *; congruence); eauto. }
          {
            apply atom_interpretation0; unfold atom_in_egraph.
            rewrite case_match_eqn; cbn.
            rewrite Hma; cbn.
            eauto.
          }
        }
        {
          eqb_case (atom_args a) (atom_args a2);
          [ rewrite H6 in *; rewrite map.get_put_same in *
          | rewrite map.get_put_diff in * ]; repeat iss_case;
            autorewrite with inversion in *; break; subst; cbn in *; eauto.
          { replace a2 with a in * by (destruct a, a2; cbn in *; congruence); eauto. }
          {
            change (map.get map.empty (atom_args a2) = Some d) in Hma.
            basic_utils_crush.
          }
        }
      }
      {
        change (map.get
                  (fold_left (fun m x => map_update m x (cons a))
                     (dedup (eqb (A:=_)) (a.(atom_ret)::a.(atom_args))) e.(parents))
                  i = Some l) in H3.
        destruct (map.get (parents e) i) eqn:Hpe.
        2:{
          assert (incl l [a]).
          {
            assert (map.get (parents e) i <?> (fun l => incl l [a])).
            { rewrite Hpe; cbn; auto. }
            revert H5 l H3.
            generalize (parents e);
            generalize (dedup eqb (atom_ret a :: atom_args a)).
            induction l;
              basic_goal_prep;
              basic_utils_crush.
            { rewrite H3 in *; cbn in *; auto. }
            {
              eapply IHl in H3; eauto.
              eqb_case i a1.
              {
                rewrite get_update_same; cbn; eauto.
                case_match; cbn in *; eauto with utils.
                basic_utils_crush.
              }
              { rewrite get_update_diff; cbn; eauto. }
            }
          }
          eapply all_incl; eauto; cbn; intuition eauto.
        }
        assert (incl l (cons a l0)).
        {
          revert H3 Hpe.
          revert l l0;
            generalize (parents e);
            generalize (dedup eqb (atom_ret a :: atom_args a)).
          induction l;
            basic_goal_prep;
            basic_utils_crush.
          { replace l0 with l by congruence; eauto with utils. }
          {
            eqb_case i a1; eapply IHl with (r:=(map_update r a1 (cons a))) in H3.
            2:{ rewrite get_update_same, Hpe; eauto. }
            3:{ rewrite get_update_diff, Hpe; eauto. }
            2: now eauto with utils.
            revert H3; clear; unfold incl; cbn; intuition eauto.
            eapply H3 in H.
            intuition subst; eauto.
          }
        }
        eapply all_incl; try eassumption.
        cbn; intuition eauto.
      }
    }    
  Qed.
  
  Lemma update_entry_sound i a
    : atom_sound_for_model m i a ->
      state_sound_for_model m i (update_entry a)
        (fun i' _ => i = i').
  Proof.
    cleanup_context.
    unfold update_entry.
    intros.
    eapply state_sound_for_model_bind; eauto using db_lookup_sound with utils.
    cbn beta;intros; subst.
    case_match; cbn in H2.
    {
      eapply state_sound_for_model_Mseq; eauto with utils.
      {
        apply union_sound.
        unfold atom_sound_for_model in *; basic_goal_prep; repeat iss_case.
        autorewrite with inversion in *; subst.
        eapply interprets_to_functional in H3; try apply H0.
        unfold eq_sound_for_model.
        rewrite Hma0; cbn; rewrite Hma2; cbn; symmetry; eauto.
      }
      {
        intros; subst.
        eapply ret_sound_for_model'; intuition subst; eauto with utils.
        break; subst; eauto.
      }
    }        
    { break; subst; eapply db_set_sound; eauto. }
  Qed.

  Context `{model_ok m}.
  
  Lemma eq_atom_implies_sound_l i a3 a1 
    : eq_atom_in_interpretation i a3 a1 ->
      atom_sound_for_model m i a3 -> atom_sound_for_model m i a1.
  Proof.
    clear idx_succ idx_zero.
    unfold eq_atom_in_interpretation, eq_sound_for_model, atom_sound_for_model, interprets_to.
    intuition eauto.
    rewrite <- TrieMap.all2_map_l
      with (f:= map.get i)
           (R:= (fun x y => x <$> (fun x' : domain m => map.get i y <$> domain_eq m x')))
      in H1.
    eapply all2_Is_Some_satisfying_l in H1.
    rewrite !TrieMap.Mmap_option_all in *.
    repeat iss_case; cbn in *.
    rewrite <- TrieMap.all2_map_r
      with (f:= map.get i)
           (R:= fun x y => y <$> domain_eq m x)
      in H1.
    eapply all2_Is_Some_satisfying_r in H1.
    repeat iss_case; cbn in *; break.
    rewrite H3 in *.
    apply interpretation_preserving with (f:=(atom_fn a1)) in H1.
    autorewrite with inversion in *; break; subst.
    erewrite H2 in *.
    cbn in *; case_match; try tauto.
    eexists; split; eauto.
    repeat (etransitivity; try eassumption;[]).
    symmetry; eauto.
  Qed.
  
  
  Instance eq_atom_interp_sym i : Symmetric (eq_atom_in_interpretation i).
  Proof.
    clear idx_succ idx_zero.
    unfold eq_atom_in_interpretation; repeat intro; basic_goal_prep;
      repeat (iss_case; cbn in * ).
    intuition eauto.
    {
      apply all2_Symmetric; eauto.
      apply eq_sound_for_model_Symmetric; eauto.
    }
    { symmetry; eauto. }
  Qed.

  

    
  Lemma db_lookup_entry_sound i f args
    : state_sound_for_model m i
        (db_lookup_entry idx symbol symbol_map idx_map idx_trie analysis_result
           f args) (fun i' e => i' = i
                                /\ e <?> (fun e => atom_sound_for_model m i
                                        (Build_atom f args e.(entry_value _ _)))).
  Proof.
    open_ssm.
    intuition eauto with utils.
    basic_goal_prep.
    case_match; cbn; auto.
    case_match; cbn; auto.
    assert (atom_in_egraph (Build_atom f args d.(entry_value _ _)) e).
    {
      unfold atom_in_egraph; cbn.
      rewrite case_match_eqn; cbn.
      rewrite case_match_eqn0; cbn.
      reflexivity.
    }
    eapply atom_interpretation; eauto.
  Qed.
  
  
  Lemma push_worklist_sound_analysis i o
    : state_sound_for_model m i
        (push_worklist idx symbol symbol_map idx_map idx_trie analysis_result
           (analysis_repair idx o)) 
        (fun i' _ => i = i').
  Proof.
    open_ssm.
    cbn; eauto.
  Qed.

  Ltac bind_with_fn H :=
    eapply state_sound_for_model_bind;
    eauto using H with utils;
    cbn beta;intros; subst; cleanup_context.
  
  Ltac ssm_bind :=
    eapply state_sound_for_model_bind;
    eauto with utils;
    cbn beta in *;intros; subst; cleanup_context.

  Lemma db_set_entry_sound i f args entry_epoch entry_value a
    : atom_sound_for_model m i (Build_atom f args entry_value) ->
      state_sound_for_model m i
       (db_set_entry idx symbol symbol_map idx_map idx_trie analysis_result 
          f args entry_epoch entry_value a) 
         (fun i' _ => i = i').
  Proof.
    intro Hsound.
    open_ssm.
    intuition eauto with utils.
    unfold atom_in_egraph in *; cbn in *.
    repeat iss_case.
    eqb_case f (atom_fn a0).
    {
      rewrite get_update_same in* by eauto.
      inversions.
      case_match.
      all: eqb_case args (atom_args a0).
      all: rewrite ?map.get_put_same in * by eauto; inversions; cbn in *; subst; eauto.
      all: rewrite  ?map.get_put_diff in * by eauto; inversions;cbn in *; subst; eauto.
      {
        eapply atom_interpretation0; rewrite case_match_eqn; cbn.
        rewrite Hma0; cbn.
        eauto.
      }
      {
        exfalso.
        change (map.get map.empty (atom_args a0) = Some d) in Hma0.
        rewrite map.get_empty in *.
        congruence.
      }
    }
    {
      rewrite get_update_diff in * by eauto.
      apply atom_interpretation0.
      rewrite Hma; cbn.
      rewrite Hma0;cbn.
      eauto.
    }   
  Qed.    

  Lemma repair_parent_analysis_sound i a
    : state_sound_for_model m i
        (repair_parent_analysis idx symbol
           symbol_map idx_map idx_trie analysis_result a)
         (fun i' _ => i = i').
  Proof.
    cleanup_context.
    unfold repair_parent_analysis.
    bind_with_fn db_lookup_entry_sound.
    case_match; break; subst.
    2:{ eapply ret_sound_for_model'; eauto with utils. }
    case_match.
    cbn in H3.
    bind_with_fn get_analyses_sound.
    cbn beta;intros; subst.
    case_match.
    { eapply ret_sound_for_model'; eauto with utils. }
    bind_with_fn update_analyses_sound.
    bind_with_fn push_worklist_sound_analysis.
    apply db_set_entry_sound; auto.
  Qed.

  Lemma state_sound_for_model_Mfoldl A B i P_const P_acc l (f : B -> A -> state instance B) acc
    : (forall (a:A) acc i', In a l ->
                            map.extends i' i ->
                            P_const i' ->
                            P_acc i' acc ->
                            state_sound_for_model m i' (f acc a)
                              (fun i' acc => P_const i' /\ P_acc i' acc)) ->
      P_const i ->
      P_acc i acc ->
      monotone1 P_acc ->
      state_sound_for_model m i (list_Mfoldl f l acc)
        (fun i' acc => P_const i' /\ P_acc i' acc).
  Proof.
    cleanup_context.
    revert i acc.
    induction l.
    {
      intros.
      eapply state_triple_wkn_ret;
        unfold Sep.and1 in *;
        basic_goal_prep; subst;
        eexists; cbn; intuition eauto with utils.
    }
    {
      intros.
      cbn [list_Mfoldl].
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        basic_goal_prep;
          basic_utils_crush.
      }
      intros.
      eapply IHl; eauto.
      all:basic_goal_prep;
        basic_utils_crush.
      eapply H1.
      all:basic_goal_prep;
        basic_utils_crush.
      eapply map_extends_trans; eauto.
    }
  Qed.
  
  Lemma atom_sound_functional i f args r1 r2
    : atom_sound_for_model m i (Build_atom f args r1) ->
      atom_sound_for_model m i (Build_atom f args r2) ->
      eq_sound_for_model m i r1 r2.
  Proof.
    clear idx_succ idx_zero.
    unfold atom_sound_for_model, eq_sound_for_model; cbn.
    intros; repeat iss_case; inversions; cbn.
    eapply interprets_to_functional; eauto.
  Qed.
  Hint Resolve atom_sound_functional : utils.
  
  Lemma add_parent_sound i ps p
    : atom_sound_for_model m i p ->
      all (atom_sound_for_model m i) ps ->
      state_sound_for_model m i
        (add_parent idx Eqb_idx idx_zero symbol Eqb_symbol symbol_map idx_map idx_trie
           analysis_result ps p)
        (fun i' a => i = i' /\ all (atom_sound_for_model m i') a).
  Proof.
    intro.
    induction ps; cbn [add_parent]; intros.
    { eapply ret_sound_for_model'; cbn; eauto with utils. }
    {
      case_match.
      cbn [all Defs.atom_ret] in *; break.
      case_match.
      eqb_case atom_fn0 atom_fn; 
        cbn - [Mbind Mret].
      1:eqb_case atom_args0 atom_args; 
        cbn - [Mbind Mret].
      {
        ssm_bind.
        {
          eapply union_sound; eauto.
          eapply atom_sound_functional; eauto.
        }
        cbn beta in *; subst.
        eapply ret_sound_for_model'; break; subst; eauto with utils.
        cbn; intuition eauto with utils.
        unfold atom_sound_for_model; cbn in *.
        unfold atom_sound_for_model in H1; cbn in *; subst.
        unfold eq_sound_for_model in H6.
        repeat (iss_case; cbn).
        unfold interprets_to in *; break; subst.
        exists x; intuition eauto.
        etransitivity; eauto.
      }
      {
        ssm_bind.
        eapply ret_sound_for_model'; break; subst; eauto with utils.
        cbn; intuition eauto.
      }
      {
        ssm_bind.
        eapply ret_sound_for_model'; break; subst; eauto with utils.
        cbn; intuition eauto.
      }
    }
  Qed.

  Lemma set_parents_sound i new_idx l
    : all (atom_sound_for_model m i) l ->
      state_sound_for_model m i
        (set_parents idx symbol symbol_map idx_map idx_trie analysis_result new_idx l) 
        (fun i' _ => i = i').
  Proof.
    intros.
    open_ssm.
    intuition cbn in *; eauto with utils.
    eqb_case i0 new_idx.
    { rewrite map.get_put_same in *; inversions; eauto. }
    { rewrite map.get_put_diff in *; eauto. }
  Qed.
        
  
  Lemma repair_sound i a
    : state_sound_for_model m i
        (repair idx_zero a)
        (fun i' _ => i = i').
  Proof.
    cleanup_context.
    destruct a; cbn [repair].
    {
      unfold repair_union.
      eapply state_sound_for_model_bind;
        [ eapply get_parents_sound |].
      cbn beta;intros; subst.
      eapply state_sound_for_model_bind; eauto with utils.
      { eapply remove_parents_sound. }
      cbn beta;intros; subst.
      eapply state_sound_for_model_bind; break; subst; eauto with utils.
      {
        eapply state_sound_for_model_Mmap with (P_const:= eq i'); auto with utils.
        cbn beta;intros; subst.
        eapply state_sound_for_model_bind; eauto with utils.
        { eapply db_remove_sound. }
        cbn beta;intros; subst.
        eapply state_sound_for_model_bind; eauto with utils.
        {
          eapply canonicalize_sound.
          eapply in_all; eassumption.
        }
        {
          cbn beta;intros; break; subst.
          eapply state_sound_for_model_bind; eauto with utils.
          {
            eapply update_entry_sound; eauto with utils.
            eapply eq_atom_implies_sound_l; try symmetry; eauto.
            eapply in_all; eauto.
          }
          cbn beta;intros; break; subst.
          eapply ret_sound_for_model'; intuition eauto with utils.
          eapply eq_atom_implies_sound_l; try symmetry; eauto.
          eapply in_all; eauto.
        }
      }
      cbn beta;intros; subst.
      bind_with_fn get_parents_sound.
      eapply state_sound_for_model_Mseq; break; subst; eauto with utils.
      {
        case_match.
        {
          eapply state_sound_for_model_Miter with (P:= fun i' _ => i'1 = i'); auto with utils.
          cbn beta;intros; subst.
          cleanup_context.
          apply repair_parent_analysis_sound.
        }
        { eapply ret_sound_for_model'; eauto with utils. }
      }
      cbn beta;intros; subst.
      ssm_bind.
      {
        eapply state_sound_for_model_Mfoldl with (P_const:= eq i'); auto.
        {
          cbn beta;intros; subst.
          eapply add_parent_sound; eauto.
          eapply in_all;[| eauto]; auto.
        }
        { cbn; auto. }
        { cbn; eauto with utils. }
      }
      {
        cbn in *; break; subst.
        apply set_parents_sound; eauto.
      }        
    }
    {
      bind_with_fn get_parents_sound.
      eapply state_sound_for_model_Miter; break; subst; auto.
      cbn beta;intros; break; subst.
      eapply repair_parent_analysis_sound.
    }
  Qed. 

  Lemma rebuild_sound i n
    : state_sound_for_model m i (rebuild n) (fun i' _ => i = i').
  Proof.
    induction n.
    {
      basic_goal_prep.
      cbv -[map.rep domain map.get]; intuition.
      eexists; intuition eauto.
    }
    {
      cbn [rebuild].
      eapply state_sound_for_model_bind;
      [eapply pull_worklist_sound
      | intros; subst].
      destruct a.
      { eapply ret_sound_for_model'; break; subst; eauto with utils. }
      eapply state_sound_for_model_bind; eauto with utils.
      {
        eapply state_sound_for_model_Mmap with (P_const:= eq i'); auto.
        {
          intros; break; subst.
          eapply canonicalize_worklist_entry_sound.
          eapply in_all; eauto.
        }
        { eauto using worklist_entry_sound_mono. }
      }
      cbn beta; intros; repeat subst.
      eapply state_sound_for_model_bind; break; subst; eauto with utils.
      {
        eapply state_sound_for_model_Miter with (P:= fun i _ => i'0 = i); auto.
        {
          intros; break; subst.
          cleanup_context.
          eapply repair_sound.
        }
      }
      cbn beta; intros; repeat subst.
      eauto.
    }
  Qed.      
      
End WithMap.

Arguments atom_in_egraph {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope
  a i.

(*
Arguments model_of {idx}%type_scope {symbol}%type_scope {idx_map}%function_scope m rw%list_scope.
*)

Arguments seq_assumptions {idx symbol}%type_scope s.
Arguments seq_conclusions {idx symbol}%type_scope s.

Arguments forall_vars {idx symbol}%type_scope s.
Arguments exists_vars {idx}%type_scope {Eqb_idx} {symbol}%type_scope s.
Arguments sequent_vars {idx symbol}%type_scope s.

Arguments eq_clause {idx symbol}%type_scope x y.
Arguments atom_clause {idx symbol}%type_scope a.


Arguments clauses_to_instance {idx}%type_scope {Eqb_idx}
  idx_succ%function_scope {idx_zero}
  {symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope
  {H}
  l%list_scope _ _.


Arguments instance_to_clauses {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope i.


Arguments db_to_atoms {idx symbol}%type_scope
  {symbol_map idx_trie}%function_scope 
  {analysis_result}%type_scope
  d.


Arguments uf_to_clauses {idx symbol}%type_scope {idx_map}%function_scope u.


Arguments state_sound_for_model {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope {analysis_result}%type_scope 
  {A}%type_scope m i s (Post)%function_scope.


Arguments model_satisfies_rule {idx symbol}%type_scope {idx_map}%function_scope m r.


(*TODO: duplicated in section *)
Ltac open_ssm' :=
    cleanup_context;
    lazymatch goal with
    | |- state_sound_for_model _ _ ?e _ =>
        let h := get_head e in
        unfold h; unfold state_sound_for_model, Sep.and1; repeat intro;
        eexists; eauto with utils;
        break; cbn[fst snd]
    end.

Ltac open_ssm :=
  open_ssm';
  intuition eauto with utils;
  break; cbn[fst snd];
  try lazymatch goal with
    | H : egraph_ok _ |- egraph_ok _ =>
        destruct H; constructor; eauto with utils
    | H : egraph_sound_for_interpretation _ _ _
      |- egraph_sound_for_interpretation _ _ _ =>
        destruct H; constructor; eauto with utils
    end.


(*TODO: duplicated in section *)
Ltac bind_with_fn H :=
  eapply state_sound_for_model_bind;
  eauto using H with utils;
  cbn beta;intros; subst; cleanup_context.

(*TODO: duplicated in section *)
Ltac ssm_bind :=
  eapply state_sound_for_model_bind;
  eauto with utils;
  cbn beta in *;intros; subst; cleanup_context.
