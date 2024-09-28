(* An implementation of the core of egglog

   TODO: benchmark, then use plist everywhere feasible and retest
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind FunctionalDB QueryOpt.
From Utils Require TrieMap.
Import Sets.
Import StateMonad.


(*TODO: move somewhere*)
Definition Is_Some_satisfying {A} (P : A -> Prop) x :=
  match x with
  | Some x => P x
  | None => False
  end.
Notation "x <$> P" :=
  (Is_Some_satisfying P x)
    (at level 56,left associativity).

(*TODO: move somewhere *)
Section TransitiveClosure.
  Context {A} (R : A -> A -> Prop).
  Inductive transitive_closure : A -> A -> Prop :=
  | trans_base a b : R a b -> transitive_closure a b
  | trans_step a b c : R a b -> transitive_closure b c -> transitive_closure a c.
  Hint Constructors  transitive_closure : utils.
  
  Lemma transitive_closure_step_r a b c
    : transitive_closure a b -> R b c -> transitive_closure a c.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Resolve transitive_closure_step_r : utils.
    
  Lemma transitive_closure_trans
    : Transitive transitive_closure.
  Proof.
    intros a b c H1 H2.
    revert H1.
    induction H2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma transitive_closure_sym
    : Symmetric R -> Symmetric transitive_closure.
  Proof.
    intros Hsym a b.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma transitive_closure_refl
    : Reflexive R -> Reflexive transitive_closure.
  Proof.
    intros Hrefl a.
    basic_goal_prep;
      basic_utils_crush.
  Qed.  
  
  Lemma transitive_closure_equiv
    : Equivalence R -> Equivalence transitive_closure.
  Proof.
    destruct 1; constructor;
      eauto using transitive_closure_trans,
      transitive_closure_sym,
      transitive_closure_refl.
  Qed.

End TransitiveClosure.
#[export] Hint Constructors transitive_closure : utils.
#[export] Hint Resolve transitive_closure_equiv : utils.

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)

      (*TODO: just extend to Natlike?*)
      (idx_succ : idx -> idx)
      (idx_zero : idx)
      (*TODO: any reason to have separate from idx?*)
      (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol).

  Notation atom := (atom idx symbol).

  Definition atom_subst (sub : named_list idx idx) (a : atom) :=
    Build_atom
      a.(atom_fn)
      (map (fun x => named_list_lookup x sub x) a.(atom_args))
      (named_list_lookup a.(atom_ret) sub a.(atom_ret)).
  
  Definition lift_idx_eq (ieq:idx -> idx -> Prop) (a b : atom) : Prop :=
    a.(atom_fn) = b.(atom_fn)
    /\ Forall2 ieq a.(atom_args) b.(atom_args)
    /\ ieq a.(atom_ret) b.(atom_ret).

  Definition reflexively {A} (R : relation A) : A -> Prop :=
    fun a => R a a.


  Definition idx_closure (R_idx : relation idx) : relation atom -> relation atom :=
    union_closure (lift_idx_eq R_idx).

  Record eqlog_data : Type :=
    {
      R_idx : relation idx;
      P_atom : atom -> Prop;
    }.

  Definition R_atom d a b := lift_idx_eq d.(R_idx) a b /\ d.(P_atom) a.                  

  Record eqlog_data_wf (d : eqlog_data) : Prop :=
    {
      (* TODO Equivalence or PER? an equiv prob. wouldn't hurt, R_atom is still a PER*)
      R_idx_equiv : Equivalence d.(R_idx);
      P_atom_respects_R_idx : forall a b, R_atom d a b -> d.(P_atom) b;
    }.

  
  
  Definition functional_dependence (P : atom -> Prop) : relation idx :=
    fun x y => exists f args, P (Build_atom f args x) /\ P (Build_atom f args y).
  
  Local Definition ifc R (P : atom -> Prop) :=
    transitive_closure (fun x y => R x y \/ functional_dependence P x y).
  
  Section __.
    Context (P : atom -> Prop)
      (R : relation idx).
    
    Inductive atom_functional_closure : atom -> Prop :=
    | atom_base a : P a -> atom_functional_closure a
    | atom_idx_closure a b
      : atom_functional_closure a ->
        lift_idx_eq (ifc R atom_functional_closure) a b ->
        atom_functional_closure b.

    (* TODO: prove it's an equivalence relation *)
    Definition idx_functional_closure : relation idx :=
      ifc R atom_functional_closure.

  End __.

  (* Assumes rule wf, d wf, & fresh assignment wf wrt rule *)
  Definition interp_rule_step
    (r : uncompiled_rw_rule idx symbol) (d : eqlog_data)
    (fresh_assignment : named_list idx idx)
    : eqlog_data :=
    let new_atoms query_assignment :=
      map (atom_subst (fresh_assignment ++ query_assignment)) r.(uc_write_clauses _ _)
    in
    let new_unions query_assignment :=
      let sub := fresh_assignment ++ query_assignment in
      map (fun '(x,y) => (named_list_lookup x sub x, named_list_lookup y sub y))
        r.(uc_write_unifications _ _)
    in
    let assignment_valid a :=
      map fst a = r.(uc_query_vars _ _)
      /\ all d.(P_atom) (map (atom_subst a) r.(uc_query_clauses _ _)) in
    let P' x := d.(P_atom) x \/ exists qa, assignment_valid qa /\ In x (new_atoms qa) in
    let R' x y := d.(R_idx) x y
                  \/ exists qa, assignment_valid qa
                                /\ (In (x,y) (new_unions qa)
                                    \/ In (y,x) (new_unions qa))
    in
    {|
      R_idx := idx_functional_closure P' R';
      P_atom := atom_functional_closure P' R';
    |}.

  Definition idx_fresh_in_atoms (P : atom -> Prop) x : Prop :=
    forall a, P a -> ~ In x (a.(atom_ret)::a.(atom_args)).
  
  Definition fresh_assignment_valid
    (fa : named_list idx idx)
    (r :uncompiled_rw_rule idx symbol)
    (S : eqlog_data) : Prop :=
    all_fresh fa
    /\ incl (map atom_ret r.(uc_write_clauses _ _)) (map fst fa ++ r.(uc_query_vars _ _))
    /\ all (idx_fresh_in_atoms S.(P_atom)) (map snd fa).
  
  (* Note: this applies the rules in order, whereas the egraph applies them in parallel.
     There is no difference in the limit though.
   *)
  Inductive interp_eqlog (l : list (uncompiled_rw_rule idx symbol)) (S0 : eqlog_data) : eqlog_data -> Prop :=
  | interp_eqlog_base : interp_eqlog l S0 S0
  | interp_eqlog_step S1 r fa
    : interp_eqlog l S0 S1 ->
      In r l ->
      fresh_assignment_valid fa r S1 ->
      interp_eqlog l S0 (interp_rule_step r S1 fa).

  Lemma functional_dependence_sym P
    : Symmetric (functional_dependence P).
  Proof.
    unfold functional_dependence.
    intros x y H;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    
  Lemma idx_functional_closure_equiv P R
    : Reflexive R -> Symmetric R -> Equivalence (idx_functional_closure P R).
  Proof.
    unfold idx_functional_closure, ifc.
    constructor.
    1:eapply transitive_closure_refl; eauto.
    {
      eapply transitive_closure_sym; eauto.
      intros x y H';
        destruct H'; [ left | right]; eauto.
      apply functional_dependence_sym.
      eauto.
    }
    {
      eapply transitive_closure_trans.
    }
  Qed.

  Lemma interp_rule_step_inflationary r S fa x
    : S.(P_atom) x -> (interp_rule_step r S fa).(P_atom) x.
  Proof.
    destruct S; cbn.
    intros; eapply atom_base.
    intuition eauto.
  Qed.
  
  Lemma interp_rule_step_wf r S fa
    : eqlog_data_wf S -> eqlog_data_wf (interp_rule_step r S fa).
  Proof.
      destruct 1;
      constructor.
    {
      destruct R_idx_equiv0.
      apply idx_functional_closure_equiv.
      all: unfold Reflexive,  Symmetric; basic_goal_prep; intuition eauto.
      basic_goal_prep; intuition eauto.
    }
    {
      intros.
      unfold R_atom in *; break.
      unfold interp_rule_step in *.
      cbn in*.
(*      intros; eapply interp_rule_step_inflationary.
      unfold R_atom in *; break.
      induction H0; intuition eauto.
      
      
      eapply P_atom_respects_R_idx0.
      intros; break.
      revert b H.
      induction H0; intuition eauto.
      {
        TODO: looks false!.
        ridx is smaller on output than input
        cbn in H.
        pose proof (fun b H => P_atom_respects_R_idx0 a b (conj H H0)).
        TODO: base case; use inflationary principle
        eapply P_atom_respects_R_idx0 in H0.
      basic_goal_prep.
        , lift_idx_eq, interp_rule_step  in *;
        basic_goal_prep; intuition eauto.
      induction H0
  Qed. *)
  Abort.


(* Alternate approach: consider the initial model of the theory.
   Terms added at the start form a no-premise rule, so can be ignored.
 *)
  Record model : Type :=
    {
      (* represents the quotiented idx.
         TODO: to realize the quotient, should I include a domain equiv?
         - would let me use e.g. terms as the domain
         - alternatively, I can use idx as the domain, and take the quotient
           to be implied by the non-bijectivity of constants.
       *)
      domain : Type;
      (* included to support setoids *)
      domain_eq : domain -> domain -> Prop;
      (*constants : idx -> domain; TODO: do I have any constants? *)
      interpretation : symbol -> list domain -> option domain;
    }.

  (*TODO: implement*)
  Axiom assignment_satisfies
    : forall m, named_list idx m.(domain) -> list atom -> Prop.

  Axiom TODO_domain : forall {m}, m.(domain).
  (* TODO: handle domain being possibly empty.
     (assignment lookup default)
   *)
  Record model_of
    (m : model)
    (rw : list (uncompiled_rw_rule idx symbol)) : Prop :=
    {
      (* TODO: does it need to be an equivalence? *)
      domain_eq_PER : PER m.(domain_eq);
      unifications_sound
      : forall r,
        In r rw ->
        forall assignment,
          assignment_satisfies m assignment r.(uc_query_clauses _ _) ->
          forall x y, In (x,y) r.(uc_write_unifications _ _) ->
                      m.(domain_eq) (named_list_lookup TODO_domain assignment x)
                          (named_list_lookup TODO_domain assignment y);
      write_clauses_sound
      : forall r,
        In r rw ->
        forall assignment,
          assignment_satisfies m assignment r.(uc_query_clauses _ _) ->
          forall a, In a r.(uc_write_clauses _ _) ->
                    m.(interpretation) a.(atom_fn)
                      (map (named_list_lookup TODO_domain assignment) a.(atom_args))
                    = named_list_lookup_err assignment a.(atom_ret)
    }.

  (*
  Record model_morphism (m1 m2 : model) : Type :=
    {
      domain_morphism : m1.(domain) -> m2.(domain);
      domain_eq_morphism
      : forall x y, m1.(domain_eq) x y -m2.(domain_eq) (domain_morphism x) (domain_morphism y);
      interpretation_morphism
      : forall f s, option_map domain_morphism (m1.(interpretation) f s)
                    = m2.(interpretation) f (map domain_morphism s);      
    }.

  Record initial_model rw m :=
    {
      initial_model_wf : model_of m rw;
      is_initial : forall m', model_of m' rw -> model_morphism m m';
    }.

  *)
(*
  Sketch:
  1. egraph soundly underapproximates the rules
  2. rules hold in all models
  3. terms are a model
 *)

  
  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_plus : map_plus symbol_map)
    (symbol_map_ok : forall A, map.ok (symbol_map A)).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_plus : map_plus idx_trie).

  Notation instance := (instance idx symbol symbol_map idx_map idx_trie).
  (*TODO: many of these relations can be functions. what's the best way to define them?*)
  Definition atom_in_egraph '(Build_atom f args out) (i : instance) :=
    (map.get i.(db _ _ _ _ _) f) <$>
      (fun tbl => (map.get tbl args) <$>
                    (fun r => snd r = out)).

  Definition SomeRel {A B} (R : A -> B -> Prop) ma mb :=
    match ma, mb with
    | Some a, Some b => R a b
    | _, _ => False
    end.

  (* TODO: this is parametric, use the initial model instead? No.
     TODO: this is proof relevant; keep it that way or no?
   *)
  Record egraph_sound_for_model e m :=
    {
      (*  TODO: Is this the best way? Could also identify idxs w/ terms/atom trees
         terms/atom trees from the initial model.

         TODO: how to ensure this covers the whole domain?
       *)
      idx_interpretation : idx -> option m.(domain);
      (* TODO: write in a more natural way*)
      atom_interpretation :
      forall a,
        atom_in_egraph a e ->
        (Mbind (m.(interpretation) a.(atom_fn))
           (list_Mmap idx_interpretation a.(atom_args))) <$>
          (fun d => (idx_interpretation a.(atom_ret)) <$> (m.(domain_eq) d));
    }.

  Definition egraph_sound e rs :=
    forall m : model,
      model_of m rs ->
      egraph_sound_for_model e m.

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).

  Theorem empty_sound rs : egraph_sound (empty_egraph idx_zero) rs.
  Proof.
    unfold empty_egraph.
    unshelve econstructor.
    1: exact (fun _ => None).
    unfold atom_in_egraph;
      destruct a;
      basic_goal_prep.
    rewrite map.get_empty in *.
    basic_goal_prep.
    tauto.    
  Qed.

  
  Notation saturate_until := (saturate_until idx_succ idx_zero spaced_list_intersect).
  
  Theorem saturation_sound e rs rs' P fuel b e'
    : (*TODO: needed: predicate_sound P rs -> *)
      egraph_sound e rs ->
      (*TODO: relationship between compiled rs' and uncompiled rs? incl rs' rs ->*)
      saturate_until rs' P fuel e = (b, e') ->
      egraph_sound e' rs.
  Proof.
    revert e.
    induction fuel;
      basic_goal_prep;
      basic_utils_crush;[].
  Abort.

End WithMap.

Arguments atom_in_egraph {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  pat i.
