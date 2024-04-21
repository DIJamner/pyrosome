(* Note: avoids the issue of universes for the moment.
   Future question: how do those interact w/ generic LRs?
 *)
Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.CutFreeInd.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  Section WithLang.
    Context (l : lang)
      (wfl : wf_lang l).
    (*TODO: parameterize red w/ a ctx or no?*)
    Context (c : ctx)
      (wfc : wf_ctx l c).

  Section WithRed.
    (* Represents the action of one redex *)
    Context (red : sort -> term -> term -> Prop)
      (* so far, always empty *)
      (red_sort :  sort -> sort -> Prop).

    Axiom red_subset
      : forall t e1 e2,
        (* not strictly necessary, but makes life easier *)
        wf_term l c e1 t ->
        red t e1 e2 ->
        eq_term l c t e1 e2.
    Axiom red_subset_sort
      : forall t1 t2,
        (* not strictly necessary, but makes life easier *)
        wf_sort l c t1 ->
        red_sort t1 t2 ->
        eq_sort l c t1 t2.
    

    (* For each whnf pattern, record which of its arguments must be in whnf.
       The set of terms should form a partition into LHSs of red and whnfs,
       although we may not need to prove this fact (to be seen).
     *)
    (*TODO: figure whether we need to separate neutrals from other things.
      Current understasnding: will be helpful in defining R_whnf below,
      but is not needed in the metatheory

      TODO: what to do with these?
      the idea is that they are all congruences of R_whnf.
      Question: add them in generically or verify congruence?
     
    Context (whnfs : list (term * list bool))
      (whnfs_sort : list (sort * list bool)).
     *)

    (* reflexive, transitive, _congruence_ (TODO) closure of red*)
    Definition red_clo : sort -> term -> term -> Prop. Admitted.
    Definition red_clo_sort : sort -> sort -> Prop. Admitted.
    (* TODO: prove*)
    Lemma red_clo_subset
      : forall t e1 e2,
        (* not strictly necessary, but makes life easier *)
        wf_term l c e1 t ->
        red_clo t e1 e2 ->
        eq_term l c t e1 e2.
    Admitted.
    Lemma red_clo_subset_sort
      : forall t1 t2,
        (* not strictly necessary, but makes life easier *)
        wf_sort l c t1 ->
        red_clo_sort t1 t2 ->
        eq_sort l c t1 t2.
    Admitted.

    (* Logical Relation. TODO: Prop or Type? *)
    Context (R_whnf : sort -> term -> term -> Prop)
      (R_whnf_sort : sort -> sort -> Prop).
    
    Axiom R_whnf_sound : forall t e1 e2, R_whnf t e1 e2 -> eq_term l c t e1 e2.
    Axiom R_whnf_sound_sort : forall t1 t2, R_whnf_sort t1 t2 -> eq_sort l c t1 t2.

    (* TODO: do I want to have wf judgments here?
       Probably, but worth checking.
     *)    
    Record R t (e1 e2 : term) : Prop :=
      {
        e1_wf : wf_term l c e1 t;
        e1' : term;
        normalize_e1 : red_clo t e1 e1';
        e2_wf : wf_term l c e2 t;
        e2' : term;
        normalize_e2 : red_clo t e2 e2';
        whnf_related : R_whnf t e1' e2';
      }.

    
    Record R_sort (t1 t2 : sort) : Prop :=
      {
        t1_wf : wf_sort l c t1;
        t1' : sort;
        normalize_t1 : red_clo_sort t1 t1';
        t2_wf : wf_sort l c t2;
        t2' : sort;
        normalize_t2 : red_clo_sort t2 t2';
        whnf_related : R_whnf_sort t1' t2';
      }.

    Lemma R_sound : forall t e1 e2, R t e1 e2 -> eq_term l c t e1 e2.
    Proof.
      destruct 1.
      eapply eq_term_trans;[|eapply eq_term_trans; [|eapply eq_term_sym]];
        cycle 2;
        [eapply red_clo_subset; eauto .. |].
      eapply R_whnf_sound; auto.
    Qed.
    Lemma R_sound_sort : forall t1 t2, R_sort t1 t2 -> eq_sort l c t1 t2.
    Proof.
      destruct 1.
      eapply eq_sort_trans;[|eapply eq_sort_trans; [|eapply eq_sort_sym]];
        cycle 2;
        [eapply red_clo_subset_sort; eauto .. |].
      eapply R_whnf_sound_sort; auto.
    Qed.

    Section Fundamental.

      (*
      Fixpoint P_args' (P_term : term -> sort -> Prop) s c :=
        match c, s with
        | [], [] => True
        | (n,t)::c', e::s =>
            P_args' P_term s c'
            /\ P_term e t[/with_names_from c' s/]
        | _, _ => False
        end.*)
      
      Lemma fundamental_property : forall t e1 e2, eq_term l c t e1 e2 -> R t e1 e2.
      Proof.
        (*TODO: want a version w/ predefined P_args, P_subst but mutual w/ sort *)
        eapply term_cut_ind; eauto; basic_goal_prep.
        {
          (* axiom case
             Acceptable to be a user goal.
             When the axiom is a reduction rule, should be auto-solvable,
             provided that the RHS reduces to a normal form.
             Note: Would be helpful to have separately from normalization
             a verified sound reduction engine.
             Normalization gives a proof that there exists a fuel for ea. term
             that reduces it to whnf
             Note: current reduction does full beta, whereas normalization only cares about whnf.
           *)
          admit.
        }
        {
          (* congruence case
             Two subcases:
             1. name is a head constructor: devolve to R_whnf (user goal)
             2. name is not a head constructor:
             - should generically solve neutral goals
             - requires handling evaluation order
           *)
        2:{ (*TODO: add a wrapper around R_whnf to verify this*) admit. }
        2:{
          destruct 3; econstructor.
          TODO: need reduction conversion, R_whnf conversion.
          TODO: prove eq_term version of f_prop instead? necessary for completeness
          R_whnf conversion should somehow derive from reduction of type?
          - to do that requires completeness
          all: eauto with lang_core.
          
          
        Fail.
      Abort.
      

    End Fundamental.

  (*requires a stronger assumption*)
    Section Completeness.
            
      Axiom R_whnf_sym : forall t e1 e2, R_whnf t e1 e2 -> R_whnf t e2 e1.
      Axiom R_whnf_sym_sort : forall t1 t2, R_whnf_sort t1 t2 -> R_whnf_sort t2 t1.

      Lemma R_sym : forall t e1 e2, R t e1 e2 -> R t e2 e1.
      Proof.
        destruct 1; econstructor; eauto using R_whnf_sym.
      Qed.
      Lemma R_sym_sort : forall t1 t2, R_sort t1 t2 -> R_sort t2 t1.
      Proof.
        destruct 1; econstructor; eauto using R_whnf_sym_sort.
      Qed.
     
      
      Axiom R_whnf_trans : forall t e1 e12 e2,
          R_whnf t e1 e12 ->
          R_whnf t e12 e2 ->
          R_whnf t e1 e2.
      Axiom R_whnf_trams_sort : forall t1 t12 t2,
          R_whnf_sort t1 t12 ->
          R_whnf_sort t12 t2 ->
          R_whnf_sort t1 t2.
      
      Lemma R_trans : forall t e1 e12 e2,
          R t e1 e12 ->
          R t e12 e2 ->
          R t e1 e2.
      Proof.
        destruct 1, 1; econstructor; eauto.
        eapply R_whnf_trans; eauto.
        Fail Qed. (*TODO: depends on confluence!*)
      Abort,
      Lemma R_trans_sort : forall t1 t12 t2,
          R_sort t1 t12 ->
          R_sort t12 t2 ->
          R_sort t1 t2.

    Lemma logical_relation_complete x y
      : eq_term [] t x y -> R t x y.
    Abort.

  End Completeness.


  Fail.
End WithVar.
