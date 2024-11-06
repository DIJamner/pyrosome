(* Note: avoids the issue of universes for the moment.
   Future question: how do those interact w/ generic LRs?
 *)
Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
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
    Context (red1 : term -> option term).
    (*
      so far, no languages have sort eqns.
      Add this if/when they do.
      Until then, assume all sorts are injective.
      (red_sort :  sort -> sort)
     *)

    (* Note: if red1 is given by a compiler-like table,
       this should generally be automatically provable.
     *)
    Axiom red_subset
      : forall t e1 e2,
        wf_term l c e1 t ->
        red1 e1 = Some e2 ->
        eq_term l c t e1 e2.

    (* decidable equality for head forms,
       given as an algebra.
       TODO: think about termination argument.
       TODO: define reduction, head_eq as list of patterns?
       solves termination issue here

       Termination idea: on the size of the sort.
       The fixpoint takes the size of the initial sort
     *)
    Context (head_eq : (term -> term -> bool) -> term -> term -> bool).

    Variant arg_kind := head_term | neutral_term | unreduced.
    (* For each neutral pattern, record which of its arguments must be reduced
       and which must be neutrals.
       Separating neutrals allows them to be handled generically.
     *)
    Context (neutrals : list (term * list arg_kind)).
    (* While sorts are injective, treat them all as heads.       
      (neutrals_sort : list (sort * list bool)).*)

    (* variable for the hole in the evaluation context *)
    Context (hole : V)
      (hole_fresh : fresh hole c).

    (* TODO: move to Term.v *)
    Fixpoint size (e:term) :=
      match e with
      | var _ => 1
      | con _ s => fold_left Nat.add (map size s) 1
      end.

    Fixpoint split_redex' sz e : (term * term) :=
      match sz with
      | 0 => (e, var hole)
      | S sz' =>
      (* TODO: algo:
         1. find the first match N in neutrals; if no match, return (e,hole)
         2. recur, producing result (r,E)
         3. return (r, N[/(hole,E)::(id_subst c)/])
       *)
          (e,var hole) (*TODO: implement*)
      end.

    Definition split_redex e := split_redex' (size e) e.
      
      (* represents one step of reduction, possibly under neutral constructor(s) *)
    Definition step1 (e : term) :=
      @! let (r, E) := split_redex e in
        let r' <- red1 r in
        ret E[/(hole,r')::(id_subst c)/].

    Fixpoint big_step' fuel e :=
      match fuel with
      | 0 => None
      | S fuel' =>
          match step1 e with
          | Some e' => big_step' fuel' e'
          | None => Some e
          end
      end.

    (* Design question: If I make the right things proof-relevant,
       is it possible to set up the LR to output this number in a relevant context
       as a function of e (and probably its type)?
       If so, it would give me a fuel-less reduction function at the end
       for user dependent type theories.
       This would also give a fuel-less conversion function/decider
       and therefore a type checker.
       Note: it might end up as a _very_ large number, so a positive version
       might be worth implementing.
     *)
    Definition big_step e v := exists fuel, big_step' fuel e = Some v.

    (* TODO: do I want this?
    Definition big_step'_sort fuel (t : sort) : option sort :=
      let (n,s) := t in
      @! let s' <- list_Mmap (big_step' fuel) s in
        ret (scon n s').

    Definition big_step_sort e v := exists fuel, big_step'_sort fuel e = Some v.
     *)
    
    (* TODO: prove*)
    Lemma big_step_subset
      : forall t e1 e2,
        wf_term l c e1 t ->
        big_step e1 e2 ->
        eq_term l c t e1 e2.
    Admitted.

    (* Logical Relation. TODO: Prop or Type?
       TODO: should be some sort of algebra over such relations,
       i.e. parameterized by R.
     *)
    Context (R_whnf : sort -> term -> term -> Prop).
      (*(R_whnf_sort : sort -> sort -> Prop).*)

    Axiom R_whnf_sound
      : forall t e1 e2,
        wf_term l c e1 t ->
        wf_term l c e2 t ->
        R_whnf t e1 e2 -> eq_term l c t e1 e2.
    (*
    Axiom R_whnf_sound_sort : forall t1 t2, R_whnf_sort t1 t2 -> eq_sort l c t1 t2.
     *)

    (* TODO: do I want to have wf judgments here?
       Probably, but worth checking.
       TODO: should reduce t as well
     *)    
    Record R t (e1 e2 : term) : Prop :=
      {
        e1_wf : wf_term l c e1 t;
        e1' : term;
        normalize_e1 : big_step e1 e1';
        e2_wf : wf_term l c e2 t;
        e2' : term;
        normalize_e2 : big_step e2 e2';
        whnf_related : R_whnf t e1' e2';
      }.

    (* TODO: how to relate sorts?
       Current thought: R_sort definition uses R, not R_whnf
       so it doesn't normalize subterms
    Record R_sort (t1 t2 : sort) : Prop :=
      {
        t1_wf : wf_sort l c t1;
        t1' : sort;
        normalize_t1 : big_step_sort t1 t1';
        t2_wf : wf_sort l c t2;
        t2' : sort;
        normalize_t2 : big_step_sort t2 t2';
        whnf_related : R_whnf_sort t1' t2';
      }.
     *)

    (* TODO: figure out sort relation
    Fixpoint R_args (kinds : list arg_kind

      Definition R_sort '(scon n1 s1) '(scon n2 s2) : Prop :=
      let kinds := repeat (length s1) TODO: head or neutral?
      match named_list_lookup_err l n1 with
      | Some r => n1 = n2 /\ R_args kinds (get_ctx r) s1 s2
      | None => False
      end.
     *)

    (* TODO: what is missing that lets me prove this w/out algorithmic conv involved?*)
    Lemma R_sound : forall t e1 e2, R t e1 e2 -> eq_term l c t e1 e2.
    Proof.
      destruct 1.
      eapply eq_term_trans;[|eapply eq_term_trans; [|eapply eq_term_sym]];
        cycle 2;
        [eapply big_step_subset; eauto .. |].
      eapply R_whnf_sound; auto.
      all: eapply eq_term_wf_r; eauto using big_step_subset.
    Qed.
    (*
    Lemma R_sound_sort : forall t1 t2, R_sort t1 t2 -> eq_sort l c t1 t2.
    Proof.
      destruct 1.
      eapply eq_sort_trans;[|eapply eq_sort_trans; [|eapply eq_sort_sym]];
        cycle 2;
        [eapply red_clo_subset_sort; eauto .. |].
      eapply R_whnf_sound_sort; auto.
    Qed.
     *)

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
             - requires 
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
