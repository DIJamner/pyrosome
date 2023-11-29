Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core CutFreeInd ModelImpls.


Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  
  Section WithLang.
    Context (l : lang)
      (wfl : wf_lang l).


    (* Note: this definition may not be quite sufficient for some cases.
       Case of concern: eliminating substitutions in depedent type theories with beta:
       we can definitely eliminate substitutions from e, but we can't do so in the conversions
       of its wfness proof.
       TODO: this might need a way to differentiate between the languages of conversion and wfness
     *)
    Definition eliminable l' : Prop :=
      (forall t, wf_sort (l'++l) [] t ->
                     exists t',
                       wf_sort l [] t'
                       /\ eq_sort (l'++l) [] t t')
      /\ (forall e t, wf_term (l'++l) [] e t ->
                      exists t' e',
                       wf_term l [] e' t'
                       /\ eq_term (l'++l) [] t' e e').

    (* Includes the functions that eliminate the extra rules.
       TODO: determine whether I want to use this.
     *)
    Definition strong_eliminable l' : Type :=
      { sf : sort -> sort
        & { f : term -> term
            & (forall t, wf_sort (l'++l) [] t ->
                             let t' := sf t in
                             wf_sort l [] t'
                             /\ eq_sort (l'++l) [] t t')
            /\ (forall e t, wf_term (l'++l) [] e t ->
                             let t' := sf t in
                             let e' := f e in
                             wf_term l [] e' t'
                             /\ eq_term (l'++l) [] t' e e')}}.

    Lemma strong_eliminable_implies_eliminable l'
      : strong_eliminable l' -> eliminable l'.
    Proof.
      unfold strong_eliminable, eliminable.
      basic_goal_prep.
      (*TODO: add sigma to break*)
      destruct X as [? [? [? ?]]].
      firstorder eauto.
    Qed.

    (*TODO: derive function from certain sets of rules*)
  End WithLang.

End WithVar.
