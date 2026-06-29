Set Implicit Arguments.

From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Semantic core of the source-rule adapter's (II) conclusion construction:
   given a wf substitution [sg] of a rule's context, the rule's own-context
   conclusion is well-formed / equal after [sg].  These are Core-only facts,
   consumed by the egraph source-rule adapter (Theorems.v).  Moved verbatim
   from the validated scratch in WIP/ConclSemantic.v. *)
Section WithV.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  (* Re-declare the section-local notations from Core (these are not exported). *)
  Local Notation wf_subst l c s c' := (wf_subst (Model:=core_model l) c s c').
  Local Notation eq_subst l c c' s1 s2 := (eq_subst (Model:=core_model l) c c' s1 s2).
  Local Notation wf_ctx l c := (wf_ctx (Model:=core_model l) c).

  Context (l : lang) (wfl : wf_lang l).

  Lemma term_eq_concl n c e1 e2 t
    : In (n, term_eq_rule c e1 e2 t) l ->
      forall sg, wf_subst l [] sg c ->
                 eq_term l [] t[/sg/] e1[/sg/] e2[/sg/].
  Proof.
    intros Hin sg Hsg.
    pose proof (rule_in_wf _ _ wfl Hin) as Hr.
    rewrite app_nil_r in Hr.
    rewrite invert_wf_term_eq_rule in Hr.
    destruct Hr as [Hc [He1 [He2 Ht]]].
    eapply eq_term_subst.
    - eapply eq_term_by. exact Hin.
    - eapply eq_subst_refl. exact Hsg.
    - exact Hc.
  Qed.

  Lemma sort_eq_concl n c t1 t2
    : In (n, sort_eq_rule c t1 t2) l ->
      forall sg, wf_subst l [] sg c ->
                 eq_sort l [] t1[/sg/] t2[/sg/].
  Proof.
    intros Hin sg Hsg.
    pose proof (rule_in_wf _ _ wfl Hin) as Hr.
    rewrite app_nil_r in Hr.
    rewrite invert_wf_sort_eq_rule in Hr.
    destruct Hr as [Hc [Ht1 Ht2]].
    eapply eq_sort_subst.
    - eapply eq_sort_by. exact Hin.
    - eapply eq_subst_refl. exact Hsg.
    - exact Hc.
  Qed.

  (* Reversed-equation variants: the [rev_rule]'d eq-rules of [posRR]
     (Automation.v) swap the two sides, so [model_satisfies_rule] for the
     reversed rule needs the SYMMETRIC equation.  The reversed rule is not in
     [l] (only the original is), so these recover the swapped equation from the
     original rule's membership via [eq_term_sym]/[eq_sort_sym].  Consumed by
     the posRR eq-adapters. *)
  Lemma term_eq_concl_rev n c e1 e2 t
    : In (n, term_eq_rule c e1 e2 t) l ->
      forall sg, wf_subst l [] sg c ->
                 eq_term l [] t[/sg/] e2[/sg/] e1[/sg/].
  Proof.
    intros Hin sg Hsg.
    apply eq_term_sym.
    eapply term_eq_concl; eassumption.
  Qed.

  Lemma sort_eq_concl_rev n c t1 t2
    : In (n, sort_eq_rule c t1 t2) l ->
      forall sg, wf_subst l [] sg c ->
                 eq_sort l [] t2[/sg/] t1[/sg/].
  Proof.
    intros Hin sg Hsg.
    apply eq_sort_sym.
    eapply sort_eq_concl; eassumption.
  Qed.

End WithV.
