Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Gluing Require Import CutTModel Eval.
Import Core.Notations.

(* The syntactic cut-free model: ceq = Core's judgmental equality.  This is the
   simplest CutTModel_ok instance; it validates the generic framework end-to-end
   (eval : pf -> ceq_term recovers/generalizes pf_checker_sound on it) and is the
   template the normalization (gluing) model will enrich. *)
Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation lang := (@lang V).

  Section WithLang.
    Context (l : lang) (wfl : wf_lang l) (c : ctx).

    Definition SynM : CutTModel :=
      {|
        ceq_sort T1 T2 := eq_sort l c T1 T2;
        ceq_term t e1 e2 := eq_term l c t e1 e2;
      |}.

    (* The CutTModel argument relation over SynM coincides with Core's eq_args. *)
    Lemma synm_ceq_args c' s1 s2
      : ceq_args (CM := SynM) c' s1 s2 ->
        eq_args (Model := core_model l) c c' s1 s2.
    Proof.
      induction 1.
      - constructor.
      - constructor; eauto.
    Qed.

    Lemma synm_cterm_var n t
      : In (n, t) c -> eq_term l c t (var n) (var n).
    Proof.
      intro H.
      apply eq_term_refl.
      apply wf_term_var.
      exact H.
    Qed.

    Lemma synm_cterm_cong c' name args t s1 s2
      : In (name, term_rule c' args t) l ->
        ceq_args (CM := SynM) c' s1 s2 ->
        eq_term l c t[/with_names_from c' s2/] (con name s1) (con name s2).
    Proof.
      intros Hin Hargs.
      apply synm_ceq_args in Hargs.
      eapply term_con_congruence; eauto.
    Qed.

    Lemma synm_cterm_by c' name e1 e2 t s1 s2
      : In (name, term_eq_rule c' e1 e2 t) l ->
        ceq_args (CM := SynM) c' s1 s2 ->
        eq_term l c t[/with_names_from c' s2/]
                e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
    Proof.
      intros Hin Hargs.
      apply synm_ceq_args in Hargs.
      eapply eq_term_subst.
      - eapply eq_term_by; eauto.
      - apply eq_args_implies_eq_subst; eauto.
      - with_rule_in_wf_crush.
    Qed.

    Lemma synm_csort_cong c' name args s1 s2
      : In (name, sort_rule c' args) l ->
        ceq_args (CM := SynM) c' s1 s2 ->
        eq_sort l c (scon name s1) (scon name s2).
    Proof.
      intros Hin Hargs.
      apply synm_ceq_args in Hargs.
      eapply sort_con_congruence; eauto.
    Qed.

    Lemma synm_csort_by c' name t1 t2 s1 s2
      : In (name, sort_eq_rule c' t1 t2) l ->
        ceq_args (CM := SynM) c' s1 s2 ->
        eq_sort l c t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
    Proof.
      intros Hin Hargs.
      apply synm_ceq_args in Hargs.
      eapply eq_sort_subst.
      - eapply eq_sort_by; eauto.
      - apply eq_args_implies_eq_subst; eauto.
      - with_rule_in_wf_crush.
    Qed.

    #[export] Instance SynM_ok : CutTModel_ok (CM := SynM) l c.
    Proof.
      constructor.
      - exact synm_cterm_var.
      - exact synm_cterm_cong.
      - exact synm_cterm_by.
      - exact (fun t e1 e12 e2 H1 H2 => eq_term_trans H1 H2).
      - exact (fun t e1 e2 H => eq_term_sym H).
      - exact (fun t1 t2 e1 e2 Hs He => eq_term_conv He Hs).
      - exact synm_csort_cong.
      - exact synm_csort_by.
      - exact (fun t1 t12 t2 H1 H2 => eq_sort_trans H1 H2).
      - exact (fun t1 t2 H => eq_sort_sym H).
    Defined.

  End WithLang.

End WithVar.
