Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils SymmetricInduction.
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


  Notation PreModel := (@PreModel V term sort).


Section Terms.
  Context (l : lang).

  
  Local Notation wf_ctx c := (wf_ctx (Model:= core_model l) c).

  Section WithCtx.
    Context (c : ctx).
    
  Local Notation eq_sort t1' t2' := (eq_sort l c t1' t2').
  Local Notation eq_subst c' s1' s2' := (eq_subst (Model:= core_model l) c c' s1' s2').
  Local Notation eq_args c' s1' s2' := (eq_args (Model:= core_model l) c c' s1' s2').

    
  Variant eq_term_step : sort -> term -> term -> Prop :=
  | eq_term_step_by : forall name c' t e1 e2 s1 s2 t',
      In (name,term_eq_rule c' e1 e2 t) l ->
      eq_subst c' s1 s2 ->
      eq_sort t[/s2/] t' ->
      eq_term_step t' e1[/s1/] e2[/s2/]
  | eq_term_step_by_sym : forall name c' t e1 e2 s1 s2 t',
      In (name,term_eq_rule c' e2 e1 t) l ->
      eq_subst c' s1 s2 ->
      eq_sort t[/s2/] t' ->
      eq_term_step t' e1[/s1/] e2[/s2/]
  | eq_term_step_cong : forall name c' args t s1 s2 t',
      In (name,term_rule c' args t) l ->
      eq_args c' s1 s2 ->
      eq_sort t[/(with_names_from c' s2)/] t' ->
      eq_term_step t' (con name s1) (con name s2)
  | eq_term_step_var : forall n t t',
      In (n, t) c ->
      eq_sort t t' ->
      eq_term_step t' (var n) (var n).
(*  with eq_subst : ctx -> subst -> subst -> Prop :=
  | eq_subst_nil : eq_subst [] [] []
  | eq_subst_cons : forall (c' : ctx) (s1 s2 : subst),
                    eq_subst c' s1 s2 ->
                    forall (name : V) (t : sort) (e1 e2 : term),
                    eq_term_step t [/s2 /] e1 e2 ->
                    eq_subst ((name, t) :: c') ((name, e1) :: s1)
                      ((name, e2) :: s2)
  with eq_args : ctx -> list term -> list term -> Prop :=
  | eq_args_nil : eq_args [] [] []
  | eq_args_cons : forall (c' : ctx) (es1 es2 : list term),
      eq_args c' es1 es2 ->
      forall (name : V) (t : sort) (e1 e2 : term),
        eq_term_step t [/with_names_from c' es2 /] e1 e2 ->
        eq_args ((name, t) :: c') (e1 :: es1) (e2 :: es2).*)
  Hint Constructors eq_term_step (*eq_subst eq_args*) : lang_core.

  Inductive eq_term t : term -> term -> Prop :=
  | eq_term_one e1 e2 : eq_term_step t e1 e2 -> eq_term t e1 e2
  | eq_term_next e1 e2 e3 : eq_term_step t e1 e2 -> eq_term t e2 e3 -> eq_term t e1 e3.
  Hint Constructors eq_term : lang_core.

  (*
Scheme min_term_step_ind := Minimality for eq_term_step Sort Prop
    with min_subst_ind := Minimality for eq_subst Sort Prop
    with min_args_ind := Minimality for eq_args Sort Prop.

  
  Combined Scheme minimal_ind
    from min_term_step_ind, min_subst_ind, min_args_ind.
*)

  Context (wfl : wf_lang l).
  
  (*TODO: move to Model.v*)
  Lemma eq_subst_sym c' s1 s2
    : eq_subst c' s1 s2 -> wf_ctx c' -> eq_subst c' s2 s1.
  Proof.
    induction 1; intros; constructor.
    1:basic_core_crush.
    all:basic_goal_prep.
    basic_core_crush.    
    eapply eq_term_conv; eauto using eq_term_sym with lang_core.
  Qed.
  
  Lemma eq_term_step_sym t e1 e2
    : eq_term_step t e1 e2 -> eq_term_step t e2 e1.
  Proof.
    induction 1;
      basic_goal_prep;
      try use_rule_in_wf;
      basic_core_crush.
    {
      eapply eq_term_step_by_sym; eauto using eq_subst_sym with lang_core.
      eapply eq_sort_trans; eauto.
      eapply eq_sort_subst; eauto with lang_core.
    }
    {
      eapply eq_term_step_by; eauto using eq_subst_sym with lang_core.
      eapply eq_sort_trans; eauto.
      eapply eq_sort_subst; eauto with lang_core.
    }
    {
      eapply eq_term_step_cong; eauto.
      { eapply eq_args_sym; eauto using core_model_ok. }
      eapply eq_sort_trans; eauto.
      eapply eq_sort_subst; eauto with lang_core.
      eapply eq_args_implies_eq_subst; eauto.
    }
  Qed.

  Lemma eq_term_trans t e1 e2 e3
    : eq_term t e1 e2 -> eq_term t e2 e3 -> eq_term t e1 e3.
  Proof.
    induction 1;
      basic_goal_prep;
      eauto with lang_core.
  Qed.
  
  Lemma eq_term_sym t e1 e2
    : eq_term t e1 e2 -> eq_term t e2 e1.
  Proof.
    induction 1;
      basic_goal_prep;
      eauto using eq_term_trans, eq_term_step_sym with lang_core.
  Qed.

  Lemma eq_term_cong name c' args t s1 s2 t'
    : In (name,term_rule c' args t) l ->
      eq_args c' s1 s2 ->
      eq_sort t[/(with_names_from c' s2)/] t' ->
      eq_term t' (con name s1) (con name s2).
  Proof.
    intros; eauto with lang_core.
  Qed.

  Context (wfc : wf_ctx c).

  Hint Resolve core_model_ok : lang_core.

  
  (*TODO: move to Model.v*)
  Lemma eq_args_implies_wf_r c' s1 s2
    : eq_args c' s1 s2 -> wf_args (Model:= core_model l) c s2 c'.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    eapply eq_term_wf_r; eauto.
  Qed.
  Hint Resolve eq_args_implies_wf_r : lang_core.

  Lemma eq_term_step_conv t t' e1 e2
    : eq_term_step t e1 e2 -> eq_sort t t' -> eq_term_step t' e1 e2.
  Proof.
    induction 1;
      basic_goal_prep;
      eauto using eq_sort_trans with lang_core.
  Qed.
  
  Lemma eq_term_conv t t' e1 e2
    : eq_term t e1 e2 -> eq_sort t t' -> eq_term t' e1 e2.
  Proof.
    induction 1;
      basic_goal_prep;
      eauto using eq_term_step_conv with lang_core.
  Qed.
  
  Lemma core_implies_eq_term t e1 e2
    : Core.eq_term l c t e1 e2 -> eq_term t e1 e2.
  Proof.
    revert t e1 e2.
    eapply term_cut_ind.
    all: basic_goal_prep.
    all: try use_rule_in_wf.
    all: eauto using eq_term_sym, eq_term_trans, eq_term_conv with lang_core.
    all: autorewrite with utils lang_core in *; break.
    {
      eapply eq_term_one.
      eapply eq_term_step_by; eauto with lang_core.
    }
    {
      eapply eq_term_cong; eauto.
      eapply eq_sort_subst; eauto with lang_core.
      eapply eq_args_implies_eq_subst; eauto with lang_core.
      eapply eq_args_refl; eauto with lang_core.
    }
  Qed.
  
  Lemma eq_term_step_implies_core t e1 e2
    : eq_term_step t e1 e2 -> Core.eq_term l c t e1 e2.
  Proof.
    induction 1;
      basic_goal_prep;
      try use_rule_in_wf;
      basic_core_crush.
    {
      eapply Core.eq_term_conv;
        eauto using Core.eq_term_sym with lang_core.
    }
    {
      eapply term_con_congruence; intuition eauto using eq_sort_sym.
    }
  Qed.
    
  Lemma eq_term_implies_core t e1 e2
    : eq_term t e1 e2 -> Core.eq_term l c t e1 e2.
  Proof.
    induction 1;
      basic_goal_prep;
      eauto using eq_term_step_implies_core, Core.eq_term_trans.
  Qed.

  Lemma eq_term_iff_core t e1 e2
    : eq_term t e1 e2 <-> Core.eq_term l c t e1 e2.
  Proof.
    split; [eapply eq_term_implies_core | eapply core_implies_eq_term ].
  Qed.

  (*TODO: eliminate eq_subst from above, make eq_args recursive w/ eq_term_step*)

  End WithCtx.
End Terms.
End WithVar.
