Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import
  Theory.Core Theory.ModelImpls Compilers.Compilers
  Tools.AllConstructors
  Tools.CompilerTools.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

 
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
  Notation compiler_case := (compiler_case V (tgt_term:=term) (tgt_sort:=sort)).
  Notation compiler := (compiler V (tgt_term:=term) (tgt_sort:=sort)).
  Notation compile := (compile (V:=V) (tgt_term:=term) (tgt_sort:=sort)
                         (tgt_Model:=syntax_model (V:=V))).
  Notation compile_subst := (compile_subst (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).
  Notation compile_ctx := (compile_ctx (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).
  Notation compile_args := (compile_args (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).
  Notation compile_sort := (compile_sort (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).


  Lemma preserving_compiler_embed cmp_pre (tgt : lang) cmp src tgt'
    : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->
      incl tgt tgt' ->
      preserving_compiler_ext (tgt_Model:=core_model tgt') cmp_pre cmp src.
  Proof.
    induction 1; basic_goal_prep; constructor; basic_core_firstorder_crush.
    - eapply wf_sort_lang_monotonicity; eauto.
    - eapply wf_term_lang_monotonicity; eauto.
    - eapply eq_sort_lang_monotonicity; eauto.
    - eapply eq_term_lang_monotonicity; eauto.
  Qed.
  #[local] Hint Resolve preserving_compiler_embed : auto_elab.

  (*TODO: move to utils*)
  #[local] Hint Resolve incl_nil_l : utils.
  Lemma incl_map_first {A B} (a b : list (A * B))
    : incl a b ->
      incl (map fst a) (map fst b).
  Proof.
    revert b;
      induction a;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma elab_compiler_prefix_implies_elab cmp_pre (target : lang)
    cmp src src_pre
    : preserving_compiler_ext (tgt_Model:=core_model target) [] cmp_pre src_pre ->
      preserving_compiler_ext (tgt_Model:=core_model target) cmp_pre cmp src ->
      preserving_compiler_ext (tgt_Model:=core_model target) [] (cmp++cmp_pre) (src++src_pre).
  Proof using.
    induction 2; basic_goal_prep; basic_core_firstorder_crush.
    all: constructor; basic_core_crush.
  Qed.

  Lemma preserving_compiler_monotonicity cmp_pre (tgt : lang) cmp src src_pre cmp_pre'
    : preserving_compiler_ext (tgt_Model:=core_model tgt) [] cmp_pre src_pre ->
      preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->
      wf_lang (src++src_pre) ->
      incl cmp_pre cmp_pre' ->
      all_fresh cmp_pre' ->
      preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre' cmp src.
  Proof.
    induction 2; basic_goal_prep; autorewrite with utils lang_core in *;
      try typeclasses eauto; try constructor; intuition eauto.
    
    all: unfold Model.wf_sort, Model.wf_term, Model.eq_sort, Model.eq_term, core_model.
    Ltac solve_sort_goal :=
      eapply all_constructors_sort_weaken;
      [typeclasses eauto|typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_sort_from_wf; eauto using core_model |];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
      eapply elab_compiler_prefix_implies_elab; eauto.
    Ltac solve_ctx_goal :=
      eapply all_constructors_ctx_weaken; [typeclasses eauto |typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_ctx_from_wf; eauto using core_model|];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
      eapply elab_compiler_prefix_implies_elab; eauto.
    
    all: erewrite ?compile_strengthen_ctx_incl'
      by (try typeclasses eauto; eauto using core_model;solve_ctx_goal); auto.
    all: erewrite !compile_strengthen_sort_incl' with (cmp':=cmp_pre')
      by (try typeclasses eauto; eauto using core_model;solve_sort_goal); auto.
    Ltac solve_term_goal :=
      eapply all_constructors_term_weaken;
      [typeclasses eauto|typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_term_from_wf; eauto using core_model |];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
      eapply elab_compiler_prefix_implies_elab; eauto.

    erewrite !compile_strengthen_term_incl' with (cmp':=cmp_pre')
      by (try typeclasses eauto; eauto using core_model;solve_term_goal); auto.
  Qed.

  
  Lemma compiler_append cmp_pre' lt' cmp' (ls' : Rule.lang V) lt cmp ls src_pre'
    : preserving_compiler_ext (tgt_Model:=core_model lt') cmp_pre' cmp' ls' ->
      preserving_compiler_ext (tgt_Model:=core_model lt) [] cmp_pre' src_pre' ->
      preserving_compiler_ext (tgt_Model:=core_model lt) [] cmp ls ->
      incl lt' lt ->
      incl cmp_pre' cmp ->
      all_fresh cmp ->
      wf_lang (ls' ++ src_pre') ->
      preserving_compiler_ext (tgt_Model:=core_model lt) [] (cmp' ++ cmp) (ls' ++ ls).
  Proof.
    intros.
    eapply preserving_compiler_embed in H2; [| eassumption].
    eapply elab_compiler_prefix_implies_elab; auto.
    eapply preserving_compiler_monotonicity.
    1:exact H0.
    all: eauto.
  Qed.

End WithVar.

#[export] Hint Resolve preserving_compiler_embed : auto_elab.
