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

  Local Notation preserving_compiler_ext tgt cmp_pre cmp src :=
    (preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).
  
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

  
  
  Lemma named_list_lookup_incl_hd A (l1 l2 : named_list A) n r a
    : incl l1 ((n,a)::l2) ->
      all_fresh ((n,a)::l2) ->
      Some r = named_list_lookup_err l1 n ->
      r = a.
  Proof.
    intros.
    apply named_list_lookup_err_in in H1.
    apply H in H1.
    basic_goal_prep.
    basic_utils_crush.
  Qed.    

  Lemma named_list_lookup_incl A (l1 l2 : named_list A) n r
    : incl l1 l2 ->
      all_fresh l2 ->
      Some r = named_list_lookup_err l1 n ->
      Some r = named_list_lookup_err l2 n.
  Proof.
    intros.
    apply named_list_lookup_err_in in H1.
    apply all_fresh_named_list_lookup_err_in; eauto.
  Qed.

  
  (*TODO: move somewhere*)
  Hint Resolve core_model_ok : lang_core.
  
  Lemma strengthening tgt' cmp' cmp l
    : preserving_compiler_ext tgt' [] cmp l ->
      wf_lang l ->
      wf_lang tgt' ->
      incl cmp cmp' ->
      all_fresh cmp' ->
      (forall c t, wf_sort l c t ->
                   compile_sort cmp' t = compile_sort cmp t)
      /\ (forall c e t, wf_term l c e t ->
                        compile cmp' e = compile cmp e)
      /\ (forall c s c', wf_args l c s c' ->
                         compile_args cmp' s = compile_args cmp s).
  Proof.
    intros.
    (*assert (all_fresh cmp) by basic_core_crush.*)
    apply wf_judge_ind;
      basic_goal_prep;
      basic_core_crush.
    (*all: pose proof (all_fresh_tail _ _ ltac:(eassumption)).*)
    all: repeat case_match; auto;
      autorewrite with utils term lang_core in *; eauto.
    all: repeat lazymatch goal with
           | H_incl : incl ?cmp _,
               H : Some _ = named_list_lookup_err ?cmp _ |- _ =>
               eapply  named_list_lookup_incl in H; eauto
           end.
    all: subst;
      unfold compile_args in *.
    all: try congruence.
    {
      apply named_list_lookup_none_iff in HeqH1.
      exfalso.
      eapply HeqH1.
      eapply sort_name_in_cmp; auto;[|eauto].
      eapply strengthen_preserving_compiler; auto.
      4:eassumption.
      all: basic_goal_prep; basic_core_crush.
    }
    {
      apply named_list_lookup_none_iff in HeqH1.
      exfalso.
      eapply HeqH1.
      eapply term_name_in_cmp; auto;[|eauto].
      eapply strengthen_preserving_compiler; auto.
      4:eassumption.
      all: basic_goal_prep; basic_core_crush.
    }
  Qed.
  
  Lemma strengthening_ctx tgt' cmp' cmp l
    : preserving_compiler_ext tgt' [] cmp l ->
      wf_lang l ->
      wf_lang tgt' ->
      incl cmp cmp' ->
      all_fresh cmp' ->
      forall c, wf_ctx l c ->
                compile_ctx cmp' c = compile_ctx cmp c.
  Proof.
    induction 6;
      basic_goal_prep; f_equal; eauto; f_equal;
      eapply strengthening; eauto.
  Qed.

  

  Lemma sort_case_in_cmp tgt cmp src c' args n
    : preserving_compiler_ext tgt [] cmp src ->
      In (n, sort_rule c' args) src ->
      exists (args : list V) (t : sort), In (n, sort_case args t) cmp.
  Proof.
    induction 1;basic_goal_prep;
      with_rule_in_wf_crush.
  Qed.
  Local Hint Resolve sort_case_in_cmp : lang_core.

  
  (*TODO: replace lemmas in Compilers that this generalizes *)
  Lemma compile_strengthen_incl (cmp1 cmp2 : compiler) e
    : all_fresh cmp1 ->
      all_fresh cmp2 ->
      incl cmp1 cmp2 ->
      AllConstructors.all_constructors (fun n0 : V => In n0 (map fst cmp1)) e ->
      compile cmp1 e = compile cmp2 e.
  Proof.
    intros ? ? ?.
    induction e;
      basic_goal_prep; basic_core_crush.
    case_match;
      basic_utils_crush.
    {
      eapply all_fresh_named_list_lookup_err_in in HeqH3; eauto.
      eapply H1 in HeqH3.
      eapply all_fresh_named_list_lookup_err_in in HeqH3; eauto.
      rewrite <- HeqH3.
      case_match; eauto.
      f_equal.
      f_equal.
      revert H2 H5.
      induction l;
        basic_goal_prep; basic_core_crush.
    }
    {
      eapply named_list_lookup_none_iff in HeqH3.
      exfalso.
      eauto.
    }
  Qed.
  
  (*TODO: move to Compilers*)
  Lemma compile_strengthen_sort_incl (cmp1 cmp2 : compiler) (t : sort)
    : all_fresh cmp1 ->
      all_fresh cmp2 ->
      incl cmp1 cmp2 ->
      AllConstructors.all_constructors_sort (fun n0 : V => In n0 (map fst cmp1)) t ->
      compile_sort cmp1 t = compile_sort cmp2 t.
  Proof.
    destruct t;
      basic_goal_prep.
    case_match;
      basic_utils_crush.
    {
      eapply all_fresh_named_list_lookup_err_in in HeqH3; eauto.
      eapply H1 in HeqH3.
      eapply all_fresh_named_list_lookup_err_in in HeqH3; eauto.
      rewrite <- HeqH3.
      case_match; eauto.
      f_equal.
      f_equal.
      revert H4.
      induction l;
        basic_goal_prep; basic_core_crush; eauto using compile_strengthen_incl.
    }
    {
      eapply named_list_lookup_none_iff in HeqH3.
      exfalso.
      eauto.
    }
  Qed.

End WithVar.

#[export] Hint Resolve preserving_compiler_embed : auto_elab.
