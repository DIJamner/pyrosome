Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core AllConstructors Compilers Elab ElabCompilers.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.



Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.

  
  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  Notation compiler := (@compiler V).

Lemma elab_preserving_compiler_embed cmp_pre tgt cmp ecmp src tgt'
    : elab_preserving_compiler cmp_pre tgt cmp ecmp src ->
      incl tgt tgt' ->
      elab_preserving_compiler cmp_pre tgt' cmp ecmp src.
Proof.
  induction 1; basic_goal_prep; constructor; basic_core_firstorder_crush.
  eapply eq_sort_lang_monotonicity; eauto.
  eapply eq_term_lang_monotonicity; eauto.
Qed.
Hint Resolve elab_preserving_compiler_embed : auto_elab.


Lemma strengthen_named_list_lookup {A} (cmp : named_list A) n
  : forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 In n (map fst cmp) ->
                 named_list_lookup_err cmp' n = named_list_lookup_err cmp n.
Proof.
  induction cmp; basic_goal_prep;  symmetry; basic_utils_crush.
  my_case neq (eqb n v); basic_goal_prep; basic_utils_crush.
  symmetry.
  basic_core_crush.
Qed.

Lemma compile_strengthen_term_incl cmp e
  : all_constructors (fun n => In n (map fst cmp)) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile cmp' e = compile cmp e.
Proof.
  induction e; basic_goal_prep; basic_core_firstorder_crush.
  erewrite strengthen_named_list_lookup; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[| basic_core_crush].
  f_equal.
  f_equal.
 
  revert dependent l.
  induction l; basic_goal_prep; f_equal; firstorder.
Qed.

Lemma compile_strengthen_args_incl cmp e
  : all (all_constructors (fun n => In n (map fst cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_args cmp' e = compile_args cmp e.
Proof.
  induction e; basic_goal_prep;
    f_equal; firstorder eauto using compile_strengthen_term_incl.
Qed.
Hint Rewrite compile_strengthen_args_incl : lang_core.


Lemma compile_strengthen_sort_incl cmp e
  : all_constructors_sort (fun n => In n (map fst cmp)) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_sort cmp' e = compile_sort cmp e.
Proof.
  induction e; basic_goal_prep; basic_core_firstorder_crush.
  erewrite strengthen_named_list_lookup; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[basic_core_crush|].
  f_equal.
  f_equal.
  apply compile_strengthen_args_incl; eauto.
Qed.


(*We use a notation so that auto recognizes it after
  reduction
  TODO: move to end of Compilers.v
*) 
Notation all_constructors_ctx P c :=
  (all (fun '(_,t) => all_constructors_sort P t) c).

Lemma compile_strengthen_ctx_incl cmp e
  : all_constructors_ctx (fun n => In n (map fst cmp)) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_ctx cmp' e = compile_ctx cmp e.
Proof.
  induction e; basic_goal_prep;
    f_equal; [f_equal|]; firstorder eauto using compile_strengthen_sort_incl.
Qed.

Fixpoint constructor_names (l:lang) : list V :=
  match l with
  | (n,term_rule _ _ _)::l' => n::(constructor_names l')
  | (n,sort_rule _ _)::l' => n::(constructor_names l')
  | _::l' => constructor_names l'
  |[] => []
  end.

Lemma preserving_compiler_constructor_names cmp_pre  tgt cmp src
  : preserving_compiler_ext cmp_pre tgt cmp src ->
    map fst cmp = constructor_names src.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.

Lemma sort_rule_in_constructor_names n c args l
  : In (n, sort_rule c args) l -> In n (constructor_names l).
Proof.
  induction l; basic_goal_prep; auto.
  (*TODO: fix automation for this*)
  repeat intuition break.
  all:autorewrite with utils term lang_core in *.
  intuition (subst; unshelve eauto 1 with utils term lang_core).
  case_match;
  intuition (subst; unshelve eauto  4 with utils term lang_core).
Qed.
Hint Resolve sort_rule_in_constructor_names : lang_core.


Lemma term_rule_in_constructor_names n c args t l
  : In (n, term_rule c args t) l -> In n (constructor_names l).
Proof.
  induction l; basic_goal_prep; auto.
  (*TODO: fix automation for this*)
  repeat intuition break.
  all:autorewrite with utils term lang_core in *.
  intuition (subst; unshelve eauto 1 with utils term lang_core).
  case_match;
  intuition (subst; unshelve eauto  4 with utils term lang_core).
Qed.
Hint Resolve term_rule_in_constructor_names : lang_core.

Local Lemma all_constructors_from_wf src
  : (forall c t,
        wf_sort src c t ->
        all_constructors_sort (fun n0 => In n0 (constructor_names src)) t)
    /\ (forall c e t,
           wf_term src c e t ->
           all_constructors (fun n0 => In n0 (constructor_names src)) e)
    /\ (forall c s c',
           wf_args src c s c' ->
           all (all_constructors (fun n0 => In n0 (constructor_names src))) s).
Proof using.
  intros; apply wf_judge_ind; basic_goal_prep;
    with_rule_in_wf_crush.  
Qed.

Definition all_constructors_sort_from_wf src
  := proj1 (all_constructors_from_wf src).
Hint Resolve all_constructors_sort_from_wf : lang_core.

Definition all_constructors_term_from_wf src 
  := proj1 (proj2 (all_constructors_from_wf src)).
Hint Resolve all_constructors_term_from_wf : lang_core.

Definition all_constructors_args_from_wf src
  := proj2 (proj2 (all_constructors_from_wf src)).
Hint Resolve all_constructors_args_from_wf : lang_core.

Lemma all_constructors_ctx_from_wf src c
  : wf_ctx src c ->
    all_constructors_ctx (fun n0 => In n0 (constructor_names src)) c.
Proof.
  induction 1; basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
Hint Resolve all_constructors_ctx_from_wf : lang_core.

Require Import Compilers.



Lemma strengthen_named_list_lookup' {A} (ecmp cmp : named_list A) n
  : forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 In n (map fst (ecmp++cmp)) ->
                 named_list_lookup_err (ecmp++cmp') n = named_list_lookup_err (ecmp++cmp) n.
Proof.
  induction ecmp; basic_goal_prep; basic_utils_crush.
  eapply strengthen_named_list_lookup; eauto.
  my_case neq (eqb n v); basic_goal_prep; basic_utils_crush.
Qed.


Lemma compile_strengthen_term_incl' ecmp cmp e
  : all_constructors (fun n => In n (map fst (ecmp++cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 (compile (ecmp ++ cmp') e) = (compile (ecmp ++ cmp) e).
Proof.
  induction e; basic_goal_prep; basic_core_firstorder_crush.
  erewrite strengthen_named_list_lookup'; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[| basic_core_crush].
  f_equal.
  f_equal.
 
  revert dependent l.
  induction l; basic_goal_prep; f_equal; firstorder.
Qed.


Lemma compile_strengthen_args_incl' ecmp cmp e
  : all (all_constructors (fun n => In n (map fst (ecmp++cmp)))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 (compile_args (ecmp ++ cmp') e) = (compile_args (ecmp ++ cmp) e).
Proof.
  induction e; basic_goal_prep;
    f_equal; firstorder eauto using compile_strengthen_term_incl'.
Qed.


Lemma compile_strengthen_sort_incl' ecmp cmp e
  : all_constructors_sort (fun n => In n (map fst (ecmp++cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_sort (ecmp++cmp') e = compile_sort (ecmp++cmp) e.
Proof.
  induction e; basic_goal_prep; basic_core_firstorder_crush.
  erewrite strengthen_named_list_lookup'; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[basic_core_crush|].
  f_equal.
  f_equal.
  apply compile_strengthen_args_incl'; eauto.
Qed.


Lemma compile_strengthen_ctx_incl' ecmp cmp e
  : all_constructors_ctx (fun n => In n (map fst (ecmp++cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_ctx (ecmp++cmp') e = compile_ctx (ecmp++cmp) e.
Proof.
  induction e; basic_goal_prep;
    f_equal; [f_equal|]; firstorder eauto using compile_strengthen_sort_incl'.
Qed.

Lemma constructor_names_app l l'
  : constructor_names (l++l') = (constructor_names l) ++ (constructor_names l').
Proof.
  induction l; basic_goal_prep; try case_match; basic_goal_prep; basic_core_crush.
Qed.


Lemma elab_preserving_compiler_monotonicity cmp' cmp_pre tgt cmp ecmp src src_pre cmp_pre'
  : elab_preserving_compiler [] tgt cmp' cmp_pre src_pre ->
    elab_preserving_compiler cmp_pre tgt cmp ecmp src ->
    wf_lang (src++src_pre) ->
    incl cmp_pre cmp_pre' ->
    all_fresh cmp_pre' ->
    elab_preserving_compiler cmp_pre' tgt cmp ecmp src.
Proof.
  induction 2; basic_goal_prep; autorewrite with utils lang_core in *; try constructor; intuition eauto.
  Abort (*TODO: update
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    eapply all_constructors_ctx_weaken; cycle 1.
    basic_core_crush.
    simpl; intro.
    erewrite !preserving_compiler_constructor_names; eauto.
    eapply elab_compiler_implies_preserving.
    eapply elab_compiler_prefix_implies_elab; eauto.
  }
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    erewrite compile_strengthen_sort_incl'; eauto.
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_ctx_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
  }
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    erewrite compile_strengthen_sort_incl'; eauto.
    erewrite (compile_strengthen_sort_incl' ecmp t2); eauto.
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_ctx_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
  }
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    erewrite compile_strengthen_sort_incl'; eauto.
    erewrite (compile_strengthen_term_incl' ecmp e1); eauto.
    erewrite (compile_strengthen_term_incl' ecmp e2); eauto.
    {
      eapply all_constructors_term_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_term_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_ctx_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
  }
Qed.
Hint Resolve elab_preserving_compiler_monotonicity : auto_elab.
         *).

End WithVar.
