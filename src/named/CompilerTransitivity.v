Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers
 CatProd.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.


Lemma compile_subst_combine cmp args s
  : compile_subst cmp (combine args s) = combine args (map (compile cmp) s).
Proof.
  revert args; induction s; destruct args; basic_goal_prep; basic_core_crush.
Qed.

Section CompileFn.
  Context (cmp : compiler).

  Definition compile_ccase (c : compiler_case) :=
    match c with
    | sort_case args t => sort_case args (compile_sort cmp t)
    | term_case args e => term_case args (compile cmp e)
    end.

  Definition compile_cmp (c: compiler) := named_map compile_ccase c.

  Lemma lookup_cmp_distributes cmp' n
    : named_list_lookup_err (compile_cmp cmp') n
      = option_map compile_ccase (named_list_lookup_err cmp' n).
  Proof.
    induction cmp'; basic_goal_prep; basic_core_crush.
    case_match; basic_core_crush.
  Qed.
  Hint Rewrite lookup_cmp_distributes : lang_core.

  
  Lemma compile_cmp_distributes src ir tgt cmp' e
    : all_fresh ir ->
      ws_lang tgt ->
      preserving_compiler tgt cmp ir ->
      preserving_compiler ir cmp' src ->
      forall c t, wf_term src c e t ->
      (compile (compile_cmp cmp') e)
      = (compile cmp (compile cmp' e)).
  Proof.
    intros frsrc wstgt pres_cmp pres_cmp'.
    induction e; basic_goal_prep; basic_core_crush.
    symmetry.
    case_match; simpl.
    2:admit (*TODO:contradiction*).
    case_match; simpl.
    2:admit (*TODO: contradiction w/ term*).
    erewrite compile_term_subst; unfold ws_lang; eauto.
    2: admit (*TODO: use term_case_in_wf lemma (write if it doesn't exist)*).
    {
      rewrite compile_subst_combine.
      rewrite map_map.
      f_equal.
      f_equal.
      (*TODO: need separate lemma*)
      assert (exists c', wf_args src c l c') by admit; clear H0.
      firstorder.
      revert dependent x.
      
      revert dependent l; induction l; destruct x; basic_goal_prep; firstorder auto;
        inversion H0; subst; clear H0.
      f_equal; eauto.

      erewrite H; eauto.
    }
    admit (*TODO: combine_map_fst*).
  Admitted.

  
  Lemma compile_args_cmp_distributes src ir tgt cmp' e
    : all_fresh ir ->
      ws_lang tgt ->
      preserving_compiler tgt cmp ir ->
      preserving_compiler ir cmp' src ->
      forall c c', wf_args src c e c'->
      (compile_args (compile_cmp cmp') e)
      = (compile_args cmp (compile_args cmp' e)).
  Proof.
     intros frsrc wstgt pres_cmp pres_cmp'.
     induction e; basic_goal_prep; basic_core_crush.

     {
       inversion H; subst; clear H.
       eapply compile_cmp_distributes; [| | eauto | eauto | ..];
         unfold ws_lang; eauto.
     }
     {
       inversion H; subst; clear H.
       eauto.
     }
  Qed.
    
  Lemma compile_sort_cmp_distributes src ir tgt cmp' e
    : all_fresh ir ->
      ws_lang tgt ->
      preserving_compiler tgt cmp ir ->
      preserving_compiler ir cmp' src ->
      forall c, wf_sort src c e ->
      (compile_sort (compile_cmp cmp') e)
      = (compile_sort cmp (compile_sort cmp' e)).
  Proof.
    intros frsrc wstgt pres_cmp pres_cmp'.
    destruct e; basic_goal_prep; basic_core_crush.
    symmetry.
    case_match; simpl.
    2:admit (*TODO:contradiction*).
    case_match; simpl.
    admit (*TODO: contradiction w/ term*).
    erewrite compile_sort_subst; unfold ws_lang; eauto.
    2: admit (*TODO: use term_case_in_wf lemma (write if it doesn't exist)*).
    {
      rewrite compile_subst_combine.
      rewrite map_map.
      f_equal.
      f_equal.
      (*TODO: need separate lemma*)
      assert (exists c', wf_args src c l c') by admit; clear H0.
      firstorder.
      pose proof  compile_args_cmp_distributes  as p.
      unfold compile_args in p.
      erewrite p; eauto.
      rewrite map_map; eauto.

      split; auto.
      admit (*TODO: should be somewhere in the context*).
  Admitted.

  
  Lemma compile_ctx_cmp_distributes src ir tgt cmp' c
    : all_fresh ir ->
      ws_lang tgt ->
      preserving_compiler tgt cmp ir ->
      preserving_compiler ir cmp' src ->
      wf_ctx src c ->
      (compile_ctx (compile_cmp cmp') c)
      = (compile_ctx cmp (compile_ctx cmp' c)).
  Proof.
    intros frsrc wstgt pres_cmp pres_cmp'.
    induction 1; basic_goal_prep; basic_core_crush.
    f_equal; eauto.
    erewrite compile_sort_cmp_distributes; [| | | eauto | eauto |..];
      eauto.
    unfold ws_lang; split; eauto.
  Qed.
    
  
  Theorem preservation_transitivity src ir tgt cmp'
    : wf_lang src ->
      wf_lang ir ->
      wf_lang tgt ->
      preserving_compiler tgt cmp ir ->
      preserving_compiler ir cmp' src ->
      preserving_compiler tgt (compile_cmp cmp') src.
  Proof using .
    intros wfsrc wfir wftgt pres_cmp pres_cmp'.
    pose proof (inductive_implies_semantic wfir wftgt pres_cmp).
    firstorder.
    revert wfsrc.
    induction pres_cmp'; basic_goal_prep; constructor;
      autorewrite with lang_core in *; firstorder eauto.

    all:repeat (erewrite compile_ctx_cmp_distributes;
                [| | | eassumption | eassumption |];
                [| basic_core_crush ..]).

    apply inductive_implies_semantic in pres_cmp'; firstorder.
    
    all: repeat (erewrite compile_sort_cmp_distributes;
        [| | | eassumption | eassumption |];
        [| basic_core_crush ..]).
    
    apply inductive_implies_semantic in pres_cmp'; firstorder.
    
    apply inductive_implies_semantic in pres_cmp'; firstorder.
    all: repeat (erewrite compile_cmp_distributes;
        [| | | eassumption | eassumption |];
        [| basic_core_crush ..]).
    
    apply inductive_implies_semantic in pres_cmp'; firstorder.
  Qed.
