Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers ElabWithPrefix ElabCompilersWithPrefix.
Import Core.Notations.

(*TODO: probably should move this to compilerDefs*)
Definition compile_rule cmp r :=
  match r with
  | sort_rule c args => sort_rule (compile_ctx cmp c) args
  | term_rule c args t => term_rule (compile_ctx cmp c) args (compile_sort cmp t)
  | sort_eq_rule c t1 t2 =>
    sort_eq_rule (compile_ctx cmp c)
                 (compile_sort cmp t1)
                 (compile_sort cmp t2)
  | term_eq_rule c e1 e2 t =>
    term_eq_rule (compile_ctx cmp c)
                 (compile cmp e1)
                 (compile cmp e2)
                 (compile_sort cmp t)
  end.

(* the identity compiler maps an extension to its lowering *)
Fixpoint ext_id ext :=
  match ext with
  | [] => []
  | (n,sort_rule c args)::ext' =>
    (n, sort_case (map fst c) (scon n (map var args)))::(ext_id ext')
  | (n,term_rule c args t)::ext' =>
    (n, term_case (map fst c) (con n (map var args)))::(ext_id ext')
  | (_,_)::ext' => ext_id ext'
  end.

(* The elaborated version *)
Fixpoint ext_id_elab ext :=
  match ext with
  | [] => []
  | (n,sort_rule c args)::ext' =>
    (n, sort_case (map fst c) (scon n (map var (map fst c))))::(ext_id_elab ext')
  | (n,term_rule c args t)::ext' =>
    (n, term_case (map fst c) (con n (map var (map fst c))))::(ext_id_elab ext')
  | (_,_)::ext' => ext_id_elab ext'
  end.

(*compiles elaborated extensions of the compiler's source 
  to be compatible with its target language
 *)
Fixpoint compile_ext cmp ext :=
  match ext with
  | [] => []
  | (n, r):: ext' =>
    (n, compile_rule (ext_id_elab ext' ++ cmp) r)::(compile_ext cmp ext')
  end.

(*TODO: move to elabwithprefix*)
Lemma elab_identity_args l_pre l c' c args
  : sublist args (map fst c) ->
    sublist c c' ->
    elab_args l_pre l c' (map var args) args (map var (map fst c)) c.
Proof.
  revert args; induction c; basic_goal_prep.
  {
    destruct args; basic_core_crush.
  }
  destruct args.
  {
    constructor; basic_core_crush.
  }
  intuition; subst.
  {
    simpl.
    constructor;
      basic_core_crush.
  }
  {
      simpl.
      constructor;
      basic_core_crush.
  }
Qed.



(*TODO: move to ARule.v*)
Definition rule_args_sublist r :=
  match r with
  | sort_rule c args => sublist args (map fst c)
  | term_rule c args _ => sublist args (map fst c)
  | sort_eq_rule _ _ _ => True
  | term_eq_rule _ _ _ _ => True
  end.

Definition lang_args_sublist : lang -> Prop :=
  all (fun p => rule_args_sublist (snd p)).

Definition compute_rule_args_sublist r :=
  match r with
  | sort_rule c args => compute_sublist string_dec args (map fst c)
  | term_rule c args _ => compute_sublist string_dec args (map fst c)
  | sort_eq_rule _ _ _ => true
  | term_eq_rule _ _ _ _ => true
  end.

Definition compute_lang_args_sublist : lang -> bool :=
  forallb (fun p => compute_rule_args_sublist (snd p)).


Lemma use_compute_rule_args_sublist r
  : compute_rule_args_sublist r = true -> rule_args_sublist r.
Proof.
  destruct r; basic_goal_prep; basic_term_crush.
  all: eapply use_compute_sublist; eauto.
Qed.
  
Lemma use_compute_lang_args_sublist l
  : compute_lang_args_sublist l = true -> lang_args_sublist l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush;
    eauto using use_compute_rule_args_sublist.
Qed.

Lemma in_lang_args_sublist l n r
  : In (n,r) l ->
    lang_args_sublist l ->
    rule_args_sublist r.
Proof.
  induction l; basic_goal_prep;
    basic_term_crush.
Qed.

(* TODO: phrase compiler extension preservation like lang extension elab *)
(* TODO: prove a variant of *)
Lemma extension_preservation' ext text tgt cmp_elab
  : incl (compile_ext cmp_elab ext) text ->
    lang_args_sublist text ->
    (*TODO: do I need freshness here? all_fresh (ext++src) ->*)
    elab_preserving_compiler cmp_elab (text ++ tgt)
                  (ext_id ext)
                  (ext_id_elab ext) ext.
Proof.
  induction ext; basic_goal_prep; basic_core_crush.
  destruct r; basic_goal_prep; constructor; eauto.
  {
    econstructor.
    basic_core_crush.
    assert (sublist l (map fst c)).
    {
      pose proof (in_lang_args_sublist _ _ _ H H0).
      simpl in H3.
      rewrite compile_ctx_fst_equal in H3.
      auto.
    }
    erewrite <- compile_ctx_fst_equal.
    apply elab_prefix_implies_elab_args.
    apply elab_identity_args.
    rewrite compile_ctx_fst_equal; auto.
    basic_utils_crush.
  }
  {
    eapply Elab.elab_term_by'.
    basic_core_crush.
    {
      assert (sublist l (map fst c)).
      {
        pose proof (in_lang_args_sublist _ _ _ H H0).
        simpl in H3.
        rewrite compile_ctx_fst_equal in H3.
        auto.
      }
      erewrite <- compile_ctx_fst_equal.
      apply elab_prefix_implies_elab_args.
      apply elab_identity_args.
      rewrite compile_ctx_fst_equal; auto.
      basic_utils_crush.
    }
    {
      rewrite <- combine_map_fst_is_with_names_from.
      rewrite compile_ctx_fst_equal.
      rewrite combine_map_fst_is_with_names_from.
      rewrite sort_subst_id.
      reflexivity.
    }
  }
  {
    econstructor.
    basic_core_crush.
  }
  {
    econstructor.
    basic_core_crush.
  }
Qed.

Lemma compile_ext_preserves_args_sublist cmp_elab ext
  :  lang_args_sublist ext ->
     lang_args_sublist (compile_ext cmp_elab ext).
Proof.
  induction ext; basic_goal_prep; basic_core_crush.
  destruct r; basic_goal_prep; basic_core_crush.
  rewrite compile_ctx_fst_equal; auto.
  rewrite compile_ctx_fst_equal; auto.
Qed.  

Theorem extension_preservation ext tgt cmp_elab
  : lang_args_sublist ext ->
    elab_preserving_compiler cmp_elab (compile_ext cmp_elab ext ++ tgt)
                  (ext_id ext)
                  (ext_id_elab ext) ext.
Proof.
  intros; apply extension_preservation'; basic_utils_crush.
  apply compile_ext_preserves_args_sublist; auto.
Qed.
