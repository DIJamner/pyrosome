Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome Require Import Theory.Core.



#[local] Notation eq_subst l :=
  (eq_subst (Model:= core_model l)).
#[local] Notation eq_args l :=
  (eq_args (Model:= core_model l)).
#[local] Notation wf_subst l :=
  (wf_subst (Model:= core_model l)).
#[local] Notation wf_args l :=
  (wf_args (Model:= core_model l)).
#[local] Notation wf_ctx l :=
  (wf_ctx (Model:= core_model l)).


(*TODO: check if this is defined somewhere.
    If not, move it to Utils.v
 *)
Definition Injective {A B : Type} (f : A -> B) := forall a a', f a = f a' -> a = a'.

Section Injective.
  Context (A B : Type)
    `{Eqb A}
    `{Eqb B}
    (f : A -> B)
    (f_inj : Injective f).

  
  Lemma injective_in a l
    : In (f a) (map f l) ->
      In a l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
  Qed.

  #[local] Hint Resolve injective_in : utils.
  

  Fixpoint rename e :=
    match e with
    | var n => var (f n)
    | con n l => con (f n) (map rename l)
    end.

  
  Definition rename_subst : subst A -> _:=
    map (fun p => (f (fst p), rename (snd p))).
  
  Definition rename_sort t :=
    match t with
    | scon n l => scon (f n) (map rename l)
    end.

  Definition rename_ctx : ctx A -> _:=
    map (fun p => (f (fst p), rename_sort (snd p))).

  Definition rename_rule r :=
    match r with
    | sort_rule c args => sort_rule (rename_ctx c) (map f args)
    | term_rule c args t => term_rule (rename_ctx c) (map f args) (rename_sort t)
    | sort_eq_rule c t t' => sort_eq_rule (rename_ctx c) (rename_sort t) (rename_sort t')
    | term_eq_rule c e e' t =>
        term_eq_rule (rename_ctx c) (rename e) (rename e') (rename_sort t)
    end.
  
  Definition rename_lang : lang A -> _ :=
    map (fun p => (f (fst p), rename_rule (snd p))).

  Lemma rename_lookup s n
    : rename (subst_lookup s n) = subst_lookup (rename_subst s) (f n).
  Proof.
    induction s; basic_goal_prep; repeat case_match; basic_term_crush.
    symmetry in HeqH1.
    basic_utils_crush.
  Qed.

  (*TODO: make this export?*)
  #[local] Hint Rewrite rename_lookup : term.
  
  (*TODO: make this export & move to Utils?*)
  #[local] Hint Rewrite map_map : utils.
  
  Lemma rename_distr_subst e s
    : rename e[/s/] = (rename e) [/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; basic_term_crush.
    revert H1.
    induction l; basic_goal_prep; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_distr_subst : term.

  
  Lemma rename_args_distr_subst e s
    : map rename e[/s/] = (map rename e) [/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; fold_Substable; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_args_distr_subst : term.

  
  Lemma rename_sort_distr_subst e s
    : rename_sort e[/s/] = (rename_sort e) [/rename_subst s/].
  Proof.
    destruct e; basic_goal_prep; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_sort_distr_subst : term.

  
  Lemma rename_subst_distr_with_names_from c' s
    : rename_subst (with_names_from c' s)
      = with_names_from (rename_ctx c') (map rename s).
  Proof.
    revert s;
      induction c';
      destruct s;
      basic_goal_prep; fold_Substable; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_subst_distr_with_names_from : term.
  

  Local Lemma rename_mono l
    : (forall c t1 t2,
          eq_sort l c t1 t2 ->
          eq_sort (rename_lang l) (rename_ctx c) (rename_sort t1) (rename_sort t2))
      /\ (forall c t e1 e2,
             eq_term l c t e1 e2 ->
             eq_term (rename_lang l) (rename_ctx c) (rename_sort t) (rename e1) (rename e2))
      /\ (forall c c' s1 s2,
             eq_subst l c c' s1 s2 ->
             eq_subst (rename_lang l) (rename_ctx c) (rename_ctx c')
               (rename_subst s1) (rename_subst s2))
      /\ (forall c t,
             wf_sort l c t ->
             wf_sort (rename_lang l) (rename_ctx c) (rename_sort t))
      /\ (forall c e t,
             wf_term l c e t ->
             wf_term (rename_lang l) (rename_ctx c) (rename e) (rename_sort t))
      /\ (forall c s c',
             wf_args l c s c' ->
             wf_args (rename_lang l) (rename_ctx c) (map rename s) (rename_ctx c'))
      /\ (forall c,
             wf_ctx l c ->
             wf_ctx (rename_lang l) (rename_ctx c)).
  Proof using f_inj.
    apply judge_ind; basic_goal_prep.
    all:
      let l := lazymatch goal with l : lang _ |- _ => l end in
      try lazymatch goal with
          H : In _ l |- _ => 
            eapply in_map in H
        end.
    {
      eapply eq_sort_by.
      exact H1.
    }
    all: basic_core_crush.
    {
      eapply eq_term_by.
      exact H1.
    }
    {
      eapply wf_sort_by; eauto.
      exact H1.
    }
    {
      eapply wf_term_by; eauto.
      exact H1.
    }
    {
      eapply wf_term_var; eauto.
      eapply in_map in H1.
      exact H1.
    }
    {
      intro.
      apply H1.
      eapply injective_in.
      revert H6.
      unfold rename_ctx.
      rewrite !map_map; simpl; auto.
    }
  Qed.
  
End Injective.

Section Inverse.
  
  Context (A B : Type)
    `{Eqb A}
    `{Eqb B}
    (f : A -> B)
    (g : B -> A)
    (f_g_inverse : forall a, g (f a) = a).

  #[local] Lemma f_inj : Injective f.
  Proof.      
    intros a a' Heq.
    congruence.
  Qed.

  Lemma rename_inverse e
    : rename g (rename f e) = e.
  Proof.
    induction e; basic_goal_prep; repeat case_match; basic_term_crush.
    revert H1.
    induction l; basic_goal_prep; repeat case_match; basic_term_crush.
  Qed.

  #[local] Hint Rewrite rename_inverse : term.
  
  Lemma rename_inverse_args s
    : map (rename g) (map (rename f) s) = s.
  Proof.
    induction s; basic_goal_prep; repeat case_match; basic_term_crush.
  Qed.

  #[local] Hint Rewrite rename_inverse_args : term.
  
  Lemma rename_inverse_sort e
    : rename_sort g (rename_sort f e) = e.
  Proof.
    induction e; basic_goal_prep; repeat case_match; basic_term_crush.
  Qed.

  #[local] Hint Rewrite rename_inverse_sort : term.

End Inverse.
  

    (*TODO: rules about renaming inverses*)

