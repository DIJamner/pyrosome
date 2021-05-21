Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilersWithPrefix.
Import Exp.Notations.


(*TODO: move to utils*)
Fixpoint no_repeats {A} (l : list A) :=
  match l with
  | [] => True
  | n::l' => ~ In n l' /\ no_repeats l'
  end.
  
(*TODO: move to utils?*)
Definition bijective_on {A B} (f : A -> B) l : Prop :=
  no_repeats (map f l).

(*TODO: move to utils*)
#[export] Hint Resolve in_map : utils.

Lemma bijective_fn_injective {A B} (f : A -> B) l
  : bijective_on f l ->
    forall x y, In x l ->
                In y l ->
                f x = f y -> x = y.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
  {
    rewrite H2 in H.
    basic_utils_crush.
  }
  {
    rewrite <-H2 in H.
    basic_utils_crush.
  }
Qed.

Section RenameFromFn.
  Context (f : string -> string).

  Fixpoint compiler_from_fn (l : lang) :=
    match l with
    | [] => []
    | (n,sort_rule c args)::l => (n, sort_case (map fst c) (scon (f n) (map var args)))::(compiler_from_fn l)
    | (n,term_rule c args _)::l => (n, term_case (map fst c) (con (f n) (map var args)))::(compiler_from_fn l)
    | _::l => compiler_from_fn l
    end.

  Fixpoint elab_compiler_from_fn (l : lang) :=
    match l with
    | [] => []
    | (n,sort_rule c _)::l => (n, sort_case (map fst c) (scon (f n) (map var (map fst c))))::(elab_compiler_from_fn l)
    | (n,term_rule c _ _)::l => (n, term_case (map fst c) (con (f n) (map var (map fst c))))::(elab_compiler_from_fn l)
    | _::l => elab_compiler_from_fn l
    end.

  Fixpoint rename_exp e :=
    match e with
    | var x => var x
    | con n s => con (f n) (map rename_exp s)
    end.

  Definition rename_sort t :=
    match t with
    | scon n s => scon (f n) (map rename_exp s)
    end.

  Definition rename_ctx c := named_map rename_sort c.
  
  Definition rename_subst s := named_map rename_exp s.
  Definition rename_args s := map rename_exp s.

  Lemma rename_subst_lookup s n
    : rename_exp (subst_lookup s n) = subst_lookup (rename_subst s) n.
  Proof.
    induction s; basic_goal_prep; basic_exp_crush.
    my_case H (n=? s0);
      basic_exp_crush.
  Qed.
  Hint Rewrite rename_subst_lookup : exp.
  
  Lemma rename_exp_subst_comm e s
    : rename_exp e[/s/] = (rename_exp e)[/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; basic_exp_crush.
    revert dependent l.
    induction l; basic_goal_prep; basic_exp_crush.
  Qed.
  Hint Rewrite rename_exp_subst_comm : exp.

  
  Lemma rename_args_subst_comm e s
    : rename_args e[/s/] = (rename_args e)[/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; basic_exp_crush.
  Qed.
  Hint Rewrite rename_args_subst_comm : exp.

  
  Lemma rename_sort_subst_comm e s
    : rename_sort e[/s/] = (rename_sort e)[/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; basic_exp_crush.
  Qed.
  Hint Rewrite rename_sort_subst_comm : exp.

  
  Lemma rename_subst_subst_comm e s
    : rename_subst e[/s/] = (rename_subst e)[/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; basic_exp_crush.
  Qed.
  Hint Rewrite rename_subst_subst_comm : exp.

  
  Lemma rename_subst_with_names_from A (c : named_list A) s
    : rename_subst (with_names_from c s) = with_names_from c (rename_args s).
  Proof.
    revert s.
    induction c;
      destruct s;
      basic_goal_prep; basic_exp_crush.
  Qed.
  Hint Rewrite rename_subst_with_names_from : exp.
    
  
  Definition rename_rule r :=
    match r with
    | sort_rule c args => sort_rule (rename_ctx c) args
    | term_rule c args t => term_rule (rename_ctx c) args (rename_sort t)
    | sort_eq_rule c t1 t2 => sort_eq_rule (rename_ctx c) (rename_sort t1) (rename_sort t2)
    | term_eq_rule c e1 e2 t => term_eq_rule (rename_ctx c) (rename_exp e1) (rename_exp e2) (rename_sort t)
    end.

  Definition rename_lang (l : lang) : lang :=
    map (fun '(n,r) => (f n,rename_rule r)) l.

  
  Local Lemma in_rename l n r
    : In (n,r) l -> In (f n, rename_rule r) (rename_lang l).
  Proof.
    unfold rename_lang.
    intro.
    eapply in_map in H.
    exact H.
  Qed.
  Local Hint Resolve in_rename : lang_core.

  Lemma with_names_from_rename_ctx A c (s : list A)
    : with_names_from (rename_ctx c) s = with_names_from c s.
  Proof.
    revert s.
    induction c; destruct s; basic_goal_prep; basic_exp_crush.
  Qed.
  
  Local Lemma rename_mono l
    : (forall c t1 t2,
          eq_sort l c t1 t2 ->
          eq_sort (rename_lang l) (rename_ctx c) (rename_sort t1) (rename_sort t2))
      /\ (forall c t e1 e2,
             eq_term l c t e1 e2 ->
             eq_term (rename_lang l) (rename_ctx c) (rename_sort t) (rename_exp e1) (rename_exp e2))
      /\ (forall c c' s1 s2,
             eq_subst l c c' s1 s2 ->
             eq_subst (rename_lang l) (rename_ctx c) (rename_ctx c') (rename_subst s1) (rename_subst s2))
      /\ (forall c t,
             wf_sort l c t ->
             wf_sort (rename_lang l) (rename_ctx c) (rename_sort t))
      /\ (forall c e t,
             wf_term l c e t ->
             wf_term (rename_lang l) (rename_ctx c) (rename_exp e) (rename_sort t))
      /\ (forall c s c',
             wf_args l c s c' ->
             wf_args (rename_lang l) (rename_ctx c) (rename_args s) (rename_ctx c'))
      /\ (forall c,
             wf_ctx l c ->
             wf_ctx (rename_lang l) (rename_ctx c)).
  Proof using.
    apply judge_ind; basic_goal_prep;
      try match goal with
            [ H : In _ l |- _] =>
            apply in_rename in H; simpl in H
          end;      
      basic_core_crush.
    {
      rewrite <- with_names_from_rename_ctx.
      basic_core_crush.
    }
    {
      eapply in_map in H.
      constructor.
      exact H.
    }
    {
      constructor.
      basic_core_crush.
      rewrite with_names_from_rename_ctx.
      basic_core_crush.
      basic_core_crush.
    }
    {
      unfold rename_ctx.
      rewrite fresh_named_map.
      assumption.
    }
  Qed.
                                                   
  Local Lemma elab_rename_mono l
    : (forall c t et,
          elab_sort l c t et ->
          elab_sort (rename_lang l) (rename_ctx c) (rename_sort t) (rename_sort et))
      /\ (forall c e ee t,
             elab_term l c e ee t ->
             elab_term (rename_lang l) (rename_ctx c) (rename_exp e) (rename_exp ee) (rename_sort t))
      /\ (forall c s args es c',
             elab_args l c s args es c' ->
             elab_args (rename_lang l)  (rename_ctx c) (rename_args s) args (rename_args es) (rename_ctx c'))
      /\ (forall c ec,
             elab_ctx l c ec ->
             elab_ctx (rename_lang l) (rename_ctx c) (rename_ctx ec)).
  Proof using.
    apply elab_ind; basic_goal_prep; 
      try match goal with
            [ H : In _ l |- _] =>
            apply in_rename in H; simpl in H
          end;      
      basic_core_crush.
    {
      rewrite <- with_names_from_rename_ctx.
      basic_core_crush.
    }
    {
      apply (proj1 (rename_mono l)) in H1.
      basic_core_crush.      
    }
    {
      eapply in_map in H.
      constructor.
      exact H.
    }
    {
      constructor.
      basic_core_crush.
      rewrite with_names_from_rename_ctx.
      basic_core_crush.
      basic_core_crush.
    }
    {
      constructor.
      basic_core_crush.
     (* TODO: rw backwards, apply earlier lem*)
  Admitted.                    


End RenameFromFn.

Hint Rewrite rename_subst_lookup : exp.

             
Definition elab_sort_lang_rename_monotonicity f l
  := proj1 (elab_rename_mono f l).
#[export] Hint Resolve elab_sort_lang_rename_monotonicity : lang_core.

Definition elab_term_lang_rename_monotonicity f l
  := proj1 (proj2 (elab_rename_mono f l)).
#[export] Hint Resolve elab_term_lang_rename_monotonicity : lang_core.

Definition elab_args_lang_rename_monotonicity f l
  := proj1 (proj2 (proj2 (elab_rename_mono f l))).
#[export] Hint Resolve elab_args_lang_rename_monotonicity : lang_core.

Definition elab_ctx_lang_rename_monotonicity f l
  := proj2 (proj2 (proj2 (elab_rename_mono f l))).
#[export] Hint Resolve elab_ctx_lang_rename_monotonicity : lang_core.


Definition eq_sort_lang_monotonicity_rename f l
  := proj1 (rename_mono f l).
#[export] Hint Resolve eq_sort_lang_monotonicity_rename : lang_core.

Definition eq_term_lang_monotonicity_rename f l
  := proj1 (proj2 (rename_mono f l)).
#[export] Hint Resolve eq_term_lang_monotonicity_rename : lang_core.

Definition eq_subst_lang_monotonicity_rename f l
  := proj1 (proj2 (proj2 (rename_mono f l))).
#[export] Hint Resolve eq_subst_lang_monotonicity_rename : lang_core.

Definition wf_sort_lang_monotonicity_rename f l
  := proj1 (proj2 (proj2 (proj2 (rename_mono f l)))).
#[export] Hint Resolve wf_sort_lang_monotonicity_rename : lang_core.

Definition wf_term_lang_monotonicity_rename f l
  := proj1 (proj2 (proj2 (proj2 (proj2 (rename_mono f l))))).
#[export] Hint Resolve wf_term_lang_monotonicity_rename : lang_core.

Definition wf_args_lang_monotonicity_rename f l
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (rename_mono f l)))))).
#[export] Hint Resolve wf_args_lang_monotonicity_rename : lang_core.

Definition wf_ctx_lang_monotonicity_rename f l
  := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (rename_mono f l)))))).
#[export] Hint Resolve wf_ctx_lang_monotonicity_rename : lang_core.

Lemma wf_rule_lang_monotonicity_rename f l r
  : wf_rule l r -> wf_rule (rename_lang f l) (rename_rule f r).
Proof.
  inversion 1; basic_goal_prep; unfold rename_ctx; basic_core_crush.
  all: rewrite !named_map_fst_eq; auto.
Qed.
#[export] Hint Resolve wf_rule_lang_monotonicity_rename : lang_core.

Local Lemma fresh_rename f n l
  : bijective_on f (n::map fst l) -> fresh n l -> fresh (f n) (rename_lang f l).
Proof.
  unfold bijective_on.
  simpl.
  induction l; basic_goal_prep.
  basic_exp_crush.
  firstorder.
Qed.

Lemma wf_lang_rename f l
  : bijective_on f (map fst l) -> wf_lang l -> wf_lang (rename_lang f l).
Proof.
  induction 2; basic_goal_prep; basic_core_crush.
  apply  fresh_rename; eauto.
  unfold bijective_on.
  simpl.
  firstorder.
Qed.  
#[export] Hint Resolve wf_lang_rename : lang_core.

(*TODO: compilers part *)
(*
Theorem renaming_preserving f tgt cmp l
  : incl (rename_lang f l) tgt -> elab_preserving_compiler cmp tgt (compiler_from_fn f l) (elab_compiler_from_fn f l) l.
Proof.
  induction l; basic_goal_prep.
  basic_core_crush.
  destruct r; basic_goal_prep; basic_core_crush.
  {
    constructor; auto.
    
    basic_core_crush.
    
    TODO: need renaming for Elab.elab
*)
