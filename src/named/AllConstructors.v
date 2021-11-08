Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core.
Import Core.Notations.

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

  

  Fixpoint all_constructors (P : V -> Prop) e :=
    match e with
    | var _ => True
    | con n s => P n /\ all (all_constructors P) s
    end.

  Definition all_constructors_sort P t :=
    match t with
    | scon n s => P n /\ all (all_constructors P) s
    end.

  
  (*We use a notation so that auto recognizes it after
  reduction
   *) 
  Notation all_constructors_ctx P c :=
    (all (fun '(_,t) => all_constructors_sort P t) c).


  Definition all_constructors_rule P r :=
    match r with
    | sort_rule c _ => all (fun '(_, t) => all_constructors_sort P t) c
    | term_rule c _ t =>
        (all_constructors_ctx P c)
        /\ (all_constructors_sort P t)
    | _ => True
    end.

  Lemma all_constructors_term_weaken (P Q : _ -> Prop) e
    : (forall n, P n -> Q n) ->
      all_constructors P e ->
      all_constructors Q e.
  Proof.
    intro.
    induction e; basic_goal_prep; basic_core_firstorder_crush.

    revert dependent l;
      induction l; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve all_constructors_term_weaken : lang_core.


  Lemma all_constructors_args_weaken (P Q : _ -> Prop) l
    : (forall n, P n -> Q n) ->
      all (all_constructors P) l ->
      all (all_constructors Q) l.
  Proof.
    intro;
      revert dependent l;
      induction l; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve all_constructors_args_weaken : lang_core.


  Lemma all_constructors_sort_weaken (P Q : _ -> Prop) e
    : (forall n, P n -> Q n) ->
      all_constructors_sort P e ->
      all_constructors_sort Q e.
  Proof.
    intro.
    destruct e; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve all_constructors_sort_weaken : lang_core.

  Lemma all_constructors_ctx_weaken (P Q : _ -> Prop) (c : ctx)
    : (forall n, P n -> Q n) ->
      all_constructors_ctx P c ->
      all_constructors_ctx Q c.
  Proof.
    intro;
      induction c; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve all_constructors_ctx_weaken : lang_core.


  Lemma all_constructors_rule_weaken (P Q : _ -> Prop) r
    : (forall n, P n -> Q n) ->
      all_constructors_rule P r ->
      all_constructors_rule Q r.
  Proof.
    intro;
      destruct r; basic_goal_prep; basic_core_crush.
    all: eapply all_constructors_ctx_weaken; eauto.
  Qed.
  Hint Resolve all_constructors_rule_weaken : lang_core.


  Lemma all_constructors_lang_weaken (P Q : _ -> Prop) (l : lang)
    : (forall n, P n -> Q n) ->
      all (fun '(_, t) => all_constructors_rule P t) l ->
      all (fun '(_, t) => all_constructors_rule Q t) l.
  Proof.
    intro;
      induction l; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve all_constructors_lang_weaken : lang_core.
  
End WithVar.

(*We use a notation so that auto recognizes it after
  reduction
 *) 
Notation all_constructors_ctx P c :=
  (all (fun '(_,t) => all_constructors_sort P t) c).

#[export] Hint Resolve all_constructors_term_weaken : lang_core.
#[export] Hint Resolve all_constructors_args_weaken : lang_core.
#[export] Hint Resolve all_constructors_sort_weaken : lang_core.
#[export] Hint Resolve all_constructors_ctx_weaken : lang_core.
#[export] Hint Resolve all_constructors_rule_weaken : lang_core.
#[export] Hint Resolve all_constructors_lang_weaken : lang_core.
