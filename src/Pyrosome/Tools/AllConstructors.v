Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
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
    | sort_eq_rule c t1 t2 =>
        (all_constructors_ctx P c)
        /\ (all_constructors_sort P t1)
        /\ (all_constructors_sort P t2)
    | term_eq_rule c e1 e2 t =>
        (all_constructors_ctx P c)
        /\ (all_constructors_sort P t)
        /\ (all_constructors P e1)
        /\ (all_constructors P e2)
    end.

  Lemma all_constructors_term_weaken (P Q : _ -> Prop) e
    : (forall n, P n -> Q n) ->
      all_constructors P e ->
      all_constructors Q e.
  Proof.
    intro.
    induction e; basic_goal_prep; basic_core_firstorder_crush.

    generalize dependent l;
      induction l; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve all_constructors_term_weaken : lang_core.


  Lemma all_constructors_args_weaken (P Q : _ -> Prop) l
    : (forall n, P n -> Q n) ->
      all (all_constructors P) l ->
      all (all_constructors Q) l.
  Proof.
    intro;
      generalize dependent l;
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

  (* A well-formed judgment only mentions symbols declared in [l]. *)
  Lemma wf_all_constructors (l : lang) :
    (forall c t1 t2, eq_sort l c t1 t2 -> True)
    /\ (forall c t e1 e2, eq_term l c t e1 e2 -> True)
    /\ (forall c c' s1 s2, eq_subst (Model:=core_model l) c c' s1 s2 -> True)
    /\ (forall c t, wf_sort l c t ->
          all_constructors_sort (fun n => In n (map fst l)) t)
    /\ (forall c e t, wf_term l c e t ->
          all_constructors (fun n => In n (map fst l)) e)
    /\ (forall c s c', wf_args (Model:=core_model l) c s c' ->
          all (all_constructors (fun n => In n (map fst l))) s)
    /\ (forall c, wf_ctx (Model:=core_model l) c -> True).
  Proof.
    apply judge_ind; basic_goal_prep; try exact I.
    all: try assumption.
    all: split; try assumption.
    all: basic_utils_crush.
  Qed.

  Lemma wf_sort_all_constructors l c t
    : wf_sort l c t -> all_constructors_sort (fun n => In n (map fst l)) t.
  Proof. destruct (wf_all_constructors l) as (_ & _ & _ & H & _). apply H. Qed.

  Lemma wf_term_all_constructors l c e t
    : wf_term l c e t -> all_constructors (fun n => In n (map fst l)) e.
  Proof. destruct (wf_all_constructors l) as (_ & _ & _ & _ & H & _). apply H. Qed.

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
