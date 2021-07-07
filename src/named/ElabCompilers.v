Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab.
(*TODO: why does this generate warnings?*)
Import Core.Notations.


Inductive elab_preserving_compiler (target : lang) : compiler -> compiler -> lang -> Prop :=
| elab_preserving_compiler_nil : elab_preserving_compiler target [] [] []
| elab_preserving_compiler_sort : forall cmp ecmp l n c args t et,
    elab_preserving_compiler target cmp ecmp l ->
    elab_sort target (compile_ctx ecmp c) t et ->
    elab_preserving_compiler target
                             ((n,sort_case (map fst c) t)::cmp)
                             ((n,sort_case (map fst c) et)::ecmp)
                             ((n,sort_rule c args) :: l)
| elab_preserving_compiler_term : forall cmp ecmp l n c args e ee t,
    elab_preserving_compiler target cmp ecmp l ->
    elab_term target (compile_ctx ecmp c) e ee (compile_sort ecmp t) ->
    elab_preserving_compiler target
                             ((n, term_case (map fst c) e)::cmp)
                             ((n, term_case (map fst c) ee)::ecmp)
                             ((n,term_rule c args t) :: l)
| elab_preserving_compiler_sort_eq : forall cmp ecmp l n c t1 t2,
    elab_preserving_compiler target cmp ecmp l ->
    eq_sort target (compile_ctx ecmp c) (compile_sort ecmp t1) (compile_sort ecmp t2) ->
    elab_preserving_compiler target cmp ecmp ((n,sort_eq_rule c t1 t2) :: l)
| elab_preserving_compiler_term_eq : forall cmp ecmp l n c e1 e2 t,
    elab_preserving_compiler target cmp ecmp l ->
    eq_term target (compile_ctx ecmp c) (compile_sort ecmp t) (compile ecmp e1) (compile ecmp e2) ->
    elab_preserving_compiler target cmp ecmp ((n,term_eq_rule c e1 e2 t) :: l).
#[export] Hint Constructors elab_preserving_compiler : lang_core.

Lemma elab_compiler_implies_preserving target cmp ecmp src
  : elab_preserving_compiler target cmp ecmp src ->
    preserving_compiler target ecmp src.
Proof using.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve elab_compiler_implies_preserving : lang_core.

      
Lemma elab_compiler_cons_nth_tail tgt cmp ecmp src n m name r
  : nth_error src m = Some (name,r) ->
    match r with
    | sort_rule c _ => 
      exists t et ecmp',
      nth_error cmp n = Some (name,sort_case (map fst c) t) /\
      nth_tail n ecmp = (name, sort_case (map fst c) et)::ecmp' /\
      let ecmp' := (nth_tail (S n) ecmp) in
      elab_preserving_compiler tgt (nth_tail (S n) cmp) ecmp' (nth_tail (S m) src) /\
      elab_sort tgt (compile_ctx ecmp' c) t et
    | term_rule c _ t =>
      exists e ee ecmp',
      nth_error cmp n = Some (name,term_case (map fst c) e) /\
      nth_tail n ecmp = (name, term_case (map fst c) ee)::ecmp' /\
      let ecmp' := (nth_tail (S n) ecmp) in
      elab_preserving_compiler tgt (nth_tail (S n) cmp) ecmp' (nth_tail (S m) src) /\
      elab_term tgt (compile_ctx ecmp' c) e ee (compile_sort ecmp' t)
    | sort_eq_rule c t1 t2 =>
      let ecmp' := (nth_tail n ecmp) in
      elab_preserving_compiler tgt (nth_tail n cmp) ecmp' (nth_tail (S m) src)
      /\ eq_sort tgt (compile_ctx ecmp' c)
                  (compile_sort ecmp' t1)
                  (compile_sort ecmp' t2)
    | term_eq_rule c e1 e2 t => 
      let ecmp' := (nth_tail n ecmp) in
      elab_preserving_compiler tgt (nth_tail n cmp) ecmp' (nth_tail (S m) src)
      /\ eq_term tgt (compile_ctx ecmp' c)
                  (compile_sort ecmp' t)
                  (compile ecmp' e1)
                  (compile ecmp' e2)
    end ->
    elab_preserving_compiler tgt (nth_tail n cmp) (nth_tail n ecmp) (nth_tail m src).
Proof.
  destruct r; intros; firstorder;
    repeat match goal with
    |[ H : nth_tail _ _ = _|-_] =>
     rewrite H; rewrite (nth_tail_equals_cons_res _ _ H); clear H
    |[ H : nth_error _ _ = _|-_] =>
     rewrite (nth_tail_to_cons _ _ H); clear H
           end;
    constructor; basic_utils_crush.
Qed.
