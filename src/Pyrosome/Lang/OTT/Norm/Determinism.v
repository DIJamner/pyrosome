Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel.
Import Core.Notations.

(* Determinism of the relational evaluator: each term has at most one value in a
   given environment (every term-former is matched by a single eval constructor).
   Needed for cterm_trans in the Norm model. Proved by mutual induction. *)

Scheme eval_sub_mind := Induction for eval_sub Sort Prop
  with eval_ty_mind  := Induction for eval_ty  Sort Prop
  with eval_rel_mind := Induction for eval_rel Sort Prop.
Combined Scheme eval_mind from eval_sub_mind, eval_ty_mind, eval_rel_mind.

Lemma eval_deterministic :
  (forall r e r', eval_sub r e r' -> forall r'', eval_sub r e r'' -> r' = r'')
  /\ (forall r e T, eval_ty r e T -> forall T', eval_ty r e T' -> T = T')
  /\ (forall r e v, eval_rel r e v -> forall v', eval_rel r e v' -> v = v').
Proof.
  apply eval_mind;
    repeat match goal with
           | [ |- forall _, _ ] => intro
           end;
    (* The conclusion is [known_result = ?goal_var].
       The second derivation is [eval_X r e ?goal_var].
       Match and invert on it. *)
    match goal with
    | [ H : eval_sub _ _ ?v, Heq : ?v = ?v |- ?w = ?v ] =>
        inversion H; subst; clear H
    | [ H : eval_sub _ _ ?v |- _ = ?v ] => inversion H; subst; clear H
    | [ H : eval_ty  _ _ ?v |- _ = ?v ] => inversion H; subst; clear H
    | [ H : eval_rel _ _ ?v |- _ = ?v ] => inversion H; subst; clear H
    end;
    repeat match goal with
           | [ IH : forall x, eval_sub _ _ x -> _ = x, H : eval_sub _ _ _ |- _ ] =>
               specialize (IH _ H); subst
           | [ IH : forall x, eval_ty  _ _ x -> _ = x, H : eval_ty  _ _ _ |- _ ] =>
               specialize (IH _ H); subst
           | [ IH : forall x, eval_rel _ _ x -> _ = x, H : eval_rel _ _ _ |- _ ] =>
               specialize (IH _ H); subst
           end;
    try reflexivity; try congruence.
Qed.

Definition eval_sub_det := proj1 eval_deterministic.
Definition eval_ty_det := proj1 (proj2 eval_deterministic).
Definition eval_rel_det := proj2 (proj2 eval_deterministic).
