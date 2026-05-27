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

(* Determinism of the environment-free relational evaluator: each term has at most
   one value.  Every term former is matched by one eval constructor, except [El],
   whose two constructors (code vs. neutral) are disambiguated by determinism of the
   code's own evaluation.  Proved by mutual induction. *)

Scheme eval_sub_mind := Induction for eval_sub Sort Prop
  with eval_ty_mind  := Induction for eval_ty  Sort Prop
  with eval_rel_mind := Induction for eval_rel Sort Prop.
Combined Scheme eval_mind from eval_sub_mind, eval_ty_mind, eval_rel_mind.

Lemma eval_deterministic :
  (forall e s, eval_sub e s -> forall s', eval_sub e s' -> s = s')
  /\ (forall e T, eval_ty e T -> forall T', eval_ty e T' -> T = T')
  /\ (forall e v, eval_rel e v -> forall v', eval_rel e v' -> v = v').
Proof.
  apply eval_mind; intros;
    (* invert the second derivation: the hypothesis whose value is the goal's RHS
       variable (premise sub-derivations have concrete values, so won't match). *)
    match goal with
    | H : eval_sub _ ?v |- _ = ?v => inversion H; subst; clear H
    | H : eval_ty _ ?v |- _ = ?v => inversion H; subst; clear H
    | H : eval_rel _ ?v |- _ = ?v => inversion H; subst; clear H
    end;
    (* turn each sub-derivation into an equality via its IH (motive is [_ = x]) *)
    repeat match goal with
    | IH : forall x, eval_sub ?e x -> _ = x, H : eval_sub ?e _ |- _ => specialize (IH _ H); subst
    | IH : forall x, eval_ty ?e x -> _ = x, H : eval_ty ?e _ |- _ => specialize (IH _ H); subst
    | IH : forall x, eval_rel ?e x -> _ = x, H : eval_rel ?e _ |- _ => specialize (IH _ H); subst
    end;
    try reflexivity; try congruence.
Qed.

Definition eval_sub_det := proj1 eval_deterministic.
Definition eval_ty_det  := proj1 (proj2 eval_deterministic).
Definition eval_rel_det := proj2 (proj2 eval_deterministic).

(* Environment normalization is deterministic too (uses eval_ty determinism). *)
Lemma eval_env_det : forall G Genv, eval_env G Genv -> forall Genv', eval_env G Genv' -> Genv = Genv'.
Proof.
  induction 1 as [ | A i G Genv S HG IH HA ]; intros Genv' H'; inversion H'; subst; clear H'.
  - reflexivity.
  - match goal with H : eval_env G _ |- _ => specialize (IH _ H) end.
    match goal with H : eval_ty A _ |- _ => pose proof (eval_ty_det HA H) end.
    subst; reflexivity.
Qed.
