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

(* Determinism of the TYPED relational evaluator: the syntactic term determines
   ALL of its semantic indices (context, type, value, codomain).  Proved by the
   4-way mutual induction [eval_mutind]: each former has one constructor, so
   inverting the second derivation pins it and the per-premise IHs equate every
   index — including the intermediate/domain contexts of [ty_subst]/[cmp]/...,
   which are recovered from the substitution's own determinism. *)

Lemma eval_deterministic :
  (((forall G Ge, eval_env G Ge -> forall Ge', eval_env G Ge' -> Ge = Ge')
    * (forall Ge A T, eval_ty Ge A T ->
         forall Ge' T', eval_ty Ge' A T' -> (Ge = Ge') * (T = T')))
   * (forall Ge e T v, eval_rel Ge e T v ->
        forall Ge' T' v', eval_rel Ge' e T' v' -> (Ge = Ge') * (T = T') * (v = v')))
  * (forall Gin Gout g sg, eval_sub Gin Gout g sg ->
       forall Gin' Gout' sg', eval_sub Gin' Gout' g sg' ->
         (Gin = Gin') * (Gout = Gout') * (sg = sg')).
Proof.
  refine (eval_mutind
    (fun G Ge _ => forall Ge', eval_env G Ge' -> Ge = Ge')
    (fun Ge A T _ => forall Ge' T', eval_ty Ge' A T' -> (Ge = Ge') * (T = T'))
    (fun Ge e T v _ => forall Ge' T' v', eval_rel Ge' e T' v' ->
                         (Ge = Ge') * (T = T') * (v = v'))
    (fun Gin Gout g sg _ => forall Gin' Gout' sg', eval_sub Gin' Gout' g sg' ->
                              (Gin = Gin') * (Gout = Gout') * (sg = sg'))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
  intros;
  (* invert the second derivation — the one about the whole [con] term *)
  match goal with
  | H : eval_env (con _ _) _ |- _ => inversion H; subst; clear H
  | H : eval_ty _ (con _ _) _ |- _ => inversion H; subst; clear H
  | H : eval_rel _ (con _ _) _ _ |- _ => inversion H; subst; clear H
  | H : eval_sub _ _ (con _ _) _ |- _ => inversion H; subst; clear H
  end;
  (* equate every subderivation's indices via its IH (matching on the term) *)
  repeat match goal with
  | IH : forall Ge', eval_env ?G Ge' -> _ = Ge', H : eval_env ?G _ |- _ =>
      specialize (IH _ H); subst; clear H
  | IH : forall Ge' T', eval_ty Ge' ?A T' -> _, H : eval_ty _ ?A _ |- _ =>
      let p := fresh in pose proof (IH _ _ H) as p; destruct p as [? ?]; subst; clear H
  | IH : forall Ge' T' v', eval_rel Ge' ?e T' v' -> _, H : eval_rel _ ?e _ _ |- _ =>
      let p := fresh in pose proof (IH _ _ _ H) as p; destruct p as [[? ?] ?]; subst; clear H
  | IH : forall Gin' Gout' sg', eval_sub Gin' Gout' ?g sg' -> _,
      H : eval_sub _ _ ?g _ |- _ =>
      let p := fresh in pose proof (IH _ _ _ H) as p; destruct p as [[? ?] ?]; subst; clear H
  end;
  repeat split; try reflexivity; try congruence.
Qed.

Definition eval_env_det : forall G Ge Ge',
    eval_env G Ge -> eval_env G Ge' -> Ge = Ge' :=
  fun G Ge Ge' H => fst (fst (fst eval_deterministic)) G Ge H Ge'.
Definition eval_ty_det : forall Ge Ge' A T T',
    eval_ty Ge A T -> eval_ty Ge' A T' -> (Ge = Ge') * (T = T') :=
  fun Ge Ge' A T T' H => snd (fst (fst eval_deterministic)) Ge A T H Ge' T'.
Definition eval_rel_det : forall Ge Ge' e T T' v v',
    eval_rel Ge e T v -> eval_rel Ge' e T' v' -> (Ge = Ge') * (T = T') * (v = v') :=
  fun Ge Ge' e T T' v v' H => snd (fst eval_deterministic) Ge e T v H Ge' T' v'.
Definition eval_sub_det : forall Gin Gin' Gout Gout' g sg sg',
    eval_sub Gin Gout g sg -> eval_sub Gin' Gout' g sg' ->
    (Gin = Gin') * (Gout = Gout') * (sg = sg') :=
  fun Gin Gin' Gout Gout' g sg sg' H => snd eval_deterministic Gin Gout g sg H Gin' Gout' sg'.
