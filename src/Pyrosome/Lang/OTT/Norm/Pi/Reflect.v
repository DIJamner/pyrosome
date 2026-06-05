Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply.
Import Core.Notations.

(* ===================================================================== *)
(* Type-directed eta-long reflection of a neutral into a value.           *)
(*                                                                        *)
(*   Reflect m T n v  :  in a context of length [m], reflecting the       *)
(*                       neutral [n] at semantic type [T] yields [v].     *)
(*                                                                        *)
(* At a BASE type (the universe, El Nat/Empty, El of a neutral code, or   *)
(* El of a proof-IRRELEVANT Pi) a neutral stays neutral ([vNe n]).  At a  *)
(* relevant Pi type [El (vPi F B)] the neutral is ETA-EXPANDED to a       *)
(* lambda whose body is the reflection of [n] applied to the (reflected)  *)
(* bound variable.  This is what makes the eta law hold on normal forms:  *)
(* every value of relevant function type is a [vLam], never a bare        *)
(* neutral.                                                               *)
(*                                                                        *)
(* In the Pi case we work under one new binder (length [S m]): the bound  *)
(* variable is de Bruijn index 0, the spine head [n] and domain code [F]  *)
(* are weakened into the binder, and the result type is the codomain [B]  *)
(* with the bound variable instantiated by the reflected argument         *)
(* (substitution [ARG :: wkn_list m], which keeps the [m] ambient indices *)
(* in place rather than decrementing them). *)

Inductive Reflect : nat -> svalty -> neutral -> sval -> Type :=
| refl_U     : forall m r l n, Reflect m (dU r l) n (vNe n)
| refl_Nat   : forall m n, Reflect m (dEl vNat) n (vNe n)
| refl_Empty : forall m n, Reflect m (dEl vEmpty) n (vNe n)
| refl_neEl  : forall m c n, Reflect m (dEl (vNe c)) n (vNe n)
| refl_PiI   : forall m F B n, Reflect m (dEl (vPiI F B)) n (vNe n)
| refl_Pi    : forall m F B n ARG B' body,
    Reflect (S m) (dEl (shift_val 0 1 F)) (nVar 0) ARG ->
    Apply_val (S m) (ARG :: wkn_list m) B B' ->
    Reflect (S m) (dEl B')
            (nApp (shift_ne 0 1 n) (shift_val 0 1 F) (shift_val 1 1 B) ARG) body ->
    Reflect m (dEl (vPi F B)) n (vLam body).

(* ===================================================================== *)
(* Determinism: (m, T, n) determines the reflected value.                 *)
(* ===================================================================== *)
Lemma Reflect_det : forall m T n v,
    Reflect m T n v -> forall v', Reflect m T n v' -> v = v'.
Proof.
  induction 1 as
    [ m r l n | m n | m n | m c n | m F B n
    | m F B n ARG B' body Harg IHarg Hb Hbody IHbody ];
    intros v' Hr; inversion Hr; subst; try reflexivity.
  (* refl_Pi *)
  specialize (IHarg _ ltac:(eassumption)); subst ARG.
  match goal with H : Apply_val _ _ B _ |- _ =>
    pose proof (Apply_val_det Hb H); subst end.
  specialize (IHbody _ ltac:(eassumption)); subst body.
  reflexivity.
Qed.
