Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Universe Declaration.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Typing Preservation ApplySubst RenSubst RenTyping LogRel2.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Phase-2/4 RENAMING STABILITY of the two-sided [LR] -- the base-PER       *)
(* layer.  [NeConv]/[RedNatEq]/[RedNeutralEq] are stable under a context     *)
(* renaming, now that [RenTyping.ren_typing] renames [wf_neutral] at every   *)
(* type (incl. the neutrals-at-[dEl] these PERs store).  The renaming        *)
(* package is [ren_ctx rho Ge Ge'] + [ren_ok rho (S (length Ge)) (length     *)
(* Ge')] + the source scopedness [ne_below_ty]/[ne_below_ctx] that           *)
(* [ren_typing] consumes; the [LR_ren_gen] presheaf supplies all of these    *)
(* from the LR pack's stored typing.                                         *)
(* ===================================================================== *)

(* The pointwise neutral conversion [NeConv] renames: both sides are          *)
(* [wf_neutral] (renamed by [ren_typing]) and the syntactic diagonal [n = m]  *)
(* is preserved by [ren_ne]. *)
Lemma NeConv_ren : forall Ge T n m, NeConv Ge T n m ->
    ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      NeConv Ge' (ren_ty rho T) (ren_ne rho n) (ren_ne rho m).
Proof.
  intros Ge T n m [[wn wm] e] Hty Hctx Ge' rho Hren Hok.
  subst m. unfold NeConv. repeat split.
  - exact (snd ren_typing Ge n T wn Hty Hctx Ge' rho Hren Hok).
  - exact (snd ren_typing Ge n T wm Hty Hctx Ge' rho Hren Hok).
Qed.

(* The PER of convertible naturals renames (it lives at [dEl vNat], whose
   scopedness is vacuous, so no [ne_below_ty] hypothesis is needed). *)
Lemma RedNatEq_ren : forall Ge v w, RedNatEq Ge v w ->
    ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      RedNatEq Ge' (ren_val rho v) (ren_val rho w).
Proof.
  intros Ge v w H Hctx Ge' rho Hren Hok.
  induction H as [ | v w Hvw IH | n m Hnm ].
  - cbn [ren_val]. apply rne_zero.
  - cbn [ren_val]. apply rne_suc. exact IH.
  - cbn [ren_val]. apply rne_ne.
    exact (NeConv_ren Hnm I Hctx Hren Hok).
Qed.

(* The PER of convertible neutrals at a fixed type renames. *)
Lemma RedNeutralEq_ren : forall Ge T v w, RedNeutralEq Ge T v w ->
    ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      RedNeutralEq Ge' (ren_ty rho T) (ren_val rho v) (ren_val rho w).
Proof.
  intros Ge T v w H Hty Hctx Ge' rho Hren Hok.
  destruct H as [n m Hnm]. cbn [ren_val]. apply rneT.
  exact (NeConv_ren Hnm Hty Hctx Hren Hok).
Qed.
