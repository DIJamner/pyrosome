Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Typing Preservation LogRel LogRelLemmas.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Smart constructors for the top-level reducibility relations            *)
(* ([RedTy]/[RedTm]) and the forgetful map [RedSub] -> [wf_ssub].          *)
(*                                                                         *)
(* These package the level bookkeeping of the finite tower ([LR2] = [LR]   *)
(* at [tl2]) so downstream proofs (the fundamental lemma, [reflect_red],    *)
(* [Apply_total_red]) can build/destruct reducibility witnesses without     *)
(* unfolding [LR2]/[RedTy]/[RedTm] by hand.  All are non-recursive: each     *)
(* introduces a single [LR] constructor or projects an existing witness.    *)
(* ===================================================================== *)

(* ---- Universe-level evidence for [LRU] (codes live strictly below). ---- *)

(* [lvl_of] only ever returns [tl0] or [tl1] (it inspects a head name), so a
   code's El level is always strictly below the top of the tower. *)
Lemma lvl_of_ne2 : forall l, lvl_of l <> tl2.
Proof.
  intro l. destruct l as [x | n args]; cbn; [ discriminate | ].
  destruct (eqb n "L1"); discriminate.
Qed.

Lemma lvl_of_lt2 : forall l, TLlt (lvl_of l) tl2.
Proof.
  intro l. pose proof (lvl_of_ne2 l).
  destruct (lvl_of l).
  - apply lt02.
  - apply lt12.
  - congruence.
Qed.

(* ===================================================================== *)
(* [RedTy] smart constructors (one per [LR] type former).                  *)
(* ===================================================================== *)

Definition redTy_nat   Ge : RedTy Ge (dEl vNat) :=
  existT _ (RedNat Ge) (@LRnat tl2 rec2 Ge).

Definition redTy_empty Ge : RedTy Ge (dEl vEmpty) :=
  existT _ (RedNeutral Ge (dEl vEmpty)) (@LRempty tl2 rec2 Ge).

Definition redTy_neEl Ge n r l (w : wf_neutral Ge n (dU r l))
  : RedTy Ge (dEl (vNe n)) :=
  existT _ (RedNeutral Ge (dEl (vNe n))) (@LRne tl2 rec2 Ge n r l w).

Definition redTy_piI Ge F B (wpi : wf_svalty Ge (dEl (vPiI F B)))
  : RedTy Ge (dEl (vPiI F B)) :=
  existT _ _ (@LRpiI tl2 rec2 Ge F B wpi).

Definition redTy_pi Ge F B (PA : PolyRedPack Ge F B)
           (wpi : wf_svalty Ge (dEl (vPi F B)))
           (ad : PolyRedPackAdequate LR2 PA)
  : RedTy Ge (dEl (vPi F B)) :=
  existT _ (PiRedTmPred PA) (@LRpi tl2 rec2 Ge F B PA wpi ad).

Definition redTy_U Ge r l : RedTy Ge (dU r l) :=
  existT _ _ (@LRU tl2 rec2 Ge r l (lvl_of_lt2 l)).

(* ===================================================================== *)
(* [RedTm] smart constructors.                                             *)
(* ===================================================================== *)

Definition redTm_nat Ge v (h : RedNat Ge v) : RedTm Ge (dEl vNat) v :=
  existT _ (RedNat Ge) (@LRnat tl2 rec2 Ge, h).

Definition redTm_empty Ge n (w : wf_neutral Ge n (dEl vEmpty))
  : RedTm Ge (dEl vEmpty) (vNe n) :=
  existT _ (RedNeutral Ge (dEl vEmpty)) (@LRempty tl2 rec2 Ge, rne w).

Definition redTm_neEl Ge n r l (w : wf_neutral Ge n (dU r l)) m
           (wm : wf_neutral Ge m (dEl (vNe n)))
  : RedTm Ge (dEl (vNe n)) (vNe m) :=
  existT _ (RedNeutral Ge (dEl (vNe n)))
         (@LRne tl2 rec2 Ge n r l w, rne wm).

Definition redTm_piI Ge F B (wpi : wf_svalty Ge (dEl (vPiI F B))) v
           (hv : has_svalty Ge v (dEl (vPiI F B)))
  : RedTm Ge (dEl (vPiI F B)) v :=
  existT _ _ (@LRpiI tl2 rec2 Ge F B wpi, hv).

(* ===================================================================== *)
(* Conversions between the two reducible-value carriers.                   *)
(* ===================================================================== *)

(* A reducible term yields a reducible type (forget the value). *)
Definition RedTm_RedTy Ge T v (h : RedTm Ge T v) : RedTy Ge T :=
  existT _ (projT1 h) (fst (projT2 h)).

(* Pack a value reducible *at the type's canonical predicate* into [RedTm]. *)
Definition RedTmOf_RedTm Ge T (RT : RedTy Ge T) v (p : RedTmOf RT v)
  : RedTm Ge T v :=
  existT _ (projT1 RT) (projT2 RT, p).

(* ===================================================================== *)
(* [RedSub] : projections, the empty substitution, and the forgetful map   *)
(* to [wf_ssub] (reducibility implies well-typedness, pointwise).          *)
(* ===================================================================== *)

Definition RedSub_length Delta sg Ge (h : RedSub Delta sg Ge)
  : length sg = length Ge := fst h.

Definition RedSub_nth Delta sg Ge (h : RedSub Delta sg Ge) k T
           (e : nth_error Ge k = Some T)
  : { T' & ((Apply_ty (length Delta) sg T T' * RedTy Delta T')
            * RedTm Delta T' (nth_default (vNe (nVar 0)) sg k))%type } :=
  snd h k T e.

Lemma RedSub_nil : forall Delta, RedSub Delta [] [].
Proof.
  intro Delta. split; [ reflexivity | ].
  intros k T He. destruct k; cbn in He; discriminate.
Qed.

(* The forgetful map: a reducible substitution is, in particular, a
   well-typed one.  Per entry, keep the substituted type and apply
   [RedTm_wf] to demote the reducible term to a typing. *)
Lemma RedSub_to_wf_ssub : forall Delta sg Ge,
    RedSub Delta sg Ge -> wf_ssub Delta sg Ge.
Proof.
  intros Delta sg Ge [Hlen Hnth]. split; [ exact Hlen | ].
  intros k T He.
  destruct (Hnth k T He) as [T' [[Hap _RTy] RTm]].
  exists T'. split; [ exact Hap | apply RedTm_wf; exact RTm ].
Qed.

(* ===================================================================== *)
(* Canonical forms at base types: invert [LR2] at a fixed type former to    *)
(* read off the predicate (the type-former determines [P]).                 *)
(* ===================================================================== *)

Lemma RedTm_nat_inv : forall Ge v, RedTm Ge (dEl vNat) v -> RedNat Ge v.
Proof.
  intros Ge v [P [HLR Pv]]. inversion HLR; subst; exact Pv.
Qed.

Lemma RedTm_empty_inv : forall Ge v,
    RedTm Ge (dEl vEmpty) v -> RedNeutral Ge (dEl vEmpty) v.
Proof.
  intros Ge v [P [HLR Pv]]. inversion HLR; subst; exact Pv.
Qed.
