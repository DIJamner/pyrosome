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
  Domain Apply Typing Preservation LogRel2.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Smart constructors + canonical-forms inversions for the TWO-SIDED       *)
(* top-level relations [RedTyEq]/[RedTmEq] (LogRel2.v).  Mirrors the        *)
(* single-sided [LogRelRed.v]: every former gets a builder that packages    *)
(* the finite-tower level bookkeeping ([LR2] = [LR] at [tl2]) and an        *)
(* inverter that reads the canonical predicate off the type pair.  All      *)
(* non-recursive (introduce / project one [LR] constructor), so the build   *)
(* stays green ahead of Phase 0.                                           *)
(* ===================================================================== *)

(* ---- Universe-level evidence for [LRU] (codes live strictly below). ---- *)

(* Copied verbatim from [LogRelRed.v]: [lvl_of] inspects a head name and only
   ever returns [tl0] or [tl1], so a code's El level is strictly below the top
   of the tower. *)
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
(* [RedTyEq] smart constructors (one per [LR] type former).                *)
(* ===================================================================== *)

Definition redTyEq_nat Ge : RedTyEq Ge (dEl vNat) (dEl vNat) :=
  existT _ (RedNatEq Ge) (@LRnat tl2 LR0 LR1 Ge).

Definition redTyEq_empty Ge : RedTyEq Ge (dEl vEmpty) (dEl vEmpty) :=
  existT _ (RedNeutralEq Ge (dEl vEmpty) (dEl vEmpty)) (@LRempty tl2 LR0 LR1 Ge).

Definition redTyEq_neEl Ge n m r l (c : NeConv Ge (dU r l) (dU r l) n m)
  : RedTyEq Ge (dEl (vNe n)) (dEl (vNe m)) :=
  existT _ (RedNeutralEq Ge (dEl (vNe n)) (dEl (vNe m))) (@LRne tl2 LR0 LR1 Ge n m r l c).

Definition redTyEq_piI Ge FA BA FB BB
           (wA : wf_svalty Ge (dEl (vPiI FA BA)))
           (wB : wf_svalty Ge (dEl (vPiI FB BB)))
  : RedTyEq Ge (dEl (vPiI FA BA)) (dEl (vPiI FB BB)) :=
  existT _ _ (@LRpiI tl2 LR0 LR1 Ge FA BA FB BB wA wB).

Definition redTyEq_pi Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
           (wpiA : wf_svalty Ge (dEl (vPi FA BA)))
           (wpiB : wf_svalty Ge (dEl (vPi FB BB)))
           (ad : PolyRedPackAdequate LR2 PA)
  : RedTyEq Ge (dEl (vPi FA BA)) (dEl (vPi FB BB)) :=
  existT _ (PiRedTmEq PA) (@LRpi tl2 LR0 LR1 Ge FA BA FB BB PA wpiA wpiB ad).

(* [LRU] is now split per source level; pick the constructor matching
   [lvl_of l] ([tl2] is impossible by [lvl_of_ne2]). *)
Definition redTyEq_U Ge r l : RedTyEq Ge (dU r l) (dU r l).
Proof.
  destruct (lvl_of l) eqn:E.
  - exact (existT _ _ (@LRU0 tl2 LR0 LR1 Ge r l lt02 E)).
  - exact (existT _ _ (@LRU1 tl2 LR0 LR1 Ge r l lt12 E)).
  - exfalso; exact (lvl_of_ne2 l E).
Defined.

(* ===================================================================== *)
(* [RedTmEq] smart constructors.                                           *)
(* ===================================================================== *)

Definition redTmEq_nat Ge a b (h : RedNatEq Ge a b)
  : RedTmEq Ge (dEl vNat) (dEl vNat) a b :=
  existT _ (RedNatEq Ge) (@LRnat tl2 LR0 LR1 Ge, h).

Definition redTmEq_empty Ge n m (c : NeConv Ge (dEl vEmpty) (dEl vEmpty) n m)
  : RedTmEq Ge (dEl vEmpty) (dEl vEmpty) (vNe n) (vNe m) :=
  existT _ (RedNeutralEq Ge (dEl vEmpty) (dEl vEmpty)) (@LRempty tl2 LR0 LR1 Ge, rneT c).

Definition redTmEq_neEl Ge n m r l (c : NeConv Ge (dU r l) (dU r l) n m) p q
           (cpq : NeConv Ge (dEl (vNe n)) (dEl (vNe m)) p q)
  : RedTmEq Ge (dEl (vNe n)) (dEl (vNe m)) (vNe p) (vNe q) :=
  existT _ (RedNeutralEq Ge (dEl (vNe n)) (dEl (vNe m)))
         (@LRne tl2 LR0 LR1 Ge n m r l c, rneT cpq).

Definition redTmEq_piI Ge FA BA FB BB
           (wA : wf_svalty Ge (dEl (vPiI FA BA)))
           (wB : wf_svalty Ge (dEl (vPiI FB BB))) f g
           (hf : has_svalty Ge f (dEl (vPiI FA BA)))
           (hg : has_svalty Ge g (dEl (vPiI FB BB)))
  : RedTmEq Ge (dEl (vPiI FA BA)) (dEl (vPiI FB BB)) f g :=
  existT _ _ (@LRpiI tl2 LR0 LR1 Ge FA BA FB BB wA wB, (hf, hg)).

Definition redTmEq_pi Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
           (wpiA : wf_svalty Ge (dEl (vPi FA BA)))
           (wpiB : wf_svalty Ge (dEl (vPi FB BB)))
           (ad : PolyRedPackAdequate LR2 PA) f g
           (h : PiRedTmEq PA f g)
  : RedTmEq Ge (dEl (vPi FA BA)) (dEl (vPi FB BB)) f g :=
  existT _ (PiRedTmEq PA) (@LRpi tl2 LR0 LR1 Ge FA BA FB BB PA wpiA wpiB ad, h).

(* ===================================================================== *)
(* Conversions between the two reducible carriers.                         *)
(* ===================================================================== *)

(* A reducible term-conversion yields a reducible type-conversion. *)
Definition RedTmEq_RedTyEq Ge A B a b (h : RedTmEq Ge A B a b) : RedTyEq Ge A B :=
  existT _ (projT1 h) (fst (projT2 h)).

(* Pack a pair related *at the type pair's canonical predicate* into [RedTmEq]. *)
Definition RedTmOfEq_RedTmEq Ge A B (RT : RedTyEq Ge A B) a b
           (p : RedTmOfEq RT a b)
  : RedTmEq Ge A B a b :=
  existT _ (projT1 RT) (projT2 RT, p).

(* ===================================================================== *)
(* Canonical forms at base types: invert [LR2] at a fixed type former to    *)
(* read off the predicate (the type-former pair determines [P]).            *)
(* ===================================================================== *)

Lemma RedTmEq_nat_inv : forall Ge a b,
    RedTmEq Ge (dEl vNat) (dEl vNat) a b -> RedNatEq Ge a b.
Proof. intros Ge a b [P [HLR Pab]]. inversion HLR; subst; exact Pab. Qed.

Lemma RedTmEq_empty_inv : forall Ge a b,
    RedTmEq Ge (dEl vEmpty) (dEl vEmpty) a b -> RedNeutralEq Ge (dEl vEmpty) (dEl vEmpty) a b.
Proof. intros Ge a b [P [HLR Pab]]. inversion HLR; subst; exact Pab. Qed.
