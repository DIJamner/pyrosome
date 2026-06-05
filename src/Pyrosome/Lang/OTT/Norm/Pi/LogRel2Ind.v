(* Custom nested induction principle for the TWO-SIDED [LR] (LogRel2.v):
   supplies induction hypotheses for the [PolyRedPackAdequate] (shpAd/posAd)
   sub-derivations, which the auto-generated recursor omits.  Rocq accepts the
   recursion through the adequacy function fields as structural.  This is the
   keystone of Phase 2 (irrelevance / escape / PER laws / transport all induct
   over [LR] through this principle).  Encoding follows CoqHott/logrel-coq and
   mirrors the single-sided [LogRelInd.v]. *)
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

Unset Implicit Arguments.

Section LRInduction.
  Context (lvl : TypeLevel) (rec0 rec1 : RedRel).
  Context (M : forall Ge A B P, @LR lvl rec0 rec1 Ge A B P -> Type).

  Context
    (mnat   : forall Ge, M _ _ _ _ (@LRnat lvl rec0 rec1 Ge))
    (mempty : forall Ge, M _ _ _ _ (@LRempty lvl rec0 rec1 Ge))
    (mne    : forall Ge n m r l (c : NeConv Ge (dU r l) (dU r l) n m),
                M _ _ _ _ (@LRne lvl rec0 rec1 Ge n m r l c))
    (mpiI   : forall Ge FA BA FB BB
                (wA : wf_svalty Ge (dEl (vPiI FA BA)))
                (wB : wf_svalty Ge (dEl (vPiI FB BB))),
                M _ _ _ _ (@LRpiI lvl rec0 rec1 Ge FA BA FB BB wA wB))
    (mpi    : forall Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
                (wpiA : wf_svalty Ge (dEl (vPi FA BA)))
                (wpiB : wf_svalty Ge (dEl (vPi FB BB)))
                (ad : PolyRedPackAdequate (@LR lvl rec0 rec1) PA),
                (forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
                        (afA : Apply_val (length Delta) sg FA FA')
                        (afB : Apply_val (length Delta) sg FB FB'),
                    M _ _ _ _ (shpAd ad ws afA afB)) ->
                (forall Delta sg a b FA' FB' (ws : wf_ssub Delta sg Ge)
                        (afA : Apply_val (length Delta) sg FA FA')
                        (afB : Apply_val (length Delta) sg FB FB')
                        (rab : redTmEq (shpRed PA ws afA afB) a b),
                    M _ _ _ _ (posAd ad ws afA afB rab)) ->
                M _ _ _ _ (@LRpi lvl rec0 rec1 Ge FA BA FB BB PA wpiA wpiB ad))
    (mU0    : forall Ge r l (h : TLlt tl0 lvl) (e : lvl_of l = tl0),
                M _ _ _ _ (@LRU0 lvl rec0 rec1 Ge r l h e))
    (mU1    : forall Ge r l (h : TLlt tl1 lvl) (e : lvl_of l = tl1),
                M _ _ _ _ (@LRU1 lvl rec0 rec1 Ge r l h e)).

  Fixpoint LR_mut Ge A B P (H : @LR lvl rec0 rec1 Ge A B P) {struct H} : M _ _ _ _ H :=
    match H as H0 return M _ _ _ _ H0 with
    | @LRnat _ _ _ Ge0              => mnat Ge0
    | @LRempty _ _ _ Ge0           => mempty Ge0
    | @LRne _ _ _ Ge0 n m r l c    => mne Ge0 n m r l c
    | @LRpiI _ _ _ Ge0 FA BA FB BB wA wB => mpiI Ge0 FA BA FB BB wA wB
    | @LRpi _ _ _ Ge0 FA BA FB BB PA wpiA wpiB ad =>
        mpi Ge0 FA BA FB BB PA wpiA wpiB ad
          (fun Delta sg FA' FB' ws afA afB => LR_mut _ _ _ _ (shpAd ad ws afA afB))
          (fun Delta sg a b FA' FB' ws afA afB rab =>
             LR_mut _ _ _ _ (posAd ad ws afA afB rab))
    | @LRU0 _ _ _ Ge0 r l h e      => mU0 Ge0 r l h e
    | @LRU1 _ _ _ Ge0 r l h e      => mU1 Ge0 r l h e
    end.

End LRInduction.
