(* Custom nested induction principle for the TWO-SIDED [LR] (LogRel2.v):
   supplies induction hypotheses for the [PolyRedPackAdequate] (shpAd/posAd)
   sub-derivations, which the auto-generated recursor omits.  Rocq accepts the
   recursion through the adequacy function fields as structural.  This is the
   keystone of Phase 2 (irrelevance / escape / PER laws / transport all induct
   over [LR] through this principle).  Encoding follows CoqHott/logrel-coq and
   mirrors the single-sided [LogRelInd.v]. *)
Set Implicit Arguments.

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
  Context (lvl : TypeLevel) (rec : forall l', TLlt l' lvl -> RedRel).
  Context (M : forall Ge A B P, @LR lvl rec Ge A B P -> Type).

  Context
    (mnat   : forall Ge, M _ _ _ _ (@LRnat lvl rec Ge))
    (mempty : forall Ge, M _ _ _ _ (@LRempty lvl rec Ge))
    (mne    : forall Ge n m r l (c : NeConv Ge (dU r l) n m),
                M _ _ _ _ (@LRne lvl rec Ge n m r l c))
    (mpiI   : forall Ge FA BA FB BB
                (wA : wf_svalty Ge (dEl (vPiI FA BA)))
                (wB : wf_svalty Ge (dEl (vPiI FB BB))),
                M _ _ _ _ (@LRpiI lvl rec Ge FA BA FB BB wA wB))
    (mpi    : forall Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
                (wpiA : wf_svalty Ge (dEl (vPi FA BA)))
                (wpiB : wf_svalty Ge (dEl (vPi FB BB)))
                (ad : PolyRedPackAdequate (@LR lvl rec) PA),
                (forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
                        (afA : Apply_val (length Delta) sg FA FA')
                        (afB : Apply_val (length Delta) sg FB FB'),
                    M _ _ _ _ (shpAd ad ws afA afB)) ->
                (forall Delta sg a b FA' FB' (ws : wf_ssub Delta sg Ge)
                        (afA : Apply_val (length Delta) sg FA FA')
                        (afB : Apply_val (length Delta) sg FB FB')
                        (rab : redTmEq (shpRed PA ws afA afB) a b),
                    M _ _ _ _ (posAd ad ws afA afB rab)) ->
                M _ _ _ _ (@LRpi lvl rec Ge FA BA FB BB PA wpiA wpiB ad))
    (mU     : forall Ge r l (h : TLlt (lvl_of l) lvl),
                M _ _ _ _ (@LRU lvl rec Ge r l h)).

  Fixpoint LR_mut Ge A B P (H : @LR lvl rec Ge A B P) {struct H} : M _ _ _ _ H :=
    match H as H0 return M _ _ _ _ H0 with
    | @LRnat _ _ Ge0              => mnat Ge0
    | @LRempty _ _ Ge0            => mempty Ge0
    | @LRne _ _ Ge0 n m r l c     => mne Ge0 n m r l c
    | @LRpiI _ _ Ge0 FA BA FB BB wA wB => mpiI Ge0 FA BA FB BB wA wB
    | @LRpi _ _ Ge0 FA BA FB BB PA wpiA wpiB ad =>
        mpi Ge0 FA BA FB BB PA wpiA wpiB ad
          (fun Delta sg FA' FB' ws afA afB => LR_mut _ _ _ _ (shpAd ad ws afA afB))
          (fun Delta sg a b FA' FB' ws afA afB rab =>
             LR_mut _ _ _ _ (posAd ad ws afA afB rab))
    | @LRU _ _ Ge0 r l h          => mU Ge0 r l h
    end.

End LRInduction.
