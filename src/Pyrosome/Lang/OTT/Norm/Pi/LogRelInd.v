(* Custom nested induction principle for [LR]: supplies induction hypotheses
   for the [PolyRedPackAdequate] (shpAd/posAd) sub-derivations, which the
   auto-generated recursor omits.  Rocq accepts the recursion through the
   adequacy function fields as structural.  Gateway for reflect_red /
   Apply_total_red (Milestone 1).  Encoding follows CoqHott/logrel-coq.  *)
Set Implicit Arguments.
Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Typing Preservation LogRel.
Import Core.Notations.

Notation term := (@term string).

Unset Implicit Arguments.

Section LRInduction.
  Context (lvl : TypeLevel) (rec : forall l', TLlt l' lvl -> RedRel).
  Context (M : forall Ge T P, @LR lvl rec Ge T P -> Type).

  Context
    (mnat   : forall Ge, M _ _ _ (@LRnat lvl rec Ge))
    (mempty : forall Ge, M _ _ _ (@LRempty lvl rec Ge))
    (mne    : forall Ge n r l (w : wf_neutral Ge n (dU r l)),
                M _ _ _ (@LRne lvl rec Ge n r l w))
    (mpiI   : forall Ge F B (w : wf_svalty Ge (dEl (vPiI F B))),
                M _ _ _ (@LRpiI lvl rec Ge F B w))
    (mpi    : forall Ge F B (PA : PolyRedPack Ge F B)
                (wpi : wf_svalty Ge (dEl (vPi F B)))
                (ad : PolyRedPackAdequate (@LR lvl rec) PA),
                (forall Delta sg F' (ws : wf_ssub Delta sg Ge)
                        (af : Apply_val (length Delta) sg F F'),
                    M _ _ _ (shpAd ad ws af)) ->
                (forall Delta sg a F' Bres (ws : wf_ssub Delta sg Ge)
                        (af : Apply_val (length Delta) sg F F')
                        (ra : redTm (shpRed PA ws af) a)
                        (hB : Apply_val (length Delta) (a :: sg) B Bres),
                    M _ _ _ (posAd ad ws af ra hB)) ->
                M _ _ _ (@LRpi lvl rec Ge F B PA wpi ad))
    (mU     : forall Ge r l (h : TLlt (lvl_of l) lvl),
                M _ _ _ (@LRU lvl rec Ge r l h)).

  Fixpoint LR_mut Ge T P (H : @LR lvl rec Ge T P) {struct H} : M _ _ _ H :=
    match H as H0 return M _ _ _ H0 with
    | @LRnat _ _ Ge0          => mnat Ge0
    | @LRempty _ _ Ge0        => mempty Ge0
    | @LRne _ _ Ge0 n r l w   => mne Ge0 n r l w
    | @LRpiI _ _ Ge0 F B w    => mpiI Ge0 F B w
    | @LRpi _ _ Ge0 F B PA wpi ad =>
        mpi Ge0 F B PA wpi ad
          (fun Delta sg F' ws af => LR_mut _ _ _ (shpAd ad ws af))
          (fun Delta sg a F' Bres ws af ra hB =>
             LR_mut _ _ _ (posAd ad ws af ra hB))
    | @LRU _ _ Ge0 r l h      => mU Ge0 r l h
    end.

End LRInduction.
