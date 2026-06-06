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
  Domain Apply Typing Preservation LogRel2Conv LogRel2 LogRel2Ind LogRel2Lemmas LogRel2Irr.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Phase-4 PER SYMMETRY of the two-sided [LR], now UNBLOCKED by the         *)
(* universe-polymorphic 3-level unfolded encoding (UNIVERSE_FIX_PLAN Step    *)
(* 1B): the carrier's swapped relation [Q] lives at the motive's relation    *)
(* universe [i], which (ladder [j0 <= i], [j1 <= i], [i < j]) is large       *)
(* enough to hold the [LRU0]/[LRU1] witnesses AND small enough to be stored  *)
(* into an [LRPack] field -- the exact contradiction that blocked the        *)
(* monomorphic encoding (former GAP 2').  The Pi backward transport (former  *)
(* GAP 1) is discharged with IRRELEVANCE ([LR_irrelevant_gen]).             *)
(*                                                                          *)
(* [SymCar P := { Q & LR Ge B A Q * (P a b -> Q b a) * (Q a b -> P b a) }]   *)
(* is BIDIRECTIONAL: in Pi, [posRed] of the swapped pack converts a          *)
(* swapped-domain membership BACK to feed the original [posRed].             *)
(* ===================================================================== *)

Section SymGen.
  Context (lvl : TypeLevel) (rec0 rec1 : RedRel).

  (* Swapped reducibility carrier.  [Q] is left at an inferred (polymorphic)
     universe; when [SymCar] is used as the [LR_mut] motive it is unified with
     [LR]'s relation universe [i], where (new ladder) the [LRU0]/[LRU1]
     witnesses already live and into which an [LRPack] field can store it. *)
  Definition SymCar Ge (A B : svalty) (P : sval -> sval -> Type) : Type :=
    { Q : sval -> sval -> Type &
      ( @LR lvl rec0 rec1 Ge B A Q
      * (forall a b, P a b -> Q b a)
      * (forall a b, Q a b -> P b a) )%type }.

  (* Symmetry of the two lower-tower relations, threaded as a hypothesis and
     instantiated for the finite tower below. *)
  Definition RecSym1 (rec : RedRel) : Type :=
    forall Ge A B P, rec Ge A B P ->
      { Q : sval -> sval -> Type &
        ( rec Ge B A Q
        * (forall a b, P a b -> Q b a)
        * (forall a b, Q a b -> P b a) )%type }.

  Context (HR0 : RecSym1 rec0) (HR1 : RecSym1 rec1).

  (* ------------------------------------------------------------------- *)
  (* Pi case: build the SWAPPED pack [PolyRedPack Ge FB BB FA BA] out of the
     bidirectional symmetry data for the domain ([Xshp]) and codomain ([Xpos])
     packs of the original [PA0].  The domain BACKWARD transport lets [posRed']
     turn a swapped-domain membership back into an original-domain membership,
     so the original [posRed PA0] can be reused -- this is why [SymCar] must be
     bidirectional. *)
  Definition sym_pack Ge FA BA FB BB (PA0 : PolyRedPack Ge FA BA FB BB)
    (Xshp : forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
              (afA : Apply_val (length Delta) sg FA FA')
              (afB : Apply_val (length Delta) sg FB FB'),
              SymCar Delta (dEl FA') (dEl FB') (redTmEq (shpRed PA0 ws afA afB)))
    (Xpos : forall Delta sg a b FA' FB' (ws : wf_ssub Delta sg Ge)
              (afA : Apply_val (length Delta) sg FA FA')
              (afB : Apply_val (length Delta) sg FB FB')
              (rab : redTmEq (shpRed PA0 ws afA afB) a b),
              SymCar Delta (dEl (posTyA PA0 rab)) (dEl (posTyB PA0 rab))
                (redTmEq (posPack PA0 rab)))
    : PolyRedPack Ge FB BB FA BA.
  Proof.
    refine {| shpRed := fun Delta sg FB' FA' ws afB afA =>
                {| redTmEq := projT1 (Xshp Delta sg FA' FB' ws afA afB) |}
            ; posRed := _ |}.
    intros Delta sg a b FB' FA' ws afB afA rab. cbn in rab.
    pose (rPA := snd (projT2 (Xshp Delta sg FA' FB' ws afA afB)) a b rab).
    refine (existT _ (posTyB PA0 rPA)
              (existT _ (posTyA PA0 rPA)
                ( (posAppB PA0 rPA, posAppA PA0 rPA) , _ ))).
    exact {| redTmEq := projT1 (Xpos Delta sg b a FA' FB' ws afA afB rPA) |}.
  Defined.

  Definition sym_adeq Ge FA BA FB BB (PA0 : PolyRedPack Ge FA BA FB BB)
    (Xshp : forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
              (afA : Apply_val (length Delta) sg FA FA')
              (afB : Apply_val (length Delta) sg FB FB'),
              SymCar Delta (dEl FA') (dEl FB') (redTmEq (shpRed PA0 ws afA afB)))
    (Xpos : forall Delta sg a b FA' FB' (ws : wf_ssub Delta sg Ge)
              (afA : Apply_val (length Delta) sg FA FA')
              (afB : Apply_val (length Delta) sg FB FB')
              (rab : redTmEq (shpRed PA0 ws afA afB) a b),
              SymCar Delta (dEl (posTyA PA0 rab)) (dEl (posTyB PA0 rab))
                (redTmEq (posPack PA0 rab)))
    : PolyRedPackAdequate (@LR lvl rec0 rec1) (sym_pack PA0 Xshp Xpos).
  Proof.
    refine {| shpAd := _; posAd := _ |}.
    - intros Delta sg FB' FA' ws afB afA. cbn.
      exact (fst (fst (projT2 (Xshp Delta sg FA' FB' ws afA afB)))).
    - intros Delta sg a b FB' FA' ws afB afA rab. cbn in rab.
      pose (rPA := snd (projT2 (Xshp Delta sg FA' FB' ws afA afB)) a b rab).
      cbn.
      exact (fst (fst (projT2 (Xpos Delta sg b a FA' FB' ws afA afB rPA)))).
  Defined.

  Lemma LR_sym_gen : forall Ge A B P (H : @LR lvl rec0 rec1 Ge A B P),
      SymCar Ge A B P.
  Proof.
    intros Ge A B P H.
    induction H using LR_mut.
    - (* LRnat *)
      eexists; repeat split;
        [ apply LRnat | apply RedNatEq_sym | apply RedNatEq_sym ].
    - (* LRempty *)
      eexists; repeat split;
        [ apply LRempty | apply RedNeutralEq_sym | apply RedNeutralEq_sym ].
    - (* LRne -- SINGLE-typed neutral relation.  The swapped node is
         [(dEl (vNe m), dEl (vNe n))] with relation [RedNeutralEq Ge (dEl (vNe
         m))] (left = the swapped left type), so the fwd/bwd maps must RE-TYPE the
         members across the convertible codes [vNe n ∼ vNe m] -- exactly the
         paper's [WfTmConv]-bridge, here [n_conv] + [conv_ne n m] (the [LRne]
         premise [cnm]).  This is what symmetry costs once neutrals are
         single-typed (the old two-typed encoding hid it inside the type pair). *)
      match goal with c : NeConv _ _ _ _ |- _ => destruct c as [[wn wm] cnm] end.
      exists (RedNeutralEq Ge (dEl (vNe m))).
      split; [ split | ].
      + eapply LRne; repeat split; [ exact wm | exact wn | exact (conv_ne_sym cnm) ].
      + intros a b H. destruct H as [p q [[wp wq] cpq]]. apply rneT. repeat split.
        * eapply n_conv; [ exact wq | apply cnf_ne; exact cnm ].
        * eapply n_conv; [ exact wp | apply cnf_ne; exact cnm ].
        * exact (conv_ne_sym cpq).
      + intros a b H. destruct H as [p q [[wp wq] cpq]]. apply rneT. repeat split.
        * eapply n_conv; [ exact wq | apply cnf_ne; exact (conv_ne_sym cnm) ].
        * eapply n_conv; [ exact wp | apply cnf_ne; exact (conv_ne_sym cnm) ].
        * exact (conv_ne_sym cpq).
    - (* LRpiI *)
      eexists; split; [ split | ].
      + apply LRpiI; assumption.
      + intros x y H'; destruct H' as [Ha Hb]; exact (Hb, Ha).
      + intros x y H'; destruct H' as [Ha Hb]; exact (Hb, Ha).
    - (* LRpi -- the boss *)
      rename PA into PA0. rename X into Xshp. rename X0 into Xpos.
      exists (PiRedTmEq (sym_pack PA0 Xshp Xpos)).
      split; [ split | ].
      + (* swapped LR derivation *)
        apply (LRpi (PA := sym_pack PA0 Xshp Xpos));
          [ exact wpiB | exact wpiA | exact (sym_adeq PA0 Xshp Xpos) ].
      + (* fwd: PiRedTmEq PA0 f g -> PiRedTmEq (sym_pack...) g f *)
        intros f g [[Hf Hg] app].
        refine ((Hg, Hf), _).
        intros Delta sg a b FB' FA' BB' BA' gsg fsg ws rn afB afA afBB afBA afsg afsf rab.
        pose (rPA := snd (projT2 (Xshp Delta sg FA' FB' ws afA afB)) a b rab).
        destruct (app Delta sg b a FA' FB' BA' BB' fsg gsg ws rn afA afB afBA afBB afsf afsg rPA)
          as [v [w [[Vf Vg] rvw]]].
        exists w, v; refine ((Vg, Vf), _).
        exact (snd (fst (projT2 (Xpos Delta sg b a FA' FB' ws afA afB rPA))) v w rvw).
      + (* bwd: PiRedTmEq (sym_pack...) f g -> PiRedTmEq PA0 g f.  Mirror of fwd,
           but the codomain pack is reached through a DOUBLE domain transport
           [rPA0 = bwd (fwd rab)] that is not definitionally [rab]; IRRELEVANCE
           ([LR_irrelevant_gen]) reconciles the two codomain relations, after
           [Apply_val_det] aligns the codomain types (same technique as
           LogRel2Irr's LRpi case: transport in the GOAL, not the hypothesis). *)
        intros f g [[Hf Hg] app].
        refine ((Hg, Hf), _).
        intros Delta sg a b FA' FB' BA' BB' Gsg Fsg ws rn afA afB afBA afBB afsG afsF rab.
        pose (rab' := snd (fst (projT2 (Xshp Delta sg FA' FB' ws afA afB))) a b rab).
        pose (rPA0 := snd (projT2 (Xshp Delta sg FA' FB' ws afA afB)) b a rab').
        destruct (app Delta sg b a FB' FA' BB' BA' Fsg Gsg ws rn afB afA afBB afBA afsF afsG rab')
          as [v [w [[Vfv Vgw] rvw]]].
        exists w, v; refine ((Vgw, Vfv), _).
        pose proof (snd (projT2 (Xpos Delta sg a b FA' FB' ws afA afB rPA0)) v w rvw) as rwv.
        assert (EA : posTyA PA0 rPA0 = posTyA PA0 rab)
          by (eapply Apply_val_det; [ exact (posAppA PA0 rPA0) | exact (posAppA PA0 rab) ]).
        assert (EB : posTyB PA0 rPA0 = posTyB PA0 rab)
          by (eapply Apply_val_det; [ exact (posAppB PA0 rPA0) | exact (posAppB PA0 rab) ]).
        assert (Had : @LR lvl rec0 rec1 Delta (dEl (posTyA PA0 rab)) (dEl (posTyB PA0 rab))
                        (redTmEq (posPack PA0 rPA0)))
          by (rewrite <- EA, <- EB; exact (posAd ad ws afA afB rPA0)).
        exact (fst (LR_irrelevant_gen Had (posAd ad ws afA afB rab)) w v rwv).
    - (* LRU0 *)
      eexists; split; [ split | ].
      + eapply LRU0; eassumption.
      + intros c d [[Hc Hd] [Qr Hr]].
        refine (pair (pair Hd Hc) _).
        destruct (HR0 Hr) as [Qr' [[Hrec' _] _]].
        exact (existT _ Qr' Hrec').
      + intros c d [[Hc Hd] [Qr Hr]].
        refine (pair (pair Hd Hc) _).
        destruct (HR0 Hr) as [Qr' [[Hrec' _] _]].
        exact (existT _ Qr' Hrec').
    - (* LRU1 *)
      eexists; split; [ split | ].
      + eapply LRU1; eassumption.
      + intros c d [[Hc Hd] [Qr Hr]].
        refine (pair (pair Hd Hc) _).
        destruct (HR1 Hr) as [Qr' [[Hrec' _] _]].
        exact (existT _ Qr' Hrec').
      + intros c d [[Hc Hd] [Qr Hr]].
        refine (pair (pair Hd Hc) _).
        destruct (HR1 Hr) as [Qr' [[Hrec' _] _]].
        exact (existT _ Qr' Hrec').
  Qed.

End SymGen.

(* ===================================================================== *)
(* Tower instantiation: discharge [RecSym1] up the finite tower, then the   *)
(* top-level PER-symmetry of [RedTyEq] / [RedTmEq].                          *)
(* ===================================================================== *)

(* The dummy bottom relation is symmetric vacuously ([LRbot _ _ _ _ = False]). *)
Definition LRbot_sym : RecSym1 LRbot.
Proof. intros Ge A B P H; destruct H. Qed.

Definition LR0_sym : RecSym1 LR0.
Proof. intros Ge A B P H. exact (LR_sym_gen LRbot_sym LRbot_sym H). Qed.

Definition LR1_sym : RecSym1 LR1.
Proof. intros Ge A B P H. exact (LR_sym_gen LR0_sym LRbot_sym H). Qed.

(* PER SYMMETRY of the top-level type-conversion relation. *)
Lemma RedTyEq_sym : forall Ge A B, RedTyEq Ge A B -> RedTyEq Ge B A.
Proof.
  intros Ge A B [P H].
  destruct (LR_sym_gen LR0_sym LR1_sym H) as [Q [[HQ _] _]].
  exact (existT _ Q HQ).
Qed.

(* PER SYMMETRY of the top-level term-conversion relation. *)
Lemma RedTmEq_sym : forall Ge A B a b, RedTmEq Ge A B a b -> RedTmEq Ge B A b a.
Proof.
  intros Ge A B a b [P [H Pab]].
  destruct (LR_sym_gen LR0_sym LR1_sym H) as [Q [[HQ fwd] _]].
  exact (existT _ Q (HQ, fwd a b Pab)).
Qed.
