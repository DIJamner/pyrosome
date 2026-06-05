Set Implicit Arguments.
Set Universe Polymorphism.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Typing Preservation LogRel2 LogRel2Ind LogRel2Lemmas.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* WIP / PARKED -- NOT BUILDABLE.  Phase-4 PER SYMMETRY of the two-sided     *)
(* [LR].  Parked because it is blocked by a FUNDAMENTAL universe limitation  *)
(* of the monomorphic finite-tower encoding (NOT a mere annotation wrinkle,  *)
(* as an earlier note claimed -- see GAP 2' below), in addition to needing   *)
(* IRRELEVANCE (GAP 1).                                                       *)
(*                                                                          *)
(* The motive [SymCar P := { Q & LR Ge B A Q * (P a b -> Q b a)              *)
(* * (Q a b -> P b a) }] is BIDIRECTIONAL: a reducible-type [A ≡ B] with      *)
(* relation [P] yields a swapped reducible type [B ≡ A] with a relation [Q]   *)
(* plus both transport directions (both needed in Pi: [posRed] of the        *)
(* swapped pack converts a swapped-domain membership BACK to feed the         *)
(* original [posRed]).                                                        *)
(*                                                                          *)
(* === GAP 2' (FUNDAMENTAL universe contradiction) ==================== *)
(*  The carrier's existential [Q] must serve two incompatible roles inside    *)
(*  the SINGLE [LR_mut] motive of [LR_sym_gen]:                               *)
(*   - Pi DOMAIN: [sym_pack] stores the swapped domain relation              *)
(*     [projT1 (Xshp ...)] as the [redTmEq] FIELD of an [LRPack], forcing     *)
(*     [univ(Q) <= LRPack.u0].                                                *)
(*   - LRU: the only [LR Ge (dU r l) (dU r l) Q] is via [LRU], so [Q] is the  *)
(*     universe WITNESS [fun c d => has*has*{P & rec h .. P}], which lives    *)
(*     at [RedRel.u2] (because [rec .. P : Type@{RedRel.u2}]), forcing        *)
(*     [univ(Q) >= RedRel.u2].                                                *)
(*  But [Print Universes Subgraph] gives [LRPack.u0 < RedRel.u2] -- the LR    *)
(*  inductive (in [Type@{RedRel.u2}]) takes a [PolyRedPack] argument (built   *)
(*  from [LRPack], in [Type@{LRPack.u0+1}]), so [LRPack.u0 < RedRel.u2] is    *)
(*  INTRINSIC to the inductive's sizing.  Hence no single [Q]-universe (and   *)
(*  no annotation -- [Type@{RedRel.u1}] below fixes LRU but then breaks the   *)
(*  [sym_pack] storage, and vice versa) can satisfy both.  This is the same   *)
(*  reason a Pi whose DOMAIN is a universe is not representable here.          *)
(*  REAL FIX: level-indexed universes (logrel-coq style) so the lower-level   *)
(*  [rec] returns relations at a STRICTLY SMALLER universe than the current   *)
(*  level's pack field -- a universe-polymorphic refactor of [LogRel2.v].     *)
(*  Naive [Set Universe Polymorphism] does NOT suffice: within one LR         *)
(*  instance [LRPack.u0 < RedRel.u2] still holds.                             *)
(*                                                                          *)
(* === GAP 1 (IRRELEVANCE, the Pi [bwd] admit) ======================== *)
(*  [bwd] needs [redTmEq (posPack PA0 rPA') = redTmEq (posPack PA0 rab)]      *)
(*  where [rPA' = bwd_d (fwd_d rab)] is not definitionally [rab]: the         *)
(*  codomain relation must be INDEPENDENT of the chosen domain-membership     *)
(*  proof (paper Def 7 / Lemma 12).  Prove IRRELEVANCE FIRST (universe-clean: *)
(*  its motive returns equivalence MAPS, no swapped derivation, no pack       *)
(*  storage) -- see [LogRel2Irr.v].                                           *)
(* ===================================================================== *)

Section SymGen.
  Context (lvl : TypeLevel) (rec : forall l', TLlt l' lvl -> RedRel).

  (* Swapped reducibility carrier: the existence of a flipped type with a
     bidirectionally-corresponding relation.  [Q] is annotated to share [P]'s
     universe [u]; when [SymCar] is used as the [LR_mut] motive, [P] is
     instantiated at [LR]'s relation universe (where the [LRU] witness
     relation [{P & rec .. P}] already lives), so [Q] is large enough to hold
     it.  A fresh universe for [Q] (the naive definition) is pinned strictly
     BELOW the motive's output universe and cannot accommodate the [LRU]
     witness -- the GAP-2 universe wrinkle. *)
  Definition SymCar Ge (A B : svalty) (P : sval -> sval -> Type) : Type :=
    { Q : sval -> sval -> Type@{RedRel.u1} &
      ( @LR lvl rec Ge B A Q
      * (forall a b, P a b -> Q b a)
      * (forall a b, Q a b -> P b a) )%type }.

  (* Symmetry of the recursive (lower-tower) relation, threaded as a
     hypothesis and instantiated for the finite tower below. *)
  Definition RecSym : Type :=
    forall l' (h : TLlt l' lvl) Ge A B P,
      @rec l' h Ge A B P ->
      { Q : sval -> sval -> Type &
        ( @rec l' h Ge B A Q
        * (forall a b, P a b -> Q b a)
        * (forall a b, Q a b -> P b a) )%type }.

  Context (HR : RecSym).

  (* ------------------------------------------------------------------- *)
  (* Pi case: build the SWAPPED pack [PolyRedPack Ge FB BB FA BA] out of   *)
  (* the bidirectional symmetry data for the domain ([Xshp]) and codomain  *)
  (* ([Xpos]) packs of the original [PA0].  The domain BACKWARD transport   *)
  (* [snd (projT2 (Xshp ...))] is what lets [posRed'] turn a swapped-domain *)
  (* membership back into an original-domain membership, so the original    *)
  (* [posRed PA0] can be reused.  This is exactly why [SymCar] must be       *)
  (* bidirectional.                                                         *)
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
    : PolyRedPackAdequate (@LR lvl rec) (sym_pack PA0 Xshp Xpos).
  Proof.
    refine {| shpAd := _; posAd := _ |}.
    - intros Delta sg FB' FA' ws afB afA. cbn.
      exact (fst (fst (projT2 (Xshp Delta sg FA' FB' ws afA afB)))).
    - intros Delta sg a b FB' FA' ws afB afA rab. cbn in rab.
      pose (rPA := snd (projT2 (Xshp Delta sg FA' FB' ws afA afB)) a b rab).
      cbn.
      exact (fst (fst (projT2 (Xpos Delta sg b a FA' FB' ws afA afB rPA)))).
  Defined.

  Lemma LR_sym_gen : forall Ge A B P (H : @LR lvl rec Ge A B P),
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
    - (* LRne *)
      match goal with c : NeConv _ _ _ _ |- _ => destruct c as [[wn wm] enm] end.
      subst.
      eexists; repeat split.
      + eapply LRne; repeat split; eassumption.
      + apply RedNeutralEq_sym.
      + apply RedNeutralEq_sym.
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
        intros Delta sg a b FB' FA' gsg fsg ws rn afB afA afsg afsf rab.
        pose (rPA := snd (projT2 (Xshp Delta sg FA' FB' ws afA afB)) a b rab).
        destruct (app Delta sg b a FA' FB' fsg gsg ws rn afA afB afsf afsg rPA)
          as [v [w [[Vf Vg] rvw]]].
        exists w, v; refine ((Vg, Vf), _).
        exact (snd (fst (projT2 (Xpos Delta sg b a FA' FB' ws afA afB rPA))) v w rvw).
      + (* bwd: PiRedTmEq (sym_pack...) f g -> PiRedTmEq PA0 g f -- NEEDS IRRELEVANCE *)
        admit.
    - (* LRU *)
      eexists; split; [ split | ].
      + apply LRU; eassumption.
      + intros c d [[Hc Hd] [Qr Hr]].
        refine (pair (pair Hd Hc) _).
        destruct (HR Hr) as [Qr' [[Hrec' _] _]].
        exact (existT _ Qr' Hrec').
      + intros c d [[Hc Hd] [Qr Hr]].
        refine (pair (pair Hd Hc) _).
        destruct (HR Hr) as [Qr' [[Hrec' _] _]].
        exact (existT _ Qr' Hrec').
  Admitted.

End SymGen.
