(* Phase-2 IRRELEVANCE for the two-sided [LR] (LogRel2.v): two reducibility
   derivations of the SAME type pair [A ≡ B] carry EQUIVALENT term-conversion
   relations.  This is the universe-CLEAN keystone of Phase 2 (the motive
   returns equivalence MAPS, with no swapped [LR] derivation and no storage of
   a relation back into an [LRPack] -- so it sidesteps the fundamental
   universe contradiction that blocks the symmetry carrier, see
   WIP/LogRel2Sym.v GAP 2').  Irrelevance discharges the [bwd] admit of PER
   symmetry (the codomain relation is independent of the chosen domain proof)
   and underpins transport.  Proof shape follows CoqHott/logrel-coq's
   [LRTmRedConv]/irrelevance. *)
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
  Domain Apply Typing Preservation LogRel2 LogRel2Ind LogRel2Lemmas.
Import Core.Notations.

Notation term := (@term string).

(* Proof irrelevance for the finite level order [TLlt] (each index pair has at
   most one constructor).  Axiom-free (convoy pattern, no K / Eqdep).  Needed
   in the [LRU] case so that [rec h] and [rec h0] agree for two proofs h, h0 of
   [TLlt (lvl_of l) lvl]. *)
Lemma TLlt_pirr : forall (l1 l2 : TypeLevel) (p q : TLlt l1 l2), p = q.
Proof.
  intros l1 l2 p. destruct p; intro q.
  - refine (match q as q0 in TLlt x y
              return (match x as x0, y as y0 return TLlt x0 y0 -> Prop with
                      | tl0, tl1 => fun q1 => lt01 = q1
                      | _, _ => fun _ => True end) q0 with
            | lt01 => eq_refl | lt12 => I | lt02 => I end).
  - refine (match q as q0 in TLlt x y
              return (match x as x0, y as y0 return TLlt x0 y0 -> Prop with
                      | tl1, tl2 => fun q1 => lt12 = q1
                      | _, _ => fun _ => True end) q0 with
            | lt01 => I | lt12 => eq_refl | lt02 => I end).
  - refine (match q as q0 in TLlt x y
              return (match x as x0, y as y0 return TLlt x0 y0 -> Prop with
                      | tl0, tl2 => fun q1 => lt02 = q1
                      | _, _ => fun _ => True end) q0 with
            | lt01 => I | lt12 => I | lt02 => eq_refl end).
Qed.

Section Irrelevance.
  Context (lvl : TypeLevel) (rec0 rec1 : RedRel).

  (* Bidirectional irrelevance carrier: for a derivation [H : LR Ge A B P], any
     OTHER derivation [H' : LR Ge A B P'] at the SAME type pair has a relation
     [P'] equivalent to [P].  The bidirection is essential: the Pi case must
     convert a swapped-pack domain membership [PA' -> PA] (the [snd] map). *)
  Definition IrrCar Ge (A B : svalty) (P : sval -> sval -> Type) : Type :=
    forall P' (H' : @LR lvl rec0 rec1 Ge A B P'),
      ( (forall a b, P a b -> P' a b)
      * (forall a b, P' a b -> P a b) )%type.

  Lemma LR_irrelevant_gen : forall Ge A B P (H : @LR lvl rec0 rec1 Ge A B P),
      IrrCar Ge A B P.
  Proof.
    intros Ge A B P H.
    induction H using LR_mut; unfold IrrCar; intros P' H'.
    - (* LRnat *)   inversion H'; subst; split; intros a b Hab; exact Hab.
    - (* LRempty *) inversion H'; subst; split; intros a b Hab; exact Hab.
    - (* LRne *)    inversion H'; subst; split; intros a b Hab; exact Hab.
    - (* LRpiI *)   inversion H'; subst; split; intros a b Hab; exact Hab.
    - (* LRpi -- the boss.  [X]/[X0] are the bidirectional domain/codomain IHs
         for [PA]; both equivalence directions reuse them (the bidirection of
         [IrrCar] is what makes the domain conversion [PA0 -> PA] available).
         [Apply_val_det] aligns the codomain TYPES [posTyA PA rab = posTyA PA0
         rab0]; the relation transport then goes through [X0].  Note the type
         transport is done in the GOAL of [Had0'] (where the target relation
         [redTmEq (posPack PA0 rab0)] does not mention [posTyA PA rab]), NOT in
         a hypothesis -- rewriting in [posAd X1 ..] directly is blocked by the
         dependency of [posPack PA0 rab0] on [posTyA PA0 rab0]. *)
      inversion H'; subst.
      split; intros f g Hfg; destruct Hfg as [[Hf Hg] app]; cbn in Hf, Hg.
      + (* PiRedTmEq PA -> PiRedTmEq PA0 *)
        refine ((Hf, Hg), _).
        intros Delta sg a0 b0 FA' FB' fsg gsg ws rn afA afB afsf afsg rab0.
        pose (rab := snd (X Delta sg FA' FB' ws afA afB _ (shpAd X1 ws afA afB))
                       a0 b0 rab0).
        destruct (app Delta sg a0 b0 FA' FB' fsg gsg ws rn afA afB afsf afsg rab)
          as [v [w [[Vf Vg] rvw]]].
        assert (EA : posTyA PA rab = posTyA PA0 rab0)
          by (eapply Apply_val_det; [exact (posAppA PA rab) | exact (posAppA PA0 rab0)]).
        assert (EB : posTyB PA rab = posTyB PA0 rab0)
          by (eapply Apply_val_det; [exact (posAppB PA rab) | exact (posAppB PA0 rab0)]).
        assert (Had0' : @LR lvl rec0 rec1 Delta (dEl (posTyA PA rab)) (dEl (posTyB PA rab))
                          (redTmEq (posPack PA0 rab0)))
          by (rewrite EA, EB; exact (posAd X1 ws afA afB rab0)).
        exists v, w; refine ((Vf, Vg), _).
        exact (fst (X0 Delta sg a0 b0 FA' FB' ws afA afB rab _ Had0') v w rvw).
      + (* PiRedTmEq PA0 -> PiRedTmEq PA *)
        refine ((Hf, Hg), _).
        intros Delta sg a0 b0 FA' FB' fsg gsg ws rn afA afB afsf afsg rab.
        pose (rab0 := fst (X Delta sg FA' FB' ws afA afB _ (shpAd X1 ws afA afB))
                        a0 b0 rab).
        destruct (app Delta sg a0 b0 FA' FB' fsg gsg ws rn afA afB afsf afsg rab0)
          as [v [w [[Vf Vg] rvw]]].
        assert (EA : posTyA PA rab = posTyA PA0 rab0)
          by (eapply Apply_val_det; [exact (posAppA PA rab) | exact (posAppA PA0 rab0)]).
        assert (EB : posTyB PA rab = posTyB PA0 rab0)
          by (eapply Apply_val_det; [exact (posAppB PA rab) | exact (posAppB PA0 rab0)]).
        assert (Had0' : @LR lvl rec0 rec1 Delta (dEl (posTyA PA rab)) (dEl (posTyB PA rab))
                          (redTmEq (posPack PA0 rab0)))
          by (rewrite EA, EB; exact (posAd X1 ws afA afB rab0)).
        exists v, w; refine ((Vf, Vg), _).
        exact (snd (X0 Delta sg a0 b0 FA' FB' ws afA afB rab _ Had0') v w rvw).
    - (* LRU0.  The split relations no longer depend on the [TLlt] proof, so
         the matching sub-case is reflexive; the off-diagonal [LRU1] sub-case is
         impossible ([lvl_of l] cannot be both [tl0] and [tl1]). *)
      inversion H'; subst.
      + split; intros a b Hab; exact Hab.
      + congruence.
    - (* LRU1 (symmetric). *)
      inversion H'; subst.
      + congruence.
      + split; intros a b Hab; exact Hab.
  Qed.

End Irrelevance.

(* Finite-tower (top-level) irrelevance: any two [LR2] derivations of the same
   type pair carry equivalent relations. *)
Lemma LR2_irrelevant : forall Ge A B P (H : LR2 Ge A B P) P' (H' : LR2 Ge A B P'),
    ( (forall a b, P a b -> P' a b)
    * (forall a b, P' a b -> P a b) )%type.
Proof. intros Ge A B P H P' H'. exact (LR_irrelevant_gen H H'). Qed.

(* Paper Def 7 (irrelevance) at the top level: reducible term-conversion is
   INDEPENDENT of the chosen [RedTyEq] witness for the type pair.  This is the
   form consumed by transport and by the [bwd] direction of PER symmetry (the
   codomain relation does not depend on the domain-membership proof). *)
Lemma RedTmEq_irr : forall Ge A B a b (RT RT' : RedTyEq Ge A B),
    RedTmOfEq RT a b -> RedTmOfEq RT' a b.
Proof.
  intros Ge A B a b [P H] [P' H'] Hab.
  exact (fst (LR2_irrelevant H H') a b Hab).
Qed.
