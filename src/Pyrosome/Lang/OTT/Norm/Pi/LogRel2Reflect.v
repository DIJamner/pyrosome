(* Phase-3 PROPER: mutual reify / reflect (paper Theorem 11) connecting the
   structural neutral/normal-form conversion [conv_ne]/[conv_nf] (LogRel2Conv.v)
   to REDUCIBLE conversion [RedTmEq] (LogRel2.v).

   - REFLECT: a [conv_ne]-related pair of well-typed neutrals is reducibly
     convertible (at a reducible type); at the UNIVERSE the reflected neutral
     codes form a reducible type-conversion ([LRne]).
   - REIFY:   reducibly-convertible members are structurally convertible normal
     forms ([conv_nf]).

   This file collects the BASE + UNIVERSE cases, which are self-contained (no
   recursion through Pi members).  They are the leaves the eventual mutual Pi
   induction plugs in.  The Pi/PiI cases are the genuine mutual knot (reifying a
   function applies it to a reflected variable -> reflect at the domain;
   reflecting at a Pi recurses into the codomain pack -- well-founded on the [LR]
   derivation) and are developed separately. *)
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
  Domain Apply Typing Preservation LogRel2Conv LogRel2 LogRel2Lemmas.
Import Core.Notations.

(* ===================================================================== *)
(* REIFY (base cases): a reducible member pair reads back to structurally   *)
(* convertible normal forms.  Both are immediate from the base PERs.        *)
(* ===================================================================== *)

Lemma reify_nat : forall Ge a b, RedNatEq Ge a b -> conv_nf a b.
Proof.
  intros Ge a b H; induction H.
  - apply cnf_zero.
  - apply cnf_suc; assumption.
  - apply cnf_ne. destruct n0 as [_ c]. exact c.
Qed.

Lemma reify_neutral : forall Ge T S a b, RedNeutralEq Ge T S a b -> conv_nf a b.
Proof.
  intros Ge T S a b H; destruct H as [n m [_ c]].
  apply cnf_ne; exact c.
Qed.

(* ===================================================================== *)
(* REFLECT (base element types): two [conv_ne]-related neutrals, well-typed *)
(* at the SAME base element type, are reducibly convertible there.  At base *)
(* element types reflection is the identity ([Reflect]'s [refl_Nat]/etc.),  *)
(* so the members are literally [vNe n], [vNe m].                           *)
(* ===================================================================== *)

Lemma reflect_nat : forall Ge n m,
    NeConv Ge (dEl vNat) (dEl vNat) n m ->
    RedTmEq Ge (dEl vNat) (dEl vNat) (vNe n) (vNe m).
Proof.
  intros Ge n m c.
  exists (RedNatEq Ge); split.
  - apply LRnat.
  - apply rne_ne; exact c.
Qed.

Lemma reflect_empty : forall Ge n m,
    NeConv Ge (dEl vEmpty) (dEl vEmpty) n m ->
    RedTmEq Ge (dEl vEmpty) (dEl vEmpty) (vNe n) (vNe m).
Proof.
  intros Ge n m c.
  exists (RedNeutralEq Ge (dEl vEmpty) (dEl vEmpty)); split.
  - apply LRempty.
  - apply rneT; exact c.
Qed.

Lemma reflect_neEl : forall Ge n m p q r l,
    NeConv Ge (dU r l) (dU r l) p q ->
    NeConv Ge (dEl (vNe p)) (dEl (vNe q)) n m ->
    RedTmEq Ge (dEl (vNe p)) (dEl (vNe q)) (vNe n) (vNe m).
Proof.
  intros Ge n m p q r l cpq cnm.
  exists (RedNeutralEq Ge (dEl (vNe p)) (dEl (vNe q))); split.
  - apply LRne with (r:=r) (l:=l); exact cpq.
  - apply rneT; exact cnm.
Qed.

(* ===================================================================== *)
(* REFLECT (universe): two [conv_ne]-related neutral CODES are a reducible   *)
(* type-conversion -- the El-of-them is reducible via [LRne].  This is the   *)
(* substantive base case: it manufactures a NEW reducible type from a        *)
(* neutral.  It lands in [LR0]/[LR1] (the level-0/1 sub-relations of [LR2]), *)
(* selected by [lvl_of l]; either way [LRne] (which has no level guard)      *)
(* supplies the witness.                                                     *)
(* ===================================================================== *)

(* [lvl_of] never returns [tl2] -- it is [tl0] or [tl1]. *)
Lemma lvl_of_cases : forall l, (lvl_of l = tl0) + (lvl_of l = tl1).
Proof.
  intros l; destruct l as [x | n args].
  - left; reflexivity.
  - simpl. destruct (eqb n "L1"); [ right | left ]; reflexivity.
Qed.

(* The El of two [conv_ne]-related neutral CODES is a reducible TYPE-conversion
   (the type-formation companion of [reflect_U] -- its inner witness, repackaged
   at the top level [LR2] via [LRne]).  This is what lets the fundamental lemma
   FORM the reducible type [El n] from a neutral code [n]. *)
Lemma reflect_neEl_ty : forall Ge r l n m,
    NeConv Ge (dU r l) (dU r l) n m ->
    RedTyEq Ge (dEl (vNe n)) (dEl (vNe m)).
Proof.
  intros Ge r l n m c.
  exists (RedNeutralEq Ge (dEl (vNe n)) (dEl (vNe m))).
  apply LRne with (r:=r) (l:=l); exact c.
Qed.

Lemma reflect_U : forall Ge r l n m,
    NeConv Ge (dU r l) (dU r l) n m ->
    RedTmEq Ge (dU r l) (dU r l) (vNe n) (vNe m).
Proof.
  intros Ge r l n m c.
  destruct c as [[wn wm] cnm].
  destruct (lvl_of_cases l) as [E | E].
  - (* lvl_of l = tl0 : use LRU0, witness lives in rec0 = LR0 *)
    eexists; split.
    + apply (@LRU0 tl2 LR0 LR1 Ge r l lt02 E).
    + cbn. split; [ split | ].
      * apply t_ne; exact wn.
      * apply t_ne; exact wm.
      * exists (RedNeutralEq Ge (dEl (vNe n)) (dEl (vNe m))).
        change LR0 with (@LR tl0 LRbot LRbot).
        apply (@LRne tl0 LRbot LRbot Ge n m r l).
        repeat split; assumption.
  - (* lvl_of l = tl1 : use LRU1, witness lives in rec1 = LR1 *)
    eexists; split.
    + apply (@LRU1 tl2 LR0 LR1 Ge r l lt12 E).
    + cbn. split; [ split | ].
      * apply t_ne; exact wn.
      * apply t_ne; exact wm.
      * exists (RedNeutralEq Ge (dEl (vNe n)) (dEl (vNe m))).
        change LR1 with (@LR tl1 LR0 LRbot).
        apply (@LRne tl1 LR0 LRbot Ge n m r l).
        repeat split; assumption.
Qed.
