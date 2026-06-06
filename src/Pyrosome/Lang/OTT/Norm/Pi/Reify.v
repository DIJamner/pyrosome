Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply Reflect.
Import Core.Notations.

(* ===================================================================== *)
(* Type-directed eta-long READ-BACK (reify), the dual of [Reflect].        *)
(*                                                                         *)
(*   ReifyTy m c c'   : a type CODE [c] reads back to [c'] (structural;    *)
(*                      level-independent, hence no [dU] level reps).      *)
(*   Reify   m T v nf : at context length [m] and semantic type [T], the   *)
(*                      value [v] reads back to the eta-long normal form   *)
(*                      [nf].                                              *)
(*   ReifyNe m n n'   : a neutral [n] reads back to [n'] (head + type      *)
(*                      annotations + value-arguments reified).            *)
(*                                                                         *)
(* The ONLY place read-back is not structural is a relevant Pi type        *)
(* [dEl (vPi F B)]: there the value [f] (whether an eta-SHORT bare neutral *)
(* or an eta-long lambda) is ETA-EXPANDED to [vLam body], where [body] is  *)
(* the read-back of [f] applied to the reflected bound variable.  This is  *)
(* exactly what makes reify-tm hold at function types: two eta-equal but   *)
(* structurally-distinct members read back to the SAME normal form, so     *)
(* their normal forms are [conv_nf]-related even though the raw members    *)
(* are not.  (cf. memory ott-r2-hereditary-eta: the [is_lam] member gate   *)
(* alone does NOT make reify-tm hold -- a member body can be eta-short at  *)
(* a nested function codomain, so a structural readback is required.)      *)
(* ===================================================================== *)

Inductive ReifyTy : nat -> sval -> sval -> Type :=
| rty_Nat   : forall m, ReifyTy m vNat vNat
| rty_Empty : forall m, ReifyTy m vEmpty vEmpty
| rty_Pi    : forall m F B F' B',
    ReifyTy m F F' -> ReifyTy (S m) B B' -> ReifyTy m (vPi F B) (vPi F' B')
| rty_PiI   : forall m F B F' B',
    ReifyTy m F F' -> ReifyTy (S m) B B' -> ReifyTy m (vPiI F B) (vPiI F' B')
| rty_ne    : forall m n n', ReifyNe m n n' -> ReifyTy m (vNe n) (vNe n')
with Reify : nat -> svalty -> sval -> sval -> Type :=
(* type codes at a universe: structural read-back *)
| rfy_code  : forall m r l c c', ReifyTy m c c' -> Reify m (dU r l) c c'
(* values at an El type *)
| rfy_zero  : forall m, Reify m (dEl vNat) vZero vZero
| rfy_suc   : forall m v v', Reify m (dEl vNat) v v' ->
    Reify m (dEl vNat) (vSuc v) (vSuc v')
| rfy_neNat   : forall m n n', ReifyNe m n n' -> Reify m (dEl vNat)   (vNe n) (vNe n')
| rfy_neEmpty : forall m n n', ReifyNe m n n' -> Reify m (dEl vEmpty) (vNe n) (vNe n')
| rfy_neEl    : forall m c n n', ReifyNe m n n' -> Reify m (dEl (vNe c)) (vNe n) (vNe n')
(* proof-irrelevant Pi: neutral stays neutral (eta-long reify deferred, Ph6) *)
| rfy_PiI   : forall m F B n n', ReifyNe m n n' ->
    Reify m (dEl (vPiI F B)) (vNe n) (vNe n')
| rfy_LamI  : forall m F B b b', Reify (S m) (dEl B) b b' ->
    Reify m (dEl (vPiI F B)) (vLamI b) (vLamI b')
(* the eta case: relevant Pi *)
| rfy_Pi    : forall m F B f ARG B' fa body,
    Reflect (S m) (dEl (shift_val 0 1 F)) (nVar 0) ARG ->
    Apply_val (S m) (ARG :: wkn_list m) B B' ->
    Vapp (S m) (shift_val 0 1 F) (shift_val 1 1 B) (shift_val 0 1 f) ARG fa ->
    Reify (S m) (dEl B') fa body ->
    Reify m (dEl (vPi F B)) f (vLam body)
with ReifyNe : nat -> neutral -> neutral -> Type :=
| rne_var : forall m k, ReifyNe m (nVar k) (nVar k)
| rne_emptyrec : forall m rA lA A A' s s',
    ReifyTy m A A' -> ReifyNe m s s' ->
    ReifyNe m (nEmptyrec rA lA A s) (nEmptyrec rA lA A' s')
| rne_app : forall m f f' F F' B B' a a',
    ReifyNe m f f' ->
    ReifyTy m F F' ->
    ReifyTy (S m) B B' ->
    Reify m (dEl F) a a' ->
    ReifyNe m (nApp f F B a) (nApp f' F' B' a')
| rne_appI : forall m f f' F F' B B' a a',
    ReifyNe m f f' ->
    ReifyTy m F F' ->
    ReifyTy (S m) B B' ->
    Reify m (dEl F) a a' ->
    ReifyNe m (nAppI f F B a) (nAppI f' F' B' a').

Scheme ReifyTy_mut_rect := Induction for ReifyTy Sort Type
  with Reify_mut_rect   := Induction for Reify   Sort Type
  with ReifyNe_mut_rect := Induction for ReifyNe Sort Type.

Combined Scheme Reify_mutind from ReifyTy_mut_rect, Reify_mut_rect, ReifyNe_mut_rect.

(* ===================================================================== *)
(* Determinism: the index data determines the read-back normal form.       *)
(* ===================================================================== *)
Lemma Reify_det :
  (forall m c c', ReifyTy m c c' -> forall c'', ReifyTy m c c'' -> c' = c'')
  * ((forall m T v nf, Reify m T v nf -> forall nf', Reify m T v nf' -> nf = nf')
  * (forall m n n', ReifyNe m n n' -> forall n'', ReifyNe m n n'' -> n' = n'')).
Proof.
  apply Reify_mutind.
  - (* rty_Nat *) intros m c'' H; inversion H; subst; reflexivity.
  - (* rty_Empty *) intros m c'' H; inversion H; subst; reflexivity.
  - (* rty_Pi *) intros m F B F' B' HF IHF HB IHB c'' H; inversion H; subst.
    f_equal; [ apply IHF | apply IHB ]; assumption.
  - (* rty_PiI *) intros m F B F' B' HF IHF HB IHB c'' H; inversion H; subst.
    f_equal; [ apply IHF | apply IHB ]; assumption.
  - (* rty_ne *) intros m n n' Hn IHn c'' H; inversion H; subst.
    f_equal; apply IHn; assumption.
  - (* rfy_code *) intros m r l c c' Hc IHc nf' H; inversion H; subst.
    apply IHc; assumption.
  - (* rfy_zero *) intros m nf' H; inversion H; subst; reflexivity.
  - (* rfy_suc *) intros m v v' Hv IHv nf' H; inversion H; subst.
    f_equal; apply IHv; assumption.
  - (* rfy_neNat *) intros m n n' Hn IHn nf' H; inversion H; subst.
    f_equal; apply IHn; assumption.
  - (* rfy_neEmpty *) intros m n n' Hn IHn nf' H; inversion H; subst.
    f_equal; apply IHn; assumption.
  - (* rfy_neEl *) intros m c n n' Hn IHn nf' H; inversion H; subst.
    f_equal; apply IHn; assumption.
  - (* rfy_PiI *) intros m F B n n' Hn IHn nf' H; inversion H; subst.
    f_equal; apply IHn; assumption.
  - (* rfy_LamI *) intros m F B b b' Hb IHb nf' H; inversion H; subst.
    f_equal; apply IHb; assumption.
  - (* rfy_Pi *) intros m F B f ARG B' fa body Harg Hap Hva Hbody IHbody nf' H.
    inversion H; subst.
    assert (eA : ARG = ARG0) by (eapply Reflect_det; eassumption). subst ARG0.
    assert (eB : B' = B'0) by (eapply Apply_val_det; eassumption). subst B'0.
    assert (eF : fa = fa0) by (eapply Vapp_det; eassumption). subst fa0.
    f_equal; apply IHbody; eassumption.
  - (* rne_var *) intros m k n'' H; inversion H; subst; reflexivity.
  - (* rne_emptyrec *) intros m rA lA A A' s s' HA IHA Hs IHs n'' H; inversion H; subst.
    f_equal; [ apply IHA | apply IHs ]; assumption.
  - (* rne_app *) intros m f f' F F' B B' a a' Hf IHf HF IHF HB IHB Ha IHa n'' H.
    inversion H; subst.
    f_equal; [ apply IHf | apply IHF | apply IHB | apply IHa ]; assumption.
  - (* rne_appI *) intros m f f' F F' B B' a a' Hf IHf HF IHF HB IHB Ha IHa n'' H.
    inversion H; subst.
    f_equal; [ apply IHf | apply IHF | apply IHB | apply IHa ]; assumption.
Qed.

Definition ReifyTy_det := fst Reify_det.
Definition Reify_det_val := fst (snd Reify_det).
Definition ReifyNe_det := snd (snd Reify_det).
