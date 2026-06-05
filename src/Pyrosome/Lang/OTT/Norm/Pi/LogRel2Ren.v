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
  Domain Apply Typing Preservation ApplySubst RenSubst RenTyping LogRel2.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Phase-2/4 RENAMING STABILITY of the two-sided [LR] -- the base-PER       *)
(* layer.  [NeConv]/[RedNatEq]/[RedNeutralEq] are stable under a context     *)
(* renaming, now that [RenTyping.ren_typing] renames [wf_neutral] at every   *)
(* type (incl. the neutrals-at-[dEl] these PERs store).  The renaming        *)
(* package is [ren_ctx rho Ge Ge'] + [ren_ok rho (S (length Ge)) (length     *)
(* Ge')] + the source scopedness [ne_below_ty]/[ne_below_ctx] that           *)
(* [ren_typing] consumes; the [LR_ren_gen] presheaf supplies all of these    *)
(* from the LR pack's stored typing.                                         *)
(* ===================================================================== *)

(* The pointwise neutral conversion [NeConv] renames: both sides are          *)
(* [wf_neutral] (renamed by [ren_typing]) and the syntactic diagonal [n = m]  *)
(* is preserved by [ren_ne]. *)
Lemma NeConv_ren : forall Ge T n m, NeConv Ge T n m ->
    ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      NeConv Ge' (ren_ty rho T) (ren_ne rho n) (ren_ne rho m).
Proof.
  intros Ge T n m [[wn wm] e] Hty Hctx Ge' rho Hren Hok.
  subst m. unfold NeConv. repeat split.
  - exact (snd ren_typing Ge n T wn Hty Hctx Ge' rho Hren Hok).
  - exact (snd ren_typing Ge n T wm Hty Hctx Ge' rho Hren Hok).
Qed.

(* The PER of convertible naturals renames (it lives at [dEl vNat], whose
   scopedness is vacuous, so no [ne_below_ty] hypothesis is needed). *)
Lemma RedNatEq_ren : forall Ge v w, RedNatEq Ge v w ->
    ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      RedNatEq Ge' (ren_val rho v) (ren_val rho w).
Proof.
  intros Ge v w H Hctx Ge' rho Hren Hok.
  induction H as [ | v w Hvw IH | n m Hnm ].
  - cbn [ren_val]. apply rne_zero.
  - cbn [ren_val]. apply rne_suc. exact IH.
  - cbn [ren_val]. apply rne_ne.
    exact (NeConv_ren Hnm I Hctx Hren Hok).
Qed.

(* The PER of convertible neutrals at a fixed type renames. *)
Lemma RedNeutralEq_ren : forall Ge T v w, RedNeutralEq Ge T v w ->
    ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      RedNeutralEq Ge' (ren_ty rho T) (ren_val rho v) (ren_val rho w).
Proof.
  intros Ge T v w H Hty Hctx Ge' rho Hren Hok.
  destruct H as [n m Hnm]. cbn [ren_val]. apply rneT.
  exact (NeConv_ren Hnm Hty Hctx Hren Hok).
Qed.

(* ===================================================================== *)
(* REVERSE renaming-composition [Apply_ren_uncomp_sc] -- the engine the      *)
(* presheaf's codomain ([posRed']) needs but the algebra layer lacked.       *)
(*                                                                           *)
(* [Apply_ren_comp_sc] proves the FORWARD direction (rename then [s2] =>      *)
(* composite [s3]).  The Pi codomain instead has a composite-side witness     *)
(* [Apply (a::sg3) BA Bres] (from reusing [posRed PA0]) and must RETURN the   *)
(* renamed-side witness [Apply (a::sg2) (ren BA) Bres].  Inducting on the      *)
(* EXISTING composite derivation REPLAYS its reductions on the renamed side   *)
(* -- no [Apply]-totality is manufactured (the key gap that blocks            *)
(* transitivity but NOT renaming: here the composite derivation already       *)
(* exists, so every beta step is given, not produced).                       *)
(* ===================================================================== *)
Lemma Apply_ren_uncomp_sc :
  (forall m2 s3 T T', Apply_ty m2 s3 T T' ->
     forall N rho s2, ne_below_ty N T -> RenSubSc N m2 s2 (ren_sub rho) s3 ->
       Apply_ty m2 s2 (ren_ty rho T) T')
  * (forall m2 s3 v v', Apply_val m2 s3 v v' ->
       forall N rho s2, ne_below_val N v -> RenSubSc N m2 s2 (ren_sub rho) s3 ->
         Apply_val m2 s2 (ren_val rho v) v')
  * (forall m2 s3 n v, Apply_ne m2 s3 n v ->
       forall N rho s2, ne_below_ne N n -> RenSubSc N m2 s2 (ren_sub rho) s3 ->
         Apply_ne m2 s2 (ren_ne rho n) v)
  * (forall m F B vf a v, Vapp m F B vf a v -> unit)
  * (forall m F B vf a v, VappI m F B vf a v -> unit).
Proof.
  refine (Apply_mutind
    (fun m2 s3 T T' _ => forall N rho s2, ne_below_ty N T ->
       RenSubSc N m2 s2 (ren_sub rho) s3 -> Apply_ty m2 s2 (ren_ty rho T) T')
    (fun m2 s3 v v' _ => forall N rho s2, ne_below_val N v ->
       RenSubSc N m2 s2 (ren_sub rho) s3 -> Apply_val m2 s2 (ren_val rho v) v')
    (fun m2 s3 n v _ => forall N rho s2, ne_below_ne N n ->
       RenSubSc N m2 s2 (ren_sub rho) s3 -> Apply_ne m2 s2 (ren_ne rho n) v)
    (fun _ _ _ _ _ _ _ => unit)
    (fun _ _ _ _ _ _ _ => unit)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ap_dU *) intros m2 s3 r l N rho s2 Hne Hrs. apply ap_dU.
  - (* ap_dEl *) intros m2 s3 e e' He IHe N rho s2 Hne Hrs.
    cbn [ne_below_ty] in Hne. cbn [ren_ty]. apply ap_dEl. eapply IHe; eassumption.
  - (* ap_ne (val) *) intros m2 s3 n v Hn IHn N rho s2 Hne Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_ne. eapply IHn; eassumption.
  - (* ap_zero *) intros m2 s3 N rho s2 Hne Hrs. apply ap_zero.
  - (* ap_suc *) intros m2 s3 v v' Hv IHv N rho s2 Hne Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_suc. eapply IHv; eassumption.
  - (* ap_nat *) intros m2 s3 N rho s2 Hne Hrs. apply ap_nat.
  - (* ap_empty *) intros m2 s3 N rho s2 Hne Hrs. apply ap_empty.
  - (* ap_pi *) intros m2 s3 F F' B B' HF IHF HB IHB N rho s2 Hne Hrs.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB]. cbn [ren_val]. apply ap_pi.
    + eapply IHF; eassumption.
    + eapply IHB; [ exact HneB | rewrite <- up_ren_sub; apply RenSubSc_up; exact Hrs ].
  - (* ap_piI *) intros m2 s3 F F' B B' HF IHF HB IHB N rho s2 Hne Hrs.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB]. cbn [ren_val]. apply ap_piI.
    + eapply IHF; eassumption.
    + eapply IHB; [ exact HneB | rewrite <- up_ren_sub; apply RenSubSc_up; exact Hrs ].
  - (* ap_lam *) intros m2 s3 b b' Hb IHb N rho s2 Hne Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_lam.
    eapply IHb; [ exact Hne | rewrite <- up_ren_sub; apply RenSubSc_up; exact Hrs ].
  - (* ap_lamI *) intros m2 s3 b b' Hb IHb N rho s2 Hne Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_lamI.
    eapply IHb; [ exact Hne | rewrite <- up_ren_sub; apply RenSubSc_up; exact Hrs ].
  - (* ap_var *) intros m2 s3 k N rho s2 Hne Hrs.
    cbn [ne_below_ne] in Hne. cbn [ren_ne].
    pose proof (Hrs k Hne) as Hk. rewrite ren_sub_nth in Hk.
    pose proof (Apply_val_det (ap_ne (ap_var m2 s2 (renm rho k))) Hk) as Heq.
    rewrite <- Heq. apply ap_var.
  - (* ap_emptyrec *) intros m2 s3 rA lA A A' scrut scrut' HA IHA Hsc IHsc N rho s2 Hne Hrs.
    cbn [ne_below_ne] in Hne. destruct Hne as [HneA Hnesc].
    cbn [ren_ne ren_val]. apply ap_emptyrec.
    + eapply IHA; eassumption.
    + eapply IHsc; eassumption.
  - (* ap_app *) intros m2 s3 f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp
      N rho s2 Hne Hrs.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    cbn [ren_ne]. eapply ap_app.
    + eapply IHf; eassumption.
    + eapply IHF; eassumption.
    + eapply IHB; [ exact HneB | rewrite <- up_ren_sub; apply RenSubSc_up; exact Hrs ].
    + eapply IHa; eassumption.
    + exact Hvapp.
  - (* ap_appI *) intros m2 s3 f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp
      N rho s2 Hne Hrs.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    cbn [ren_ne]. eapply ap_appI.
    + eapply IHf; eassumption.
    + eapply IHF; eassumption.
    + eapply IHB; [ exact HneB | rewrite <- up_ren_sub; apply RenSubSc_up; exact Hrs ].
    + eapply IHa; eassumption.
    + exact Hvapp.
  - (* vapp_lam *) intros; exact tt.
  - (* vapp_ne *) intros; exact tt.
  - (* vappI_lam *) intros; exact tt.
  - (* vappI_ne *) intros; exact tt.
Qed.

Definition Apply_ty_ren_uncomp_sc  := fst (fst (fst (fst Apply_ren_uncomp_sc))).
Definition Apply_val_ren_uncomp_sc := snd (fst (fst (fst Apply_ren_uncomp_sc))).
Definition Apply_ne_ren_uncomp_sc  := snd (fst (fst Apply_ren_uncomp_sc)).

(* ===================================================================== *)
(* The COMPOSITE substitution [comp_sub sg2 rho n] = "[sg2] after the        *)
(* renaming [rho]", i.e. the [sg2]-image of [ren_sub rho] truncated to the    *)
(* source length [n].  This is the [sg3] that the presheaf's Pi case feeds    *)
(* to the ORIGINAL pack: applying [sg2] to a [rho]-renamed value equals        *)
(* applying [comp_sub sg2 rho] to the original (the [RenSubSc] below + the     *)
(* forward/reverse comp lemmas).                                              *)
(* ===================================================================== *)
Definition comp_sub (sg2 : ssub) (rho : list nat) (n : nat) : ssub :=
  map (fun k => nth_default (vNe (nVar 0)) sg2 (renm rho k)) (seq 0 n).

Lemma comp_sub_length : forall sg2 rho n, length (comp_sub sg2 rho n) = n.
Proof. intros. unfold comp_sub. rewrite length_map, length_seq. reflexivity. Qed.

Lemma comp_sub_nth : forall sg2 rho n k d, k < n ->
    nth_default d (comp_sub sg2 rho n) k = nth_default (vNe (nVar 0)) sg2 (renm rho k).
Proof.
  intros sg2 rho n k d Hk. unfold comp_sub, nth_default.
  rewrite nth_error_map. rewrite nth_error_seq_some by exact Hk. reflexivity.
Qed.

(* [comp_sub sg2 rho n] IS the [RenSubSc]-composite of [sg2] and [ren_sub rho]
   (below [n]): reading a renaming variable then applying [sg2] hits exactly
   the selected [sg2] entry. *)
Lemma comp_sub_RenSubSc : forall sg2 rho n m2,
    (forall k, k < n -> renm rho k < length sg2) ->
    RenSubSc n m2 sg2 (ren_sub rho) (comp_sub sg2 rho n).
Proof.
  intros sg2 rho n m2 Hb k Hk. rewrite ren_sub_nth, comp_sub_nth by exact Hk.
  apply ap_ne.
  (* in range => the [vNe (nVar 0)] default of [comp_sub] agrees with [ap_var]'s *)
  assert (E : nth_default (vNe (nVar 0)) sg2 (renm rho k)
            = nth_default (vNe (nVar (renm rho k))) sg2 (renm rho k)).
  { specialize (Hb k Hk). unfold nth_default.
    destruct (nth_error sg2 (renm rho k)) eqn:Eo; [ reflexivity | ].
    apply nth_error_None in Eo. Lia.lia. }
  rewrite E. apply ap_var.
Qed.

(* A general [wf_ssub] into [Ge'] precomposes with a renaming [Ge -> Ge'] to a
   [wf_ssub] into [Ge].  The type-side [Apply_ty] is recovered via the FORWARD
   composition lemma (renamed-then-[sg2] => composite); the term-side reads off
   the selected [sg2] entry directly. *)
Lemma wf_ssub_comp : forall Delta sg2 Ge Ge' rho,
    wf_ssub Delta sg2 Ge' -> ren_ctx rho Ge Ge' -> ne_below_ctx Ge ->
    wf_ssub Delta (comp_sub sg2 rho (length Ge)) Ge.
Proof.
  intros Delta sg2 Ge Ge' rho [Hlen Hsg] Hren Hctx.
  assert (Hbound : forall j, j < length Ge -> renm rho j < length sg2).
  { intros j Hj. rewrite Hlen. destruct (nth_error Ge j) as [Tj|] eqn:Ej.
    - apply nth_error_Some. rewrite (Hren j Tj Ej). discriminate.
    - apply nth_error_None in Ej. Lia.lia. }
  split.
  - apply comp_sub_length.
  - intros k T Hnth.
    assert (Hk : k < length Ge) by (apply nth_error_Some; rewrite Hnth; discriminate).
    pose proof (Hren k T Hnth) as Hnth'.
    destruct (Hsg (renm rho k) (ren_ty rho T) Hnth') as [T' [Hap Hhas]].
    exists T'. split.
    + (* Apply_ty (length Delta) (comp_sub..) T T' *)
      eapply (Apply_ty_ren_comp_sc (ren_is_Apply_ty T (length Ge) rho)
                (is_ren_ren_sub rho) (Hctx k T Hnth)
                (@comp_sub_RenSubSc sg2 rho (length Ge) (length Delta) Hbound)).
      exact Hap.
    + rewrite comp_sub_nth by exact Hk. exact Hhas.
Qed.
