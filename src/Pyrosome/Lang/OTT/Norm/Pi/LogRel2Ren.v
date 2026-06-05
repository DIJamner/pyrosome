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
  Domain Apply Typing Preservation ApplySubst RenSubst RenTyping
  LogRel2Conv LogRel2 LogRel2Ind LogRel2Lemmas LogRel2Irr.
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

(* Genuine [conv_ne]/[conv_nf] are stable under a syntactic renaming: both are
   purely structural maps, so [ren_ne]/[ren_val] preserve them (binder
   annotations recurse under [up_renl rho]).  This replaces the diagonal's
   trivial [n = m] preservation. *)
Lemma conv_ren :
  (forall a b, conv_nf a b -> forall rho, conv_nf (ren_val rho a) (ren_val rho b))
  * (forall n m, conv_ne n m -> forall rho, conv_ne (ren_ne rho n) (ren_ne rho m)).
Proof.
  apply (conv_mutind
    (fun a b (_ : conv_nf a b) => forall rho, conv_nf (ren_val rho a) (ren_val rho b))
    (fun n m (_ : conv_ne n m) => forall rho, conv_ne (ren_ne rho n) (ren_ne rho m))).
  - intros n m _ IH rho. cbn [ren_val]. apply cnf_ne. exact (IH rho).
  - intros rho. apply cnf_zero.
  - intros v w _ IH rho. cbn [ren_val]. apply cnf_suc. exact (IH rho).
  - intros rho. apply cnf_nat.
  - intros rho. apply cnf_empty.
  - intros F B F' B' _ IHF _ IHB rho. cbn [ren_val].
    apply cnf_pi; [ exact (IHF rho) | exact (IHB (up_renl rho)) ].
  - intros F B F' B' _ IHF _ IHB rho. cbn [ren_val].
    apply cnf_piI; [ exact (IHF rho) | exact (IHB (up_renl rho)) ].
  - intros b b' _ IH rho. cbn [ren_val]. apply cnf_lam. exact (IH (up_renl rho)).
  - intros b b' _ IH rho. cbn [ren_val]. apply cnf_lamI. exact (IH (up_renl rho)).
  - intros k rho. cbn [ren_ne]. apply cne_var.
  - intros rA lA A scrut A' scrut' _ IHA _ IHs rho. cbn [ren_ne].
    apply cne_emptyrec; [ exact (IHA rho) | exact (IHs rho) ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa rho. cbn [ren_ne].
    apply cne_app; [ exact (IHf rho) | exact (IHF rho) | exact (IHB (up_renl rho)) | exact (IHa rho) ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa rho. cbn [ren_ne].
    apply cne_appI; [ exact (IHf rho) | exact (IHF rho) | exact (IHB (up_renl rho)) | exact (IHa rho) ].
Qed.

(* The pointwise neutral conversion [NeConv] renames: both sides are
   [wf_neutral] (renamed by [ren_typing], each at its OWN type [T]/[S]) and the
   structural [conv_ne] is preserved by [ren_ne] ([conv_ren]). *)
Lemma NeConv_ren : forall Ge T T2 n m, NeConv Ge T T2 n m ->
    ne_below_ty (length Ge) T -> ne_below_ty (length Ge) T2 -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      NeConv Ge' (ren_ty rho T) (ren_ty rho T2) (ren_ne rho n) (ren_ne rho m).
Proof.
  intros Ge T T2 n m [[wn wm] cnm] HtyT HtyS Hctx Ge' rho Hren Hok.
  unfold NeConv. repeat split.
  - exact (snd ren_typing Ge n T wn HtyT Hctx Ge' rho Hren Hok).
  - exact (snd ren_typing Ge m T2 wm HtyS Hctx Ge' rho Hren Hok).
  - exact (snd conv_ren n m cnm rho).
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
    exact (NeConv_ren Hnm I I Hctx Hren Hok).
Qed.

(* The PER of convertible neutrals at a (two-typed) pair renames. *)
Lemma RedNeutralEq_ren : forall Ge T T2 v w, RedNeutralEq Ge T T2 v w ->
    ne_below_ty (length Ge) T -> ne_below_ty (length Ge) T2 -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      RedNeutralEq Ge' (ren_ty rho T) (ren_ty rho T2) (ren_val rho v) (ren_val rho w).
Proof.
  intros Ge T T2 v w H HtyT HtyS Hctx Ge' rho Hren Hok.
  destruct H as [n m Hnm]. cbn [ren_val]. apply rneT.
  exact (NeConv_ren Hnm HtyT HtyS Hctx Hren Hok).
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

(* The composite of two renamings is a renaming (the Pi app-clause's [is_ren]
   gate must be re-established at [comp_sub]). *)
Lemma is_ren_comp_sub : forall sg2 rho n, is_ren sg2 -> is_ren (comp_sub sg2 rho n).
Proof.
  intros sg2 rho n [r2 ->].
  exists (map (fun k => nth_default 0 r2 (renm rho k)) (seq 0 n)).
  unfold comp_sub. rewrite map_map. apply map_ext_in. intros k _.
  unfold nth_default. rewrite nth_error_map.
  destruct (nth_error r2 (renm rho k)) eqn:E; reflexivity.
Qed.

(* [RenSubSc] extended under a binder by a fixed head [a]: the composite
   [a :: comp_sub sg2 rho n] is the [(a::sg2)]-image of the lifted renaming
   [ren_sub (up_renl rho)].  This is the codomain analogue of
   [comp_sub_RenSubSc] (used by [posRed']/the app-clause's [up] level). *)
Lemma comp_sub_cons_RenSubSc : forall sg2 rho n m2 a,
    (forall k, k < n -> renm rho k < length sg2) ->
    RenSubSc (S n) m2 (a :: sg2) (ren_sub (up_renl rho)) (a :: comp_sub sg2 rho n).
Proof.
  intros sg2 rho n m2 a Hb k Hk. rewrite ren_sub_nth. destruct k as [|j].
  - rewrite renm_up_0. unfold nth_default; cbn [nth_error].
    apply ap_ne. change (vNe (nVar 0)) with (nth_default (vNe (nVar 0)) (a :: sg2) 0).
    apply ap_var.
  - assert (Hj : j < n) by Lia.lia. rewrite renm_up_S.
    replace (nth_default (vNe (nVar (S j))) (a :: comp_sub sg2 rho n) (S j))
       with (nth_default (vNe (nVar (S j))) (comp_sub sg2 rho n) j)
       by (unfold nth_default; reflexivity).
    rewrite (@comp_sub_nth sg2 rho n j (vNe (nVar (S j))) Hj).
    apply ap_ne.
    assert (E : nth_default (vNe (nVar 0)) sg2 (renm rho j)
              = nth_default (vNe (nVar (S (renm rho j)))) (a :: sg2) (S (renm rho j))).
    { specialize (Hb j Hj). unfold nth_default; cbn [nth_error].
      destruct (nth_error sg2 (renm rho j)) eqn:Eo; [ reflexivity | ].
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

(* ===================================================================== *)
(* The RENAMED Pi pack [ren_pack] and its adequacy [ren_adeq].  The Pi case  *)
(* of the presheaf REUSES the original pack [PA0] at the COMPOSITE             *)
(* substitution [comp_sub sg2 rho (length Ge)] (no domain/codomain IHs --      *)
(* "cleaner than symmetry"):                                                  *)
(*   - [shpRed'] RETURNS [shpRed PA0] at the composite, so its [redTmEq] IS    *)
(*     the original's -- [posRed'] then feeds [rab] to [posRed PA0] with NO    *)
(*     irrelevance (definitional, via the SHARED [rp_*] helpers below);        *)
(*   - [posRed']'s codomain [Apply] witnesses are recovered in RENAMED form    *)
(*     by the REVERSE composition [Apply_val_ren_uncomp_sc];                   *)
(*   - adequacy is the original [shpAd]/[posAd] verbatim.                      *)
(* ===================================================================== *)
Section RenPackSec.
  Context (lvl : TypeLevel) (rec0 rec1 : RedRel).
  Context (Ge : senv) (FA BA FB BB : sval) (PA0 : PolyRedPack Ge FA BA FB BB).
  Context (ad : PolyRedPackAdequate (@LR lvl rec0 rec1) PA0).
  Context (wpiA : wf_svalty Ge (dEl (vPi FA BA))) (wpiB : wf_svalty Ge (dEl (vPi FB BB))).
  Context (Hctx : ne_below_ctx Ge).
  Context (Ge' : senv) (rho : list nat) (Hren : ren_ctx rho Ge Ge')
          (Hok : ren_ok rho (S (length Ge)) (length Ge')).

  Local Definition rp_HFA : ne_below_val (length Ge) FA := proj1 (wf_svalty_scoped wpiA).
  Local Definition rp_HBA : ne_below_val (S (length Ge)) BA := proj2 (wf_svalty_scoped wpiA).
  Local Definition rp_HFB : ne_below_val (length Ge) FB := proj1 (wf_svalty_scoped wpiB).
  Local Definition rp_HBB : ne_below_val (S (length Ge)) BB := proj2 (wf_svalty_scoped wpiB).

  (* the in-range bound for [comp_sub_RenSubSc], from [ws2]'s length + [ren_ok]. *)
  Local Definition rp_bound Delta sg2 (ws2 : wf_ssub Delta sg2 Ge')
    : forall k, k < length Ge -> renm rho k < length sg2.
  Proof. intros k Hk. rewrite (fst ws2). apply Hok. Lia.lia. Defined.

  Local Definition rp_ws3 Delta sg2 (ws2 : wf_ssub Delta sg2 Ge')
    : wf_ssub Delta (comp_sub sg2 rho (length Ge)) Ge
    := wf_ssub_comp ws2 Hren Hctx.

  Local Definition rp_afA3 Delta sg2 (ws2 : wf_ssub Delta sg2 Ge') FA1
    (afA2 : Apply_val (length Delta) sg2 (ren_val rho FA) FA1)
    : Apply_val (length Delta) (comp_sub sg2 rho (length Ge)) FA FA1
    := Apply_val_ren_comp_sc (ren_is_Apply_val FA (length Ge) rho) (is_ren_ren_sub rho)
         rp_HFA (@comp_sub_RenSubSc sg2 rho (length Ge) (length Delta) (rp_bound ws2)) afA2.

  Local Definition rp_afB3 Delta sg2 (ws2 : wf_ssub Delta sg2 Ge') FB1
    (afB2 : Apply_val (length Delta) sg2 (ren_val rho FB) FB1)
    : Apply_val (length Delta) (comp_sub sg2 rho (length Ge)) FB FB1
    := Apply_val_ren_comp_sc (ren_is_Apply_val FB (length Ge) rho) (is_ren_ren_sub rho)
         rp_HFB (@comp_sub_RenSubSc sg2 rho (length Ge) (length Delta) (rp_bound ws2)) afB2.

  (* [shpRed']/[posRed'] as STANDALONE named constants (not the record's self-
     projection -- that becomes an unsolved evar [shpRed ?PA] under [refine],
     blocking the [redTmEq] reduction [rab] needs).  [ren_shpRed] RETURNS the
     original [shpRed PA0] at the composite, so [posRed']'s [rab] feeds [posRed
     PA0] with NO irrelevance (definitional via [unfold ren_shpRed]). *)
  Definition ren_shpRed Delta sg2 FA1 FB1 (ws2 : wf_ssub Delta sg2 Ge')
    (afA2 : Apply_val (length Delta) sg2 (ren_val rho FA) FA1)
    (afB2 : Apply_val (length Delta) sg2 (ren_val rho FB) FB1)
    : LRPack Delta (dEl FA1) (dEl FB1)
    := shpRed PA0 (rp_ws3 ws2) (rp_afA3 ws2 afA2) (rp_afB3 ws2 afB2).

  Definition ren_posRed Delta sg2 a b FA1 FB1 (ws2 : wf_ssub Delta sg2 Ge')
    (afA2 : Apply_val (length Delta) sg2 (ren_val rho FA) FA1)
    (afB2 : Apply_val (length Delta) sg2 (ren_val rho FB) FB1)
    (rab : redTmEq (ren_shpRed ws2 afA2 afB2) a b)
    : { BresA & { BresB &
        ( Apply_val (length Delta) (a :: sg2) (ren_val (up_renl rho) BA) BresA
        * Apply_val (length Delta) (b :: sg2) (ren_val (up_renl rho) BB) BresB
        * LRPack Delta (dEl BresA) (dEl BresB) )%type } }.
  Proof.
    unfold ren_shpRed in rab.
    refine (existT _ (posTyA PA0 rab) (existT _ (posTyB PA0 rab)
              ((_, _), posPack PA0 rab))).
    - eapply Apply_val_ren_uncomp_sc;
        [ exact (posAppA PA0 rab) | exact rp_HBA
        | apply comp_sub_cons_RenSubSc; exact (rp_bound ws2) ].
    - eapply Apply_val_ren_uncomp_sc;
        [ exact (posAppB PA0 rab) | exact rp_HBB
        | apply comp_sub_cons_RenSubSc; exact (rp_bound ws2) ].
  Defined.

  Definition ren_pack
    : PolyRedPack Ge' (ren_val rho FA) (ren_val (up_renl rho) BA)
                      (ren_val rho FB) (ren_val (up_renl rho) BB)
    := Build_PolyRedPack ren_shpRed ren_posRed.

  Definition ren_adeq : PolyRedPackAdequate (@LR lvl rec0 rec1) ren_pack.
  Proof.
    refine (@Build_PolyRedPackAdequate (@LR lvl rec0 rec1) Ge'
              (ren_val rho FA) (ren_val (up_renl rho) BA)
              (ren_val rho FB) (ren_val (up_renl rho) BB) ren_pack _ _).
    - intros Delta sg2 FA1 FB1 ws2 afA2 afB2.
      change (shpRed ren_pack ws2 afA2 afB2) with (ren_shpRed ws2 afA2 afB2).
      unfold ren_shpRed.
      exact (shpAd ad (rp_ws3 ws2) (rp_afA3 ws2 afA2) (rp_afB3 ws2 afB2)).
    - intros Delta sg2 a b FA1 FB1 ws2 afA2 afB2 rab.
      change (redTmEq (shpRed ren_pack ws2 afA2 afB2) a b)
        with (redTmEq (ren_shpRed ws2 afA2 afB2) a b) in rab.
      unfold ren_shpRed in rab.
      exact (posAd ad (rp_ws3 ws2) (rp_afA3 ws2 afA2) (rp_afB3 ws2 afB2) rab).
  Defined.

  (* FORWARD MAP: original Pi-conversion of [f],[g] renames to Pi-conversion of
     [ren f],[ren g] at the renamed pack.  Typing is [ren_typing]; the app-clause
     REUSES the original [app] at the composite [sg3] (the [rp_*] witnesses), so
     the domain conv [rab] and the codomain relation match DEFINITIONALLY -- NO
     irrelevance/[Apply_val_det] (cleaner than symmetry's bwd). *)
  Lemma ren_pack_fwd : forall f g,
      PiRedTmEq PA0 f g -> PiRedTmEq ren_pack (ren_val rho f) (ren_val rho g).
  Proof.
    intros f g [[Hf Hg] app]. refine ((_, _), _).
    - exact (fst ren_typing Ge f (dEl (vPi FA BA)) Hf
               (wf_svalty_scoped wpiA) Hctx Ge' rho Hren Hok).
    - exact (fst ren_typing Ge g (dEl (vPi FB BB)) Hg
               (wf_svalty_scoped wpiB) Hctx Ge' rho Hren Hok).
    - intros Delta sg2 a b FA1 FB1 BA1 BB1 fsg gsg ws2 rn2 afA2 afB2 afBA2 afBB2 afsf2 afsg2 rab2.
      assert (afBA3 : Apply_val (S (length Delta)) (up (comp_sub sg2 rho (length Ge))) BA BA1).
      { eapply Apply_val_ren_comp_sc;
          [ exact (ren_is_Apply_val BA (S (length Ge)) (up_renl rho)) | apply is_ren_ren_sub
          | exact rp_HBA
          | rewrite <- up_ren_sub; apply RenSubSc_up;
            exact (@comp_sub_RenSubSc sg2 rho (length Ge) (length Delta) (rp_bound ws2))
          | exact afBA2 ]. }
      assert (afBB3 : Apply_val (S (length Delta)) (up (comp_sub sg2 rho (length Ge))) BB BB1).
      { eapply Apply_val_ren_comp_sc;
          [ exact (ren_is_Apply_val BB (S (length Ge)) (up_renl rho)) | apply is_ren_ren_sub
          | exact rp_HBB
          | rewrite <- up_ren_sub; apply RenSubSc_up;
            exact (@comp_sub_RenSubSc sg2 rho (length Ge) (length Delta) (rp_bound ws2))
          | exact afBB2 ]. }
      assert (afsf3 : Apply_val (length Delta) (comp_sub sg2 rho (length Ge)) f fsg).
      { eapply Apply_val_ren_comp_sc;
          [ exact (ren_is_Apply_val f (length Ge) rho) | apply is_ren_ren_sub
          | exact (has_svalty_ne_below Hf Hctx)
          | exact (@comp_sub_RenSubSc sg2 rho (length Ge) (length Delta) (rp_bound ws2))
          | exact afsf2 ]. }
      assert (afsg3 : Apply_val (length Delta) (comp_sub sg2 rho (length Ge)) g gsg).
      { eapply Apply_val_ren_comp_sc;
          [ exact (ren_is_Apply_val g (length Ge) rho) | apply is_ren_ren_sub
          | exact (has_svalty_ne_below Hg Hctx)
          | exact (@comp_sub_RenSubSc sg2 rho (length Ge) (length Delta) (rp_bound ws2))
          | exact afsg2 ]. }
      change (redTmEq (shpRed ren_pack ws2 afA2 afB2) a b)
        with (redTmEq (shpRed PA0 (rp_ws3 ws2) (rp_afA3 ws2 afA2) (rp_afB3 ws2 afB2)) a b) in rab2.
      destruct (app Delta (comp_sub sg2 rho (length Ge)) a b FA1 FB1 BA1 BB1 fsg gsg
                  (rp_ws3 ws2) (@is_ren_comp_sub sg2 rho (length Ge) rn2)
                  (rp_afA3 ws2 afA2) (rp_afB3 ws2 afB2) afBA3 afBB3 afsf3 afsg3 rab2)
        as [v [w [[Vf Vg] rvw]]].
      exists v, w. refine ((Vf, Vg), _). exact rvw.
  Qed.

End RenPackSec.

(* ===================================================================== *)
(* The RENAMING-STABILITY presheaf [LR_ren_gen]: a context renaming [Ge ->     *)
(* Ge'] sends [LR Ge A B P] to [LR Ge' A[rho] B[rho] Q] with a forward map      *)
(* [P a b -> Q a[rho] b[rho]].  Mirrors [LR_sym_gen]'s shape (carrier +         *)
(* [RecRen1] tower hypothesis, by [LR_mut]) but is FORWARD-ONLY and needs NO    *)
(* domain/codomain IHs: the Pi case reuses [ren_pack]/[ren_adeq]/[ren_pack_fwd] *)
(* (the original pack at the composite substitution).  Base cases are the       *)
(* base-PER renaming lemmas; [LRU0]/[LRU1] use [RecRen1] for the lower tower.   *)
(* ===================================================================== *)
Section RenGen.
  Context (lvl : TypeLevel) (rec0 rec1 : RedRel).

  Definition RenCar Ge (A B : svalty) (P : sval -> sval -> Type) : Type :=
    wf_svalty Ge A -> wf_svalty Ge B -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      { Q : sval -> sval -> Type &
        ( @LR lvl rec0 rec1 Ge' (ren_ty rho A) (ren_ty rho B) Q
        * (forall a b, P a b -> Q (ren_val rho a) (ren_val rho b)) )%type }.

  Definition RecRen1 (rec : RedRel) : Type :=
    forall Ge A B P, rec Ge A B P ->
      wf_svalty Ge A -> wf_svalty Ge B -> ne_below_ctx Ge ->
      forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
        { Q : sval -> sval -> Type &
          ( rec Ge' (ren_ty rho A) (ren_ty rho B) Q
          * (forall a b, P a b -> Q (ren_val rho a) (ren_val rho b)) )%type }.

  Context (HR0 : RecRen1 rec0) (HR1 : RecRen1 rec1).

  Lemma LR_ren_gen : forall Ge A B P (H : @LR lvl rec0 rec1 Ge A B P), RenCar Ge A B P.
  Proof.
    intros Ge A B P H. induction H using LR_mut; unfold RenCar;
      intros wfA wfB Hctx Ge' rho Hren Hok.
    - (* LRnat *)
      exists (RedNatEq Ge'). split.
      + cbn [ren_ty ren_val]. apply LRnat.
      + intros a b Hab. exact (RedNatEq_ren Hab Hctx Hren Hok).
    - (* LRempty *)
      exists (RedNeutralEq Ge' (dEl vEmpty) (dEl vEmpty)). split.
      + cbn [ren_ty ren_val]. apply LRempty.
      + intros a b Hab. exact (RedNeutralEq_ren Hab I I Hctx Hren Hok).
    - (* LRne *)
      exists (RedNeutralEq Ge' (dEl (vNe (ren_ne rho n))) (dEl (vNe (ren_ne rho m)))). split.
      + cbn [ren_ty ren_val]. eapply LRne. exact (NeConv_ren c I I Hctx Hren Hok).
      + intros a b Hab.
        exact (RedNeutralEq_ren Hab (wf_svalty_scoped wfA) (wf_svalty_scoped wfB) Hctx Hren Hok).
    - (* LRpiI *)
      exists (fun f g => (has_svalty Ge' f (dEl (vPiI (ren_val rho FA) (ren_val (up_renl rho) BA)))
                        * has_svalty Ge' g (dEl (vPiI (ren_val rho FB) (ren_val (up_renl rho) BB))))%type).
      split.
      + cbn [ren_ty ren_val]. apply LRpiI; [ exact (wf_svalty_ren wfA Hren) | exact (wf_svalty_ren wfB Hren) ].
      + intros f g [Hf Hg]. split.
        * exact (fst ren_typing Ge f (dEl (vPiI FA BA)) Hf (wf_svalty_scoped wfA) Hctx Ge' rho Hren Hok).
        * exact (fst ren_typing Ge g (dEl (vPiI FB BB)) Hg (wf_svalty_scoped wfB) Hctx Ge' rho Hren Hok).
    - (* LRpi -- reuse the renamed pack *)
      exists (PiRedTmEq (ren_pack PA wfA wfB Hctx Hren Hok)). split.
      + cbn [ren_ty ren_val].
        apply (LRpi (PA := ren_pack PA wfA wfB Hctx Hren Hok));
          [ exact (wf_svalty_ren wfA Hren) | exact (wf_svalty_ren wfB Hren)
          | exact (ren_adeq ad wfA wfB Hctx Hren Hok) ].
      + intros f g Hfg. exact (ren_pack_fwd wfA wfB Hctx Hren Hok Hfg).
    - (* LRU0 *)
      exists (fun c d => (has_svalty Ge' c (dU r l) * has_svalty Ge' d (dU r l) *
                 { P : sval -> sval -> Type & rec0 Ge' (dEl c) (dEl d) P })%type).
      split.
      + cbn [ren_ty]. apply LRU0; assumption.
      + intros c d [[Hc Hd] [P0 HP0]]. cbn [ren_ty ren_val]. refine ((_, _), _).
        * exact (fst ren_typing Ge c (dU r l) Hc I Hctx Ge' rho Hren Hok).
        * exact (fst ren_typing Ge d (dU r l) Hd I Hctx Ge' rho Hren Hok).
        * destruct (HR0 HP0 (wf_dEl Hc) (wf_dEl Hd) Hctx Hren Hok)
            as [Q' [Hrec' _]]. exists Q'. exact Hrec'.
    - (* LRU1 *)
      exists (fun c d => (has_svalty Ge' c (dU r l) * has_svalty Ge' d (dU r l) *
                 { P : sval -> sval -> Type & rec1 Ge' (dEl c) (dEl d) P })%type).
      split.
      + cbn [ren_ty]. apply LRU1; assumption.
      + intros c d [[Hc Hd] [P0 HP0]]. cbn [ren_ty ren_val]. refine ((_, _), _).
        * exact (fst ren_typing Ge c (dU r l) Hc I Hctx Ge' rho Hren Hok).
        * exact (fst ren_typing Ge d (dU r l) Hd I Hctx Ge' rho Hren Hok).
        * destruct (HR1 HP0 (wf_dEl Hc) (wf_dEl Hd) Hctx Hren Hok)
            as [Q' [Hrec' _]]. exists Q'. exact Hrec'.
  Qed.

End RenGen.

(* ===================================================================== *)
(* Tower instantiation + top-level RENAMING STABILITY of [RedTyEq]/[RedTmEq]. *)
(* ===================================================================== *)
Definition LRbot_ren : RecRen1 LRbot.
Proof. intros Ge A B P H; destruct H. Qed.

Definition LR0_ren : RecRen1 LR0.
Proof. intros Ge A B P H. exact (LR_ren_gen LRbot_ren LRbot_ren H). Qed.

Definition LR1_ren : RecRen1 LR1.
Proof. intros Ge A B P H. exact (LR_ren_gen LR0_ren LRbot_ren H). Qed.

Lemma RedTyEq_ren : forall Ge A B, RedTyEq Ge A B ->
    wf_svalty Ge A -> wf_svalty Ge B -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      RedTyEq Ge' (ren_ty rho A) (ren_ty rho B).
Proof.
  intros Ge A B [P H] wA wB Hctx Ge' rho Hren Hok.
  destruct (LR_ren_gen LR0_ren LR1_ren H wA wB Hctx Hren Hok) as [Q [HQ _]].
  exact (existT _ Q HQ).
Qed.

Lemma RedTmEq_ren : forall Ge A B a b, RedTmEq Ge A B a b ->
    wf_svalty Ge A -> wf_svalty Ge B -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      RedTmEq Ge' (ren_ty rho A) (ren_ty rho B) (ren_val rho a) (ren_val rho b).
Proof.
  intros Ge A B a b [P [H Pab]] wA wB Hctx Ge' rho Hren Hok.
  destruct (LR_ren_gen LR0_ren LR1_ren H wA wB Hctx Hren Hok) as [Q [HQ Hmap]].
  exact (existT _ Q (HQ, Hmap a b Pab)).
Qed.
