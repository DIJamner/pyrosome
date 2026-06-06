Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Reflect LogRel2Conv Typing Preservation ApplySubst RenSubst RenTyping.
Import Core.Notations.

(* ===================================================================== *)
(* PROTOTYPE (WIP, not in build): the eta-closed DECLARATIVE conversion    *)
(* judgment that [n_conv] will consume (UPDATE 2026-06-06j/k).             *)
(*                                                                         *)
(* UPDATE 2026-06-06k -- DESIGN REFINEMENT.  The eta rule [ctm_eta] and    *)
(* the neutral-app rules carry [Reflect]/[Apply_val]/[Vapp] premises.  Two  *)
(* facts force WELL-SCOPEDNESS SIDE-CONDITIONS ([ne_below_*]) on those      *)
(* constructors:                                                            *)
(*  (1) ne_below transport [ne_below f -> ne_below g] across [ctm_eta] is   *)
(*      UNPROVABLE structurally: [g] relates to [f] only through the BETA-  *)
(*      REDUCED applications [fa]/[ga] ([Vapp] reduces [vLam]), and [Vapp]  *)
(*      cannot be inverted backward to recover [ne_below g].                *)
(*  (2) renaming the [Reflect] premise needs [Reflect_ren], whose signature *)
(*      DEMANDS [ne_below_ty m T] and [ne_below_ne m n].                    *)
(* Carrying [ne_below] side-conditions discharges both -- and crucially     *)
(* keeps [conv_*_eta] a STANDALONE inductive: [ne_below] premises (not full *)
(* typing) suffice for the metatheory, so we do NOT need to fuse the        *)
(* conversion into the [has_svalty]/[wf_neutral] mutual block (the earlier  *)
(* UPDATE-j instinct).  This file validates: (i) the constructor set type-  *)
(* checks + positivity OK, (ii) [conv_ty_eta_ne_below] (the forward         *)
(* transport [n_conv] consumers at RenTyping:263/425 need).                 *)
(* ===================================================================== *)

Section ConvEta.
  Notation term := (@term string).
  Notation ext F Ge := (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge).

  Unset Elimination Schemes.
  (* type-code conversion (paper ConvTy): structural congruence; eta lives at
     the term level inside neutral arguments. *)
  Inductive conv_ty_eta : senv -> sval -> sval -> Prop :=
  | cte_nat   : forall Ge, conv_ty_eta Ge vNat vNat
  | cte_empty : forall Ge, conv_ty_eta Ge vEmpty vEmpty
  | cte_pi    : forall Ge F F' B B',
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_ty_eta Ge (vPi F B) (vPi F' B')
  | cte_piI   : forall Ge F F' B B',
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_ty_eta Ge (vPiI F B) (vPiI F' B')
  | cte_ne    : forall Ge n n' r l,
      conv_ne_eta Ge (dU r l) n n' ->
      conv_ty_eta Ge (vNe n) (vNe n')
  (* type-DIRECTED value conversion (paper ConvTm): structural at base/code,
     ETA-expanding at relevant Pi (the rule that makes it eta-closed). *)
  with conv_tm_eta : senv -> svalty -> sval -> sval -> Prop :=
  | ctm_ne_nat   : forall Ge n n', conv_ne_eta Ge (dEl vNat) n n' ->
      conv_tm_eta Ge (dEl vNat) (vNe n) (vNe n')
  | ctm_ne_empty : forall Ge n n', conv_ne_eta Ge (dEl vEmpty) n n' ->
      conv_tm_eta Ge (dEl vEmpty) (vNe n) (vNe n')
  | ctm_ne_el    : forall Ge c n n', conv_ne_eta Ge (dEl (vNe c)) n n' ->
      conv_tm_eta Ge (dEl (vNe c)) (vNe n) (vNe n')
  | ctm_zero  : forall Ge, conv_tm_eta Ge (dEl vNat) vZero vZero
  | ctm_suc   : forall Ge v v', conv_tm_eta Ge (dEl vNat) v v' ->
      conv_tm_eta Ge (dEl vNat) (vSuc v) (vSuc v')
  | ctm_code  : forall Ge r l c c', conv_ty_eta Ge c c' ->
      conv_tm_eta Ge (dU r l) c c'
  (* ETA at relevant Pi.  [f],[g] are arbitrary values of [vPi F B]; relate
     their eta-expansions ([fa],[ga] = [f]/[g] applied to the reflected bound
     var [ARG]) at the instantiated codomain [B'].  SIDE-CONDITIONS [nbF],
     [nbf],[nbg] carry scopedness (see header (1)+(2)). *)
  | ctm_eta   : forall Ge F B f g ARG B' fa ga,
      ne_below_val (length Ge) F ->
      ne_below_val (length Ge) f ->
      ne_below_val (length Ge) g ->
      Reflect (S (length Ge)) (dEl (shift_val 0 1 F)) (nVar 0) ARG ->
      Apply_val (S (length Ge)) (ARG :: id_list (S (length Ge)))
                (shift_val 1 1 B) B' ->
      Vapp (S (length Ge)) (shift_val 0 1 F) (shift_val 1 1 B)
           (shift_val 0 1 f) ARG fa ->
      Vapp (S (length Ge)) (shift_val 0 1 F) (shift_val 1 1 B)
           (shift_val 0 1 g) ARG ga ->
      conv_tm_eta (ext F Ge) (dEl B') fa ga ->
      conv_tm_eta Ge (dEl (vPi F B)) f g
  (* proof-irrelevant Pi: deferred (Ph6).  Neutral/LamI structural for now. *)
  | ctm_piI_ne : forall Ge F B n n', conv_ne_eta Ge (dEl (vPiI F B)) n n' ->
      conv_tm_eta Ge (dEl (vPiI F B)) (vNe n) (vNe n')
  | ctm_lamI   : forall Ge F B b b',
      conv_tm_eta (ext F Ge) (dEl B) b b' ->
      conv_tm_eta Ge (dEl (vPiI F B)) (vLamI b) (vLamI b')
  (* neutral conversion (paper ConvNe): args related by conv_tm_eta at the
     annotation type (this is where eta enters type codes). *)
  with conv_ne_eta : senv -> svalty -> neutral -> neutral -> Prop :=
  | cne_eta_var : forall Ge k T, nth_error Ge k = Some T ->
      conv_ne_eta Ge T (nVar k) (nVar k)
  | cne_eta_emptyrec : forall Ge rA lA A A' s s',
      conv_ty_eta Ge A A' ->
      conv_ne_eta Ge (dEl vEmpty) s s' ->
      conv_ne_eta Ge (dEl A) (nEmptyrec rA lA A s) (nEmptyrec rA lA A' s')
  | cne_eta_app : forall Ge f f' F F' B B' a a' Bres,
      conv_ne_eta Ge (dEl (vPi F B)) f f' ->
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_tm_eta Ge (dEl F) a a' ->
      Apply_val (length Ge) (a :: id_list (length Ge)) B Bres ->
      conv_ne_eta Ge (dEl Bres) (nApp f F B a) (nApp f' F' B' a')
  | cne_eta_appI : forall Ge f f' F F' B B' a a' Bres,
      conv_ne_eta Ge (dEl (vPiI F B)) f f' ->
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_tm_eta Ge (dEl F) a a' ->
      Apply_val (length Ge) (a :: id_list (length Ge)) B Bres ->
      conv_ne_eta Ge (dEl Bres) (nAppI f F B a) (nAppI f' F' B' a').
  Set Elimination Schemes.

  Scheme conv_ty_eta_ind := Induction for conv_ty_eta Sort Prop
    with conv_tm_eta_ind := Induction for conv_tm_eta Sort Prop
    with conv_ne_eta_ind := Induction for conv_ne_eta Sort Prop.
  Combined Scheme conv_eta_mutind from
    conv_ty_eta_ind, conv_tm_eta_ind, conv_ne_eta_ind.

  (* Sanity: the constructor set is well-formed and the base diagonal works. *)
  Definition cte_sanity1 Ge : conv_ty_eta Ge vNat vNat := cte_nat Ge.

  (* The Pi typing-bridge SHAPE (what n_conv needs for the right member):
     conv_ty_eta at a Pi follows from domain + codomain-under-binder conv. *)
  Definition cte_pi_bridge Ge F F' B B'
    (hF : conv_ty_eta Ge F F')
    (hB : conv_ty_eta (ext F Ge) B B')
    : conv_ty_eta Ge (vPi F B) (vPi F' B')
    := cte_pi hF hB.

End ConvEta.

(* The [Vapp] projection of [Apply_ne_below] (RenSubst), not exported there. *)
Definition Vapp_ne_below := snd (fst Apply_ne_below).

(* ===================================================================== *)
(* KEY METATHEORY #1 : forward ne_below transport.  This is what the        *)
(* [n_conv] cases of [typing_ne_below]/[ren_typing] (RenTyping.v:263/425)   *)
(* consume.  With the side-conditions in place every constructor either     *)
(* recurses structurally (reading [ne_below] of all sub-terms off the LEFT  *)
(* member) or reads the result's scopedness directly off a side-condition   *)
(* ([ctm_eta]).                                                             *)
(* ===================================================================== *)
Lemma conv_eta_ne_below :
  (forall Ge A B, conv_ty_eta Ge A B ->
     ne_below_val (length Ge) A -> ne_below_val (length Ge) B)
  /\ (forall Ge T a b, conv_tm_eta Ge T a b ->
     ne_below_ty (length Ge) T -> ne_below_val (length Ge) a ->
     ne_below_val (length Ge) b)
  /\ (forall Ge T n m, conv_ne_eta Ge T n m ->
     ne_below_ty (length Ge) T -> ne_below_ne (length Ge) n ->
     ne_below_ne (length Ge) m).
Proof.
  apply conv_eta_mutind.
  (* ---- conv_ty_eta ---- *)
  - (* cte_nat *) intros Ge HA. exact HA.
  - (* cte_empty *) intros Ge HA. exact HA.
  - (* cte_pi *) intros Ge F F' B B' _ IHF _ IHB HA.
    cbn [ne_below_val] in HA |- *. destruct HA as [HF HB].
    split.
    + apply IHF; exact HF.
    + pose proof (IHB) as IHB'.
      cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HB.
  - (* cte_piI *) intros Ge F F' B B' _ IHF _ IHB HA.
    cbn [ne_below_val] in HA |- *. destruct HA as [HF HB].
    split.
    + apply IHF; exact HF.
    + pose proof (IHB) as IHB'.
      cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HB.
  - (* cte_ne *) intros Ge n n' r l _ IH HA.
    cbn [ne_below_val] in HA |- *.
    apply (IH I HA).
  (* ---- conv_tm_eta ---- *)
  - (* ctm_ne_nat *) intros Ge n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH I Ha).
  - (* ctm_ne_empty *) intros Ge n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH I Ha).
  - (* ctm_ne_el *) intros Ge c n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH HT Ha).
  - (* ctm_zero *) intros Ge HT Ha. exact Ha.
  - (* ctm_suc *) intros Ge v v' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH I Ha).
  - (* ctm_code *) intros Ge r l c c' _ IH HT Ha.
    cbn [ne_below_ty] in *. apply IH; exact Ha.
  - (* ctm_eta -- result scopedness is the side-condition [nbg]. *)
    intros Ge F B f g ARG B' fa ga _nbF _nbf nbg _ _ _ _ _ _ HT Hf.
    exact nbg.
  - (* ctm_piI_ne *) intros Ge F B n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH HT Ha).
  - (* ctm_lamI *) intros Ge F B b b' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *.
    pose proof (IH) as IH'. cbn [length] in IH'; rewrite length_map in IH'.
    apply IH'; [ exact (proj2 HT) | exact Ha ].
  (* ---- conv_ne_eta ---- *)
  - (* cne_eta_var *) intros Ge k T He HT Hn. exact Hn.
  - (* cne_eta_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs HT Hn.
    cbn [ne_below_ne ne_below_ty] in *. destruct Hn as [HA Hs].
    split; [ apply (IHA HA) | apply (IHs I Hs) ].
  - (* cne_eta_app *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn.
    cbn [ne_below_ne] in Hn |- *. destruct Hn as (Hnf & HnF & HnB & Hna).
    repeat split.
    + (* f' *) apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf ].
    + (* F' *) apply (IHF HnF).
    + (* B' *) pose proof (IHB) as IHB'. cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HnB.
    + (* a' *) apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna ].
  - (* cne_eta_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn.
    cbn [ne_below_ne] in Hn |- *. destruct Hn as (Hnf & HnF & HnB & Hna).
    repeat split.
    + apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf ].
    + apply (IHF HnF).
    + pose proof (IHB) as IHB'. cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HnB.
    + apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna ].
Qed.

Definition conv_ty_eta_ne_below : forall Ge A B, conv_ty_eta Ge A B ->
    ne_below_val (length Ge) A -> ne_below_val (length Ge) B :=
  proj1 conv_eta_ne_below.

(* The [Vapp] shift projection of the commutation engine (Preservation). *)
Definition Vapp_shift := snd (fst Apply_shift_commute).

(* ===================================================================== *)
(* KEY METATHEORY #2 : stability under SHIFT (binder insertion at cutoff   *)
(* [c]).  Mirrors [weaken_typing] (Preservation.v:578); the [ctm_eta] case  *)
(* is [t_lam_eta]'s shift case PLUS the two [Vapp] eta-application premises  *)
(* (shifted via [Vapp_shift] + the same comm lemmas).  Consumed by the      *)
(* [n_conv] case of [shift_typing] (Preservation.v:661,                     *)
(* [conv_nf_shift] -> [conv_ty_eta_shift]).                                 *)
(* ===================================================================== *)
Lemma conv_eta_shift :
  (forall Ge A B, conv_ty_eta Ge A B ->
     forall c T0, c <= length Ge ->
       conv_ty_eta (wk_ctx c T0 Ge) (shift_val c 1 A) (shift_val c 1 B))
  /\ (forall Ge T a b, conv_tm_eta Ge T a b ->
     forall c T0, c <= length Ge ->
       conv_tm_eta (wk_ctx c T0 Ge) (shift_ty c 1 T)
                   (shift_val c 1 a) (shift_val c 1 b))
  /\ (forall Ge T n m, conv_ne_eta Ge T n m ->
     forall c T0, c <= length Ge ->
       conv_ne_eta (wk_ctx c T0 Ge) (shift_ty c 1 T)
                   (shift_ne c 1 n) (shift_ne c 1 m)).
Proof.
  apply conv_eta_mutind.
  (* ---- conv_ty_eta ---- *)
  - (* cte_nat *) intros Ge c T0 Hc. cbn [shift_val]. apply cte_nat.
  - (* cte_empty *) intros Ge c T0 Hc. cbn [shift_val]. apply cte_empty.
  - (* cte_pi *) intros Ge F F' B B' _ IHF _ IHB c T0 Hc. cbn [shift_val].
    apply cte_pi.
    + exact (IHF c T0 Hc).
    + pose proof (IHB (S c) (shift_ty 0 1 T0)
                    ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
      rewrite wk_ctx_under_binder in IH. cbn [shift_ty] in IH. exact IH.
  - (* cte_piI *) intros Ge F F' B B' _ IHF _ IHB c T0 Hc. cbn [shift_val].
    apply cte_piI.
    + exact (IHF c T0 Hc).
    + pose proof (IHB (S c) (shift_ty 0 1 T0)
                    ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
      rewrite wk_ctx_under_binder in IH. cbn [shift_ty] in IH. exact IH.
  - (* cte_ne *) intros Ge n n' r l _ IH c T0 Hc. cbn [shift_val].
    eapply cte_ne. pose proof (IH c T0 Hc) as IH'. cbn [shift_ty] in IH'. exact IH'.
  (* ---- conv_tm_eta ---- *)
  - (* ctm_ne_nat *) intros Ge n n' _ IH c T0 Hc. cbn [shift_val shift_ty].
    apply ctm_ne_nat. pose proof (IH c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
  - (* ctm_ne_empty *) intros Ge n n' _ IH c T0 Hc. cbn [shift_val shift_ty].
    apply ctm_ne_empty. pose proof (IH c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
  - (* ctm_ne_el *) intros Ge cc n n' _ IH c T0 Hc. cbn [shift_val shift_ty].
    apply ctm_ne_el. pose proof (IH c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
  - (* ctm_zero *) intros Ge c T0 Hc. cbn [shift_val shift_ty]. apply ctm_zero.
  - (* ctm_suc *) intros Ge v v' _ IH c T0 Hc. cbn [shift_val shift_ty].
    apply ctm_suc. pose proof (IH c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
  - (* ctm_code *) intros Ge r l cc cc' _ IH c T0 Hc. cbn [shift_val shift_ty].
    apply ctm_code. exact (IH c T0 Hc).
  - (* ctm_eta *)
    intros Ge F B f g ARG B' fa ga nbF nbf nbg HR Hap Hfa Hga _Hcod IHcod c T0 Hc.
    cbn [shift_val shift_ty].
    assert (HL : length (wk_ctx c T0 Ge) = S (length Ge)) by (apply wk_ctx_length; exact Hc).
    eapply ctm_eta.
    + (* nbF *) rewrite HL. apply ne_below_shift_val. exact nbF.
    + (* nbf *) rewrite HL. apply ne_below_shift_val. exact nbf.
    + (* nbg *) rewrite HL. apply ne_below_shift_val. exact nbg.
    + (* Reflect *) rewrite HL.
      pose proof (@Reflect_weaken _ _ _ _ HR (S c) ltac:(Lia.lia)) as IH.
      cbn [shift_ty shift_val shift_ne] in IH.
      rewrite shift_val_comm0. exact IH.
    + (* Apply_val *) rewrite HL.
      pose proof (Apply_val_shiftc Hap
                    (@ShiftSub_beta (S (length Ge)) ARG (S c) ltac:(Lia.lia))
                    ltac:(Lia.lia)) as IH.
      rewrite (fst (snd shift_shift_comm) B 1 (S c) ltac:(Lia.lia)). exact IH.
    + (* Vapp fa *) rewrite HL.
      pose proof (@Vapp_shift _ _ _ _ _ _ Hfa (S c) ltac:(Lia.lia)) as IH.
      cbn [shift_val shift_ne] in IH.
      rewrite !shift_val_comm0.
      rewrite (fst (snd shift_shift_comm) B 1 (S c) ltac:(Lia.lia)). exact IH.
    + (* Vapp ga *) rewrite HL.
      pose proof (@Vapp_shift _ _ _ _ _ _ Hga (S c) ltac:(Lia.lia)) as IH.
      cbn [shift_val shift_ne] in IH.
      rewrite !shift_val_comm0.
      rewrite (fst (snd shift_shift_comm) B 1 (S c) ltac:(Lia.lia)). exact IH.
    + (* codomain conv *)
      pose proof (IHcod (S c) (shift_ty 0 1 T0)
                    ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
      rewrite wk_ctx_under_binder in IH. cbn [shift_ty] in IH. exact IH.
  - (* ctm_piI_ne *) intros Ge F B n n' _ IH c T0 Hc. cbn [shift_val shift_ty].
    apply ctm_piI_ne. pose proof (IH c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
  - (* ctm_lamI *) intros Ge F B b b' _ IH c T0 Hc. cbn [shift_val shift_ty].
    apply ctm_lamI.
    pose proof (IH (S c) (shift_ty 0 1 T0)
                  ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH'.
    rewrite wk_ctx_under_binder in IH'. cbn [shift_ty] in IH'. exact IH'.
  (* ---- conv_ne_eta ---- *)
  - (* cne_eta_var *) intros Ge k T He c T0 Hc. cbn -[Nat.ltb shift_ty].
    destruct (Nat.ltb k c) eqn:E; cbn -[Nat.ltb shift_ty].
    + apply ltb_true in E. apply cne_eta_var.
      exact (@wk_ctx_nth_lt c T0 Ge k T E Hc He).
    + apply ltb_false in E. replace (k + 1) with (S k) by Lia.lia.
      apply cne_eta_var. exact (@wk_ctx_nth_ge c T0 Ge k T E Hc He).
  - (* cne_eta_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs c T0 Hc.
    cbn [shift_ne shift_ty shift_val].
    apply cne_eta_emptyrec.
    + exact (IHA c T0 Hc).
    + pose proof (IHs c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
  - (* cne_eta_app *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap c T0 Hc.
    cbn [shift_ne shift_ty shift_val].
    eapply cne_eta_app.
    + (* f *) pose proof (IHf c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
    + (* F *) exact (IHF c T0 Hc).
    + (* B *) pose proof (IHB (S c) (shift_ty 0 1 T0)
                    ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH'.
      rewrite wk_ctx_under_binder in IH'. cbn [shift_ty] in IH'. exact IH'.
    + (* a *) pose proof (IHa c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
    + (* Apply_val Bres *) rewrite (@wk_ctx_length c T0 Ge Hc).
      exact (Apply_val_shiftc Hap (@ShiftSub_beta (length Ge) a c Hc) Hc).
  - (* cne_eta_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap c T0 Hc.
    cbn [shift_ne shift_ty shift_val].
    eapply cne_eta_appI.
    + pose proof (IHf c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
    + exact (IHF c T0 Hc).
    + pose proof (IHB (S c) (shift_ty 0 1 T0)
                    ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH'.
      rewrite wk_ctx_under_binder in IH'. cbn [shift_ty] in IH'. exact IH'.
    + pose proof (IHa c T0 Hc) as IH'. cbn [shift_ty shift_val] in IH'. exact IH'.
    + rewrite (@wk_ctx_length c T0 Ge Hc).
      exact (Apply_val_shiftc Hap (@ShiftSub_beta (length Ge) a c Hc) Hc).
Qed.

(* ===================================================================== *)
(* KEY METATHEORY #1b : BACKWARD ne_below transport (right member scoped   *)
(* => left member scoped).  Needed by the [n_conv] case of [ren_typing]    *)
(* (RenTyping.v:425), which currently derives [ne_below A] from [ne_below   *)
(* B] via [conv_nf_sym]+[conv_nf_ne_below]; the eta-closed conversion may    *)
(* not be symmetric (the [cne_eta_app] result type [Bres] is computed from   *)
(* the LEFT arg), so we transport scopedness directly instead.             *)
(* ===================================================================== *)
Lemma conv_eta_ne_below_rev :
  (forall Ge A B, conv_ty_eta Ge A B ->
     ne_below_val (length Ge) B -> ne_below_val (length Ge) A)
  /\ (forall Ge T a b, conv_tm_eta Ge T a b ->
     ne_below_ty (length Ge) T -> ne_below_val (length Ge) b ->
     ne_below_val (length Ge) a)
  /\ (forall Ge T n m, conv_ne_eta Ge T n m ->
     ne_below_ty (length Ge) T -> ne_below_ne (length Ge) m ->
     ne_below_ne (length Ge) n).
Proof.
  apply conv_eta_mutind.
  (* ---- conv_ty_eta ---- *)
  - (* cte_nat *) intros Ge HB. exact HB.
  - (* cte_empty *) intros Ge HB. exact HB.
  - (* cte_pi *) intros Ge F F' B B' _ IHF _ IHB HB0.
    cbn [ne_below_val] in HB0 |- *. destruct HB0 as [HF HB].
    split.
    + apply IHF; exact HF.
    + cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HB.
  - (* cte_piI *) intros Ge F F' B B' _ IHF _ IHB HB0.
    cbn [ne_below_val] in HB0 |- *. destruct HB0 as [HF HB].
    split.
    + apply IHF; exact HF.
    + cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HB.
  - (* cte_ne *) intros Ge n n' r l _ IH HB0.
    cbn [ne_below_val] in HB0 |- *. apply (IH I HB0).
  (* ---- conv_tm_eta ---- *)
  - (* ctm_ne_nat *) intros Ge n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH I Hb).
  - (* ctm_ne_empty *) intros Ge n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH I Hb).
  - (* ctm_ne_el *) intros Ge cc n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH HT Hb).
  - (* ctm_zero *) intros Ge HT Hb. exact Hb.
  - (* ctm_suc *) intros Ge v v' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH I Hb).
  - (* ctm_code *) intros Ge r l cc cc' _ IH HT Hb. cbn [ne_below_ty] in *. apply IH; exact Hb.
  - (* ctm_eta -- left scopedness is the side-condition [nbf]. *)
    intros Ge F B f g ARG B' fa ga nbF nbf _nbg _ _ _ _ _ _ HT Hg. exact nbf.
  - (* ctm_piI_ne *) intros Ge F B n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH HT Hb).
  - (* ctm_lamI *) intros Ge F B b b' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *.
    cbn [length] in IH; rewrite length_map in IH. apply IH; [ exact (proj2 HT) | exact Hb ].
  (* ---- conv_ne_eta ---- *)
  - (* cne_eta_var *) intros Ge k T He HT Hm. exact Hm.
  - (* cne_eta_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs HT Hm.
    cbn [ne_below_ne ne_below_ty] in *. destruct Hm as [HA Hs].
    split; [ apply (IHA HA) | apply (IHs I Hs) ].
  - (* cne_eta_app -- derive unprimed F,B,a first, then f (which needs the
       unprimed type index). *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hm.
    cbn [ne_below_ne] in Hm |- *. destruct Hm as (Hnf' & HnF' & HnB' & Hna').
    assert (HnF : ne_below_val (length Ge) F) by (apply (IHF HnF')).
    assert (HnB : ne_below_val (S (length Ge)) B).
    { cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HnB'. }
    assert (Hna : ne_below_val (length Ge) a)
      by (apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna' ]).
    repeat split.
    + apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf' ].
    + exact HnF.
    + exact HnB.
    + exact Hna.
  - (* cne_eta_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hm.
    cbn [ne_below_ne] in Hm |- *. destruct Hm as (Hnf' & HnF' & HnB' & Hna').
    assert (HnF : ne_below_val (length Ge) F) by (apply (IHF HnF')).
    assert (HnB : ne_below_val (S (length Ge)) B).
    { cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HnB'. }
    assert (Hna : ne_below_val (length Ge) a)
      by (apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna' ]).
    repeat split.
    + apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf' ].
    + exact HnF.
    + exact HnB.
    + exact Hna.
Qed.

(* Consumer-facing projections (names match the conv_nf_* they replace). *)
Definition conv_ty_eta_shift : forall Ge A B, conv_ty_eta Ge A B ->
    forall c T0, c <= length Ge ->
      conv_ty_eta (wk_ctx c T0 Ge) (shift_val c 1 A) (shift_val c 1 B) :=
  proj1 conv_eta_shift.
Definition conv_ty_eta_ne_below_rev : forall Ge A B, conv_ty_eta Ge A B ->
    ne_below_val (length Ge) B -> ne_below_val (length Ge) A :=
  proj1 conv_eta_ne_below_rev.

(* ===================================================================== *)
(* STATUS (UPDATE 2026-06-06k).  VALIDATED in this prototype, all axiom-    *)
(* free, against the REAL Apply/Reflect/Vapp metatheory:                    *)
(*   * inductive conv_ty_eta/conv_tm_eta/conv_ne_eta (with ne_below side-   *)
(*     conditions on ctm_eta) -- type-checks, positivity OK.               *)
(*   * conv_ty_eta_ne_below      (fwd transport)  -> RenTyping.v:263.      *)
(*   * conv_ty_eta_ne_below_rev  (bwd transport)  -> RenTyping.v:425.      *)
(*   * conv_ty_eta_shift         (binder insert)  -> Preservation.v:661.   *)
(*   * conv_ty_eta_ren           (renaming)       -> RenTyping.v:428.      *)
(*     (needed the new helper [ne_below_ren_val] -- ne_below transports     *)
(*      along a ren_ok renaming -- since t_lam_eta has no ne_below side-     *)
(*      conds so ren_typing never needed it.)                              *)
(* The METATHEORY is COMPLETE: switching Typing.v's n_conv from conv_nf to  *)
(* conv_ty_eta can be re-greened with these four lemmas.  NEXT = mechanical *)
(* core port (move inductive below Typing, swap n_conv, migrate the         *)
(* Preservation:661 + RenTyping:263/425/428 consumers), then the HIGH       *)
(* "reify produces conv_ty_eta" lemma + LogRel2Sym diagonal + soundness.    *)
(* ===================================================================== *)

(* NEW HELPER ren needs (t_lam_eta has no ne_below side-conds, so ren_typing
   never needed this): ne_below transports along a ren_ok renaming. *)
Definition Vapp_ren := snd (fst Apply_ren_commute).

Lemma ne_below_ren_val : forall v N rho m2,
    ne_below_val N v -> ren_ok rho N m2 -> ne_below_val m2 (ren_val rho v).
Proof.
  intros v N rho m2 Hv Hok.
  refine (Apply_val_ne_below (ren_is_Apply_val v m2 rho) Hv _).
  intros k Hk. rewrite ren_sub_nth. cbn [ne_below_val ne_below_ne].
  apply Hok; exact Hk.
Qed.

(* The [Vapp] ne_below projection (RenSubst Apply_ne_below). *)
Definition Vapp_ne_below' := snd (fst Apply_ne_below).

(* ===================================================================== *)
(* KEY METATHEORY #3 : stability under RENAMING.  Mirrors [ren_typing]     *)
(* (RenTyping.v); the [ctm_eta] case = [t_lam_eta]'s ren case + two         *)
(* [Vapp_ren] premises + re-establishing the ne_below side-conds over the   *)
(* target ctx via [ne_below_ren_val].  Consumed by [ren_typing]'s [n_conv]  *)
(* case (RenTyping.v:428, [conv_nf_ren] -> [conv_ty_eta_ren]).              *)
(* ===================================================================== *)
Lemma conv_eta_ren :
  (forall Ge A B, conv_ty_eta Ge A B ->
     ne_below_val (length Ge) A -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       conv_ty_eta Ge' (ren_val rho A) (ren_val rho B))
  /\ (forall Ge T a b, conv_tm_eta Ge T a b ->
     ne_below_ty (length Ge) T -> ne_below_val (length Ge) a -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       conv_tm_eta Ge' (ren_ty rho T) (ren_val rho a) (ren_val rho b))
  /\ (forall Ge T n m, conv_ne_eta Ge T n m ->
     ne_below_ty (length Ge) T -> ne_below_ne (length Ge) n -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       conv_ne_eta Ge' (ren_ty rho T) (ren_ne rho n) (ren_ne rho m)).
Proof.
  apply conv_eta_mutind.
  (* ---- conv_ty_eta ---- *)
  - (* cte_nat *) intros Ge HA Hctx Ge' rho Hren Hok. cbn [ren_val]. apply cte_nat.
  - (* cte_empty *) intros Ge HA Hctx Ge' rho Hren Hok. cbn [ren_val]. apply cte_empty.
  - (* cte_pi *) intros Ge F F' B B' _ IHF _ IHB HA Hctx Ge' rho Hren Hok.
    cbn [ren_val] in *. destruct HA as [HFn HBn]. apply cte_pi.
    + exact (IHF HFn Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ cbn [length]; rewrite length_map; exact HBn
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFn ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* cte_piI *) intros Ge F F' B B' _ IHF _ IHB HA Hctx Ge' rho Hren Hok.
    cbn [ren_val] in *. destruct HA as [HFn HBn]. apply cte_piI.
    + exact (IHF HFn Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ cbn [length]; rewrite length_map; exact HBn
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFn ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* cte_ne *) intros Ge n n' r l _ IH HA Hctx Ge' rho Hren Hok.
    cbn [ren_val] in *. eapply cte_ne.
    pose proof (IH I HA Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty] in IH'. exact IH'.
  (* ---- conv_tm_eta ---- *)
  - (* ctm_ne_nat *) intros Ge n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_ne_nat.
    pose proof (IH I Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_ne_empty *) intros Ge n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_ne_empty.
    pose proof (IH I Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_ne_el *) intros Ge cc n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_ne_el.
    pose proof (IH HT Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_zero *) intros Ge HT Ha Hctx Ge' rho Hren Hok. cbn [ren_val ren_ty]. apply ctm_zero.
  - (* ctm_suc *) intros Ge v v' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_suc.
    pose proof (IH I Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_code *) intros Ge r l cc cc' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_code. exact (IH Ha Hctx Ge' rho Hren Hok).
  - (* ctm_eta *)
    intros Ge F B f g ARG B' fa ga nbF nbf nbg HR Hap Hfa Hga _Hcod IHcod HT Hf Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. cbn [ne_below_ty ne_below_val] in HT. destruct HT as [HFt HBt].
    assert (Hokc : ren_ok rho (length Ge) (length Ge'))
      by (apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]).
    assert (HARG : ne_below_val (S (length Ge)) ARG)
      by (eapply Reflect_scoped;
          [ exact HR | cbn [ne_below_ty]; apply ne_below_shift_val; exact HFt
          | cbn [ne_below_ne]; Lia.lia ]).
    assert (Hsf : ne_below_val (S (length Ge)) (shift_val 0 1 f))
      by (apply ne_below_shift_val; exact nbf).
    assert (Hsg : ne_below_val (S (length Ge)) (shift_val 0 1 g))
      by (apply ne_below_shift_val; exact nbg).
    assert (HsF : ne_below_val (S (length Ge)) (shift_val 0 1 F))
      by (apply ne_below_shift_val; exact HFt).
    assert (HB' : ne_below_val (S (length Ge)) B')
      by (eapply Apply_val_ne_below;
          [ exact Hap | apply ne_below_shift_val; exact HBt
          | apply sub_below_beta; [ Lia.lia | exact HARG ] ]).
    assert (HsB : ne_below_val (S (S (length Ge))) (shift_val 1 1 B))
      by (apply ne_below_shift_val; exact HBt).
    assert (Hfanb : ne_below_val (S (length Ge)) fa)
      by (exact (Vapp_ne_below' Hfa Hsf HARG HsF HsB)).
    eapply ctm_eta.
    + (* nbF' *) eapply ne_below_ren_val; [ exact nbF | exact Hokc ].
    + (* nbf' *) eapply ne_below_ren_val; [ exact nbf | exact Hokc ].
    + (* nbg' *) eapply ne_below_ren_val; [ exact nbg | exact Hokc ].
    + (* Reflect *)
      pose proof (Reflect_ren HR
                    ltac:(cbn [ne_below_ty]; apply ne_below_shift_val; exact HFt)
                    ltac:(cbn [ne_below_ne]; Lia.lia)
                    (ren_ok_up Hok)) as HRr.
      cbn [ren_ty ren_ne ren_val] in HRr.
      rewrite renm_up_0, ren_shift_comm0_val in HRr. exact HRr.
    + (* Apply_val *)
      pose proof (@Apply_val_ren_commute
                    (S (length Ge)) (ARG :: id_list (S (length Ge)))
                    (shift_val 1 1 B) B' Hap
                    (S (S (length Ge)))
                    ltac:(apply ne_below_shift_val; exact HBt)
                    ltac:(apply sub_below_beta; [ Lia.lia | exact HARG ])
                    (S (length Ge')) (up_renl (up_renl rho)) (up_renl rho)
                    (ren_val (up_renl rho) ARG :: id_list (S (length Ge')))
                    (ren_ok_up Hok)
                    ltac:(eapply RenShSc_beta;
                            [ Lia.lia | apply ren_ok_le with (N := S (S (length Ge))); [ exact (ren_ok_up Hok) | Lia.lia ]
                            | apply ren_is_Apply_val ])) as Hapr.
      rewrite ren_shift_comm1_val in Hapr. exact Hapr.
    + (* Vapp fa *)
      pose proof (@Vapp_ren _ _ _ _ _ _ Hfa (S (length Ge)) Hsf HARG ltac:(Lia.lia)
                    (S (length Ge')) (up_renl rho) (ren_ok_up Hok)) as Hfar.
      cbn [ren_val] in Hfar.
      rewrite !ren_shift_comm0_val, ren_shift_comm1_val in Hfar. exact Hfar.
    + (* Vapp ga *)
      pose proof (@Vapp_ren _ _ _ _ _ _ Hga (S (length Ge)) Hsg HARG ltac:(Lia.lia)
                    (S (length Ge')) (up_renl rho) (ren_ok_up Hok)) as Hgar.
      cbn [ren_val] in Hgar.
      rewrite !ren_shift_comm0_val, ren_shift_comm1_val in Hgar. exact Hgar.
    + (* codomain conv *)
      eapply IHcod;
        [ cbn [ne_below_ty length]; rewrite length_map; exact HB'
        | cbn [length]; rewrite length_map; exact Hfanb
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFt ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* ctm_piI_ne *) intros Ge F B n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_piI_ne.
    pose proof (IH HT Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_lamI *) intros Ge F B b b' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. cbn [ne_below_ty ne_below_val] in HT. destruct HT as [HFt HBt].
    cbn [ne_below_val] in Ha.
    apply ctm_lamI.
    eapply IH;
      [ cbn [ne_below_ty length]; rewrite length_map; exact HBt
      | cbn [length]; rewrite length_map; exact Ha
      | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFt ]
      | apply ren_ctx_up_dEl; exact Hren
      | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  (* ---- conv_ne_eta ---- *)
  - (* cne_eta_var *) intros Ge k T He HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne]. apply cne_eta_var. exact (Hren k T He).
  - (* cne_eta_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty ren_val] in *. cbn [ne_below_ne] in Hn. destruct Hn as [HnA Hns].
    apply cne_eta_emptyrec.
    + exact (IHA HnA Hctx Ge' rho Hren Hok).
    + pose proof (IHs I Hns Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* cne_eta_app *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty ren_val] in *. cbn [ne_below_ne] in Hn.
    destruct Hn as (Hnf & HnF & HnB & Hna).
    eapply cne_eta_app.
    + (* f *) pose proof (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ])
                            Hnf Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + (* F *) exact (IHF HnF Hctx Ge' rho Hren Hok).
    + (* B *) eapply IHB;
        [ cbn [length]; rewrite length_map; exact HnB
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HnF ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
    + (* a *) pose proof (IHa ltac:(cbn [ne_below_ty]; exact HnF) Hna Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + (* Apply Bres *)
      pose proof (@Apply_val_ren_commute
                    (length Ge) (a :: id_list (length Ge)) B Bres Hap
                    (S (length Ge)) HnB
                    ltac:(apply sub_below_beta; [ Lia.lia | exact Hna ])
                    (length Ge') (up_renl rho) rho
                    (ren_val rho a :: id_list (length Ge'))
                    ltac:(apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ])
                    ltac:(eapply RenShSc_beta;
                            [ Lia.lia | apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]
                            | apply ren_is_Apply_val ])) as Hapr. exact Hapr.
  - (* cne_eta_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty ren_val] in *. cbn [ne_below_ne] in Hn.
    destruct Hn as (Hnf & HnF & HnB & Hna).
    eapply cne_eta_appI.
    + pose proof (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ])
                            Hnf Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + exact (IHF HnF Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ cbn [length]; rewrite length_map; exact HnB
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HnF ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
    + pose proof (IHa ltac:(cbn [ne_below_ty]; exact HnF) Hna Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + pose proof (@Apply_val_ren_commute
                    (length Ge) (a :: id_list (length Ge)) B Bres Hap
                    (S (length Ge)) HnB
                    ltac:(apply sub_below_beta; [ Lia.lia | exact Hna ])
                    (length Ge') (up_renl rho) rho
                    (ren_val rho a :: id_list (length Ge'))
                    ltac:(apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ])
                    ltac:(eapply RenShSc_beta;
                            [ Lia.lia | apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]
                            | apply ren_is_Apply_val ])) as Hapr. exact Hapr.
Qed.

Definition conv_ty_eta_ren : forall Ge A B, conv_ty_eta Ge A B ->
    ne_below_val (length Ge) A -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      conv_ty_eta Ge' (ren_val rho A) (ren_val rho B) :=
  proj1 conv_eta_ren.
