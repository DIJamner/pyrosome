Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply ApplyLemmas Typing Preservation.
Import Core.Notations.

(* ===================================================================== *)
(* Totality-free substitution algebra needed by the reducibility closure   *)
(* lemmas (Milestone 1).  Everything here is structural (plain induction    *)
(* on the value / on the [Apply] derivation), independent of the            *)
(* normalization / logical-relation argument.                               *)
(*                                                                          *)
(*   Part A : scoping        — well-typed values are [ne_below]-scoped.      *)
(*   Part B : apply = shift   — applying the renaming substitution [shsub]   *)
(*                              equals the cutoff shift (relational form).   *)
(*   Part C : [wf_ssub_wkn]   — the weakening substitution is well-typed.    *)
(*   Part D : Apply composition + [wf_ssub_snoc] / [wf_ssub_comp].           *)
(* ===================================================================== *)

(* ===================================================================== *)
(* Part A : well-typed values / neutrals are scoped.                       *)
(* ===================================================================== *)

Lemma typing_scoped :
  (forall Ge v T, has_svalty Ge v T -> ne_below_val (length Ge) v)
  * (forall Ge n T, wf_neutral Ge n T -> ne_below_ne (length Ge) n).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => ne_below_val (length Ge) v)
    (fun Ge n T _ => ne_below_ne (length Ge) n)
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn. exact IHn.
  - (* t_zero *) intros Ge. exact I.
  - (* t_suc *) intros Ge v hv IHv. exact IHv.
  - (* t_Nat *) intros; exact I.
  - (* t_Empty *) intros; exact I.
  - (* t_Pi *) intros Ge F B rF lF rB lB r l hF IHF hB IHB. cbn. split.
    + exact IHF.
    + cbn [length] in IHB. rewrite length_map in IHB. exact IHB.
  - (* t_PiI *) intros Ge F B rF lF rB lB r l hF IHF hB IHB. cbn. split.
    + exact IHF.
    + cbn [length] in IHB. rewrite length_map in IHB. exact IHB.
  - (* t_lam *) intros Ge F B b hb IHb. cbn.
    cbn [length] in IHb. rewrite length_map in IHb. exact IHb.
  - (* t_lamI *) intros Ge F B b hb IHb. cbn.
    cbn [length] in IHb. rewrite length_map in IHb. exact IHb.
  - (* n_var *) intros Ge k T He. cbn.
    apply (proj1 (nth_error_Some Ge k)). rewrite He. discriminate.
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr. cbn. split; assumption.
  - (* n_app *) intros Ge f F B a B' hf IHf ha IHa Hap. cbn. split; assumption.
  - (* n_appI *) intros Ge f F B a B' hf IHf ha IHa Hap. cbn. split; assumption.
Qed.

Definition has_svalty_scoped Ge v T (H : has_svalty Ge v T) := fst typing_scoped Ge v T H.
Definition wf_neutral_scoped Ge n T (H : wf_neutral Ge n T) := snd typing_scoped Ge n T H.

(* ===================================================================== *)
(* Part B : applying the renaming substitution [shsub c n] = shifting at    *)
(* cutoff [c].  [shsub c n] reads variable [k] (in range) to [vNe (nVar     *)
(* (sh c k))]; with [c = 0] this is the weakening substitution [wkn_list].  *)
(* ===================================================================== *)

Lemma nth_error_seq_some : forall len start k,
    k < len -> nth_error (seq start len) k = Some (start + k).
Proof.
  induction len as [|len IH]; intros start k Hk; [ Lia.lia | ].
  cbn [seq]. destruct k as [|k].
  - cbn [nth_error]. f_equal. Lia.lia.
  - cbn [nth_error]. rewrite IH by Lia.lia. f_equal. Lia.lia.
Qed.

Definition shsub (c n : nat) : ssub := map (fun k => vNe (nVar (sh c k))) (seq 0 n).

Lemma shsub_length : forall c n, length (shsub c n) = n.
Proof. intros c n. unfold shsub. rewrite length_map, length_seq. reflexivity. Qed.

Lemma shsub_nth_any : forall c n k d,
    nth_default d (shsub c n) k
    = if Nat.ltb k n then vNe (nVar (sh c k)) else d.
Proof.
  intros c n k d. unfold shsub, nth_default. rewrite nth_error_map.
  destruct (Nat.ltb k n) eqn:E.
  - apply ltb_true in E. rewrite (@nth_error_seq_some n 0 k E). cbn [option_map].
    reflexivity.
  - apply ltb_false in E.
    assert (Hn : nth_error (seq 0 n) k = None)
      by (apply nth_error_None; rewrite length_seq; Lia.lia).
    rewrite Hn. reflexivity.
Qed.

Lemma shsub_nth : forall c n k d,
    k < n -> nth_default d (shsub c n) k = vNe (nVar (sh c k)).
Proof.
  intros c n k d H. rewrite shsub_nth_any, (@ltbT k n H). reflexivity.
Qed.

Lemma shsub_0 : forall n, shsub 0 n = wkn_list n.
Proof.
  intro n. unfold shsub, wkn_list. apply map_ext. intro k. unfold sh. reflexivity.
Qed.

(* Snoc unfolding: [shsub c (S n)] appends the [n]-th renamed variable. *)
Lemma shsub_S : forall c n, shsub c (S n) = shsub c n ++ [vNe (nVar (sh c n))].
Proof.
  intros c n. unfold shsub. rewrite seq_S, map_app. cbn [map]. reflexivity.
Qed.

(* Lifting [shsub] under a binder bumps both the cutoff and the length. *)
Lemma up_shsub : forall n c, up (shsub c n) = shsub (S c) (S n).
Proof.
  induction n as [|n IH]; intro c.
  - reflexivity.
  - rewrite (shsub_S c n), (shsub_S (S c) (S n)).
    unfold up. rewrite map_app. cbn [map]. rewrite app_comm_cons.
    replace (vNe (nVar 0) :: map (shift_val 0 1) (shsub c n))
      with (up (shsub c n)) by reflexivity.
    rewrite IH. f_equal.
    cbn [shift_val shift_ne]. rewrite sh_S, Nat.add_1_r. reflexivity.
Qed.

(* The headline: applying [shsub c m] is the cutoff-[c] shift (on scoped
   inputs).  Used both for the weakening substitution ([c = 0]) and, under
   binders, at higher cutoffs. *)
Lemma Apply_shift_eq :
  (forall T m c, ne_below_ty m T -> Apply_ty (S m) (shsub c m) T (shift_ty c 1 T))
  * ((forall v m c, ne_below_val m v -> Apply_val (S m) (shsub c m) v (shift_val c 1 v))
  *  (forall n m c, ne_below_ne m n -> Apply_ne (S m) (shsub c m) n (vNe (shift_ne c 1 n)))).
Proof.
  apply (sval_mutind
    (fun T => forall m c, ne_below_ty m T -> Apply_ty (S m) (shsub c m) T (shift_ty c 1 T))
    (fun v => forall m c, ne_below_val m v -> Apply_val (S m) (shsub c m) v (shift_val c 1 v))
    (fun n => forall m c, ne_below_ne m n -> Apply_ne (S m) (shsub c m) n (vNe (shift_ne c 1 n)))).
  - (* dU *) intros r l m c _. cbn. apply ap_dU.
  - (* dEl *) intros e IHe m c H. cbn. apply ap_dEl. apply IHe. exact H.
  - (* vNe *) intros n IHn m c H. cbn. apply ap_ne. apply IHn. exact H.
  - (* vZero *) intros m c _. cbn. apply ap_zero.
  - (* vSuc *) intros v IHv m c H. cbn. apply ap_suc. apply IHv. exact H.
  - (* vNat *) intros m c _. cbn. apply ap_nat.
  - (* vEmpty *) intros m c _. cbn. apply ap_empty.
  - (* vPi *) intros F IHF B IHB m c H. cbn [ne_below_val] in H. destruct H as [HF HB].
    cbn [shift_val]. apply ap_pi.
    + apply IHF. exact HF.
    + rewrite up_shsub. apply IHB. exact HB.
  - (* vPiI *) intros F IHF B IHB m c H. cbn [ne_below_val] in H. destruct H as [HF HB].
    cbn [shift_val]. apply ap_piI.
    + apply IHF. exact HF.
    + rewrite up_shsub. apply IHB. exact HB.
  - (* vLam *) intros b IHb m c H. cbn [ne_below_val] in H.
    cbn [shift_val]. apply ap_lam. rewrite up_shsub. apply IHb. exact H.
  - (* vLamI *) intros b IHb m c H. cbn [ne_below_val] in H.
    cbn [shift_val]. apply ap_lamI. rewrite up_shsub. apply IHb. exact H.
  - (* nVar *) intros k m c H. cbn [ne_below_ne] in H. cbn [shift_ne].
    replace (vNe (nVar (if Nat.ltb k c then k else k + 1)))
      with (nth_default (vNe (nVar k)) (shsub c m) k);
      [ apply ap_var | ].
    rewrite (@shsub_nth c m k (vNe (nVar k)) H). unfold sh.
    destruct (Nat.ltb k c); [ reflexivity | do 2 f_equal; Lia.lia ].
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr m c H. cbn [ne_below_ne] in H.
    destruct H as [HA Hscr]. cbn [shift_ne]. apply ap_emptyrec.
    + apply IHA. exact HA.
    + apply IHscr. exact Hscr.
  - (* nApp *) intros f IHf a IHa m c H. cbn [ne_below_ne] in H.
    destruct H as [Hf Ha]. cbn [shift_ne]. eapply ap_app.
    + apply IHf. exact Hf.
    + apply IHa. exact Ha.
    + apply vapp_ne.
  - (* nAppI *) intros f IHf a IHa m c H. cbn [ne_below_ne] in H.
    destruct H as [Hf Ha]. cbn [shift_ne]. eapply ap_appI.
    + apply IHf. exact Hf.
    + apply IHa. exact Ha.
    + apply vappI_ne.
Qed.

Definition Apply_ty_shift_eq  := fst Apply_shift_eq.
Definition Apply_val_shift_eq := fst (snd Apply_shift_eq).
Definition Apply_ne_shift_eq  := snd (snd Apply_shift_eq).

(* The weakening corollary ([c = 0]): applying [wkn_list m] = front shift. *)
Lemma Apply_ty_wkn : forall T m, ne_below_ty m T ->
    Apply_ty (S m) (wkn_list m) T (shift_ty 0 1 T).
Proof. intros T m H. rewrite <- shsub_0. apply Apply_ty_shift_eq. exact H. Qed.

Lemma Apply_val_wkn : forall v m, ne_below_val m v ->
    Apply_val (S m) (wkn_list m) v (shift_val 0 1 v).
Proof. intros v m H. rewrite <- shsub_0. apply Apply_val_shift_eq. exact H. Qed.

(* ===================================================================== *)
(* Part C : the weakening substitution is well-typed.                      *)
(* ===================================================================== *)

Lemma wf_svalty_scoped : forall Ge T, wf_svalty Ge T -> ne_below_ty (length Ge) T.
Proof.
  intros Ge T H. destruct H as [Ge r l | Ge e r l He].
  - exact I.
  - cbn. apply (has_svalty_scoped He).
Qed.

(* [wkn_list (length Ge)] is a well-typed substitution from [Ge] into the
   context extended (at the front) by an arbitrary [T0].  This is the
   reducibility/weakening substitution used by [reflect_red]: it keeps the
   ambient variables fixed (modulo the front shift) and makes room for the
   freshly-bound variable. *)
Lemma wf_ssub_wkn : forall Ge T0, wf_senv Ge ->
    wf_ssub (T0 :: map (shift_ty 0 1) Ge) (wkn_list (length Ge)) Ge.
Proof.
  intros Ge T0 Hwf. split.
  - apply wkn_list_length.
  - intros k T He.
    assert (Hk : k < length Ge)
      by (apply (proj1 (nth_error_Some Ge k)); rewrite He; discriminate).
    exists (shift_ty 0 1 T). split.
    + cbn [length]. rewrite length_map. apply Apply_ty_wkn.
      apply wf_svalty_scoped. exact (Hwf k T He).
    + assert (Hnth : nth_default (vNe (nVar 0)) (wkn_list (length Ge)) k
                     = vNe (nVar (S k))).
      { unfold wkn_list, nth_default. rewrite nth_error_map.
        rewrite (@nth_error_seq_some (length Ge) 0 k Hk). cbn [option_map]. reflexivity. }
      rewrite Hnth. apply t_ne, n_var.
      cbn [nth_error]. rewrite nth_error_map, He. cbn [option_map]. reflexivity.
Qed.
