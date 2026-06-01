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
    _ _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  - (* t_lam_eta *) intros Ge F B b ARG B' HR Hap hb IHb. cbn.
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

(* ===================================================================== *)
(* Part D : shift-cons cancellation and [wf_ssub_snoc].                    *)
(*                                                                        *)
(* The renaming-then-substitution identity  (a · s) ∘ ↑ = s : applying     *)
(* [a :: s] to a once-shifted (scoped) value is the same as applying [s]   *)
(* to the value — the head [a] is never reached because [shift_val c 1]    *)
(* skips index [c].  This is the structural ingredient that lets a         *)
(* substitution go under a binder when the bound variable receives a       *)
(* CONCRETE value (the application / [a :: sg] case), the dual of          *)
(* [wf_ssub_up] (which handles the [up sg] / weakening-the-substitution    *)
(* case).  Proof is by induction on the value, INVERTING the [Apply]       *)
(* derivation: the output and the codomain length [m] are preserved, so    *)
(* the [Vapp]/beta witness is reused verbatim — no hereditary reduction    *)
(* has to be re-run. *)
(* ===================================================================== *)

(* [s2] inserts a hole at cutoff [c] into [s]: reading [s2] at the shifted
   index returns [s]'s entry, for in-range indices (which is all a scoped
   value reaches). *)
Definition InsAt (c n : nat) (s s2 : ssub) : Prop :=
  forall k, k < n ->
    nth_default (vNe (nVar (sh c k))) s2 (sh c k) = nth_default (vNe (nVar k)) s k.

Lemma nth_default_up : forall s i,
    nth_default (vNe (nVar (S i))) (up s) (S i)
    = shift_val 0 1 (nth_default (vNe (nVar i)) s i).
Proof.
  intros s i. unfold up. rewrite nth_default_cons_S. unfold nth_default.
  rewrite nth_error_map. destruct (nth_error s i) as [w|]; cbn [option_map].
  - reflexivity.
  - cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
Qed.

Lemma InsAt_up : forall c n s s2,
    InsAt c n s s2 -> InsAt (S c) (S n) (up s) (up s2).
Proof.
  intros c n s s2 H k Hk. destruct k as [|k'].
  - replace (sh (S c) 0) with 0 by reflexivity.
    unfold up, nth_default. cbn [nth_error]. reflexivity.
  - rewrite sh_S, !nth_default_up. f_equal. apply H. Lia.lia.
Qed.

Lemma InsAt_base : forall s a, InsAt 0 (length s) s (a :: s).
Proof.
  intros s a k Hk. replace (sh 0 k) with (S k) by (unfold sh; reflexivity).
  rewrite nth_default_cons_S. apply nth_default_irrel. exact Hk.
Qed.

Lemma Apply_cancel :
  (forall T n0 m c s s2 T', ne_below_ty n0 T -> InsAt c n0 s s2 ->
     Apply_ty m s T T' -> Apply_ty m s2 (shift_ty c 1 T) T')
  * ((forall v n0 m c s s2 v', ne_below_val n0 v -> InsAt c n0 s s2 ->
       Apply_val m s v v' -> Apply_val m s2 (shift_val c 1 v) v')
  *  (forall nn n0 m c s s2 w, ne_below_ne n0 nn -> InsAt c n0 s s2 ->
       Apply_ne m s nn w -> Apply_ne m s2 (shift_ne c 1 nn) w)).
Proof.
  apply (sval_mutind
    (fun T => forall n0 m c s s2 T', ne_below_ty n0 T -> InsAt c n0 s s2 ->
       Apply_ty m s T T' -> Apply_ty m s2 (shift_ty c 1 T) T')
    (fun v => forall n0 m c s s2 v', ne_below_val n0 v -> InsAt c n0 s s2 ->
       Apply_val m s v v' -> Apply_val m s2 (shift_val c 1 v) v')
    (fun nn => forall n0 m c s s2 w, ne_below_ne n0 nn -> InsAt c n0 s s2 ->
       Apply_ne m s nn w -> Apply_ne m s2 (shift_ne c 1 nn) w)).
  - (* dU *) intros r l n0 m c s s2 T' _ Hins Hap. inversion Hap; subst. cbn. apply ap_dU.
  - (* dEl *) intros e IHe n0 m c s s2 T' Hne Hins Hap. inversion Hap; subst.
    cbn. apply ap_dEl. eapply IHe; [ exact Hne | exact Hins | eassumption ].
  - (* vNe *) intros nn IHnn n0 m c s s2 v' Hne Hins Hap. inversion Hap; subst.
    cbn. apply ap_ne. eapply IHnn; [ exact Hne | exact Hins | eassumption ].
  - (* vZero *) intros n0 m c s s2 v' _ Hins Hap. inversion Hap; subst. cbn. apply ap_zero.
  - (* vSuc *) intros v IHv n0 m c s s2 v' Hne Hins Hap. inversion Hap; subst.
    cbn. apply ap_suc. eapply IHv; [ exact Hne | exact Hins | eassumption ].
  - (* vNat *) intros n0 m c s s2 v' _ Hins Hap. inversion Hap; subst. cbn. apply ap_nat.
  - (* vEmpty *) intros n0 m c s s2 v' _ Hins Hap. inversion Hap; subst. cbn. apply ap_empty.
  - (* vPi *) intros F IHF B IHB n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB].
    inversion Hap; subst. cbn. apply ap_pi.
    + eapply IHF; [ exact HneF | exact Hins | eassumption ].
    + eapply IHB; [ exact HneB | apply InsAt_up; exact Hins | eassumption ].
  - (* vPiI *) intros F IHF B IHB n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB].
    inversion Hap; subst. cbn. apply ap_piI.
    + eapply IHF; [ exact HneF | exact Hins | eassumption ].
    + eapply IHB; [ exact HneB | apply InsAt_up; exact Hins | eassumption ].
  - (* vLam *) intros b IHb n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. inversion Hap; subst. cbn. apply ap_lam.
    eapply IHb; [ exact Hne | apply InsAt_up; exact Hins | eassumption ].
  - (* vLamI *) intros b IHb n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. inversion Hap; subst. cbn. apply ap_lamI.
    eapply IHb; [ exact Hne | apply InsAt_up; exact Hins | eassumption ].
  - (* nVar *) intros k n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. inversion Hap; subst. cbn [shift_ne].
    replace (if Nat.ltb k c then k else k + 1) with (sh c k)
      by (unfold sh; destruct (Nat.ltb k c); [ reflexivity | f_equal; Lia.lia ]).
    rewrite <- (Hins k Hne). apply ap_var.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. destruct Hne as [HneA Hnescr].
    inversion Hap; subst. cbn [shift_ne]. eapply ap_emptyrec.
    + eapply IHA; [ exact HneA | exact Hins | eassumption ].
    + eapply IHscr; [ exact Hnescr | exact Hins | eassumption ].
  - (* nApp *) intros f IHf a IHa n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. destruct Hne as [Hnef Hnea].
    inversion Hap; subst. cbn [shift_ne]. eapply ap_app.
    + eapply IHf; [ exact Hnef | exact Hins | eassumption ].
    + eapply IHa; [ exact Hnea | exact Hins | eassumption ].
    + eassumption.
  - (* nAppI *) intros f IHf a IHa n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. destruct Hne as [Hnef Hnea].
    inversion Hap; subst. cbn [shift_ne]. eapply ap_appI.
    + eapply IHf; [ exact Hnef | exact Hins | eassumption ].
    + eapply IHa; [ exact Hnea | exact Hins | eassumption ].
    + eassumption.
Qed.

Definition Apply_ty_cancel  := fst Apply_cancel.
Definition Apply_val_cancel := fst (snd Apply_cancel).
Definition Apply_ne_cancel  := snd (snd Apply_cancel).

(* Extending a well-typed substitution by a concrete value for the freshly
   bound variable.  This is the substitution that goes under a binder in the
   APPLICATION direction ([a :: sg], dual to [wf_ssub_up]'s [up sg]). *)
Lemma wf_ssub_snoc : forall Delta sg Ge a F F' rF lF,
    wf_senv Ge ->
    has_svalty Ge F (dU rF lF) ->
    wf_ssub Delta sg Ge ->
    Apply_val (length Delta) sg F F' ->
    has_svalty Delta a (dEl F') ->
    wf_ssub Delta (a :: sg)
            (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge).
Proof.
  intros Delta sg Ge a F F' rF lF Hwf HF [Hlen Hpt] HFa Ha.
  assert (HinsB : InsAt 0 (length Ge) sg (a :: sg)).
  { rewrite <- Hlen. apply InsAt_base. }
  split.
  - cbn [length]. rewrite length_map. rewrite Hlen. reflexivity.
  - intros k T He. destruct k as [|k'].
    + (* head : the fresh variable maps to [a] at [dEl F'] *)
      cbn [nth_error] in He. injection He as He. subst T.
      exists (dEl F'). split.
      * apply ap_dEl.
        eapply Apply_val_cancel;
          [ exact (has_svalty_scoped HF) | exact HinsB | exact HFa ].
      * cbn [nth_default nth_error]. exact Ha.
    + (* tail : reuse the original entry, post-composed with the cancel *)
      cbn [nth_error] in He. rewrite nth_error_map in He.
      destruct (nth_error Ge k') as [Tk|] eqn:E; cbn [option_map] in He;
        [ injection He as He; subst T | discriminate He ].
      destruct (Hpt k' Tk E) as [Tk' [Hap Hty]].
      assert (Hk : k' < length Ge)
        by (apply (proj1 (nth_error_Some Ge k')); rewrite E; discriminate).
      exists Tk'. split.
      * (* [cancel] on the UNSHIFTED [Tk]: its conclusion is exactly the goal
           [Apply_ty _ (a::sg) (shift_ty 0 1 Tk) Tk']. *)
        eapply Apply_ty_cancel;
          [ exact (wf_svalty_scoped (Hwf k' Tk E)) | exact HinsB | exact Hap ].
      * rewrite nth_default_cons_S. exact Hty.
Qed.

(* ===================================================================== *)
(* Part E : reflection codomain coherence.                                 *)
(*                                                                        *)
(* In [refl_Pi] the eta-expanded body is reflected at [dEl B'] where        *)
(* [Apply_val (S m) (ARG :: wkn_list m) B B'] (substitute ARG for the bound *)
(* variable, keep the [m] ambient indices).  When TYPING the body's neutral *)
(* [nApp (shift n) ARG] by [n_app], its result type uses the substitution   *)
(* [ARG :: id_list (S m)] applied to the once-shifted codomain              *)
(* [shift_val 1 1 B].  Both substitutions compute B[0↦ARG, j+1↦j], so they  *)
(* produce the SAME [B']; by determinism the lambda's body type matches the *)
(* typing judgment's result type.  This is the [c = 1] instance of          *)
(* [Apply_cancel].                                                          *)
(* ===================================================================== *)

Lemma id_list_nth_lt : forall n k d, k < n -> nth_default d (id_list n) k = vNe (nVar k).
Proof. intros n k d H. rewrite id_list_nth_any, (@ltbT k n H). reflexivity. Qed.

Lemma wkn_list_nth : forall m k d, k < m -> nth_default d (wkn_list m) k = vNe (nVar (S k)).
Proof.
  intros m k d H. rewrite <- shsub_0, (@shsub_nth 0 m k d H). unfold sh. reflexivity.
Qed.

Lemma InsAt_1_wkn_id : forall m a,
    InsAt 1 (S m) (a :: wkn_list m) (a :: id_list (S m)).
Proof.
  intros m a k Hk. destruct k as [|k'].
  - reflexivity.
  - replace (sh 1 (S k')) with (S (S k')) by (unfold sh; reflexivity).
    assert (Hk' : k' < m) by Lia.lia.
    rewrite !nth_default_cons_S.
    rewrite (@id_list_nth_lt (S m) (S k') (vNe (nVar (S (S k')))) ltac:(Lia.lia)).
    rewrite (@wkn_list_nth m k' (vNe (nVar (S k'))) Hk').
    reflexivity.
Qed.

Lemma Apply_reflect_cod : forall m a B B',
    ne_below_val (S m) B ->
    Apply_val (S m) (a :: wkn_list m) B B' ->
    Apply_val (S m) (a :: id_list (S m)) (shift_val 1 1 B) B'.
Proof.
  intros m a B B' Hne Hap.
  eapply Apply_val_cancel; [ exact Hne | apply InsAt_1_wkn_id | exact Hap ].
Qed.
