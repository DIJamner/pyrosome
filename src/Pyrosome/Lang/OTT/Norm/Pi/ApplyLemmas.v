Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply.
Import Core.Notations.

(* Basic algebra of the identity / weakening substitution lists and of the
   relational [Apply], for the Pi-extended domain.  These are the
   totality-free facts (no normalization argument needed): they hold by plain
   structural induction on the value being substituted into. *)
Section ApplyLemmas.

  (* The k-th element of [id_list n] is [vNe (nVar k)] for ANY k (verbatim when
     in range; the [nth_default] default coincides when out of range). *)
  Lemma id_list_nth : forall n k,
      nth_default (vNe (nVar k)) (id_list n) k = vNe (nVar k).
  Proof.
    induction n as [| n IHn]; intro k.
    - unfold id_list. cbn [seq map]. unfold nth_default. destruct k; reflexivity.
    - unfold id_list in *. cbn [seq map].
      destruct k as [| k'].
      + unfold nth_default. cbn. reflexivity.
      + unfold nth_default in *. cbn [nth_error].
        rewrite <- seq_shift, map_map, nth_error_map.
        destruct (nth_error (seq 0 n) k') eqn:He.
        * cbn. specialize (IHn k'). rewrite nth_error_map, He in IHn.
          cbn in IHn. inversion IHn. reflexivity.
        * cbn. reflexivity.
  Qed.

  (* [snoc #wkn #hd = #id] at the list level. *)
  Lemma snoc_wkn_hd_list : forall n, vNe (nVar 0) :: wkn_list n = id_list (S n).
  Proof.
    intro n. unfold id_list, wkn_list. cbn [seq map].
    f_equal. rewrite <- seq_shift, map_map. reflexivity.
  Qed.

  (* Lifting the identity substitution under a binder is again the identity. *)
  Lemma up_id_list : forall m, up (id_list m) = id_list (S m).
  Proof.
    intro m. unfold up. rewrite <- snoc_wkn_hd_list. f_equal.
    unfold id_list, wkn_list. rewrite map_map. apply map_ext.
    intro k. cbn. do 2 f_equal. Lia.lia.
  Qed.

  (* Applying the identity substitution is the identity, UNCONDITIONALLY. *)
  Lemma Apply_id_all :
      (forall T m, Apply_ty m (id_list m) T T)
      * ((forall v m, Apply_val m (id_list m) v v)
      *  (forall n m, Apply_ne m (id_list m) n (vNe n))).
  Proof.
    apply (sval_mutind
      (fun T => forall m, Apply_ty m (id_list m) T T)
      (fun v => forall m, Apply_val m (id_list m) v v)
      (fun n => forall m, Apply_ne m (id_list m) n (vNe n))).
    - (* dU *) intros; apply ap_dU.
    - (* dEl *) intros e IHe m. apply ap_dEl, IHe.
    - (* vNe *) intros n IHn m. apply ap_ne, IHn.
    - (* vZero *) intros; apply ap_zero.
    - (* vSuc *) intros v IHv m. apply ap_suc, IHv.
    - (* vNat *) intros; apply ap_nat.
    - (* vEmpty *) intros; apply ap_empty.
    - (* vPi *) intros F IHF B IHB m. apply ap_pi; [ apply IHF | rewrite up_id_list; apply IHB ].
    - (* vPiI *) intros F IHF B IHB m. apply ap_piI; [ apply IHF | rewrite up_id_list; apply IHB ].
    - (* vLam *) intros b IHb m. apply ap_lam. rewrite up_id_list. apply IHb.
    - (* vLamI *) intros b IHb m. apply ap_lamI. rewrite up_id_list. apply IHb.
    - (* nVar *) intros k m. rewrite <- (id_list_nth m k). apply ap_var.
    - (* nEmptyrec *) intros rA lA A IHA scrut IHscr m.
      apply ap_emptyrec; [ apply IHA | apply IHscr ].
    - (* nApp *) intros f IHf F IHF B IHB a IHa m.
      eapply ap_app;
        [ apply IHf | apply IHF | rewrite up_id_list; apply IHB | apply IHa | apply vapp_ne ].
    - (* nAppI *) intros f IHf F IHF B IHB a IHa m.
      eapply ap_appI;
        [ apply IHf | apply IHF | rewrite up_id_list; apply IHB | apply IHa | apply vappI_ne ].
  Qed.

  Definition Apply_ty_id  : forall T m, Apply_ty m (id_list m) T T := fst Apply_id_all.
  Definition Apply_val_id : forall v m, Apply_val m (id_list m) v v := fst (snd Apply_id_all).
  Definition Apply_ne_id  : forall n m, Apply_ne m (id_list m) n (vNe n) := snd (snd Apply_id_all).

  (* Length facts. *)
  Lemma id_list_length : forall n, length (id_list n) = n.
  Proof. intro n. unfold id_list. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma wkn_list_length : forall n, length (wkn_list n) = n.
  Proof. intro n. unfold wkn_list. rewrite length_map, length_seq. reflexivity. Qed.

End ApplyLemmas.
