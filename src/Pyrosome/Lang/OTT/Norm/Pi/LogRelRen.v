Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply ApplyLemmas LogRel.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Renaming algebra for the [is_ren] predicate that gates [PiRedTmPred]'s   *)
(* application clause.  A renaming is a substitution all of whose entries   *)
(* are variable-neutrals ([is_ren] in LogRel.v).  These structural facts    *)
(* are what [reflect_red] and the validity layer use to discharge the       *)
(* clause's renaming hypothesis (the FL applies at [id_list]; reflection    *)
(* under a binder uses [up]/[wkn_list]).                                    *)
(* ===================================================================== *)

Lemma is_ren_nil : is_ren [].
Proof. exists []. reflexivity. Qed.

(* The tail of a renaming is a renaming. *)
Lemma is_ren_tl : forall {h t}, is_ren (h :: t) -> is_ren t.
Proof.
  intros h t [rho Heq]. destruct rho as [|r rs]; cbn in Heq; [ discriminate | ].
  injection Heq as _ Ht. exists rs. exact Ht.
Qed.

(* Consing a variable-neutral onto a renaming is a renaming. *)
Lemma is_ren_cons : forall k t, is_ren t -> is_ren (vNe (nVar k) :: t).
Proof.
  intros k t [rho Heq]. exists (k :: rho). cbn [map]. rewrite Heq. reflexivity.
Qed.

Lemma is_ren_id : forall n, is_ren (id_list n).
Proof. intro n. exists (seq 0 n). reflexivity. Qed.

Lemma is_ren_wkn : forall n, is_ren (wkn_list n).
Proof.
  intro n. exists (map S (seq 0 n)). unfold wkn_list. rewrite map_map. reflexivity.
Qed.

Lemma is_ren_up : forall s, is_ren s -> is_ren (up s).
Proof.
  intros s [rho Heq]. subst s. exists (0 :: map S rho).
  unfold up. cbn [map]. f_equal.
  rewrite !map_map. apply map_ext. intro k.
  cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
Qed.

(* Reading a renaming at any index returns a variable-neutral. *)
Lemma ren_nth_var : forall sg, is_ren sg ->
    forall k, { j & nth_default (vNe (nVar k)) sg k = vNe (nVar j) }.
Proof.
  intros sg [rho ->] k. unfold nth_default. rewrite nth_error_map.
  destruct (nth_error rho k) as [j|]; cbn [option_map].
  - exists j; reflexivity.
  - exists k; reflexivity.
Qed.

(* ===================================================================== *)
(* Under a RENAMING, [Apply_*] is TOTAL and preserves neutrality.          *)
(*                                                                         *)
(* The key structural fact behind the renaming-gated Pi clause: applying a  *)
(* renaming never creates a beta redex (a variable head maps to a variable  *)
(* head, so every [Vapp]/[VappI] stays in its [vapp_ne]/[vappI_ne] case).   *)
(* Hence substitution is structurally terminating on ALL values, and a       *)
(* neutral maps to a neutral.  Proof by [sval_mutind]; the binder cases use  *)
(* [is_ren_up].                                                              *)
(* ===================================================================== *)
Lemma ren_Apply_total :
  (forall T m sg, is_ren sg -> { T' & Apply_ty m sg T T' })
  * ((forall v m sg, is_ren sg -> { v' & Apply_val m sg v v' })
  *  (forall nn m sg, is_ren sg -> { n' & Apply_ne m sg nn (vNe n') })).
Proof.
  apply (sval_mutind
    (fun T  => forall m sg, is_ren sg -> { T' & Apply_ty  m sg T  T' })
    (fun v  => forall m sg, is_ren sg -> { v' & Apply_val m sg v  v' })
    (fun nn => forall m sg, is_ren sg -> { n' & Apply_ne  m sg nn (vNe n') })).
  - (* dU *) intros r l m sg Hr. exists (dU r l). apply ap_dU.
  - (* dEl *) intros e IHe m sg Hr. destruct (IHe m sg Hr) as [e' He].
    exists (dEl e'). apply ap_dEl; exact He.
  - (* vNe *) intros nn IHnn m sg Hr. destruct (IHnn m sg Hr) as [n' Hn].
    exists (vNe n'). apply ap_ne; exact Hn.
  - (* vZero *) intros m sg Hr. exists vZero. apply ap_zero.
  - (* vSuc *) intros v IHv m sg Hr. destruct (IHv m sg Hr) as [v' Hv].
    exists (vSuc v'). apply ap_suc; exact Hv.
  - (* vNat *) intros m sg Hr. exists vNat. apply ap_nat.
  - (* vEmpty *) intros m sg Hr. exists vEmpty. apply ap_empty.
  - (* vPi *) intros F IHF B IHB m sg Hr.
    destruct (IHF m sg Hr) as [F' HF].
    destruct (IHB (S m) (up sg) (is_ren_up Hr)) as [B' HB].
    exists (vPi F' B'). apply ap_pi; [ exact HF | exact HB ].
  - (* vPiI *) intros F IHF B IHB m sg Hr.
    destruct (IHF m sg Hr) as [F' HF].
    destruct (IHB (S m) (up sg) (is_ren_up Hr)) as [B' HB].
    exists (vPiI F' B'). apply ap_piI; [ exact HF | exact HB ].
  - (* vLam *) intros b IHb m sg Hr.
    destruct (IHb (S m) (up sg) (is_ren_up Hr)) as [b' Hb].
    exists (vLam b'). apply ap_lam; exact Hb.
  - (* vLamI *) intros b IHb m sg Hr.
    destruct (IHb (S m) (up sg) (is_ren_up Hr)) as [b' Hb].
    exists (vLamI b'). apply ap_lamI; exact Hb.
  - (* nVar *) intros k m sg Hr. destruct (ren_nth_var Hr k) as [j Hj].
    exists (nVar j). rewrite <- Hj. apply ap_var.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr m sg Hr.
    destruct (IHA m sg Hr) as [A' HA].
    destruct (IHscr m sg Hr) as [s' Hs].
    exists (nEmptyrec rA lA A' s'). apply ap_emptyrec; [ exact HA | exact Hs ].
  - (* nApp *) intros f IHf a IHa m sg Hr.
    destruct (IHf m sg Hr) as [nf' Hf].
    destruct (IHa m sg Hr) as [a' Ha].
    exists (nApp nf' a'). eapply ap_app; [ exact Hf | exact Ha | apply vapp_ne ].
  - (* nAppI *) intros f IHf a IHa m sg Hr.
    destruct (IHf m sg Hr) as [nf' Hf].
    destruct (IHa m sg Hr) as [a' Ha].
    exists (nAppI nf' a'). eapply ap_appI; [ exact Hf | exact Ha | apply vappI_ne ].
Qed.

Definition ren_Apply_ty_total  := fst ren_Apply_total.
Definition ren_Apply_val_total := fst (snd ren_Apply_total).
Definition ren_Apply_ne_total  := snd (snd ren_Apply_total).
