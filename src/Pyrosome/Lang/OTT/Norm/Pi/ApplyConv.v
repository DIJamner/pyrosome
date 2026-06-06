Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply ApplyLemmas Preservation RenSubst LogRel2Conv.
Import Core.Notations.

(* ===================================================================== *)
(* [Apply] is a CONGRUENCE for structural conversion.                       *)
(*                                                                         *)
(* Applying pointwise-[conv_nf]-related substitutions to [conv_nf]-related  *)
(* inputs yields [conv_nf]-related outputs.  Proved by induction on the     *)
(* (LEFT) [Apply] derivation -- crucially NOT on the type, so the           *)
(* dependent-codomain "B[arg] is not smaller" non-termination never bites.  *)
(* This is the keystone for read-back being a congruence (reify preserves   *)
(* conv), which in turn makes reify-tm hold at function types (option A,    *)
(* the NbE read-back; see Reify.v and memory ott-r2-hereditary-eta).        *)
(* ===================================================================== *)

(* Pointwise conversion of substitutions (carries length equality so that
   out-of-range reads -- where [nth_default] returns the default -- are
   handled uniformly). *)
Definition conv_sub (s s' : ssub) : Type :=
  (length s = length s') *
  (forall k, conv_nf (nth_default (vNe (nVar k)) s k) (nth_default (vNe (nVar k)) s' k)).

(* Read at ANY (self-conv) default. *)
Lemma conv_sub_nth : forall s s' k d,
    conv_sub s s' -> conv_nf d d ->
    conv_nf (nth_default d s k) (nth_default d s' k).
Proof.
  intros s s' k d [Hlen Hpt] Hd.
  destruct (le_lt_dec (length s) k) as [Hk|Hk].
  - unfold nth_default.
    rewrite (proj2 (nth_error_None s k)) by exact Hk.
    rewrite (proj2 (nth_error_None s' k)) by (rewrite <- Hlen; exact Hk).
    exact Hd.
  - rewrite (@nth_default_irrel s k d (vNe (nVar k))) by exact Hk.
    rewrite (@nth_default_irrel s' k d (vNe (nVar k))) by (rewrite <- Hlen; exact Hk).
    exact (Hpt k).
Qed.

Lemma conv_sub_refl : forall s, conv_sub s s.
Proof. intros s; split; [ reflexivity | intro k; apply conv_nf_refl ]. Qed.

Lemma conv_sub_cons : forall a a' s s',
    conv_nf a a' -> conv_sub s s' -> conv_sub (a :: s) (a' :: s').
Proof.
  intros a a' s s' Ha Hs. destruct Hs as [Hlen Hpt]. split.
  - cbn [length]. f_equal; exact Hlen.
  - intros [|k].
    + unfold nth_default; cbn [nth_error]. exact Ha.
    + rewrite !nth_default_cons_S.
      apply (@conv_sub_nth s s' k (vNe (nVar (S k))) (Hlen, Hpt) (conv_nf_refl _)).
Qed.

Lemma conv_sub_up : forall s s', conv_sub s s' -> conv_sub (up s) (up s').
Proof.
  intros s s' Hs. destruct Hs as [Hlen Hpt]. split.
  - unfold up; cbn [length]. rewrite !length_map. f_equal; exact Hlen.
  - intros [|k].
    + unfold up, nth_default; cbn [nth_error]. apply conv_nf_refl.
    + rewrite !up_nth_S. apply conv_nf_shift. exact (Hpt k).
Qed.

(* Conversion of (semantic) types: codes related by [conv_nf]. *)
Definition conv_tyc (T T2 : svalty) : Type :=
  match T, T2 with
  | dEl e, dEl e2 => conv_nf e e2
  | dU _ _, dU _ _ => unit
  | _, _ => unit
  end.

(* ===================================================================== *)
(* The congruence (keystone).                                              *)
(* ===================================================================== *)
Lemma Apply_conv :
  ((((
     (forall m s T T', Apply_ty m s T T' ->
        forall s' T2 T2', conv_sub s s' -> conv_tyc T T2 -> Apply_ty m s' T2 T2' -> conv_tyc T' T2')
   * (forall m s v v', Apply_val m s v v' ->
        forall s' v2 v2', conv_sub s s' -> conv_nf v v2 -> Apply_val m s' v2 v2' -> conv_nf v' v2') )
   * (forall m s n v, Apply_ne m s n v ->
        forall s' n2 v2, conv_sub s s' -> conv_ne n n2 -> Apply_ne m s' n2 v2 -> conv_nf v v2) )
   * (forall m F B vf a v, Vapp m F B vf a v ->
        forall F2 B2 vf2 a2 v2, conv_nf F F2 -> conv_nf B B2 -> conv_nf vf vf2 -> conv_nf a a2 ->
          Vapp m F2 B2 vf2 a2 v2 -> conv_nf v v2) )
   * (forall m F B vf a v, VappI m F B vf a v ->
        forall F2 B2 vf2 a2 v2, conv_nf F F2 -> conv_nf B B2 -> conv_nf vf vf2 -> conv_nf a a2 ->
          VappI m F2 B2 vf2 a2 v2 -> conv_nf v v2)).
Proof.
  refine (Apply_mutind
    (fun m s T T' _ => forall s' T2 T2', conv_sub s s' -> conv_tyc T T2 -> Apply_ty m s' T2 T2' -> conv_tyc T' T2')
    (fun m s v v' _ => forall s' v2 v2', conv_sub s s' -> conv_nf v v2 -> Apply_val m s' v2 v2' -> conv_nf v' v2')
    (fun m s n v _ => forall s' n2 v2, conv_sub s s' -> conv_ne n n2 -> Apply_ne m s' n2 v2 -> conv_nf v v2)
    (fun m F B vf a v _ => forall F2 B2 vf2 a2 v2, conv_nf F F2 -> conv_nf B B2 -> conv_nf vf vf2 -> conv_nf a a2 -> Vapp m F2 B2 vf2 a2 v2 -> conv_nf v v2)
    (fun m F B vf a v _ => forall F2 B2 vf2 a2 v2, conv_nf F F2 -> conv_nf B B2 -> conv_nf vf vf2 -> conv_nf a a2 -> VappI m F2 B2 vf2 a2 v2 -> conv_nf v v2)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ap_dU *) intros m s r l s' T2 T2' Hs Hconv Hap2. destruct T2'; exact tt.
  - (* ap_dEl *) intros m s e e' Hae IHe s' T2 T2' Hs Hconv Hap2.
    destruct T2 as [r l|e2].
    + inversion Hap2; subst. exact tt.
    + cbn in Hconv. inversion Hap2; subst. cbn. eapply IHe; eassumption.
  - (* ap_ne *) intros m s n v Hne IHne s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst. eapply IHne; eassumption.
  - (* ap_zero *) intros m s s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst. apply cnf_zero.
  - (* ap_suc *) intros m s v v' Hv IHv s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst. apply cnf_suc. eapply IHv; eassumption.
  - (* ap_nat *) intros m s s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst. apply cnf_nat.
  - (* ap_empty *) intros m s s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst. apply cnf_empty.
  - (* ap_pi *) intros m s F F' B B' HF IHF HB IHB s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst.
    apply cnf_pi.
    + eapply IHF; eassumption.
    + eapply IHB; [ apply conv_sub_up; exact Hs | eassumption | eassumption ].
  - (* ap_piI *) intros m s F F' B B' HF IHF HB IHB s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst.
    apply cnf_piI.
    + eapply IHF; eassumption.
    + eapply IHB; [ apply conv_sub_up; exact Hs | eassumption | eassumption ].
  - (* ap_lam *) intros m s b b' Hb IHb s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst.
    apply cnf_lam. eapply IHb; [ apply conv_sub_up; exact Hs | eassumption | eassumption ].
  - (* ap_lamI *) intros m s b b' Hb IHb s' v2 v2' Hs Hconv Hap2.
    inversion Hconv; subst. inversion Hap2; subst.
    apply cnf_lamI. eapply IHb; [ apply conv_sub_up; exact Hs | eassumption | eassumption ].
  - (* ap_var *) intros m s k s' n2 v2 Hs Hcne Hap2.
    inversion Hcne; subst. inversion Hap2; subst. exact (snd Hs k).
  - (* ap_emptyrec *) intros m s rA lA A A' scrut scrut' HA IHA Hsc IHsc s' n2 v2 Hs Hcne Hap2.
    inversion Hcne; subst. inversion Hap2; subst.
    apply cnf_ne. apply cne_emptyrec.
    + eapply IHA; eassumption.
    + assert (Hr : conv_nf (vNe scrut') (vNe _)) by (eapply IHsc; eassumption).
      inversion Hr; subst. assumption.
  - (* ap_app *) intros m s f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hv IHv
                   s' n2 v2 Hs Hcne Hap2.
    inversion Hcne; subst. inversion Hap2; subst.
    eapply IHv.
    + eapply IHF; eassumption.
    + eapply IHB; [ apply conv_sub_up; exact Hs | eassumption | eassumption ].
    + eapply IHf; eassumption.
    + eapply IHa; eassumption.
    + eassumption.
  - (* ap_appI *) intros m s f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hv IHv
                   s' n2 v2 Hs Hcne Hap2.
    inversion Hcne; subst. inversion Hap2; subst.
    eapply IHv.
    + eapply IHF; eassumption.
    + eapply IHB; [ apply conv_sub_up; exact Hs | eassumption | eassumption ].
    + eapply IHf; eassumption.
    + eapply IHa; eassumption.
    + eassumption.
  - (* vapp_lam *) intros m F B b a v Hbeta IHbeta F2 B2 vf2 a2 v2 HF HB Hvf Ha Hva2.
    inversion Hvf; subst. inversion Hva2; subst.
    eapply IHbeta; [ apply conv_sub_cons; [ exact Ha | apply conv_sub_refl ] | eassumption | eassumption ].
  - (* vapp_ne *) intros m F B n a F2 B2 vf2 a2 v2 HF HB Hvf Ha Hva2.
    inversion Hvf; subst. inversion Hva2; subst.
    apply cnf_ne. apply cne_app; eassumption.
  - (* vappI_lam *) intros m F B b a v Hbeta IHbeta F2 B2 vf2 a2 v2 HF HB Hvf Ha Hva2.
    inversion Hvf; subst. inversion Hva2; subst.
    eapply IHbeta; [ apply conv_sub_cons; [ exact Ha | apply conv_sub_refl ] | eassumption | eassumption ].
  - (* vappI_ne *) intros m F B n a F2 B2 vf2 a2 v2 HF HB Hvf Ha Hva2.
    inversion Hvf; subst. inversion Hva2; subst.
    apply cnf_ne. apply cne_appI; eassumption.
Qed.
