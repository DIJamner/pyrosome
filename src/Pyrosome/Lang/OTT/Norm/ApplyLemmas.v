Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel.
Import Core.Notations.

(* Foundational computation lemmas about [apply_*] (Domain.v) and the
   identity/weakening substitution lists (EvalRel.v), used to close the
   Tier-A/B [cterm_by] cases of the Norm model.

   The headline fact is that [apply]ing the identity substitution is the
   identity on every value/type/neutral, UNCONDITIONALLY: a variable index
   [k] is mapped to [vNe (nVar k)] whether [k] is in range of [id_list n]
   (it appears verbatim) or out of range (the default is the same). *)
Section ApplyLemmas.

  (* Helper: the k-th element of id_list n is vNe (nVar k), for any k.
     When k < n the value appears verbatim; when k >= n the nth_default
     default coincides, so the result is vNe (nVar k) in both cases. *)
  Lemma id_list_nth : forall n k,
      nth_default (vNe (nVar k)) (id_list n) k = vNe (nVar k).
  Proof.
    induction n as [| n IHn]; intro k.
    - unfold id_list. cbn [seq map].
      unfold nth_default. destruct k; reflexivity.
    - unfold id_list in *.
      cbn [seq map].
      destruct k as [| k'].
      + unfold nth_default. cbn. reflexivity.
      + unfold nth_default in *.
        cbn [nth_error].
        rewrite <- seq_shift.
        rewrite map_map.
        rewrite nth_error_map.
        destruct (nth_error (seq 0 n) k') eqn:He.
        * cbn.
          specialize (IHn k'). rewrite nth_error_map, He in IHn.
          cbn in IHn. inversion IHn. reflexivity.
        * cbn. reflexivity.
  Qed.

  (* Combined mutual induction: apply_{ty,val,ne} (id_list n) is the identity.
     We use sval_mutind (which returns a product type) and destructure the result. *)
  Lemma apply_id_all : forall n,
      (forall T, apply_ty (id_list n) T = T)
      * (forall v, apply_val (id_list n) v = v)
      * (forall e, apply_ne (id_list n) e = vNe e).
  Proof.
    intro n.
    destruct (sval_mutind
      (fun T => apply_ty (id_list n) T = T)
      (fun v => apply_val (id_list n) v = v)
      (fun e => apply_ne (id_list n) e = vNe e)
      (* dNe: apply_ty (id_list n) (dNe e) = dNe e, using IH: apply_ne ... e = vNe e *)
      (fun e IHe => ltac:(cbn; rewrite IHe; reflexivity))
      (* dNat *)
      (ltac:(reflexivity))
      (* dEmpty *)
      (ltac:(reflexivity))
      (* dU *)
      (fun r l => ltac:(reflexivity))
      (* vNe: apply_val (id_list n) (vNe e) = vNe e, using IH *)
      (fun e IHe => ltac:(cbn; exact IHe))
      (* vZero *)
      (ltac:(reflexivity))
      (* vSuc *)
      (fun v IHv => ltac:(cbn; rewrite IHv; reflexivity))
      (* vCode *)
      (fun T IHT => ltac:(cbn; rewrite IHT; reflexivity))
      (* nVar k: apply_ne (id_list n) (nVar k) = vNe (nVar k) by id_list_nth *)
      (fun k => ltac:(cbn; apply id_list_nth))
      (* nEmptyrec: IHscrut says apply_ne ... scrut = vNe scrut; IHA handles motive *)
      (fun rA lA A IHA scrut IHscrut => ltac:(cbn; rewrite IHscrut, IHA; reflexivity))
    ) as [Hty [Hval Hne]].
    exact (Hty, Hval, Hne).
  Qed.

  (* [apply (id_list n)] is the identity, by mutual induction on the value
     domain (n fixed across the recursion). *)
  Lemma apply_id_ty : forall n T, apply_ty (id_list n) T = T.
  Proof. intros n T. exact (fst (fst (apply_id_all n)) T). Qed.

  Lemma apply_id_val : forall n v, apply_val (id_list n) v = v.
  Proof. intros n v. exact (snd (fst (apply_id_all n)) v). Qed.

  Lemma apply_id_ne : forall n e, apply_ne (id_list n) e = vNe e.
  Proof. intros n e. exact (snd (apply_id_all n) e). Qed.

  (* Mapping [apply (id_list n)] over a substitution is the identity. *)
  Lemma apply_id_map : forall n (l : ssub), map (apply_val (id_list n)) l = l.
  Proof.
    intros n l.
    rewrite <- (map_id l) at 2.
    apply map_ext.
    intro v.
    apply apply_id_val.
  Qed.

  (* The [snoc_wkn_hd] / [id] coherence at the list level. *)
  Lemma snoc_wkn_hd_list : forall n, vNe (nVar 0) :: wkn_list n = id_list (S n).
  Proof.
    intro n.
    unfold id_list, wkn_list.
    cbn [seq map].
    f_equal.
    (* wkn_list n = map (fun k => vNe (nVar (S k))) (seq 0 n)
       id_list (S n) tail = map (fun k => vNe (nVar k)) (seq 1 n)
       seq 1 n = map S (seq 0 n) by seq_shift *)
    rewrite <- seq_shift.
    rewrite map_map.
    reflexivity.
  Qed.

End ApplyLemmas.
