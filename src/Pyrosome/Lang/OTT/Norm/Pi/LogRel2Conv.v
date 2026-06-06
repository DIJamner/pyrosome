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
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain.
Import Core.Notations.

(* ===================================================================== *)
(* GENUINE neutral / normal-form conversion ([∼ne] / [∼nf]) -- Phase 3.    *)
(*                                                                        *)
(* This replaces the PROVISIONAL strict-diagonal [NeConv] of [LogRel2.v]   *)
(* ([n = m]) with the real structural conversion the two-sided PER needs:  *)
(* two normal forms are convertible when they have the SAME spine shape    *)
(* and their sub-values are recursively convertible -- crucially their     *)
(* type ANNOTATIONS ([F],[B] on [nApp]/[nAppI], the motive [A] on          *)
(* [nEmptyrec]) need only be CONVERTIBLE, not syntactically equal.  This    *)
(* is the paper's [∼annot] (Def 13): it lets two neutrals at convertible-   *)
(* but-unequal types ([dEl (vNe n)] vs [dEl (vNe m)]) be related, which the *)
(* diagonal cannot express.                                                *)
(*                                                                        *)
(* The relation is UNTYPED and purely structural.  This is sound and        *)
(* complete in THIS domain precisely because [Reflect] bakes eta into the   *)
(* normal forms: every value of relevant function type is a [vLam] (never   *)
(* a bare neutral), so two convertible normal forms have the same outer     *)
(* former and structural comparison loses nothing.  Being independent of    *)
(* [LR], it is positivity-safe to reference from [LR]'s base cases (via      *)
(* [NeConv] = well-typed both sides + [conv_ne]); the connection to         *)
(* REDUCIBLE conversion is the job of reify/reflect (Theorem 11).           *)
(* ===================================================================== *)

Unset Elimination Schemes.
Inductive conv_nf : sval -> sval -> Type :=
| cnf_ne    : forall n m, conv_ne n m -> conv_nf (vNe n) (vNe m)
| cnf_zero  : conv_nf vZero vZero
| cnf_suc   : forall v w, conv_nf v w -> conv_nf (vSuc v) (vSuc w)
| cnf_nat   : conv_nf vNat vNat
| cnf_empty : conv_nf vEmpty vEmpty
| cnf_pi    : forall F B F' B',
    conv_nf F F' -> conv_nf B B' -> conv_nf (vPi F B) (vPi F' B')
| cnf_piI   : forall F B F' B',
    conv_nf F F' -> conv_nf B B' -> conv_nf (vPiI F B) (vPiI F' B')
| cnf_lam   : forall b b', conv_nf b b' -> conv_nf (vLam b) (vLam b')
| cnf_lamI  : forall b b', conv_nf b b' -> conv_nf (vLamI b) (vLamI b')
with conv_ne : neutral -> neutral -> Type :=
| cne_var      : forall k, conv_ne (nVar k) (nVar k)
| cne_emptyrec : forall rA lA A scrut A' scrut',
    conv_nf A A' -> conv_ne scrut scrut' ->
    conv_ne (nEmptyrec rA lA A scrut) (nEmptyrec rA lA A' scrut')
| cne_app      : forall f F B a f' F' B' a',
    conv_ne f f' -> conv_nf F F' -> conv_nf B B' -> conv_nf a a' ->
    conv_ne (nApp f F B a) (nApp f' F' B' a')
| cne_appI     : forall f F B a f' F' B' a',
    conv_ne f f' -> conv_nf F F' -> conv_nf B B' -> conv_nf a a' ->
    conv_ne (nAppI f F B a) (nAppI f' F' B' a').
Set Elimination Schemes.

Scheme conv_nf_rect := Induction for conv_nf Sort Type
  with conv_ne_rect := Induction for conv_ne Sort Type.
Combined Scheme conv_mutind from conv_nf_rect, conv_ne_rect.

(* ===================================================================== *)
(* Reflexivity: every value / neutral is convertible to itself.  (Gives    *)
(* the diagonal embedding [conv_ne_of_eq] below, so every site that built   *)
(* the provisional [NeConv] from [n = m] still builds the genuine one.)     *)
(* ===================================================================== *)
Lemma conv_refl :
  (forall T : svalty, True)
  * ((forall v : sval, conv_nf v v)
  *  (forall n : neutral, conv_ne n n)).
Proof.
  apply (sval_mutind
    (fun _ : svalty => True)
    (fun v : sval => conv_nf v v)
    (fun n : neutral => conv_ne n n)).
  - exact (fun _ _ => I).
  - exact (fun _ _ => I).
  - intros n IH. apply cnf_ne; exact IH.
  - apply cnf_zero.
  - intros v IH. apply cnf_suc; exact IH.
  - apply cnf_nat.
  - apply cnf_empty.
  - intros F IHF B IHB. apply cnf_pi; assumption.
  - intros F IHF B IHB. apply cnf_piI; assumption.
  - intros b IH. apply cnf_lam; exact IH.
  - intros b IH. apply cnf_lamI; exact IH.
  - intros k. apply cne_var.
  - intros rA lA A IHA scrut IHs. apply cne_emptyrec; assumption.
  - intros f IHf F IHF B IHB a IHa. apply cne_app; assumption.
  - intros f IHf F IHF B IHB a IHa. apply cne_appI; assumption.
Qed.

Definition conv_nf_refl : forall v, conv_nf v v := fst (snd conv_refl).
Definition conv_ne_refl : forall n, conv_ne n n := snd (snd conv_refl).

Definition conv_ne_of_eq : forall n m, n = m -> conv_ne n m :=
  fun n m e => match e in _ = m' return conv_ne n m' with
               | eq_refl => conv_ne_refl n end.

Definition conv_nf_of_eq : forall v w, v = w -> conv_nf v w :=
  fun v w e => match e in _ = w' return conv_nf v w' with
               | eq_refl => conv_nf_refl v end.

(* ===================================================================== *)
(* Symmetry.                                                               *)
(* ===================================================================== *)
Lemma conv_sym :
  (forall a b, conv_nf a b -> conv_nf b a)
  * (forall n m, conv_ne n m -> conv_ne m n).
Proof.
  apply (conv_mutind
    (fun a b (_ : conv_nf a b) => conv_nf b a)
    (fun n m (_ : conv_ne n m) => conv_ne m n)).
  - intros n m _ IH. apply cnf_ne; exact IH.
  - apply cnf_zero.
  - intros v w _ IH. apply cnf_suc; exact IH.
  - apply cnf_nat.
  - apply cnf_empty.
  - intros F B F' B' _ IHF _ IHB. apply cnf_pi; assumption.
  - intros F B F' B' _ IHF _ IHB. apply cnf_piI; assumption.
  - intros b b' _ IH. apply cnf_lam; exact IH.
  - intros b b' _ IH. apply cnf_lamI; exact IH.
  - intros k. apply cne_var.
  - intros rA lA A scrut A' scrut' _ IHA _ IHs. apply cne_emptyrec; assumption.
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa. apply cne_app; assumption.
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa. apply cne_appI; assumption.
Qed.

Definition conv_nf_sym : forall a b, conv_nf a b -> conv_nf b a := fst conv_sym.
Definition conv_ne_sym : forall n m, conv_ne n m -> conv_ne m n := snd conv_sym.

(* ===================================================================== *)
(* Transitivity (induct on the first derivation, invert the second).      *)
(* ===================================================================== *)
Lemma conv_trans :
  (forall a b, conv_nf a b -> forall c, conv_nf b c -> conv_nf a c)
  * (forall n m, conv_ne n m -> forall p, conv_ne m p -> conv_ne n p).
Proof.
  apply (conv_mutind
    (fun a b (_ : conv_nf a b) => forall c, conv_nf b c -> conv_nf a c)
    (fun n m (_ : conv_ne n m) => forall p, conv_ne m p -> conv_ne n p)).
  - intros n m _ IH c Hc. inversion Hc; subst. apply cnf_ne. apply IH; assumption.
  - intros c Hc. exact Hc.
  - intros v w _ IH c Hc. inversion Hc; subst. apply cnf_suc. apply IH; assumption.
  - intros c Hc. exact Hc.
  - intros c Hc. exact Hc.
  - intros F B F' B' _ IHF _ IHB c Hc. inversion Hc; subst.
    apply cnf_pi; [ apply IHF | apply IHB ]; assumption.
  - intros F B F' B' _ IHF _ IHB c Hc. inversion Hc; subst.
    apply cnf_piI; [ apply IHF | apply IHB ]; assumption.
  - intros b b' _ IH c Hc. inversion Hc; subst. apply cnf_lam. apply IH; assumption.
  - intros b b' _ IH c Hc. inversion Hc; subst. apply cnf_lamI. apply IH; assumption.
  - intros k p Hp. inversion Hp; subst. apply cne_var.
  - intros rA lA A scrut A' scrut' _ IHA _ IHs p Hp. inversion Hp; subst.
    apply cne_emptyrec; [ apply IHA | apply IHs ]; assumption.
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa p Hp. inversion Hp; subst.
    apply cne_app; [ apply IHf | apply IHF | apply IHB | apply IHa ]; assumption.
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa p Hp. inversion Hp; subst.
    apply cne_appI; [ apply IHf | apply IHF | apply IHB | apply IHa ]; assumption.
Qed.

Definition conv_nf_trans : forall a b c, conv_nf a b -> conv_nf b c -> conv_nf a c :=
  fun a b c H => fst conv_trans a b H c.
Definition conv_ne_trans : forall n m p, conv_ne n m -> conv_ne m p -> conv_ne n p :=
  fun n m p H => snd conv_trans n m H p.

(* ===================================================================== *)
(* Stability of structural conversion under SHIFT.  [shift_val]/[shift_ne] *)
(* apply the SAME index map to both members (the variable case stays       *)
(* [nVar k] on both sides), so structure -- and hence [conv_nf]/[conv_ne]  *)
(* -- is preserved.  Needed by the [n_conv] case of [weaken_typing]        *)
(* (Preservation.v).                                                        *)
(* ===================================================================== *)
Lemma conv_shift :
  (forall a b, conv_nf a b -> forall c d, conv_nf (shift_val c d a) (shift_val c d b))
  * (forall n m, conv_ne n m -> forall c d, conv_ne (shift_ne c d n) (shift_ne c d m)).
Proof.
  apply (conv_mutind
    (fun a b (_ : conv_nf a b) => forall c d, conv_nf (shift_val c d a) (shift_val c d b))
    (fun n m (_ : conv_ne n m) => forall c d, conv_ne (shift_ne c d n) (shift_ne c d m))).
  - intros n m _ IH c d. cbn [shift_val]. apply cnf_ne. apply IH.
  - intros c d. apply cnf_zero.
  - intros v w _ IH c d. cbn [shift_val]. apply cnf_suc. apply IH.
  - intros c d. apply cnf_nat.
  - intros c d. apply cnf_empty.
  - intros F B F' B' _ IHF _ IHB c d. cbn [shift_val]. apply cnf_pi; [ apply IHF | apply IHB ].
  - intros F B F' B' _ IHF _ IHB c d. cbn [shift_val]. apply cnf_piI; [ apply IHF | apply IHB ].
  - intros b b' _ IH c d. cbn [shift_val]. apply cnf_lam. apply IH.
  - intros b b' _ IH c d. cbn [shift_val]. apply cnf_lamI. apply IH.
  - intros k c d. cbn [shift_ne]. apply cne_var.
  - intros rA lA A scrut A' scrut' _ IHA _ IHs c d. cbn [shift_ne].
    apply cne_emptyrec; [ apply IHA | apply IHs ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa c d. cbn [shift_ne].
    apply cne_app; [ apply IHf | apply IHF | apply IHB | apply IHa ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa c d. cbn [shift_ne].
    apply cne_appI; [ apply IHf | apply IHF | apply IHB | apply IHa ].
Qed.

Definition conv_nf_shift : forall a b, conv_nf a b -> forall c d,
    conv_nf (shift_val c d a) (shift_val c d b) := fst conv_shift.
Definition conv_ne_shift : forall n m, conv_ne n m -> forall c d,
    conv_ne (shift_ne c d n) (shift_ne c d m) := snd conv_shift.
