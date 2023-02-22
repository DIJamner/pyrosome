Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool List.
Import ListNotations.
Import BoolNotations.
Open Scope list.

Require Import Utils.Base.

Lemma eqb_refl_inv A (x : A) : x = x <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite eqb_refl_inv : utils.

Lemma not_True : ~ True <-> False.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite not_True : utils.

Lemma not_False : ~ False <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite not_False : utils.


Lemma False_and P : False /\ P <-> False.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite False_and : utils.

Lemma and_False P : P /\ False <-> False.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite and_False : utils.

Lemma False_or P : False \/ P <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite False_or : utils.

Lemma or_False P : P \/ False <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite or_False : utils.

Lemma True_and P : True /\ P <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite True_and : utils.

Lemma and_True P : P /\ True <-> P.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite and_True : utils.

Lemma True_or P : True \/ P <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite True_or : utils.

Lemma or_True P : P \/ True <-> True.
Proof.
  intuition congruence.
Qed.
#[export] Hint Rewrite or_True : utils.

(* TODO: look into how many prop rules are necessary when intuition exists *)
