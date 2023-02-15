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

(* TODO: look into how many prop rules are necessary when intuition exists *)
