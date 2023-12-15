Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Base Bool Datatypes.String Lists.List.
Import ListNotations.
Import BoolNotations.
Open Scope string.
Open Scope list.

From Utils Require Import Base.

Lemma invert_eq_0_S x : 0 = S x <-> False.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_0_S : utils.

Lemma invert_eq_S_0 x : S x = 0 <-> False.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_S_0 : utils.

Lemma invert_eq_S_S x y : S x = S y <-> x = y.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_S_S : utils.
