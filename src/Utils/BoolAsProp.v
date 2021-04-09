Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.


Create HintDb bool_utils discriminated.

Lemma bool_to_prop_andb b1 b2 : b1 && b2 <-> b1 /\ b2.
Proof.
  split; move /andP; auto.
Qed.
Hint Rewrite bool_to_prop_andb : bool_utils.


Lemma bool_to_prop_orb b1 b2 : b1 || b2 <-> b1 \/ b2.
Proof.
  split; move /orP; auto.
Qed.
Hint Rewrite bool_to_prop_orb : bool_utils.


Lemma bool_to_prop_negb b: ~~ b <-> ~ b.
Proof.
  split; move /negP; auto.
Qed.
Hint Rewrite bool_to_prop_negb : bool_utils.

Lemma rewrite_reflect A B b
  : (A <-> B) -> reflect B b -> reflect A b.
Proof.
  intros AB Br; inversion Br; constructor; intuition.
Qed.

Ltac reflect_from_iff thm :=
  eapply rewrite_reflect; [rewrite <- thm; apply iff_refl| simple apply idP].

Require Import String.
Lemma rewrite_string_eqb s1 s2
  : (s1 =? s2)%string = (s1 == s2).
Proof.
  reflexivity.
Qed.
Hint Rewrite rewrite_string_eqb : bool_utils.
Lemma rewrite_opt_eq_eqb (A:eqType) (a b : option A)
  : (opt_eq a b) = (a == b).
Proof.
  reflexivity.
Qed.
Hint Rewrite rewrite_opt_eq_eqb : bool_utils.
Lemma rewrite_eqseq_eqb (A:eqType) (a b : list A)
  : (eqseq a b) = (a == b).
Proof.
  reflexivity.
Qed.
Hint Rewrite rewrite_eqseq_eqb : bool_utils.
Lemma rewrite_true_equal a
  : (true = a) <-> (is_true a).
Proof.
  easy.
Qed.
Hint Rewrite rewrite_true_equal : bool_utils.
Lemma rewrite_eqb_equal (A:eqType) (a b : A)
  : (a == b) <-> (a = b).
Proof.
  split; [move /eqP; auto|intros; apply /eqP => //].
Qed.
Hint Rewrite rewrite_eqb_equal : bool_utils.
Lemma rewrite_false_equal a
  : (false = a) <-> (~ is_true a).
Proof.
  split.
  {
    intro H.
    rewrite <- H.
    easy.
  }
  {
    intro H.
    symmetry.
    apply /negP.
    assumption.
  }
Qed.
Hint Rewrite rewrite_false_equal : bool_utils.

Hint Rewrite Bool.andb_true_r : bool_utils.
Hint Rewrite Bool.andb_false_r : bool_utils.



Lemma invert_Some_eq (A : eqType) (a1 a2 : A)
  : (Some a1 = Some a2) <-> (a1 = a2).
Proof.
  intuition; subst; try inversion H;
  reflexivity.
Qed.
Hint Rewrite invert_Some_eq : bool_utils.

Lemma iff_sym A (a b : A) : (a = b) <-> (b = a).
Proof.
  intuition.
Qed.
Hint Immediate iff_sym : bool_utils.

Lemma false_False : false <-> False. intuition. Qed.
Hint Rewrite false_False : bool_utils.
Lemma true_True : true <-> True. intuition. Qed.
Hint Rewrite true_True : bool_utils.


Hint Extern 4 => match goal with [H : False |-_] => safe_invert H end : bool_utils.


Lemma peel_exists_iff A (P Q : A -> Prop)
  : (forall e, P e <-> Q e) ->
    (exists e, P e) <-> (exists e, Q e).
Proof.
  intro ptq.
  setoid_rewrite ptq.
  apply iff_refl.
Qed.
Hint Resolve peel_exists_iff : bool_utils.

Lemma and_iff_compat A B C D
  : A <-> C ->
    B <-> D ->
    A /\ B <-> C /\ D.
Proof.
  intuition.
Qed.
Hint Resolve and_iff_compat : bool_utils.

Hint Immediate iff_refl : bool_utils.

Lemma rewrite_reflexivity A (a :A)
  : (a = a) <-> True.
Proof.
  intuition.
Qed.
Hint Rewrite rewrite_reflexivity : bool_utils.


Hint Rewrite eq_refl : bool_utils.
