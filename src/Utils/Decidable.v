From Utils Require Import Utils.


Lemma bounded_exists_decidable (max : nat) P
  : (forall n, {P n} + {~ P n}) ->
    ({exists n : nat, n <= max /\ P n}
     + {~exists n : nat, n <= max /\ P n}).
Proof.
  intro dec_n.
  induction max.
  {
    destruct (dec_n 0); [left | right];
      basic_goal_prep;
      basic_utils_crush.
    eapply n.
    replace x with 0 in * by Lia.lia.
    auto.
  }
  {
    destruct (dec_n (S max)); [left | ];
      basic_goal_prep;
      basic_utils_crush.
    right;
      basic_goal_prep;
      basic_utils_crush.
    eqb_case x (S max);
      basic_goal_prep;
      basic_utils_crush.
    eapply b; exists x;
      basic_goal_prep;
      basic_utils_crush.
    Lia.lia.
  }
Qed.
