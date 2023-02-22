Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Base Booleans Eqb Default.

Section __.
  Context (A : Type)
    `{Eqb_ok A}.  

  Lemma invert_none_some (x : A)
    : None = Some x <-> False.
  Proof.
    solve_invert_constr_eq_lemma.
  Qed.
  Hint Rewrite invert_none_some : utils.

  Lemma invert_some_none (x : A)
    : Some x = None <-> False.
  Proof.
    solve_invert_constr_eq_lemma.
  Qed.
  Hint Rewrite invert_some_none : utils.
  
  Lemma invert_some_some (x y : A)
    : Some x = Some y <-> x = y.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_some_some : utils.

  #[export] Instance option_eqb : Eqb (option A) :=
    fun a b =>
      match a, b with
      | Some a, Some b => eqb a b
      | None, None => true
      | _, _ => false
      end.

  #[export] Instance option_eqb_ok : Eqb_ok option_eqb.
  Proof.
    unfold Eqb_ok, option_eqb, eqb.
    intros a b;
      destruct a;
      destruct b;
      basic_goal_prep;
      basic_utils_crush.
    pose proof (H0 a a0) as H'.
    unfold eqb in *.
    revert H'.
    case_match;
      basic_utils_crush.
  Qed.

  #[export] Instance option_default : WithDefault (option A) := None.

End __.

#[export] Hint Rewrite invert_none_some : utils.
#[export] Hint Rewrite invert_some_none : utils.
#[export] Hint Rewrite invert_some_some : utils.
