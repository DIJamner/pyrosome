(* For the hint db *)
From coqutil Require Export PropRewrite InversionRewrite.
From coqutil.Tactics Require Export ProveInversion safe_invert case_match.


(***************
 Tactics 
****************)

Tactic Notation "intro_to" constr(ty) :=
  repeat match goal with
         | |- ty -> _ => idtac
         | |- ty _ -> _ => idtac
         | |- ty _ _-> _ => idtac
         | |- ty _ _ _ -> _ => idtac
         | |- ty _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ _ -> _ => idtac
         | |- _ -> _ => intro
         | |- _ => fail 2 "could not find argument with head" ty
         end.


Ltac break :=
  repeat match goal with
         | [H: unit|-_]=> destruct H
         | [H: _*_|-_]=> destruct H
         | [H: _/\_|-_]=> destruct H
         | [H: exists x, _|-_]=> destruct H
         end.

#[deprecated(note="Use `destruct exp eqn:eqnname` instead.")]
Ltac my_case eqnname exp :=
  destruct exp eqn:eqnname.

Ltac generic_crush rewrite_tac hint_auto :=
  repeat (intuition break; subst; rewrite_tac;
          (*TODO: is this the best place for this? Maybe hints should handle it *)
          (*try typeclasses eauto;*)
          intuition unshelve hint_auto).
(* Uses firstorder, which can have strange edge cases
   and interacts poorly with terms
 *)
Ltac generic_firstorder_crush rewrite_tac hint_auto :=
  repeat (intuition break; subst; rewrite_tac;
          (*TODO: is this the best place for this?*)
          (*try typeclasses eauto;*)
          firstorder unshelve hint_auto).
(*try (solve [ repeat (unshelve f_equal; hint_auto)])). *)

Create HintDb utils discriminated.

(* Adds a hint to utils so that the rewriting base exists.
   TODO: find a better way for this.
 *)
#[export] Hint Rewrite pair_equal_spec : utils.

#[export] Hint Extern 100 => exfalso : utils.
#[export] Hint Extern 100 (_ _ = _ _) => f_equal : utils.


Ltac basic_utils_crush :=
  let x := autorewrite with bool rw_prop inversion utils in * in
        let y := eauto with utils in
            generic_crush x y.
Ltac basic_utils_firstorder_crush :=
  let x := autorewrite with bool rw_prop utils in * in
          let y := eauto with utils in
                  generic_firstorder_crush x y.

Ltac basic_goal_prep := intros; break; simpl in *.
