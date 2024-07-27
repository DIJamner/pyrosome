Require Export coqutil.Tactics.ProveInversion.

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

(*TODO: deprecate *)
Ltac my_case eqnname exp :=
  destruct exp eqn:eqnname.
  (*
  let casevar := fresh "casevar" in
  remember exp as casevar eqn:eqnname;
  destruct casevar; symmetry in eqnname.
   *)


(* Performs inversion on H exactly when 
    either: 
    - no constructors can produce H and the goal is solved
    - exactly one constructor can produce H and inversion
      makes progress
 *)
Ltac safe_invert H :=
  let t := type of H in
  inversion H; clear H;
  let n := numgoals in
  guard n <= 1;
  lazymatch goal with
  | [ H' : t|-_]=>
    fail "safe_invert did not make progress"
  | _ => subst
  end.

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


Ltac basic_utils_crush := let x := autorewrite with bool utils in * in
                                  let y := eauto with utils in
                                          generic_crush x y.
Ltac basic_utils_firstorder_crush :=
  let x := autorewrite with bool utils in * in
          let y := eauto with utils in
                  generic_firstorder_crush x y.

Ltac basic_goal_prep := intros; break; simpl in *.


Ltac case_match' c :=
  lazymatch c with
  | context [match ?c' with _ => _ end] => case_match' c'
  | _ =>
      let e' := fresh in
      remember c as e'; destruct e'
  end.
Ltac case_match :=
  match goal with
  | |- context [ match ?e with
                 | _ => _
                 end ] => case_match' e
  end.

(* TODO: replace with similar tactic?
Require Import Tactics.Tactics
Print destruct_one_match.
*)
(*TODO: make case on innermost match?
  (*TOOD: replace case_match with this? Copied once already*)
  Ltac case_match' :=
    try lazymatch goal with
          [ H :  context [ match ?e with
                           | _ => _
                           end] |- _ ] => revert H
        end;
    case_match.
 *)
