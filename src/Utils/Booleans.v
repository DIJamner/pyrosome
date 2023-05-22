Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool Lists.List.
Export Bool (Is_true).
Import ListNotations.
Export BoolNotations.
Open Scope list.

Require Import Utils.Base.

(****************
Definitions
*****************)

(* grouped right with the fixpoint for better decreasing argument analysis*)
Definition all2 := 
fun (S T : Type) (r : S -> T -> bool) =>
fix all2 (s : list S) (t : list T) {struct s} : bool :=
  match s, t with
  | [], [] => true
  | x :: s0, y::t0 => r x y && all2 s0 t0
  | _,_ => false
  end.


(****************
Rewrites
*****************)

Lemma eq_true_to_Is_true b
  : b = true <-> Is_true b.
Proof.
  destruct b; basic_goal_prep;
    basic_utils_crush.
  intuition congruence.
Qed.
#[export] Hint Rewrite eq_true_to_Is_true : utils.


Lemma true_eq_to_Is_true b
  : true = b <-> Is_true b.
Proof.
  destruct b; basic_goal_prep;
    basic_utils_crush.
  intuition congruence.
Qed.
#[export] Hint Rewrite true_eq_to_Is_true : utils.


Lemma eq_false_to_Is_true b
  : b = false <-> ~Is_true b.
Proof.
  destruct b; basic_goal_prep;
    basic_utils_crush.
Qed.
#[export] Hint Rewrite eq_false_to_Is_true : utils.


Lemma false_eq_to_Is_true b
  : false = b <-> ~Is_true b.
Proof.
  destruct b; basic_goal_prep;
    basic_utils_crush.
Qed.
#[export] Hint Rewrite false_eq_to_Is_true : utils.

Lemma orb_prop_iff
  : forall a b : bool, Is_true (a || b) <-> Is_true a \/ Is_true b.
Proof.
  split;
    [ apply orb_prop_elim
    | apply orb_prop_intro].
Qed.
#[export] Hint Rewrite orb_prop_iff : utils.


Lemma andb_prop_iff
  : forall a b : bool, Is_true (a && b) <-> Is_true a /\ Is_true b.
Proof.
  split;
    [ apply andb_prop_elim
    | apply andb_prop_intro].
Qed.
#[export] Hint Rewrite andb_prop_iff : utils.

Lemma negb_prop_iff
  : forall a : bool, Is_true (negb a) <-> ~Is_true a.
Proof.
  split;
    [ apply negb_prop_elim
    | apply negb_prop_intro].
Qed.
#[export] Hint Rewrite negb_prop_iff : utils.


Lemma Is_true_true : Is_true true <-> True.
Proof. cbv; intuition. Qed.
#[export] Hint Rewrite Is_true_true : utils.

Lemma Is_true_false : Is_true false <-> False.
Proof. cbv; intuition. Qed.
#[export] Hint Rewrite Is_true_false : utils.

(* TODO: make sure that these rewrites are done before the conversion to Prop
   so that we can get the full power of double-negation
 *)

#[export] Hint Rewrite negb_orb : utils.
#[export] Hint Rewrite negb_andb : utils.
#[export] Hint Rewrite negb_involutive : utils.




(****************
Resolution Lemmas
*****************)

Lemma Is_true_implies_eq_true b : Is_true b -> b = true.
Proof. destruct b; intuition. Qed.
(*TODO: any reason for this to be Resolve instead of Immediate?*)
#[export] Hint Immediate Is_true_implies_eq_true : utils.

Lemma Is_true_implies_true_eq b : Is_true b -> true = b.
Proof. destruct b; intuition. Qed.
(*TODO: any reason for this to be Resolve instead of Immediate?*)
#[export] Hint Immediate Is_true_implies_true_eq : utils.

