Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool String List.
Import ListNotations.
Import BoolNotations.
Open Scope string.
Open Scope list.

From Utils Require Export Base Booleans Nats Props Eqb Default
  Lists Options Pairs NamedList.

(****************
Definitions
*****************)


Inductive len_eq {A} {B} : list A -> list B -> Type :=
| len_eq_nil : len_eq [] []
| len_eq_cons : forall a a' l l',
    len_eq l l' -> len_eq (a::l) (a'::l').


(*TODO: move to standard library? *)
Lemma string_of_list_ascii_length l
  : String.length (string_of_list_ascii l) = List.length l.
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
Qed.






(*TODO: redefine as skipn?*)
(* Reduce size of language terms for smaller goals *)
Fixpoint nth_tail {A} (n: nat) (l : list A) : list A :=
  match n,l with
  | 0,_ => l
  | S_,[]=> []
  | S n', _::l'=> nth_tail n' l'
  end.

Arguments nth_tail : simpl never.

Lemma nth_tail_nil A n : @nth_tail A n [] = [].
Proof.
  destruct n; simpl; reflexivity.
Qed.
#[export] Hint Rewrite nth_tail_nil : utils.

Lemma nth_tail_S_cons A n (e:A) l : nth_tail (S n) (e::l) = nth_tail n l.
Proof.
  reflexivity.
Qed.
#[export] Hint Rewrite nth_tail_S_cons : utils.


Lemma as_nth_tail: forall (A : Type) (l : list A), l = nth_tail 0 l.
Proof.
  intros; unfold nth_tail; reflexivity.
Qed.


Lemma nth_tail_to_cons A l n (x:A)
  : nth_error l n = Some x ->
    nth_tail n l = x::(nth_tail (S n) l).
Proof.
  revert l; induction n; destruct l;
    basic_goal_prep; basic_utils_crush.
Qed.

Lemma nth_tail_equals_cons_res A n l l' (x:A)
  : nth_tail n l = x :: l' -> l' = nth_tail (S n) l.
Proof.
  revert l l'; induction n; destruct l;
    basic_goal_prep; basic_utils_crush.
  cbv in H; inversion H; subst.
  reflexivity.
Qed.
  

Lemma nth_error_nil A n : @nth_error A [] n = None.
Proof.
  destruct n; simpl; auto.
Qed.
#[export] Hint Rewrite nth_error_nil : utils.


Module SumboolNotations.
  Notation "SB! e" :=
    (if e then left _ else right _)
      (at level 90).
  Notation "e1 'SB&' e2" :=
    (Sumbool.sumbool_and _ _ _ _ e1 e2)
      (at level 58, left associativity).
End SumboolNotations.
Import SumboolNotations.

(*TODO: move to Pairs.v *)
Definition pair_eq_dec {A B}
           (A_eq_dec : forall s1 s2 : A, {s1 = s2} + {s1 <> s2})
           (B_eq_dec : forall s1 s2 : B, {s1 = s2} + {s1 <> s2})
           (p1 p2 : A*B)
  : {p1 = p2} + {~p1 = p2}.
  refine (match p1, p2 with
          | (a1,b1),(a2,b2) =>
            SB! (A_eq_dec a1 a2) SB& (B_eq_dec b1 b2)
          end); basic_utils_crush.
Defined.

Fixpoint incl_dec {A} (eq_dec : forall s1 s2 : A, {s1 = s2} + {s1 <> s2})
         (l1 l2 : list A) {struct l1} : {incl l1 l2} + {~ incl l1 l2}.
  refine(match l1 with
         | [] => left _
         | a::l1' =>
           SB! (in_dec eq_dec a l2) SB& (incl_dec _ _ l1' l2)
         end); basic_utils_firstorder_crush.
Defined.

