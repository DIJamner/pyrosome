From Stdlib Require Import Lists.List.
Import ListNotations.


From Ltac2 Require Import Ltac2 Control List.
Set Default Proof Mode "Classic".


From Utils Require Import Utils.

Create HintDb test discriminated.

Variant tag {A} (a:A) : Prop := mkTag.



Inductive top_level.
Inductive fresh_check.
Inductive leaf.

#[local] Definition tag0 := mkTag (0, leaf).
Hint Resolve tag0 : test.
#[local] Definition tag1 := mkTag (1, leaf).
Hint Resolve tag1 : test.
#[local] Definition tag2 := mkTag (2, leaf).
Hint Resolve tag2 : test.
#[local] Definition tag3 := mkTag (3, leaf).
Hint Resolve tag3 : test.
#[local] Definition tag4 := mkTag (4, leaf).
Hint Resolve tag4 : test.
#[local] Definition tag5 := mkTag (5, leaf).
Hint Resolve tag5 : test.

Ltac really_assert_fails tac :=
  assert_fails (assert_succeeds tac).

Lemma contract_tag {A} (a:A)
  : tag (a, leaf) -> tag (a, fresh_check) -> tag (a,top_level).
Proof. constructor. Qed.
Hint Resolve contract_tag : enum.


Lemma setup_tag {A} (a:A)
  : tag (a, top_level) -> tag a.
Proof. constructor. Qed.


Ltac do_fresh_check a :=
  lazymatch goal with
  | H : tag a |- _ => fail
  | _ => constructor
  end.
Hint Extern 0 (tag (?a, fresh_check)) => do_fresh_check a : enum.

Ltac enumerate_db :=
  repeat
    (let x := open_constr:(_) in
     assert (tag x);
     [apply setup_tag;
      now eauto with enum test
     | not_evar x]).

Ltac2 list_tags () :=
  flat_map (fun p =>
              let (_,_,x) := p in
              lazy_match! x with
              | tag ?a => [a]
              | _ => []
              end)
     (hyps()).

Ltac2 rec list_to_syntax l :=
  match l with
  | [] => '[] (*Note:could cause type inference problems in some cases*)
  | a::l =>
      let l' := list_to_syntax l in
      '($a::$l')
  end.
Ltac2 define_hint_db_from_tags () :=
  let x := (focus 1 1 (fun () => list_to_syntax (list_tags ()))) in
  let y := (focus 1 1 (fun () => eval vm_compute in $x)) in
    dispatch [(fun _ => exact I); (fun _ => exact $y)].

(*TODO: there should be a better way to do this.
  Creates a new dummy goal to operate in without affecting the proof term.
  The new goal is the first one.
 *)
Ltac dummy_goal P :=
  unshelve (let x := open_constr:(_ : P) in idtac).

(*TODO: eliminate junk let bindings*)
Ltac define_hint_db :=
  dummy_goal True;
  [clear; enumerate_db |];
  ltac2:(|- define_hint_db_from_tags ()).

Definition my_db : list nat.
  define_hint_db.
Defined.
Print my_db.

(*TODO: separate example fro library
  TODO: separate out a library for listing hints from the tag stuff

 *)
  

Goal False.
  dummy_goal True.
  unshelve
  (let x := open_constr:(_ : nat) in
   idtac).
  {
    assert (True) by exact I.
Show Proof.
