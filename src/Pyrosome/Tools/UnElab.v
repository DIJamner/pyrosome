Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Utils Require Export GoalDisplay.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

(*TODO: move to the right place*)
Definition as_ctx {V} (c:ctx V) :=c.
Notation "'{{c' c }}" := (as_ctx c) (at level 0, c custom ctx, only printing).

Ltac hide_implicits :=
  lazymatch goal with
  | |- eq_term ?l ?c ?t ?e1 ?e2 =>
      let c' := eval compute in (hide_ctx_implicits l c) in
        let t' := eval compute in (hide_sort_implicits l t) in
          let e1' := eval compute in (hide_term_implicits l e1) in
            let e2' := eval compute in (hide_term_implicits l e2) in
              change (eq_term l (lie_to_user (real:=c) (as_ctx c'))
                        (lie_to_user (real:=t) t')
                        (lie_to_user (real:=e1) e1')
                        (lie_to_user (real:=e2) e2'))
  end.

(*Use: `hide_implicits` shows the pre-elaboration terms,
  and `wysiwyg` shows the actual goal again.
 *)
