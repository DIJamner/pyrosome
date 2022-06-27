Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
Local Open Scope string.

(* Note: use with caution! *)
Definition lie_to_user {A B} {real:A} (fake : B) := real.

Notation "!! b" := (lie_to_user b) (at level 50, only printing).
(* give a good error message if a user copies and pastes *)
Notation "!! b" := (ltac:(fail "Do not copy-paste terms marked with '!!'. Use wysiwyg tactic first"))
                     (at level 50, only parsing).

Ltac wysiwyg :=
  cbv [lie_to_user] in *.

