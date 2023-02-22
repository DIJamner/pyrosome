Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
Local Open Scope string_scope.

From Utils Require Import Base.

Section __.
  Context (A : Type).
  
  (* Not defined as a record so that firstorder doesn't mess with it*)
  Definition WithDefault := A.
  Definition default {d : WithDefault} : A := d.
  Existing Class WithDefault.

  
  Definition unwrap_with_default `{WithDefault} ma : A :=
    match ma with None => default | Some a => a end.

End __.


Arguments default {A}%type_scope {d}.

#[export] Instance string_default : WithDefault string := "".
#[export] Instance unit_default : WithDefault unit := tt.

(* TODO: determine why this was added and remove
Hint Extern 10 (WithDefault _) => solve [typeclasses eauto].

 *)
