Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Uint63.
Local Open Scope string_scope.


Section __.
  Context (A : Type).
  
  (* Not defined as a record so that firstorder doesn't mess with it*)
  Definition WithDefault := A.
  Definition default {d : WithDefault} : A := d.
  Existing Class WithDefault.

  
  Definition unwrap_with_default `{WithDefault} ma : A :=
    match ma with None => default | Some a => a end.

End __.


Arguments default {A}%_type_scope {d}.

#[export] Instance string_default : WithDefault string := "".
#[export] Instance unit_default : WithDefault unit := tt.

#[export] Instance int_default : WithDefault int := 0%int63.
