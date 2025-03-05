Set Implicit Arguments.

From Utils Require Import Base Booleans Eqb Default.
From coqutil Require Export Option.

Section __.
  Context (A : Type).

  #[export] Instance option_default : WithDefault (option A) := None.

  
  Definition Is_Some (x : option A) := if x then True else False.

End __.
