From coqutil Require Import Datatypes.Result.

(*TODO: is there a better place for this?
  Used to put some info in the type of a failing computation.
 *)
Inductive Impossible {A} (a:A) : Prop := .
Definition Is_Success {A} (r : result A) : Prop :=
  if r then True else Impossible r.

Definition true_or (b:bool) els : result unit :=
  if b then Success tt else els.

Definition Some_or {A} (b:option A) els : result A :=
  match b with
  | Some a => Success a
  | None => els
  end.

