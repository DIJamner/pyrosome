From Ltac2 Require Import Ltac2 Std Option.
Set Default Proof Mode "Classic".

(* Uses vm_compute if do_check is idtac and vm_cast_no_check if do_check is fail*)
Ltac exact_check_if do_check v :=
  tryif do_check then (vm_compute; exact v)
  else vm_cast_no_check v.

Goal (if true then True else False).
  exact_check_if idtac I.
  Undo.
  exact_check_if fail I.
Abort.

Goal (if false then True else False).
  Fail exact_check_if idtac I.
  exact_check_if fail I.
Abort.

(* Used to locally set a flag for checking computations during proof development *)
Ltac2 mutable do_check_computations := false.

Ltac2 flagged_exact p :=
  if do_check_computations then vm_compute; exact $p
  else vm_cast_no_check p.

Ltac flagged_exact :=
  ltac2:(p |- flagged_exact (get (Ltac1.to_constr p))).
