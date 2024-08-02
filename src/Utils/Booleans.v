Require Export Datatypes.List (forallb2).
Require Export Datatypes.Bool.

Require Import Utils.Base Utils.Default.

(*TODO: move to Booleans or a new file *)
Definition compute_checked {b A} : (Is_true b -> A) -> option A :=
  if b as b return (Is_true b -> _) -> _
  then fun f => Some (f I)
  else fun _ => None.

(*TODO: move to Booleans or a new file *)
Definition compute_unchecked {b A} `{WithDefault A} : (Is_true b -> A) -> A :=
  if b as b return (Is_true b -> _) -> _
  then fun f => f I
  else fun _ => default.

Lemma compute_unchecked_eq {b A}  `{WithDefault A} (f : Is_true b -> A) Hb
  : compute_unchecked f = f Hb.
Proof.
  revert f Hb;
    destruct b; cbn;
    try tauto.
  destruct Hb; tauto.
Qed.

(* TODO: move these hints to coqutil *)

(*TODO: any reason for this to be Resolve instead of Immediate?*)
#[export] Hint Immediate Is_true_implies_eq_true : utils.
(*TODO: any reason for this to be Resolve instead of Immediate?*)
#[export] Hint Immediate Is_true_implies_true_eq : utils.
