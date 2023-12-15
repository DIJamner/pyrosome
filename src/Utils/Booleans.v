Require Export Datatypes.List (forallb2).
Require Export Datatypes.Bool.

Require Import Utils.Base.

(* TODO: move these hints to coqutil *)

(*TODO: any reason for this to be Resolve instead of Immediate?*)
#[export] Hint Immediate Is_true_implies_eq_true : utils.
(*TODO: any reason for this to be Resolve instead of Immediate?*)
#[export] Hint Immediate Is_true_implies_true_eq : utils.
