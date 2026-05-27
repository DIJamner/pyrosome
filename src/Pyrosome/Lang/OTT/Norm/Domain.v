Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

(* Semantic value domain for the cast-free OTT NbE / gluing model.

   [svalty]: semantic types (interpretations of OTT codes/types). [sval]: semantic
   values (elements). Functions/binders are represented by CLOSURES — a captured
   environment [list sval] together with a syntactic body — rather than HOAS Coq
   functions (which would be a non-strictly-positive occurrence and is rejected),
   and rather than presheaf/Kripke families (avoided per the design).

   Neutrals carry their (already-normal) syntactic form as a [term], so [reify] on
   a neutral is a projection. [vCode]/[dU] handle the Tarski universe: an element of
   [U_{r,l}] is a code, i.e. a semantic type at the level below. *)
Section Domain.
  Notation term := (@term string).

  Unset Elimination Schemes.
  Inductive svalty : Type :=
  | dNe   (T : term)                                  (* neutral type (normal form) *)
  | dNat
  | dEmpty
  | dU    (r l : term)                                (* the universe U_{r,l} as a type *)
  | dPi   (dom : svalty) (cod_env : list sval) (cod_body : term)
  | dSig  (d1 : svalty) (d2_env : list sval) (d2_body : term)
  with sval : Type :=
  | vNe   (e : term)                                  (* neutral value (normal form) *)
  | vZero
  | vSuc  (v : sval)
  | vPair (v1 v2 : sval)
  | vLam  (env : list sval) (body : term)             (* closure *)
  | vCode (T : svalty).                               (* element of U: a code *)
  Set Elimination Schemes.

  (* A semantic environment assigns a value to each (object-level) variable. *)
  Definition senv := list sval.

End Domain.
