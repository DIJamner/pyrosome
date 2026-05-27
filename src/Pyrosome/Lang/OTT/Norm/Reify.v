Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain.
Import Core.Notations.

(* Readback for the cast-free first-order NbE model.  No functions yet, so reify
   is an *untyped* structural fixpoint (no η-expansion): neutrals carry their own
   normal-form term, numerals/codes are rebuilt with the ambient env [G] in their
   annotation slot.  Pi/Sig cases are placeholders (unreachable for first-order
   results); they become type-directed/relational once η is added. *)
Section Reify.
  Notation term := (@term string).

  Definition reify_todo : term := con "_reify_TODO" [].

  Fixpoint reify_val (G : term) (v : sval) : term :=
    match v with
    | vNe e => e
    | vZero => con "zero" [G]
    | vSuc v' => con "suc" [reify_val G v'; G]
    | vCode T => reify_ty G T
    | vPair _ _ => reify_todo
    | vLam _ _ => reify_todo
    end
  with reify_ty (G : term) (T : svalty) : term :=
    match T with
    | dNe e => e
    | dNat => con "Nat" [G]
    | dEmpty => con "Empty" [G]
    | dU r l => con "U" [l; r; G]
    | dPi _ _ _ => reify_todo
    | dSig _ _ _ => reify_todo
    end.

End Reify.
