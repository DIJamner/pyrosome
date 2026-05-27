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

(* Readback for the environment-free first-order NbE model: a structural fixpoint
   turning a semantic value back into a (normal-form) term.  A neutral with de Bruijn
   index head [nVar k] reads back to the variable [k] levels in — [hd] under [k]
   weakenings.  Annotation slots use a placeholder [ann]: faithful annotations are
   type-directed and need the typing context (TODO, the soundness direction); the
   point here is that values DO read back to syntactic normal forms. *)
Section Reify.
  Notation term := (@term string).

  Definition ann : term := con "_ann" [].

  (* one weakening: e |-> exp_subst wkn e *)
  Definition wk1 (e : term) : term :=
    con "exp_subst" [e; ann; ann; con "wkn" [ann; ann; ann]; ann; ann].

  Fixpoint reify_ty (T : svalty) : term :=
    match T with
    | dNe n => con "El" [reify_ne n; ann; ann; ann]
    | dNat => con "Nat" [ann]
    | dEmpty => con "Empty" [ann]
    | dU r l => con "U" [l; r; ann]
    end
  with reify_val (v : sval) : term :=
    match v with
    | vNe n => reify_ne n
    | vZero => con "zero" [ann]
    | vSuc v' => con "suc" [reify_val v'; ann]
    | vCode T => reify_ty T
    end
  with reify_ne (n : neutral) : term :=
    match n with
    | nVar k => Nat.iter k wk1 (con "hd" [ann; ann; ann])
    | nEmptyrec rA lA A scrut =>
        con "Emptyrec" [reify_ne scrut; reify_val A; lA; rA; ann]
    end.

End Reify.
