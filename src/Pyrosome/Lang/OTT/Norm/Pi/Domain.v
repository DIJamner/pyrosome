Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

(* ===================================================================== *)
(* Semantic value domain for the cast-free OTT NbE / gluing model,        *)
(* EXTENDED with the dependent-product (Pi) binder fragment.              *)
(*                                                                        *)
(* This is the Pi-capable successor of [OTT/Norm/Domain.v].  The first-   *)
(* order design (environment-free, de Bruijn INDEX values, values =       *)
(* normal forms) is preserved; the new ingredients the binder fragment    *)
(* forces are:                                                            *)
(*                                                                        *)
(*   - value forms for codes [vPi]/[vPiI], lambdas [vLam]/[vLamI], and    *)
(*     a neutral application spine [nApp]/[nAppI] (rel / irr variants).    *)
(*     These are LEAN: a [vPi] stores only its domain/codomain CODES      *)
(*     (the universe levels live in the [eval_ty] index, not the value),  *)
(*     and an [nApp] stores only its (neutral) head and argument (the     *)
(*     domain/codomain are recovered from the head's type when typing).   *)
(*                                                                        *)
(*   - a CUTOFF-indexed shift [shift_* c d]: shifting under a binder      *)
(*     leaves the de Bruijn indices below the cutoff [c] fixed and raises  *)
(*     the rest by [d].  (The first-order [shift_* 1] becomes              *)
(*     [shift_* 0 1].)  A [vLam]/[vPi] body lives under one extra binder,  *)
(*     so it is shifted at cutoff [S c].                                   *)
(*                                                                        *)
(*   - [apply] (substitution into normal forms) is NO LONGER a structural  *)
(*     [Fixpoint]: substituting a [vLam] for an applied variable creates   *)
(*     a beta redex, so [apply] becomes a RELATION (see [Apply.v]) doing    *)
(*     hereditary substitution.  Hence this file defines only the value     *)
(*     forms and the (still structural) cutoff shift.                       *)
(*                                                                        *)
(* Eta is handled by TYPE-DIRECTED reflection (also in [Apply.v]): a       *)
(* neutral at a (relevant) Pi type is eta-expanded to a [vLam], so the     *)
(* eta law holds on normal forms.  Hence [vNe] inhabits only base types;   *)
(* an [nApp] spine has a function-typed head but bottoms out at a base     *)
(* type. *)
Section Domain.
  Notation term := (@term string).

  Unset Elimination Schemes.
  Inductive svalty : Type :=
  | dU    (r l : term)                   (* universe U_{r,l}; r,l are nf_info-normal *)
  | dEl   (e : sval)                     (* El of a code-value (typically a neutral) *)
  with sval : Type :=
  | vNe   (n : neutral)                  (* neutral value (base type only) *)
  | vZero
  | vSuc  (v : sval)
  | vNat                                 (* the code [Nat] (element of U) *)
  | vEmpty                               (* the code [Empty] (element of U) *)
  | vPi   (F B : sval)                   (* code [Pi_rel]; B is the codomain, under a binder *)
  | vPiI  (F B : sval)                   (* code [Pi_irr] *)
  | vLam  (b : sval)                     (* lambda (relevant); body under a binder *)
  | vLamI (b : sval)                     (* lambda (proof-irrelevant) *)
  with neutral : Type :=
  | nVar  (k : nat)                      (* de Bruijn index (0 = innermost) *)
  | nEmptyrec (rA lA : term) (A : sval) (scrut : neutral)
  | nApp  (f : neutral) (a : sval)       (* relevant application [f a] *)
  | nAppI (f : neutral) (a : sval).      (* irrelevant application *)
  Set Elimination Schemes.

  (* A semantic SUBSTITUTION: the values to substitute for the in-scope variables. *)
  Definition ssub := list sval.

  (* A semantic ENVIRONMENT: the (semantic) TYPES of an object context's variables. *)
  Definition senv := list svalty.

  (* Cutoff-indexed renaming.  [shift_* c d] leaves indices [< c] fixed and raises
     the rest by [d]; recursing under a binder bumps the cutoff to [S c].  The
     first-order use [shift_* 1] is recovered as [shift_* 0 1]. *)
  Fixpoint shift_val (c d : nat) (v : sval) : sval :=
    match v with
    | vNe n => vNe (shift_ne c d n)
    | vZero => vZero
    | vSuc v' => vSuc (shift_val c d v')
    | vNat => vNat
    | vEmpty => vEmpty
    | vPi F B => vPi (shift_val c d F) (shift_val (S c) d B)
    | vPiI F B => vPiI (shift_val c d F) (shift_val (S c) d B)
    | vLam b => vLam (shift_val (S c) d b)
    | vLamI b => vLamI (shift_val (S c) d b)
    end
  with shift_ne (c d : nat) (n : neutral) : neutral :=
    match n with
    | nVar k => nVar (if Nat.ltb k c then k else k + d)
    | nEmptyrec rA lA A s => nEmptyrec rA lA (shift_val c d A) (shift_ne c d s)
    | nApp f a => nApp (shift_ne c d f) (shift_val c d a)
    | nAppI f a => nAppI (shift_ne c d f) (shift_val c d a)
    end.

  Definition shift_ty (c d : nat) (T : svalty) : svalty :=
    match T with
    | dU r l => dU r l
    | dEl e => dEl (shift_val c d e)
    end.

End Domain.

(* Mutual induction principle for the value domain. *)
Scheme svalty_rect := Induction for svalty Sort Type
  with sval_rect   := Induction for sval   Sort Type
  with neutral_rect := Induction for neutral Sort Type.
Combined Scheme sval_mutind from svalty_rect, sval_rect, neutral_rect.
