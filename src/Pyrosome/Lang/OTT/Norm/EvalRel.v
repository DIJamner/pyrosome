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

(* Relational evaluator for the cast-free OTT NbE model (first-order fragment:
   the substitution calculus + U/El + Nat/Empty; no Pi/Sig yet).

   Three mutual relations over a semantic environment [senv = list sval] (object-
   level de Bruijn, [hd] = index 0):
     eval_sub  : senv -> term -> senv  -> Type   (substitution terms)
     eval_ty   : senv -> term -> svalty -> Type  (type terms: U, El, ty_subst)
     eval_rel  : senv -> term -> sval  -> Type    (expression terms)

   A substitution g : sub G G' acts on environments G->G' (covariantly on envs);
   codes (Nat/Empty) are expressions of U, evaluating to [vCode ...]; the type is
   recovered by [El] decoding the code. Free (Pyrosome meta) variables reflect to
   neutrals carrying their own (already-normal) syntactic form, so [Emptyrec] of a
   neutral is itself neutral. Arities per the dumped table. Totality on well-typed
   terms comes from the generic pf-eval, not from these relations. *)
Section EvalRel.
  Notation term := (@term string).

  Inductive eval_sub : senv -> term -> senv -> Type :=
  | ev_id   : forall r G, eval_sub r (con "id" [G]) r
  | ev_wkn  : forall r v G i A, eval_sub (v :: r) (con "wkn" [A; i; G]) r
  | ev_forget : forall r G, eval_sub r (con "forget" [G]) []
  | ev_cmp  : forall r r' r'' G3 G2 G1 f g,
      eval_sub r f r' -> eval_sub r' g r'' ->
      eval_sub r (con "cmp" [g; f; G3; G2; G1]) r''
  | ev_snoc : forall r r' vv G G' i A g v,
      eval_sub r g r' -> eval_rel r v vv ->
      eval_sub r (con "snoc" [v; g; A; i; G'; G]) (vv :: r')
  (* meta substitution-variable: never fires under c=[] (meta-substitutions do not
     occur in normalization); present only for totality of cterm_var. *)
  | ev_sub_var : forall r x, eval_sub r (var x) r

  with eval_ty : senv -> term -> svalty -> Type :=
  | ev_U    : forall r G rl l, eval_ty r (con "U" [l; rl; G]) (dU rl l)
  | ev_El   : forall r G rl l e T,
      eval_rel r e (vCode T) ->
      eval_ty r (con "El" [e; l; rl; G]) T
  | ev_ty_subst : forall r r' G G' g i A T,
      eval_sub r g r' -> eval_ty r' A T ->
      eval_ty r (con "ty_subst" [A; i; g; G'; G]) T
  (* meta type-variable: never fires under the empty meta-context (c=[]); present
     only so the universal cterm_var field is total. *)
  | ev_ty_var : forall r x, eval_ty r (var x) (dNe (var x))

  with eval_rel : senv -> term -> sval -> Type :=
  | ev_hd   : forall r v G i A, eval_rel (v :: r) (con "hd" [A; i; G]) v
  | ev_exp_subst : forall r r' G G' g i A e v,
      eval_sub r g r' -> eval_rel r' e v ->
      eval_rel r (con "exp_subst" [e; A; i; g; G'; G]) v
  | ev_var  : forall r x, eval_rel r (var x) (vNe (var x))
  | ev_zero : forall r G, eval_rel r (con "zero" [G]) vZero
  | ev_suc  : forall r G n v,
      eval_rel r n v -> eval_rel r (con "suc" [n; G]) (vSuc v)
  | ev_Nat  : forall r G, eval_rel r (con "Nat" [G]) (vCode dNat)
  | ev_Empty : forall r G, eval_rel r (con "Empty" [G]) (vCode dEmpty)
  | ev_Emptyrec : forall r G rA lA A e ne,
      eval_rel r e (vNe ne) ->
      eval_rel r (con "Emptyrec" [e; A; lA; rA; G])
               (vNe (con "Emptyrec" [ne; A; lA; rA; G])).

End EvalRel.
