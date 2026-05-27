Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Gluing Require Import CutTModel.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Env.
Import Core.Notations.

(* The normalization (gluing) model as a cut-free Type-valued model over the
   first-order cast-free OTT language. Two terms are related when they evaluate to
   the same semantic value in the reflecting environment of their sort's context
   [G] (which [eval_env] builds by normalizing [G] to its ext-telescope). Two
   sorts are related when they share a head and a normalized context.

   This file gives the judgments [Norm : CutTModel]; the CutTModel_ok operations
   (the per-former congruence/computation coherence) come next. *)
Section Model.
  Notation term := (@term string).
  Notation sort := (@sort string).
  Notation ctx := (@ctx string).

  Definition sort_head (S : sort) : string := match S with scon n _ => n end.
  Definition sort_env (S : sort) : term :=
    match S with scon _ (G :: _) => G | _ => con "emp" [] end.

  Definition norm_ceq_term (t : sort) (e1 e2 : term) : Type :=
    match t with
    | scon n (G :: _) =>
        if eqb n "exp"
        then { v : sval & (eval_rel (eval_env G) e1 v * eval_rel (eval_env G) e2 v)%type }
        else if eqb n "ty"
        then { S : svalty & (eval_ty (eval_env G) e1 S * eval_ty (eval_env G) e2 S)%type }
        else if eqb n "sub"
        then { rr : senv & (eval_sub (eval_env G) e1 rr * eval_sub (eval_env G) e2 rr)%type }
        else unit
    | _ => (eval_env e1 = eval_env e2)    (* the [env] sort (no args) *)
    end.

  Definition norm_ceq_sort (S1 S2 : sort) : Type :=
    ((eqb (sort_head S1) (sort_head S2) = true)
     * (eval_env (sort_env S1) = eval_env (sort_env S2)))%type.

  Definition Norm : CutTModel :=
    {|
      ceq_sort := norm_ceq_sort;
      ceq_term := norm_ceq_term;
    |}.

End Model.
