Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound StlcNormalization.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC.
Import Core.Notations.

(* Groundwork for the normalization model of [stlc ++ exp_subst ++ value_subst].

   DESIGN.  The meta-level context is closed ([c = []]); openness is carried at
   the object level by the environment [G], so an "open term in context G" is a
   closed Pyrosome term of sort [#"exp" G A].  Object-level variables are
   therefore [hd] and its [wkn]-shifts, not meta-level variables -- which makes
   the [cterm_var] obligation vacuous.  Relations are needed at all five sorts
   ([env], [ty], [sub], [val], [exp]), since [ceq_args] threads through every
   argument of every rule, including the index arguments.

   SHAPES.  The surface notation and the internal representation disagree, so
   every shape below was read off the compiled language, not the notation: a
   rule's context is stored most-recent-first and [con]'s argument list follows
   that order.  Hence [#"app" "G" "A" "B" e e'] is [con "app" [e';e;B;A;G]].
   Note also that [hd], [wkn], [id], [forget] carry their index arguments in the
   [con] list even though their [args] field is empty. *)

(* ---- sorts ---- *)
Definition Sty : sort := scon "ty" [].
Definition Senv : sort := scon "env" [].
Definition Ssub (G G' : term) : sort := scon "sub" [G'; G].
Definition Sval (G A : term) : sort := scon "val" [A; G].
Definition Sexp (G A : term) : sort := scon "exp" [A; G].

(* ---- term constructors (verified against the compiled language) ---- *)
Definition Arr (A B : term) : term := con "->" [B; A].
Definition Unit : term := con "unit" [].
Definition Tt (G : term) : term := con "tt" [G].
Definition Emp : term := con "emp" [].
Definition Ext (G A : term) : term := con "ext" [A; G].
Definition Id (G : term) : term := con "id" [G].
Definition Forget (G : term) : term := con "forget" [G].
Definition Cmp (G1 G2 G3 f g : term) : term := con "cmp" [g; f; G3; G2; G1].
Definition Wkn (G A : term) : term := con "wkn" [A; G].
Definition Hd (G A : term) : term := con "hd" [A; G].
Definition Snoc (G G' g A v : term) : term := con "snoc" [v; A; g; G'; G].
Definition ValSubst (G G' g A v : term) : term := con "val_subst" [v; A; g; G'; G].
Definition ExpSubst (G G' g A e : term) : term := con "exp_subst" [e; A; g; G'; G].
Definition Ret (G A v : term) : term := con "ret" [v; A; G].
Definition Lam (G A B e : term) : term := con "lambda" [e; B; A; G].
Definition App (G A B e e' : term) : term := con "app" [e'; e; B; A; G].

(* ---- well-shapedness of the index syntax ----

   [ty] is a plain sort ([sort_rule [] []]) in this presentation, so with a
   closed meta-context a type is built from the base type and [->] alone.  This
   is the language [stlc_unit], where [unit_lang] supplies that base case; over
   bare [stlc] the predicate would be empty and every normalization statement
   vacuous.  Recursion on [TyOk] is what makes the reducibility relation well
   founded. *)
Inductive TyOk : term -> Prop :=
| tyok_unit : TyOk Unit
| tyok_arr : forall A B, TyOk A -> TyOk B -> TyOk (Arr A B).

Inductive EnvOk : term -> Prop :=
| envok_emp : EnvOk Emp
| envok_ext : forall G A, EnvOk G -> TyOk A -> EnvOk (Ext G A).

