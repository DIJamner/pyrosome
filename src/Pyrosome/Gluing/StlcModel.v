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

(* The reducibility (Tait) relation for [stlc ++ exp_subst ++ value_subst].

   Shape notes, verified against the compiled language rather than the surface
   notation, since the two disagree:  a rule's context is stored most-recent
   first, and [con]'s argument list follows that order.  So the concrete syntax
   [#"app" "G" "A" "B" e e'] is [con "app" [e'; e; B; A; G]].

   [ty] here is a *plain* sort ([sort_rule [] []]) -- this is the simply typed
   presentation, so a type is built from [->] and type variables only, with no
   base type constructor and no dependence on the environment.  That is what
   makes recursion on the type well founded below. *)

Section WithCtx.
  (* The ambient context supplies the type variables.  Environments are then
     built from [emp]/[ext] alone, which is what lets the relation recurse. *)
  Context (c : ctx).

  Notation L := stlc_full.

  (* ---- sort and term abbreviations (internal, reversed-argument form) ---- *)
  Definition Sty : sort := scon "ty" [].
  Definition Senv : sort := scon "env" [].
  Definition Ssub (G G' : term) : sort := scon "sub" [G'; G].
  Definition Sval (G A : term) : sort := scon "val" [A; G].
  Definition Sexp (G A : term) : sort := scon "exp" [A; G].

  Definition Arr (A B : term) : term := con "->" [B; A].
  Definition Emp : term := con "emp" [].
  Definition Ext (G A : term) : term := con "ext" [A; G].
  Definition Ret (G A v : term) : term := con "ret" [v; A; G].
  Definition Lam (G A B e : term) : term := con "lambda" [e; B; A; G].
  Definition App (G A B e e' : term) : term := con "app" [e'; e; B; A; G].

  (* ---- well-shapedness of the index syntax ---- *)
  Inductive TyOk : term -> Prop :=
  | tyok_var : forall n, In (n, Sty) c -> TyOk (var n)
  | tyok_arr : forall A B, TyOk A -> TyOk B -> TyOk (Arr A B).

  Inductive EnvOk : term -> Prop :=
  | envok_emp : EnvOk Emp
  | envok_ext : forall G A, EnvOk G -> TyOk A -> EnvOk (Ext G A).

  (* ---- the reducibility relation ----

     Defined at the empty environment and by recursion on the type, which is
     legitimate because [ty] is generated solely by [->] and variables.  The
     expression level is inlined into the value level (rather than made mutual)
     so that the recursion stays visibly structural.

     At a type variable there are no closed values at all -- the language has no
     base-type constructor -- so the clause is [False].  That is not a defect:
     it is exactly the canonicity content, and the arrow clause is where the
     work happens. *)
  Fixpoint R_val (A : term) (v : term) : Prop :=
    match A with
    | con "->" [B; A1] =>
        (exists e0, eq_term L c (Sval Emp (Arr A1 B)) v (Lam Emp A1 B e0))
        /\ (forall v', R_val A1 v' ->
                       exists v2,
                         R_val B v2
                         /\ eq_term L c (Sexp Emp B)
                              (App Emp A1 B (Ret Emp (Arr A1 B) v) (Ret Emp A1 v'))
                              (Ret Emp B v2))
    | _ => False
    end.

  (* A closed expression is reducible when it evaluates -- provably, in the
     theory -- to a reducible value. *)
  Definition R_exp (A e : term) : Prop :=
    exists v, R_val A v /\ eq_term L c (Sexp Emp A) e (Ret Emp A v).

  (* ---- basic structural facts ---- *)

  Lemma R_val_arr_inv A1 B v
    : R_val (Arr A1 B) v ->
      (exists e0, eq_term L c (Sval Emp (Arr A1 B)) v (Lam Emp A1 B e0)).
  Proof.
    intro H; cbn in H; unfold Arr in H; cbn in H; tauto.
  Qed.

  Lemma R_val_arr_app A1 B v v'
    : R_val (Arr A1 B) v ->
      R_val A1 v' ->
      R_exp B (App Emp A1 B (Ret Emp (Arr A1 B) v) (Ret Emp A1 v')).
  Proof.
    intros Hv Hv'.
    cbn in Hv; unfold Arr in Hv; cbn in Hv.
    destruct Hv as [_ Happ].
    destruct (Happ _ Hv') as [v2 [Hv2 Heq]].
    exists v2; split; assumption.
  Qed.

  (* Reducible values are, in particular, canonical: at an arrow type every
     closed reducible value is provably a lambda. *)
  Theorem R_val_canonical A1 B v
    : R_val (Arr A1 B) v ->
      exists e0, eq_term L c (Sval Emp (Arr A1 B)) v (Lam Emp A1 B e0).
  Proof. apply R_val_arr_inv. Qed.

End WithCtx.
