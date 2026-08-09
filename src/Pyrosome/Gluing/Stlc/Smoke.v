Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string. Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing.Stlc Require Import Syntax Normalization NormalForms LogRel RSub Ceq ModelOk.
Import Core.Notations.

(* NON-VACUITY: a concrete well-typed open term gets a normal form.
   G0 = Ext Emp (Arr Unit Unit) is a genuinely open environment: its variable
   is the object-level [hd].  The term applies the identity function to it. *)
Definition G0 := Ext Emp (Arr Unit Unit).
Definition idlam := Lam G0 Unit Unit (Ret (Ext G0 Unit) Unit (Hd G0 Unit)).
Definition tm := App G0 Unit Unit (Ret G0 (Arr Unit Unit) idlam) (Ret G0 Unit (Tt G0)).

Lemma EnvOk_G0 : EnvOk G0.
Proof. unfold G0; repeat constructor. Qed.

Lemma wf_tm : wf_term stlc_unit [] tm (Sexp G0 Unit).
Proof. unfold tm, idlam, G0. wfa. Qed.

Theorem tm_has_normal_form
  : exists n, NfE n /\ eq_term stlc_unit [] (Sexp G0 Unit) tm n.
Proof.
  apply stlc_unit_normalization.
  - apply EnvOk_G0.
  - constructor.
  - apply wf_tm.
Qed.


