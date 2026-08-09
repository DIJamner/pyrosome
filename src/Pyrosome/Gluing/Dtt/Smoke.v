Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms.
Import Core.Notations.

(* =====================================================================
   NON-VACUITY of the Layer-1 normal forms.

   The analogue of Gluing/Stlc/Smoke.v, and it matters more here than it
   does there, because types are DECODED CODES: the closed codes of
   [ott_dtt] are exactly [Nat], [Empty] and [Pi_rel]/[Pi_irr] built from
   codes, and Pi has no base case.  Without [ott_nat] every [U _ L0] would
   be empty, every [El _ _ _ e] uninhabited, [TyOk] empty, and every
   normalization statement about the language vacuous.  [Nat] plays exactly
   the role [unit] plays in the simply-typed proof.

   Everything below is a pure inductive construction -- no object-theory
   reasoning -- except the two facts that need a [wkn]-instance of the type
   ([hd] and its neutral), which are what actually exercise the "named
   normal representative" design of [NormalForms.v].
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* The empty environment, and the type of natural numbers over it. *)
Definition natC : term := oNat oEmp.
Definition natT : term := oEl oEmp oRel oL0 natC.

(* An OPEN environment: one variable of type Nat. *)
Definition G1 : term := oExtC oEmp oRel oL0 natC.

Lemma smoke_EnvOk_emp : EnvOk oEmp.
Proof. constructor. Qed.

Lemma smoke_NfCode_nat : NfCode oEmp oRel oL0 natC.
Proof. apply nfcode_nat; constructor. Qed.

(* The universe is inhabited: [Nat] is a normal term of [U emp rel L0]. *)
Lemma smoke_NfET_nat : NfET oEmp (iCode oL0) (oU oEmp oRel oL0) natC.
Proof. apply nfet_code, smoke_NfCode_nat. Qed.

(* ... and the universe is itself a normal type. *)
Lemma smoke_TyOk_U : TyOk oEmp (iCode oL0) (oU oEmp oRel oL0).
Proof. apply tyok_U; constructor. Qed.

(* A closed type. *)
Lemma smoke_TyOk_nat : TyOk oEmp (iEl oRel oL0) natT.
Proof. apply tyok_El, smoke_NfCode_nat. Qed.

Lemma smoke_EnvOk_G1 : EnvOk G1.
Proof. apply envok_ext; [ constructor | apply smoke_TyOk_nat ]. Qed.

(* The first genuinely dependent-shaped witness: the codomain code lives in
   the extended environment. *)
Definition piNN : term := oPiRel oEmp oRel oL0 oL0 natC (oNat G1).

Lemma smoke_NfCode_pi : NfCode oEmp oRel oL0 piNN.
Proof.
  apply nfcode_pi_rel.
  - constructor.
  - constructor.
  - constructor.
  - apply smoke_NfCode_nat.
  - apply nfcode_nat, smoke_EnvOk_G1.
Qed.

Lemma smoke_TyOk_pi : TyOk oEmp (iEl oRel oL0) (oEl oEmp oRel oL0 piNN).
Proof. apply tyok_El, smoke_NfCode_pi. Qed.

(* Normal terms of Nat. *)
Lemma smoke_NfET_zero : NfET oEmp (iEl oRel oL0) natT (oZero oEmp).
Proof. apply nfet_zero; constructor. Qed.

Lemma smoke_NfET_one : NfET oEmp (iEl oRel oL0) natT (oSuc oEmp (oZero oEmp)).
Proof. apply nfet_suc, smoke_NfET_zero. Qed.

(* An ETA-LONG normal function: the constant-zero function.  Note the only
   [NfET] clause available at a [Pi_rel] type is [nfet_lam_rel] -- there is
   deliberately no neutral clause there, which is exactly what eta buys. *)
Definition constZero : term :=
  oLamRel oEmp oRel oL0 oL0 natC (oNat G1) (oZero G1).

Lemma smoke_NfET_constZero
  : NfET oEmp (iEl oRel oL0) (oEl oEmp oRel oL0 piNN) constZero.
Proof.
  apply nfet_lam_rel.
  - constructor.
  - constructor.
  - constructor.
  - apply smoke_NfCode_nat.
  - apply nfcode_nat, smoke_EnvOk_G1.
  - apply nfet_zero, smoke_EnvOk_G1.
Qed.

(* ------------------------------------------------------------------ *)
(* Still to come: the OPEN witnesses                                    *)
(* ------------------------------------------------------------------ *)

(* [hd] has type [Nat[wkn]], which is NOT a normal type; its normal
   representative is [Nat G1], and the two are identified by "Nat subst".
   That is the smallest instance of the mechanism [NormalForms.v]'s
   [vart_hd]/[neet_app_rel] clauses are built around.

   Building it needs the [next0] bookkeeping described in Eqns.v's
   header, in BOTH positions at once: "Nat subst" is stated at
   [info rel (iota L1)] while [sCode G r l] is [info rel (next l)], and the
   info also occurs INSIDE the [exp_subst] argument list -- so the chain is
   [ExpSubst_cong] (to move the info inside the term), then [eq_Nat_subst],
   then [eq_term_conv] along a sort congruence (to move the info in the
   sort).  The reusable helpers for that -- [sExp_cong] and friends
   -- belong in the Layer-1 typing file, so the open witnesses land here
   once that exists. *)
