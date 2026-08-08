(* Rigidity coverage on the simply-typed stacks: decides whether the runtime
   gate can be rigid-ONLY (replacing syntactic_sort_eq_langb) without
   regressing the STLC/CPS query minimization. *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFixCPS.
Require Import RigidityChecker.
Import Core.Notations.

(* CPS target (the fix_cps diagnosis language). *)
Definition Ltgt : lang :=
  fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst.
(* STLC source. *)
Definition Lsrc : lang := stlc ++ exp_subst ++ value_subst.

Eval vm_compute in
  ("Ltgt eq rules", n_eq_rules Ltgt,
   "candidates", n_candidates Ltgt,
   "rigid", n_rigid Ltgt,
   "all-rigid rules", n_rules_all_rigid Ltgt).
Eval vm_compute in (failures Ltgt).

Eval vm_compute in
  ("Lsrc eq rules", n_eq_rules Lsrc,
   "candidates", n_candidates Lsrc,
   "rigid", n_rigid Lsrc,
   "all-rigid rules", n_rules_all_rigid Lsrc).
Eval vm_compute in (failures Lsrc).
