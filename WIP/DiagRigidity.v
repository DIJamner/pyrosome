(* Coverage measurement over poly_full (see RigidityChecker.v). *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome Require Import Lang.PolySubst Lang.PolyCompilers.
Require Import RigidityChecker.
Import Core.Notations.


Definition poly_full : lang :=

  poly ++ exp_param_substs ++ exp_ty_subst ++ val_param_substs ++ val_ty_subst
       ++ env_ty_subst ++ ty_subst_lang ++ exp_parameterized ++ val_parameterized
       ++ ty_env_lang.
Definition exists_full : lang := exists_lang ++ poly_full.

(* ==== poly_full coverage ==== *)
Eval vm_compute in
  ("eq rules", n_eq_rules poly_full,
   "rules with all nodes rigid", n_rules_nodes_ok poly_full,
   "candidate (rule,var) pairs", n_candidates poly_full,
   "rigid-skippable pairs", n_rigid poly_full,
   "rules with ALL candidates rigid", n_rules_all_rigid poly_full).

Eval vm_compute in (failures poly_full).

(* ==== exists_full coverage (bonus) ==== *)
Eval vm_compute in
  ("eq rules", n_eq_rules exists_full,
   "candidates", n_candidates exists_full,
   "rigid", n_rigid exists_full,
   "all-rigid rules", n_rules_all_rigid exists_full).
