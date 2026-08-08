(* End-to-end: does the REAL auto_elab_compiler now complete under size weight? *)
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations. Open Scope string. Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference Tools.EGraph.ComputeWf Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS.
Import Core.Notations.
Import CompilerDefs.Notations.
From Stdlib Require derive.Derive.
Notation compiler := (compiler string).

Derive fix_cps_real
  in (elab_preserving_compiler (cps++cps_subst)
        (fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst)
        fix_cps_def fix_cps_real fix_lang)
  as fix_cps_preserving_real.
Proof. auto_elab_compiler. Qed.
Check fix_cps_preserving_real.
Print Assumptions fix_cps_preserving_real.
Eval vm_compute in (map fst fix_cps_real).
