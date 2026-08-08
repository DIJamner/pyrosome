(* Step 1 for the FAILING cases: time the real engine on the fix_cps obligations
   (esp. goal-2 fix_beta, which never unifies and blows up).  The engine returns
   `result unit` (small) so vm_compute timing is artifact-free; scaling sat_fuel
   (sf) / red_fuel (rf) characterizes the blowup. *)
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List BinNums BinPos.
Import ListNotations. Open Scope string. Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference Tools.EGraph.ComputeWf Tools.Resolution
  Tools.EGraph.Defs.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS.
Import Core.Notations.
Import CompilerDefs.Notations.
From Stdlib Require derive.Derive.
Notation compiler := (compiler string).

Fixpoint tsize (e : Term.term string) : nat :=
  match e with var _ => 1 | con _ args => S (fold_right (fun a n => tsize a + n) 0 args) end.

(* On an eq_term obligation, report input sizes then TIME the real engine at a
   few (sf,rf).  `time (tac)` is the Ltac timer; the vm_compute of `result unit`
   is small => artifact-free. *)
Ltac trun l c e1 e2 sf rf :=
  let v := eval vm_compute in
    (fst (PositiveInstantiation.egraph_reducing_equal' l filter_rules
            (fun _ : string * Rule.rule string => true) empty_inj_rules 100 sf 100 rf c e1 e2)) in
  idtac "  sf=" sf " rf=" rf " =>" v.

Ltac time_g :=
  lazymatch goal with
  | |- eq_term ?l ?c ?t ?e1 ?e2 =>
      let s1 := eval vm_compute in (tsize e1) in
      let s2 := eval vm_compute in (tsize e2) in
      idtac "=== eq_term obligation; size(e1)=" s1 " size(e2)=" s2 " ===";
      time (trun l c e1 e2 6 1);
      time (trun l c e1 e2 6 3);
      time (trun l c e1 e2 6 6);
      time (trun l c e1 e2 6 12)
  | |- ?g => idtac "(skip non-eq_term goal)"
  end.

Goal (elab_preserving_compiler (cps++cps_subst)
        (fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst)
        fix_cps_def fix_cps fix_lang).
Proof.
  idtac "===== FAILING-CASE ENGINE TIMING =====";
  cleanup_elab_after setup_elab_compiler;
  [> repeat Matches.t .. ];
  try decompose_sort_eq.
  all: try time_g.
Abort.
