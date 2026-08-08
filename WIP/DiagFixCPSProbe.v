(* Diagnostic probe: where does fix_cps auto_elab_compiler blow up now that
   sort_rule + term_rule decls are filtered out of the schedule?

   Strategy: force flagged_exact to vm_compute EAGERLY (per-goal) instead of
   deferring to Qed, then run the fix_cps Derive with a fuel-parameterized
   by_reduction so we can watch which obligation (goal 1 = structural fix,
   goal 2 = fix_beta) blows up and how cost scales with sat_fuel vs red_fuel. *)

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List BinNums BinPos.
Import ListNotations.
Open Scope string.
Open Scope list.
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

(* Per-obligation probe: apply egraph_sound at given (sat,red) fuel, then on
   the Is_Success goal report TRUE/FALSE and ADMIT on failure so we proceed to
   the next obligation and observe ALL of them. Wrapped in Goal/Abort. *)
Ltac probe sf rf :=
  lazymatch goal with
  | |- eq_term _ _ _ ?e1 ?e2 =>
    idtac "--- eq_term obligation ---";
    apply (egraph_sound 100 sf 100 rf filter_rules
             (fun _ : string * Rule.rule string => true) empty_inj_rules);
    [ prove_by_lang_db | shelve | shelve | shelve |
      lazymatch goal with
      | |- ?G => let r := eval vm_compute in G in idtac "  => RESULT (True=success):" r
      end ]
  | |- ?g => idtac "--- (non-eq_term goal, skipped) ---"
  end.

Ltac probe_all sf rf :=
  cleanup_elab_after setup_elab_compiler;
  [> repeat Matches.t .. ];
  try decompose_sort_eq;
  probe sf rf.

(* GOAL-SELECTIVE: GSEL picks which of the two eq_term obligations to probe;
   the other is just announced and shelved. *)
Ltac probe_g1 sf rf := [> (try decompose_sort_eq; probe sf rf)
                        | (idtac "  [goal2 SKIPPED]"; shelve) ].
Ltac probe_g2 sf rf := [> (idtac "  [goal1 SKIPPED]"; shelve)
                        | (try decompose_sort_eq; probe sf rf) ].
Ltac probe_sel GSEL sf rf :=
  cleanup_elab_after setup_elab_compiler;
  [> repeat Matches.t .. ];
  GSEL sf rf.

Goal (elab_preserving_compiler (cps++cps_subst)
        (fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst)
        fix_cps_def fix_cps fix_lang).
Proof. idtac "===== PROBE GSEL SAT RED ====="; probe_sel GSEL SAT RED. Abort.

(* ===== NORMAL-FORM DIFF: reduce goal-2's LHS and RHS separately ===== *)
Ltac nf_probe :=
  lazymatch goal with
  | |- eq_term ?l ?c ?t ?e1 ?e2 =>
    idtac "--- eq_term obligation: normal forms ---";
    let n1 := eval vm_compute in
      (@PositiveInstantiation.egraph_simpl' string _ _ (option positive)
         (weighted_size_analysis (fun _ => Some 1%positive)) l 100 30 100 c e1) in
    let n2 := eval vm_compute in
      (@PositiveInstantiation.egraph_simpl' string _ _ (option positive)
         (weighted_size_analysis (fun _ => Some 1%positive)) l 100 30 100 c e2) in
    idtac "LHS-nf:" n1;
    idtac "RHS-nf:" n2
  | |- ?g => idtac "(skip non-eq_term)"
  end.

Ltac nf_all :=
  cleanup_elab_after setup_elab_compiler;
  [> repeat Matches.t .. ];
  try decompose_sort_eq;
  nf_probe.

Goal (elab_preserving_compiler (cps++cps_subst)
        (fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst)
        fix_cps_def fix_cps fix_lang).
Proof. idtac "===== NORMAL FORMS ====="; nf_all. Abort.

(* ===== MEASURE: size & depth of input vs depth-min-extracted normal form ===== *)
Fixpoint tsize (e : Term.term string) : nat :=
  match e with
  | var _ => 1
  | con _ args => S (fold_right (fun a n => tsize a + n) 0 args)
  end.
Fixpoint tdepth (e : Term.term string) : nat :=
  match e with
  | var _ => 1
  | con _ args => S (fold_right (fun a n => Nat.max (tdepth a) n) 0 args)
  end.

Ltac measure_probe :=
  lazymatch goal with
  | |- eq_term ?l ?c ?t ?e1 ?e2 =>
    let nf1 := constr:(@PositiveInstantiation.egraph_simpl' string _ _ (option positive)
                 (weighted_size_analysis (fun _ => Some 1%positive)) l 100 30 100 c e1) in
    let s_in  := eval vm_compute in (tsize e1) in
    let d_in  := eval vm_compute in (tdepth e1) in
    let s_out := eval vm_compute in (tsize nf1) in
    let d_out := eval vm_compute in (tdepth nf1) in
    idtac "INPUT  size:" s_in " depth:" d_in;
    idtac "EXTRACT size:" s_out " depth:" d_out
  | |- ?g => idtac "(skip)"
  end.

Ltac measure_all :=
  cleanup_elab_after setup_elab_compiler;
  [> repeat Matches.t .. ];
  try decompose_sort_eq;
  measure_probe.

Goal (elab_preserving_compiler (cps++cps_subst)
        (fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst)
        fix_cps_def fix_cps fix_lang).
Proof. idtac "===== MEASURE size/depth ====="; measure_all. Abort.
