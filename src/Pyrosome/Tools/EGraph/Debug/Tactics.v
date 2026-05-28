(* Debug scaffolding: drive the bounded diagnosis from a live, stuck proof.

   When `Automation.by_reduction` (which applies `Automation.egraph_sound`)
   hangs, the goal at that point is `eq_term l c t e1 e2`.  These tactics grab
   l/c/e1/e2 off that goal, run the bounded diagnosis from Debug.Diagnose with
   low fuels, and `idtac`-print the report -- without altering the goal, and
   without risking the non-termination of the real run (all fuels are bounded).

   Typical use, in place of `by_reduction` on a hanging subgoal:

     egraph_diagnose.            (* find the stuck leaf for the whole goal *)
     egraph_diagnose_trace.      (* watch the size/unification trajectory *)
     egraph_diagnose_probe.      (* which forward rules match at the leaf? *)

   The fuel knobs (see egraph_diagnose_with) are, in order:
     rn        rule-set variable bound (mirror of by_reduction's 100; 1000 ok)
     rfuel     rebuild fuel per step
     sat_fuel  OUTER saturation fuel per cong step (keep small: 1-5)
     efuel     extraction fuel
     red_depth congruence-recursion depth (how deep to chase the divergence)
     sched_cap cap on the engine's per-schedule-entry fuel (keep small: 1-3) *)
Set Implicit Arguments.

From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string.

From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Automation.
From Pyrosome.Tools.EGraph.Debug Require Import Diagnose.

(* Defaults matching Automation.by_reduction. *)
Definition dbg_reversible : string * Rule.rule string -> bool := fun _ => true.
Definition dbg_inj : list (string * list string) := [].

(* Bounded fuel profile suitable for a hanging goal. *)
Definition dbg_rn := 1000%nat.
Definition dbg_rfuel := 100%nat.
Definition dbg_sat := 4%nat.
Definition dbg_efuel := 100%nat.
Definition dbg_depth := 4%nat.
Definition dbg_cap := 2%nat.
Definition dbg_trace_max := 6%nat.

(* Pinpoint the stuck leaf for the current eq_term goal. *)
Ltac egraph_diagnose_with rn rfuel sat efuel depth cap :=
  match goal with
  | [ |- eq_term ?l ?c ?t ?e1 ?e2 ] =>
      let res := eval vm_compute in
        (Diagnose.diagnose l filter_rules dbg_reversible dbg_inj
           rn rfuel sat efuel depth cap c e1 e2) in
      idtac "egraph_diagnose (stuck-leaf report):"; idtac res
  | [ |- ?g ] => fail 1 "egraph_diagnose: goal is not eq_term:" g
  end.

Ltac egraph_diagnose :=
  egraph_diagnose_with dbg_rn dbg_rfuel dbg_sat dbg_efuel dbg_depth dbg_cap.

(* Per-iteration trajectory (fuel 1..maxn) for the top-level pair. *)
Ltac egraph_diagnose_trace_with rn rfuel efuel maxn cap :=
  match goal with
  | [ |- eq_term ?l ?c ?t ?e1 ?e2 ] =>
      let res := eval vm_compute in
        (Diagnose.diagnose_trace l filter_rules dbg_reversible dbg_inj
           rn rfuel efuel maxn cap c e1 e2) in
      idtac "egraph_diagnose_trace (per-iteration trajectory):"; idtac res
  | [ |- ?g ] => fail 1 "egraph_diagnose_trace: goal is not eq_term:" g
  end.

Ltac egraph_diagnose_trace :=
  egraph_diagnose_trace_with dbg_rn dbg_rfuel dbg_efuel dbg_trace_max dbg_cap.

(* Top pair at sat_fuel + which forward rules match in the resulting state. *)
Ltac egraph_diagnose_probe_with rn rfuel sat efuel cap :=
  match goal with
  | [ |- eq_term ?l ?c ?t ?e1 ?e2 ] =>
      let res := eval vm_compute in
        (Diagnose.diagnose_probe l filter_rules dbg_reversible dbg_inj
           rn rfuel sat efuel cap c e1 e2) in
      idtac "egraph_diagnose_probe (report, [(rule_index, #matches)]):"; idtac res
  | [ |- ?g ] => fail 1 "egraph_diagnose_probe: goal is not eq_term:" g
  end.

Ltac egraph_diagnose_probe :=
  egraph_diagnose_probe_with dbg_rn dbg_rfuel dbg_sat dbg_efuel dbg_cap.
