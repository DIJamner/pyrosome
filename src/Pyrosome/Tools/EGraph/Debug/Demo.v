(* Self-test / usage demo for the e-graph diagnosis scaffolding, on the small
   `monoid` signature {S, *, assoc}.

   IMPORTANT IMPORT NOTE: running the diagnosis via `vm_compute` (here, or in a
   `Compute`, or inside the egraph_diagnose* tactics) requires the `Eqb string`
   instance to be in scope -- it lives in `coqutil.Eqb` (`string_Eqb`).  If it
   is missing, `vm_compute` cannot reduce the `eqb` comparisons, gets stuck on a
   huge partially-symbolic term, and *appears* to hang / blow up memory.  When
   used as a tactic on a real `eq_term` goal this is automatic (the goal already
   carries the instance); for standalone `Compute` make sure `coqutil.Eqb` is
   imported, as below. *)
#[local] Set Warnings "-native-compiler-disabled".
Set Implicit Arguments.

From Stdlib Require Import Lists.List Strings.String. Import ListNotations. Open Scope string.
From coqutil Require Import Eqb Datatypes.Result.
From Utils Require Import Default.   (* string_default : WithDefault string *)
From Pyrosome.Theory Require Import Core. Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Automation.
From Pyrosome.Tools.EGraph.Debug Require Import Diagnose Tactics.

Definition monoid : lang string :=
  {[l
  [s|
      -----------------------------------------------
      #"S" srt
  ];
  [:|  "a": #"S", "b" : #"S"
       -----------------------------------------------
       #"*" "a" "b" : #"S"
  ];
  [:=  "a": #"S", "b" : #"S", "c" : #"S"
       ----------------------------------------------- ("assoc")
       #"*" (#"*" "a" "b") "c"
       = #"*" "a" (#"*" "b" "c")
       : #"S"
  ]
  ]}.

Definition c : ctx string := {{c "a" : #"S", "b" : #"S", "c" : #"S" }}.
Definition lhs : term string := {{e #"*" (#"*" "a" "b") "c" }}.       (* (a*b)*c *)
Definition rhs : term string := {{e #"*" "a" (#"*" "b" "c") }}.       (* a*(b*c) *)
Definition ab  : term string := {{e #"*" "a" "b" }}.                  (* a*b     *)

(* ----------------------------------------------------------------------------
   (1) NEGATIVE case: (a*b)*c vs a*b never unify.  diagnose returns
   Success of reports; the leaf has it_res=false (saturation completed without
   converging) and it_unified=false -- the genuine "these are not equal" leaf
   that the long_horizon egraph_reducing_cong now reports as a fuel-exhaustion
   Failure instead of looping. *)
Definition negative_diag : result (list iter_report) :=
  Eval vm_compute in
  (diagnose monoid filter_rules dbg_reversible dbg_inj 1000 100 4 100 4 2 c lhs ab).

(* (2) POSITIVE case: (a*b)*c vs a*(b*c) unify via assoc. *)
Definition positive_trace : result (list iter_report) :=
  Eval vm_compute in
  (diagnose_trace monoid filter_rules dbg_reversible dbg_inj 1000 100 100 6 2 c lhs rhs).

(* (3) RULE PROBE: which forward rules' LHS match at the bounded state. *)
Definition probe : result (iter_report * list (nat * nat)) :=
  Eval vm_compute in
  (diagnose_probe monoid filter_rules dbg_reversible dbg_inj 1000 100 4 100 2 c lhs ab).

(* ---- self-checks: the tool reports the right thing on each example -------- *)
Definition any_unified (r : result (list iter_report)) : bool :=
  match r with Success l => existsb (it_unified (V:=string)) l | Failure _ => false end.
Definition any_stuck (r : result (list iter_report)) : bool :=
  match r with
  | Success l => existsb (fun rep => negb (it_res (V:=string) rep)) l
  | Failure _ => false end.

(* negative: no unification, and it reaches a stuck (saturated) leaf *)
Goal any_unified negative_diag = false /\ any_stuck negative_diag = true.
Proof. vm_compute. split; reflexivity. Qed.

(* positive: unification is reached (no false stall) *)
Goal any_unified positive_trace = true.
Proof. vm_compute. reflexivity. Qed.

(* the assoc rule does match at the stuck state *)
Goal match probe with Success (_, ps) => existsb (fun p => negb (Nat.eqb (snd p) 0)) ps
                    | Failure _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

(* ----------------------------------------------------------------------------
   (4) LIVE GOAL usage -- in place of a hanging by_reduction, grab l/c/e1/e2 off
   the goal and print the bounded stuck-leaf report without changing the goal:

   Goal eq_term monoid c {{s #"S"}} lhs ab.
   Proof. egraph_diagnose. egraph_diagnose_probe. egraph_diagnose_trace. Abort.
---------------------------------------------------------------------------- *)
