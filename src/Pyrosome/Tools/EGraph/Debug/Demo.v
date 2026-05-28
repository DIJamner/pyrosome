(* Usage reference for the e-graph diagnosis scaffolding (Observe / Diagnose /
   Tactics), on the small `monoid` signature {S, *, assoc}.

   IMPORTANT: the diagnosis is designed to be run INTERACTIVELY -- from a live
   proof via the `egraph_diagnose*` tactics, or via `Compute`/`Eval vm_compute`
   in an open session / rocq-mcp.  We deliberately do NOT force any e-graph
   computation at file-compile time: `vm_compute` over the engine requires
   compiling the whole transitive dependency closure (EGraph.Semantics,
   QueryOpt, ...) to VM bytecode, which is far too memory-heavy for batch
   `coqc` (it OOMs) even though each computation takes well under 100ms in an
   already-loaded interactive session.  So everything below is commented; run
   the commented lines in a session to reproduce.  The recorded outputs were
   produced exactly this way. *)
#[local] Set Warnings "-native-compiler-disabled".
Set Implicit Arguments.

From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string.

From Pyrosome.Theory Require Import Core.
Import Core.Notations.
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

Definition c : ctx string :=
  {{c "a" : #"S", "b" : #"S", "c" : #"S" }}.

Definition lhs : term string := {{e #"*" (#"*" "a" "b") "c" }}.       (* (a*b)*c *)
Definition rhs : term string := {{e #"*" "a" (#"*" "b" "c") }}.       (* a*(b*c) *)
Definition ab  : term string := {{e #"*" "a" "b" }}.                  (* a*b     *)

(* ----------------------------------------------------------------------------
   (1) NEGATIVE case -- the interesting one: (a*b)*c vs a*b never unify.
   `diagnose` returns one report per congruence step until it hits the stuck
   leaf.  The args are: l filter reversible inj  rn rfuel sat efuel depth cap
   c e1 e2.

   Compute (diagnose monoid filter_rules dbg_reversible dbg_inj
              1000 100 4 100 4 2 c lhs ab).

   ==> Success [ <iter_report> ; ... ], each report carrying:
       it_res := false;        (* saturation completed WITHOUT converging... *)
       it_unified := false;    (* ...so the ids never merged: this is the leaf *)
       it_nf1 := {{e #"*" #"a" (#"*" #"b" #"c")}};   (* (a*b)*c normalised via assoc *)
       it_nf2 := {{e #"*" #"a" #"b"}};
       it_diverge := [( a*(b*c) , a*b )];            (* the irreducible mismatch *)
       it_stats := {| num_eclasses := ...; total_rows := ...; ... |}
   Reading: both sides fully reduce, the engine cannot equate `a*(b*c)` with
   `a*b`, and (it_res=false) saturation reached a fixpoint there -- exactly the
   point where the long_horizon egraph_reducing_cong now returns a
   fuel-exhaustion Failure instead of looping.  (it_res=true & it_unified=false
   would instead mean "weight decreased, recursing on the simpler form".)
   The result is wrapped in `Success`; a `Failure` here means a context
   variable clashed with a language symbol (the ctx/lang disjointness guard).

   (2) POSITIVE case -- (a*b)*c vs a*(b*c) SHOULD unify via assoc:

   Compute (match diagnose_trace monoid filter_rules dbg_reversible dbg_inj
                    1000 100 100 6 2 c lhs rhs with
            | Success l => existsb (it_unified (V:=string)) l
            | Failure _ => false end).
   ==> true     (* it_unified flips to true along the fuel-1..6 trajectory *)

   (3) RULE PROBE -- which forward rules' LHS match at the bounded state:

   Compute (match diagnose_probe monoid filter_rules dbg_reversible dbg_inj
                     1000 100 4 100 2 c lhs ab with
            | Success (_, probes) => probes | Failure _ => [] end).
   ==> [(0%nat, 1%nat)]   (* rule 0 (assoc) matches once *)

   (4) LIVE GOAL -- in place of a hanging `by_reduction`, grab l/c/e1/e2 off
   the goal and print the stuck-leaf report without changing the goal:

   Goal eq_term monoid c {{s #"S"}} lhs ab.
   Proof.
     egraph_diagnose.        (* prints the stuck-leaf report *)
     egraph_diagnose_probe.  (* prints (report, [(rule_index,#matches)]) *)
     egraph_diagnose_trace.  (* prints the per-iteration size/unification trace *)
   Abort.
---------------------------------------------------------------------------- *)
