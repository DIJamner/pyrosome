Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* imports for compilers *)
(* copied from LinearCPS.v *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for `match # from high_level_multilanguage with` *)
(* CompilerDefs, for preserving_compiler_ext, is already imported. Prolly through something else. *)

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

From Stdlib Require derive.Derive.

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC. 
From Pyrosome.Lang Require Import UTLC. 
From Pyrosome.Lang Require Import BoolType. 
From Pyrosome.Lang Require Import SimpleVProd.


(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers. (* for parameterizing existing languages*)
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.
From Pyrosome.Lang.Multilanguages Require Export TrecTerms.



(* simple to poly compiler *)
Definition simple_multilang_compiler_def : compiler :=
    match # from boundaries with
    | {{e #"dtt" "G" "A" "e"}} => {{e @"app" @("D" := #"ty_emp")
                                      (#".2" {trec_boundaries_unelab}) "e" }}
    | {{e #"ttd" "G" "A" "e"}} => {{e @"app" @("D" := #"ty_emp")
                                      (#".1" {trec_boundaries_unelab}) "e" }}
    end.

Ltac solve_multilang_compiler :=
  unshelve (setup_elab_compiler;
            match goal with
            | |- elab_term _ _ _ _ _ => solve_elab_term_or_sort target_multilanguage
            | |- _ => shelve
            end);
  unshelve (apply TODO (*TODO: the bug fix may have caused this to no longer terminate Automation.by_reduction*));
  match goal with
  | |- wf_term _ _ _ _ => compute_term_wf
  | |- _ => solve_wf_ctx
  end.

Derive simple_multilang_compiler 
  in (elab_preserving_compiler 
              interoperating_langs_compiler
              target_multilanguage
              simple_multilang_compiler_def
              simple_multilang_compiler
              boundaries) 
  as simple_multilang_compiler_preserving.
Proof. solve_multilang_compiler. Qed. 
#[local] Definition simple_multilang_compiler_entry :=
  cmp_entry (elab_compiler_implies_preserving simple_multilang_compiler_preserving).
#[export] Hint Resolve simple_multilang_compiler_entry : preserving_db.

(*
Require Import Pyrosome.Tools.EGraph.TypeInference.
(* you _could_ do it with egraphs if you mark which things are injective for the target lang (see STLC), and then do it with egraphs. (that's what this def is for) *)
Definition multilang_compiler' :=
  Eval vm_compute in
    (infer_compiler_simple
       target_multilanguage
       shared_fragment_compiler
       multilang_compiler_def
       (boundaries ++ uif)
\       []).
(* above will have succeeded if we don't see @ or ?. If that succeeds, then we can throw out the old tactics and only use the computational tactics *)
(* Print multilang_compiler'. *)
 *)



