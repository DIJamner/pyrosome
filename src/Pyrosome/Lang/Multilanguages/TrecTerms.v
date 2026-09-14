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
From Pyrosome.Lang.Multilanguages Require Export TypeCasing.


(* deriving the terms used in the compiler *)
Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | 1 => {{e #"wkn"}}
  | S n' =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Definition ovar n := {{e #"val_subst" {wkn_n n} #"hd" }}.  

(* (* it seems this is still needed *) *)
(* (* replaced by assert (wf_lang target_multilanguage) by prove_by_lang_db. *) *)
(* (* gonna comment this out to see if it's still needed *) *)
(* Lemma target_multilanguage_wf : wf_lang target_multilanguage. *)
(* Proof. prove_by_lang_db. Qed. *)
(* #[local] Definition target_multilanguage_entry := *)
(*   lang_entry target_multilanguage_wf. *)
(* #[export] Hint Resolve target_multilanguage_entry : wf_lang_db. *)

Ltac derive_elab_term := (* no longer used *)
  assert (wf_lang target_multilanguage) by prove_by_lang_db;
  unshelve (repeat t); t'. (* repeat t then unshelve; then on the unshelved do t'. *)

Ltac solve_eq_sort_disj := (* no longer used *)
  right; compute_eq_compilation; sort_cong; repeat by_reduction.

Ltac solve_elab_term_or_sort language :=
  assert (wf_lang language) by prove_by_lang_db;
  (* NOTE: the by_reduction below seems to me redundant given the def of solve_eq_sort_disj, but it's necessary for trec_boundaries and for both elab_term goals in the compiler *)
  (* the elab_term goals in the compiler were goals that I had to do out of order. Wonder if that has to do with it? *)
  (* and now that I think about it, the way I was doing the elab_term goals in trec_boundaries was doing the last one first. Then the rest went through. So it does seem like an order thing... but this solves it? *)
  unshelve (repeat t; decompose_sort_eq; repeat by_reduction; by_reduction); compute_term_wf.

(* tactic to see if progress can be made on an elab_term goal. unused, but keeping because it's a good example of pyrosome workflow. *)
Ltac quick_goal_match :=
  lazymatch goal with
  | |- elab_term _ _ (con ?s _) (con ?s _) _ =>
      idtac "can go further"
  | |- elab_term _ _ (con ?s _) (con ?s' _) _ =>
      fail "cannot go further"
  | |- _  => idtac "neither case"
  end.

Definition trec_star_case_unelab :=
  {{e #"pair"
      (#"ret" (#"lambda" #"*" (#"ret" #"hd")))
      (#"ret" (#"lambda" #"*" (#"ret" #"hd"))) }}.
Derive trec_star_case
  in ( elab_term target_multilanguage
         [("G", {{s #"env" #"ty_emp"}})]
         trec_star_case_unelab
         trec_star_case
         {{s #"exp" #"ty_emp" "G"
             (#"prod" #"ty_emp"
                (#"->" #"ty_emp" (#"*" #"ty_emp") (#"*" #"ty_emp"))
                (#"->" #"ty_emp" (#"*" #"ty_emp") (#"*" #"ty_emp"))
             )
         }}
     ) as trec_star_case_wf.
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed. (* used to be derive_elab_term *)

Definition trec_bool_case_unelab :=
  {{e #"pair"
      (#"ret" (#"lambda" #"bool" (#"if" (#"ret" #"hd") (#"ret" #"uT") (#"ret" #"uF"))))
      (#"ret" (#"lambda" #"*" (#"mif" (#"ret" #"hd") (#"ret" #"T") (#"ret" #"F")))) }}. 
Derive trec_bool_case
  in ( elab_term target_multilanguage
         [("G", {{s #"env" #"ty_emp"}})]
         trec_bool_case_unelab
         trec_bool_case
         {{s #"exp" #"ty_emp" "G"
             (#"prod" #"ty_emp"
                (#"->" #"ty_emp" (#"bool" #"ty_emp") (#"*" #"ty_emp"))
                (#"->" #"ty_emp" (#"*" #"ty_emp") (#"bool" #"ty_emp"))
             )
         }}
     ) as trec_bool_case_wf. 
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed. (* used to be derive_elab_term *)

Derive trec_func_case_sort
  in (elab_sort target_multilanguage
        [("G", {{s #"env" #"ty_emp"}})]
        {{s #"exp" #"ty_emp" "G"
            (#"All" 
               (#"->" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
                  (#"All"
                     (#"->" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
                        (#"prod" (#"->" (#"->" {ty_ovar 1} {ty_ovar 0}) #"*") (#"->" #"*" (#"->" {ty_ovar 1} {ty_ovar 0}))))))) }}
        trec_func_case_sort
     )
    as trec_func_case_sort_wf.
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed. (* used to be derive_elab_term *)

(* The two wrappers are written so that they are *literally* the compiled image
   of the boundary rules' right-hand sides:
   - [#".1"] (the [ttd] direction) mirrors ("ttd func");
   - [#".2"] (the [dtt] direction) mirrors ("dtt func"), and eagerly checks with
     [#"bool?"]/[#"mif"] that the untyped value really is a function, so that
     [#"dtt" (#"->" "A" "B") (#"ret" #"uT"/#"uF")] reduces to [#"Error"].
   Inside the two [#"Lam"]s, [ty_ovar 1] is the domain type and [ty_ovar 0] the
   codomain; the two [#"lambda"]-bound pair variables hold the recursive
   [typerec] results for those two types.                                     *)
Definition trec_func_case_unelab :=
  {{e #"ret" (#"Lam" (#"ret" (#"lambda" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
     (#"ret" (#"Lam" (#"ret" (#"lambda" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
       (#"pair"
          (#"ret" (#"lambda" (#"->" {ty_ovar 1} {ty_ovar 0})
             (#"ret" (#"ulambda"
                (#"let" (#"app" (#"ret" {ovar 1})
                                (#"let" (#"ret" {ovar 0})
                                        (#"app" (#".2" (#"ret" {ovar 4})) (#"ret" {ovar 0}))))
                        (#"app" (#".1" (#"ret" {ovar 3})) (#"ret" {ovar 0})))))))
          (#"ret" (#"lambda" #"*"
             (#"mif" (#"bool?" (#"ret" {ovar 0}))
                (#"Error" (#"->" {ty_ovar 1} {ty_ovar 0}))
                (#"ret" (#"lambda" {ty_ovar 1}
                   (#"let" (#"uapp" (#"ret" {ovar 1})
                                    (#"let" (#"ret" {ovar 0})
                                            (#"app" (#".1" (#"ret" {ovar 4})) (#"ret" {ovar 0}))))
                           (#"app" (#".2" (#"ret" {ovar 3})) (#"ret" {ovar 0}))))))))
       )))))))) }}.
Derive trec_func_case
  in ( elab_term target_multilanguage
         [("G", {{s #"env" #"ty_emp"}})]
         trec_func_case_unelab
         trec_func_case
         trec_func_case_sort
     ) as trec_func_case_wf.
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed. 

Definition trec_boundaries_unelab :=
  {{e #"typerec" "A" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
      {trec_star_case_unelab}
      {trec_bool_case_unelab}
      {trec_func_case_unelab} }}.
Derive trec_boundaries
         in ( elab_term target_multilanguage
                [("A", {{s #"ty" #"ty_emp"}}); ("G", {{s #"env" #"ty_emp"}})]
                trec_boundaries_unelab
                trec_boundaries
                {{s #"exp" #"ty_emp" "G"
                    (#"prod" #"ty_emp"
                       (#"->" #"ty_emp" "A" (#"*" #"ty_emp"))
                       (#"->" #"ty_emp" (#"*" #"ty_emp") "A")) }}
            ) as trec_boundaries_wf.
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed.
