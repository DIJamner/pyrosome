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
From Pyrosome Require Import Tools.EGraph.InjRuleGen.

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


(* ------------------------------------------------------------------ *)
(* The three boundary cases, as VALUE CONSTANTS.

   Previously these were three big derived terms plugged into [#"typerec"].
   Substituting through them (either a term substitution, for the
   ["exp_subst dtt"]/["exp_subst ttd"] equations, or the type substitution
   that ["typerec func"] produces) meant traversing the whole wrapper, which
   the e-graph could not do in 900s.  As constants with defining equations,
   a substitution passes through them in a single rewrite.               *)

(* [P X] is [sigma[X]] for the concrete [sigma] used by the boundaries,
   [sigma] being [prod (arrow ty_hd star) (arrow star ty_hd)]. *)
Definition P X := {{e #"prod" (#"->" {X} #"*") (#"->" #"*" {X}) }}.
Definition boundary_sigma := Eval compute in P {{e #"ty_hd"}}.

Definition Pa := Eval compute in P tva.
Definition Pb := Eval compute in P tvb.
Definition Pab := Eval compute in P {{e #"->" {tva} {tvb} }}.

Definition bfunc_sort :=
  {{s #"val" (#"ty_ext" (#"ty_ext" "D")) (#"ext" (#"ext" {G2} {Pa}) {Pb}) {Pab} }}.
Definition bfunc_sort' :=
  {{s #"val" (#"ty_ext" (#"ty_ext" "D")) (#"ext" (#"ext" {G2'} {Pa}) {Pb}) {Pab} }}.

Definition bstar_body :=
  {{e #"pair_val" (#"lambda" #"*" (#"ret" #"hd")) (#"lambda" #"*" (#"ret" #"hd")) }}.

Definition bbool_body :=
  {{e #"pair_val"
      (#"lambda" #"bool" (#"if" (#"ret" #"hd") (#"ret" #"uT") (#"ret" #"uF")))
      (#"lambda" #"*" (#"mif" (#"ret" #"hd") (#"ret" #"T") (#"ret" #"F"))) }}.

(* The two wrappers, verbatim from the old [trec_func_case]: at the point of
   the [#"pair"] the old term's environment was [ext (ext G Pa) Pb] too, so
   every [ovar] index is unchanged.  [{ovar 1}] is the recursive result for
   the domain type [a], [{ovar 0}] the one for the codomain [b].          *)
Definition bfunc_body :=
  {{e #"pair_val"
      (#"lambda" (#"->" {tva} {tvb})
         (#"ret" (#"ulambda"
            (#"let" (#"app" (#"ret" {ovar 1})
                            (#"let" (#"ret" {ovar 0})
                                    (#"app" (#".2" (#"ret" {ovar 4})) (#"ret" {ovar 0}))))
                    (#"app" (#".1" (#"ret" {ovar 3})) (#"ret" {ovar 0}))))))
      (#"lambda" #"*"
         (#"mif" (#"bool?" (#"ret" {ovar 0}))
            (#"Error" (#"->" {tva} {tvb}))
            (#"ret" (#"lambda" {tva}
               (#"let" (#"uapp" (#"ret" {ovar 1})
                                (#"let" (#"ret" {ovar 0})
                                        (#"app" (#".1" (#"ret" {ovar 4})) (#"ret" {ovar 0}))))
                       (#"app" (#".2" (#"ret" {ovar 3})) (#"ret" {ovar 0}))))))) }}.

Definition boundary_cases_def : lang :=
  {[l
    [:| "D" : #"ty_env", "G" : #"env" "D"
        -----------------------------------------------
        #"bstar" : #"val" "D" "G" {P {{e #"*"}} }
    ];
    [:| "D" : #"ty_env", "G" : #"env" "D"
        -----------------------------------------------
        #"bbool" : #"val" "D" "G" {P {{e #"bool"}} }
    ];
    [:| "D" : #"ty_env", "G" : #"env" "D"
        -----------------------------------------------
        #"bfunc" : {bfunc_sort}
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D", "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G"
        ----------------------------------------------- ("val_subst bstar")
        #"val_subst" "g" #"bstar" = #"bstar" : #"val" "D" "G'" {P {{e #"*"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D", "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G"
        ----------------------------------------------- ("val_subst bbool")
        #"val_subst" "g" #"bbool" = #"bbool" : #"val" "D" "G'" {P {{e #"bool"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D", "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G"
        ----------------------------------------------- ("val_subst bfunc")
        #"val_subst" {g_lift} #"bfunc" = #"bfunc" : {bfunc_sort'}
    ];
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D"
        ----------------------------------------------- ("ty_subst bstar")
        #"val_ty_subst" "g" #"bstar" = #"bstar"
        : #"val" "D'" (#"env_ty_subst" "g" "G") {P {{e #"*"}} }
    ];
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D"
        ----------------------------------------------- ("ty_subst bbool")
        #"val_ty_subst" "g" #"bbool" = #"bbool"
        : #"val" "D'" (#"env_ty_subst" "g" "G") {P {{e #"bool"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D"
        ----------------------------------------------- ("bstar def")
        #"bstar" = {bstar_body} : #"val" "D" "G" {P {{e #"*"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D"
        ----------------------------------------------- ("bbool def")
        #"bbool" = {bbool_body} : #"val" "D" "G" {P {{e #"bool"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D"
        ----------------------------------------------- ("bfunc def")
        #"bfunc" = {bfunc_body} : {bfunc_sort}
    ]
  ]}.

Definition boundary_cases :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 target_multilanguage_pre boundary_cases_def.

Lemma boundary_cases_wf : wf_lang_ext target_multilanguage_pre boundary_cases.
Proof. Time compute_wf_lang. Qed.
#[local] Definition boundary_cases_entry := lang_entry boundary_cases_wf.
#[export] Hint Resolve boundary_cases_entry : wf_lang_db.

Definition target_multilanguage := boundary_cases ++ target_multilanguage_pre.
Hint Unfold target_multilanguage : auto_elab.

Lemma target_multilanguage_wf : wf_lang target_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_entry :=
  lang_entry target_multilanguage_wf.
#[export] Hint Resolve target_multilanguage_entry : wf_lang_db.

(* ------------------------------------------------------------------ *)
(* [trec_boundaries] is now just the [#"typerec"] value applied to the three
   constants.                                                              *)
Definition trec_boundaries_unelab :=
  {{e #"typerec" "A" {boundary_sigma} #"bstar" #"bbool" #"bfunc" }}.

Definition trec_boundaries_sort :=
  {{s #"val" #"ty_emp" "G"
      (#"prod" #"ty_emp"
         (#"->" #"ty_emp" "A" (#"*" #"ty_emp"))
         (#"->" #"ty_emp" (#"*" #"ty_emp") "A")) }}.

Derive trec_boundaries
  in ( elab_term target_multilanguage
         [("A", {{s #"ty" #"ty_emp"}}); ("G", {{s #"env" #"ty_emp"}})]
         trec_boundaries_unelab
         trec_boundaries
         trec_boundaries_sort
     ) as trec_boundaries_wf.
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed.
