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
From Pyrosome.Lang.Multilanguages Require Export Boundaries.

(* now we define the type casing fragment for the target multilanguage without boundaries. First, some helpers. *)
Fixpoint ty_wkn_n n :=
  match n with
  | 0 => {{e #"ty_id"}}
  | 1 => {{e #"ty_wkn"}}
  | S n' => {{e #"ty_cmp" #"ty_wkn" {ty_wkn_n n'} }}
  end.

Definition ty_ovar n :=
  match n with 
  | 0 => {{e #"ty_hd"}} (* bc ty_subst ty_id ty_hd is just ty_hd *)
  | S _ => {{e #"ty_subst" {ty_wkn_n n} #"ty_hd" }}
  end.  

(* This is for the semantic rule for arrow. It's the type of (#"app" (#"@" "e3" "t1") (#"typerec" "t1" "sigma" "e1" "e2" "e3")). This type has a type variable, and we are going to substitute it with t2. The derivation for this is on page 32 of your UROP notebook *)
Definition A_var := {{e #"ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" (#"ty_snoc" #"ty_id" "t1")) #"ty_hd") (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma")) }}.

(* One thing to immediately note is that the type signature on e3 is modified from the type signature in Harper and Morrisett. It is equivalent, since it is just the change of some arrows and quantifiers that don't change bindings. This is helpful in pyrosome because it makes the first appearance of sigma in the signature substitution-less, because now that sigma is only under one All and we substitute it with only one variable (there are no other variables in sigma and if there are any others in the environment we want to conserve them), so we can actually leave sigma as is -- that first variable in sigma get bound by the All, as desired. If you write the substitution for the second type out on paper, it looks like [0/0]. Why can't we do the same trick there? That's because pyrosome does entire-environment substitutions. Since we have two extra variables, we must also include those in the substitution. The reason this is not the identity is the same reason the first sigma would not have been the identity had we not done this trick: even though we substitute the first variable in sigma with the first additional All variable, we have another variable in the environment now (the second All in the case of the unmodified version of the rule in Harper and Morrisett) and so we must account for it (it would have had a {ty_wkn_n 1} there).  *)
Definition type_casing_def : lang :=
  {[l
    [:| "D" : #"ty_env",
        "G" : #"env" "D",
        "mu" : #"ty" "D", (* is mu *)
        "sigma" : #"ty" (#"ty_ext" "D"), (* this is sigma. it has a variable (hence the ext *)
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "sigma"), (* substitute identity type for all except the last (which is A), which we change to star *)
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "sigma"),
        "e3" : #"exp" "D" "G" (#"All" (#"->" "sigma" (#"All" (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma"))))) (* look at arrow case in 134 *)
        -----------------------------------------------
        #"typerec" "mu" "sigma" "e1" "e2" "e3"
        : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "mu") "sigma") (* verbose way of writing the [u/t]sigma in the rule on 134, verbose in that its the _full_ substitution *)
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "sigma"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "sigma"),
        "e3" : #"exp" "D" "G" (#"All" (#"->" "sigma" (#"All" (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma")))))
        ----------------------------------------------- ("typerec star")
        #"typerec" #"*" "sigma" "e1" "e2" "e3"
        = "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "sigma")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "sigma"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "sigma"),
        "e3" : #"exp" "D" "G" (#"All" (#"->" "sigma" (#"All" (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma")))))
        ----------------------------------------------- ("typerec bool")
        #"typerec" #"bool" "sigma" "e1" "e2" "e3"
        = "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "sigma")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "t1" : #"ty" "D",
        "t2" : #"ty" "D",
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "sigma"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "sigma"),
        "e3" : #"exp" "D" "G" (#"All" (#"->" "sigma" (#"All" (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma")))))
        ----------------------------------------------- ("typerec func") (* trec-fn on page 135 *)
        #"typerec" (#"->" "t1" "t2") "sigma" "e1" "e2" "e3"
        = #"app" (@"@" @("A" := {A_var}) (#"app" (#"@" "e3" "t1") (#"typerec" "t1" "sigma" "e1" "e2" "e3")) "t2") (#"typerec" "t2" "sigma" "e1" "e2" "e3")
        : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" (#"->" "t1" "t2")) "sigma")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G",
        "mu" : #"ty" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "sigma"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "sigma"),
        "e3" : #"exp" "D" "G" (#"All" (#"->" "sigma" (#"All" (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma")))))
        ----------------------------------------------- ("exp_subst typerec")
        #"exp_subst" "g" (#"typerec" "mu" "sigma" "e1" "e2" "e3")
        = #"typerec" "mu" "sigma" (#"exp_subst" "g" "e1") (#"exp_subst" "g" "e2") (#"exp_subst" "g" "e3")
        : #"exp" "D" "G'" (#"ty_subst" (#"ty_snoc" #"ty_id" "mu") "sigma")
    ];
    [:= "D" : #"ty_env",
        "D'" : #"ty_env",
        "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D",
        "mu" : #"ty" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "sigma"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "sigma"),
        "e3" : #"exp" "D" "G" (#"All" (#"->" "sigma" (#"All" (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma")))))
        ----------------------------------------------- ("ty_subst typerec")
        #"exp_ty_subst" "g" (#"typerec" "mu" "sigma" "e1" "e2" "e3")
        = #"typerec" (#"ty_subst" "g" "mu") (#"ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" "g") #"ty_hd") "sigma") (#"exp_ty_subst" "g" "e1") (#"exp_ty_subst" "g" "e2") (#"exp_ty_subst" "g" "e3")
        : #"exp" "D'" (#"env_ty_subst" "g" "G") (#"ty_subst" "g" (#"ty_subst" (#"ty_snoc" #"ty_id" "mu") "sigma"))
    ]
  ]}.
Derive type_casing
  in (elab_lang_ext (
                stlc_ty_subst ++
                  typed_bool_ty_subst ++ 
                  star_type_ty_subst ++ error_t_ty_subst ++
                  typed_bool_parameterized ++
                  stlc_parameterized ++
                  star_type_parameterized ++ error_t_parameterized ++
                  poly ++ (* needed for #"All" *)
                  (* base polymorphic stuff *)
                  exp_param_substs ++ exp_ty_subst ++
                  val_param_substs ++ val_ty_subst ++
                  env_ty_subst ++ ty_subst_lang ++
                  exp_parameterized ++ val_parameterized ++ ty_env_lang
              ) 
                type_casing_def type_casing)
        as type_casing_wf.
Proof. Timeout 1500 auto_elab. Qed.
#[local] Definition type_casing_entry :=
  lang_entry (elab_lang_implies_wf type_casing_wf).
#[export] Hint Resolve type_casing_entry : wf_lang_db.

Definition source_multilanguage := 
            boundaries ++ simple_interoperating_langs.
Hint Unfold source_multilanguage : auto_elab. 

Definition target_multilanguage :=
  prod_ty_subst ++ prod_parameterized ++
    type_casing ++
    polymorphic_interoperating_langs.
Hint Unfold target_multilanguage : auto_elab.

Lemma source_multilanguage_wf : wf_lang source_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition source_multilanguage_entry :=
  lang_entry source_multilanguage_wf.
#[export] Hint Resolve source_multilanguage_entry : wf_lang_db.

Lemma target_multilanguage_wf : wf_lang target_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_entry :=
  lang_entry target_multilanguage_wf.
#[export] Hint Resolve target_multilanguage_entry : wf_lang_db.
