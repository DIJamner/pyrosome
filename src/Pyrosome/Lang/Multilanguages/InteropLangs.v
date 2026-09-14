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
From Pyrosome.Lang.Multilanguages Require Export ParamFragments.



Definition simple_interoperating_langs :=
  boolhuh ++
    mif ++
    utlc_bool ++ 
    utlc ++ 
    untyped_bool ++ 
    star_type ++ error_t ++ 
    typed_bool ++ 
    stlc ++ 
    exp_subst ++ 
    value_subst.

Definition polymorphic_interoperating_langs :=
  boolhuh_ty_subst ++ boolhuh_parameterized ++
    mif_ty_subst ++ mif_parameterized ++
    utlc_bool_parameterized ++
    utlc_ty_subst ++ utlc_parameterized ++
    untyped_bool_ty_subst ++ untyped_bool_parameterized ++
    star_type_ty_subst ++ error_t_ty_subst ++
    star_type_parameterized ++ error_t_parameterized ++
    typed_bool_ty_subst ++ typed_bool_parameterized ++
    stlc_ty_subst ++ stlc_parameterized ++
    (* all polymorphic base stuff. Don't need poly because we don't have type lambdas or type application. but we might as well add it now bc we'll extend this list with polymorphic stuff for the polymorphic to polymorphic compiler *)
    poly ++
    exp_param_substs ++
    exp_ty_subst ++
    val_param_substs ++
    val_ty_subst ++
    env_ty_subst ++
    ty_subst_lang ++
    exp_parameterized ++ val_parameterized ++ ty_env_lang.


Lemma simple_interoperating_langs_wf : wf_lang simple_interoperating_langs.
Proof. prove_by_lang_db. Qed.
#[local] Definition simple_interoperating_langs_entry := lang_entry simple_interoperating_langs_wf.
#[export] Hint Resolve simple_interoperating_langs_entry : wf_lang_db.

Lemma polymorphic_interoperating_langs_wf : wf_lang polymorphic_interoperating_langs.
Proof. prove_by_lang_db. Qed.
#[local] Definition polymorphic_interoperating_langs_entry := lang_entry polymorphic_interoperating_langs_wf.
#[export] Hint Resolve polymorphic_interoperating_langs_entry : wf_lang_db.

Local Notation compiler := (compiler string).

Definition interoperating_langs_compiler_def : compiler :=
  match # from simple_interoperating_langs with
  | {{s#"ty"}} => {{s #"ty" #"ty_emp"}}
  | {{s#"env"}} => {{s #"env" #"ty_emp"}}
  | {{s#"sub" "G" "G'"}} => {{s #"sub" #"ty_emp" "G" "G'"}}
  | {{e#"id" "G"}} => {{e @"id" @("D" := #"ty_emp")}}
  | {{e#"cmp" "G1" "G2" "G3" "f" "g"}} => {{e @"cmp" @("D" := #"ty_emp") "f" "g"}}
  | {{s#"val" "G" "A"}} => {{s #"val" #"ty_emp" "G" "A"}}
  | {{e#"val_subst" "G" "G'" "g" "A" "v"}} => {{e @"val_subst" @("D" := #"ty_emp") "g" "v"}}
  | {{e#"emp"}} => {{e @"emp" @("D" := #"ty_emp")}}
  | {{e#"forget" "G"}} => {{e @"forget" @("D" := #"ty_emp")}}
  | {{e#"ext" "G" "A"}} => {{e @"ext" @("D" := #"ty_emp") "G" "A"}}
  | {{e#"snoc" "G" "G'" "g" "A" "v"}} => {{e @"snoc" @("D" := #"ty_emp") "g" "v"}}
  | {{e#"wkn" "G" "A"}} => {{e @"wkn" @("D" := #"ty_emp")}}
  | {{e#"hd" "G" "A"}} => {{e @"hd" @("D" := #"ty_emp")}}
  | {{s#"exp" "G" "A"}} => {{s #"exp" #"ty_emp" "G" "A"}}
  | {{e#"exp_subst" "G" "G'" "g" "A" "e"}} => {{e @"exp_subst" @("D" := #"ty_emp") "g" "e"}}
  | {{e#"ret" "G" "A" "v"}} => {{e @"ret" @("D" := #"ty_emp") "v"}}
  | {{e#"->" "t" "t'"}} => {{e @"->" @("D" := #"ty_emp") "t" "t'"}}
  | {{e#"lambda" "G" "A" "B" "e"}} => {{e @"lambda" @("D" := #"ty_emp") "A" "e"}}
  | {{e#"app" "G" "A" "B" "e" "e'"}} => {{e @"app" @("D" := #"ty_emp") "e" "e'"}}
  | {{e#"bool"}} => {{e @"bool" @("D" := #"ty_emp")}}
  | {{e#"T" "G"}} => {{e @"T" @("D" := #"ty_emp")}}
  | {{e#"F" "G"}} => {{e @"F" @("D" := #"ty_emp")}}
  | {{e#"if" "G" "A" "cond" "e2" "e3"}} => {{e @"if" @("D" := #"ty_emp") "cond" "e2" "e3"}}
  | {{e#"*"}} => {{e @"*" @("D" := #"ty_emp")}}
  | {{e#"Error" "G" "t"}} => {{e @"Error" @("D" := #"ty_emp") "t"}}
  | {{e#"uT" "G"}} => {{e @"uT" @("D" := #"ty_emp")}}
  | {{e#"uF" "G"}} => {{e @"uF" @("D" := #"ty_emp")}}
  | {{e#"ulambda" "G" "e"}} => {{e @"ulambda" @("D" := #"ty_emp") "e"}}
  | {{e#"uapp" "G" "e" "e'"}} => {{e @"uapp" @("D" := #"ty_emp") "e" "e'"}}
  | {{e#"bool?" "G" "e"}} => {{e @"bool?" @("D" := #"ty_emp") "e"}}
  | {{e#"mif" "G" "A" "cond" "e2" "e3"}} => {{e @"mif" @("D" := #"ty_emp") "cond" "e2" "e3"}}
  end.

Derive interoperating_langs_compiler
        in (elab_preserving_compiler 
                    []
                    polymorphic_interoperating_langs
                    interoperating_langs_compiler_def
                    interoperating_langs_compiler
                    simple_interoperating_langs) 
        as interoperating_langs_compiler_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition interoperating_langs_entry :=
  cmp_entry (elab_compiler_implies_preserving interoperating_langs_compiler_preserving).
#[export] Hint Resolve interoperating_langs_entry : preserving_db.
