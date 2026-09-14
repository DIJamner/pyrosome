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
  Tools.EGraph.TypeInference Tools.EGraph.InjRuleGen Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

From Stdlib Require derive.Derive.

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC. 
From Pyrosome.Lang Require Import UTLC. 
From Pyrosome.Lang Require Import BoolType. 
From Pyrosome.Lang Require Import SimpleVProd.
From Pyrosome.Lang Require Import Let.


(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers. (* for parameterizing existing languages*)
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.



(* Our target multilanguage without boundaries will be polymorphic. So, we need to make polymorphic versions of all the fragments that constitute the two interoperating languages. *)
(* NOTE: the following helpers are abstracted from the definition of stlc_parameterized in PolyCompilers.v *)
Definition parameterize_wrapper (l : lang) : lang := 
    let ps := (elab_param "D" (l
                                 ++ exp_ret 
                                 ++ exp_subst_base
                                 ++ value_subst
                                 )
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps l.
Local Definition evp'_general (l : lang) : lang := 
    let ps := (elab_param "D" (l ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_ret ++ exp_subst_base ++ value_subst).
Ltac solve_parameterize_wrapper l := (* deleted comments in equivalent code from PolyCompilers.v*)
  change (exp_parameterized++val_parameterized) with (evp'_general l);
  eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor
    | now prove_by_lang_db..
    | vm_compute; exact I].

Definition typed_bool_parameterized := parameterize_wrapper typed_bool. 
Lemma typed_bool_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      typed_bool_parameterized.
Proof. solve_parameterize_wrapper typed_bool. Qed. 
#[local] Definition typed_bool_parameterized_entry :=
  lang_entry typed_bool_parameterized_wf.
#[export] Hint Resolve typed_bool_parameterized_entry : wf_lang_db.

(* NOTE: stlc_parameterized already exists in PolyCompilers.v *)

(* the parameterizer does not do the type substitutions, so we have do do those manually as a small fragment. *)
Definition ty_subst_def_maker (parameterized_lang : lang) parameterized_dependencies := eqn_rules
  type_subst_mode
  (parameterized_dependencies ++
    exp_param_substs ++ exp_ty_subst ++
     val_param_substs ++ val_ty_subst ++
     env_ty_subst ++ ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
    (hide_lang_implicits (parameterized_lang ++ parameterized_dependencies ++
                            exp_param_substs ++
                            exp_ty_subst ++
                            val_param_substs ++
                            val_ty_subst ++
                            env_ty_subst ++
                            ty_subst_lang ++
                            exp_parameterized ++ val_parameterized ++ ty_env_lang
       )
       parameterized_lang).

Definition typed_bool_ty_subst_def := Eval vm_compute in ty_subst_def_maker typed_bool_parameterized [].
Derive typed_bool_ty_subst
  in (elab_lang_ext (typed_bool_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              typed_bool_ty_subst_def typed_bool_ty_subst)
  as typed_bool_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition typed_bool_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf typed_bool_ty_subst_wf).
#[export] Hint Resolve typed_bool_ty_subst_entry : wf_lang_db.

Definition stlc_ty_subst_def := Eval vm_compute in ty_subst_def_maker stlc_parameterized [].
Derive stlc_ty_subst
  in (elab_lang_ext (stlc_parameterized ++
                             exp_param_substs ++ exp_ty_subst ++
                             val_param_substs ++ val_ty_subst ++
                             env_ty_subst ++ ty_subst_lang ++
                             exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              stlc_ty_subst_def stlc_ty_subst)
  as stlc_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition stlc_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf stlc_ty_subst_wf).
#[export] Hint Resolve stlc_ty_subst_entry : wf_lang_db.

Definition star_type_parameterized := parameterize_wrapper star_type.
Lemma star_type_parameterized_wf : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang) star_type_parameterized.
Proof. solve_parameterize_wrapper star_type. Qed.
#[local] Definition star_type_parameterized_entry :=
  lang_entry star_type_parameterized_wf.
#[export] Hint Resolve star_type_parameterized_entry : wf_lang_db.

Definition error_t_parameterized := parameterize_wrapper error_t.
Lemma error_t_parameterized_wf : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang) error_t_parameterized.
Proof. solve_parameterize_wrapper error_t. Qed.
#[local] Definition error_t_parameterized_entry :=
  lang_entry error_t_parameterized_wf.
#[export] Hint Resolve error_t_parameterized_entry : wf_lang_db.

Definition star_type_ty_subst_def := Eval vm_compute in ty_subst_def_maker star_type_parameterized [].
Derive star_type_ty_subst
  in (elab_lang_ext (star_type_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              star_type_ty_subst_def star_type_ty_subst)
  as star_type_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition star_type_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf star_type_ty_subst_wf).
#[export] Hint Resolve star_type_ty_subst_entry : wf_lang_db.

Definition error_t_ty_subst_def := Eval vm_compute in ty_subst_def_maker error_t_parameterized [].
Derive error_t_ty_subst
  in (elab_lang_ext (error_t_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              error_t_ty_subst_def error_t_ty_subst)
  as error_t_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition error_t_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf error_t_ty_subst_wf).
#[export] Hint Resolve error_t_ty_subst_entry : wf_lang_db.



(* TODO from this point on, try to generalize the parameterizing function and combine it with what's above *)

Definition utlc_parameterized := 
    let ps := (elab_param "D" (utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps utlc.
(* for some reason need to redo the evp functions for these languages. think it has to do with the dependencies. *)
Local Definition evp'_utlc : lang := 
    let ps := (elab_param "D" (utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma utlc_parameterized_wf
  : wf_lang_ext ((star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      utlc_parameterized.
Proof.
  replace (star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_utlc.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | now prove_by_lang_db..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition utlc_parameterized_entry :=
  lang_entry utlc_parameterized_wf.
#[export] Hint Resolve utlc_parameterized_entry : wf_lang_db.

Definition utlc_ty_subst_def := Eval vm_compute in ty_subst_def_maker utlc_parameterized (star_type_parameterized ++ error_t_parameterized). 
Derive utlc_ty_subst
  in (elab_lang_ext (
                utlc_parameterized ++
                  star_type_ty_subst ++ error_t_ty_subst ++
                  star_type_parameterized ++ error_t_parameterized ++
                  exp_param_substs ++
                  exp_ty_subst ++
                  val_param_substs ++
                  val_ty_subst ++
                  env_ty_subst ++
                  ty_subst_lang ++
                  exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              utlc_ty_subst_def utlc_ty_subst)
  as utlc_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition utlc_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf utlc_ty_subst_wf).
#[export] Hint Resolve utlc_ty_subst_entry : wf_lang_db.

Definition untyped_bool_parameterized := 
    let ps := (elab_param "D" (untyped_bool ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps untyped_bool.
Local Definition evp'_untyped_bool : lang := 
    let ps := (elab_param "D" (untyped_bool ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma untyped_bool_parameterized_wf
  : wf_lang_ext ((star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      untyped_bool_parameterized.
Proof. 
  replace (star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_untyped_bool.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | now prove_by_lang_db..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition untyped_bool_parameterized_entry :=
  lang_entry untyped_bool_parameterized_wf.
#[export] Hint Resolve untyped_bool_parameterized_entry : wf_lang_db.

Definition untyped_bool_ty_subst_def := Eval vm_compute in ty_subst_def_maker untyped_bool_parameterized (star_type_parameterized ++ error_t_parameterized). 
Derive untyped_bool_ty_subst
  in (elab_lang_ext (
                untyped_bool_parameterized ++
                  star_type_ty_subst ++ error_t_ty_subst ++
                  star_type_parameterized ++ error_t_parameterized ++
                  exp_param_substs ++
                  exp_ty_subst ++
                  val_param_substs ++
                  val_ty_subst ++
                  env_ty_subst ++
                  ty_subst_lang ++
                  exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              untyped_bool_ty_subst_def untyped_bool_ty_subst)
  as untyped_bool_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition untyped_bool_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf untyped_bool_ty_subst_wf).
#[export] Hint Resolve untyped_bool_ty_subst_entry : wf_lang_db.

Definition boolhuh_parameterized := 
    let ps := (elab_param "D" (boolhuh ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps boolhuh.
Local Definition evp'_boolhuh : lang := 
    let ps := (elab_param "D" (boolhuh ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma boolhuh_parameterized_wf
  : wf_lang_ext ((untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      boolhuh_parameterized.
Proof. 
  replace (untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_boolhuh.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | now prove_by_lang_db..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition boolhuh_parameterized_entry :=
  lang_entry boolhuh_parameterized_wf.
#[export] Hint Resolve boolhuh_parameterized_entry : wf_lang_db.

Definition boolhuh_ty_subst_def := Eval vm_compute in ty_subst_def_maker boolhuh_parameterized (untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized).
Derive boolhuh_ty_subst
  in (elab_lang_ext ( (* add all dependencies with their ty_subst versions and the current parameterized lang *)
                boolhuh_parameterized ++
                untyped_bool_ty_subst ++
                untyped_bool_parameterized ++
                utlc_ty_subst ++
                utlc_parameterized ++
                star_type_ty_subst ++ error_t_ty_subst ++ 
                star_type_parameterized ++ error_t_parameterized ++
                exp_param_substs ++
                exp_ty_subst ++
                val_param_substs ++
                val_ty_subst ++
                env_ty_subst ++
                ty_subst_lang ++
                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              boolhuh_ty_subst_def boolhuh_ty_subst)
  as boolhuh_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition boolhuh_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf boolhuh_ty_subst_wf).
#[export] Hint Resolve boolhuh_ty_subst_entry : wf_lang_db.

(* NOTE: utlc_bool does not need a ty_subst lang because there is no new syntax in utlc_bool *)
Definition utlc_bool_parameterized := 
    let ps := (elab_param "D" (utlc_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps utlc_bool.
Local Definition evp'_utlc_bool : lang := 
    let ps := (elab_param "D" (utlc_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma utlc_bool_parameterized_wf
  : wf_lang_ext ((untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      utlc_bool_parameterized.
Proof. 
  replace (untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_utlc_bool.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | now prove_by_lang_db..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition utlc_bool_parameterized_entry :=
  lang_entry utlc_bool_parameterized_wf.
#[export] Hint Resolve utlc_bool_parameterized_entry : wf_lang_db.

Definition mif_parameterized := 
    let ps := (elab_param "D" (mif ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps mif.
Local Definition evp'_mif : lang := 
    let ps := (elab_param "D" (mif ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma mif_parameterized_wf
  : wf_lang_ext ((untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      mif_parameterized.
Proof. 
  replace (untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_mif.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor
    | now prove_by_lang_db..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition mif_parameterized_entry :=
  lang_entry mif_parameterized_wf.
#[export] Hint Resolve mif_parameterized_entry : wf_lang_db.

Definition mif_ty_subst_def := Eval vm_compute in ty_subst_def_maker mif_parameterized (untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized).
Derive mif_ty_subst
  in (elab_lang_ext ( (* add all dependencies with their ty_subst versions and the current parameterized lang *)
                mif_parameterized ++
                untyped_bool_ty_subst ++
                untyped_bool_parameterized ++
                utlc_ty_subst ++
                utlc_parameterized ++
                star_type_ty_subst ++ error_t_ty_subst ++ 
                star_type_parameterized ++ error_t_parameterized ++
                exp_param_substs ++
                exp_ty_subst ++
                val_param_substs ++
                val_ty_subst ++
                env_ty_subst ++
                ty_subst_lang ++
                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              mif_ty_subst_def mif_ty_subst)
  as mif_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition mif_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf mif_ty_subst_wf).
#[export] Hint Resolve mif_ty_subst_entry : wf_lang_db.

Definition prod_parameterized := parameterize_wrapper prod. 
Lemma prod_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      prod_parameterized.
Proof. solve_parameterize_wrapper prod. Qed. 
#[local] Definition prod_parameterized_entry :=
  lang_entry prod_parameterized_wf.
#[export] Hint Resolve prod_parameterized_entry : wf_lang_db.
Definition prod_ty_subst_def := Eval vm_compute in ty_subst_def_maker prod_parameterized [].
Derive prod_ty_subst
  in (elab_lang_ext (prod_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              prod_ty_subst_def prod_ty_subst)
  as prod_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition prod_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf prod_ty_subst_wf).
#[export] Hint Resolve prod_ty_subst_entry : wf_lang_db.


(* ------------------------------------------------------------------ *)
(* The let extension (Let.v) and a one-rule eta law for it.

   These are added to the target multilanguage so that the boundary
   compiler can let-bind its argument (a variable is a value, so
   [STLC-beta] fires), and so that [let e (ret hd)] collapses to [e].  *)

Definition let_eta_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:= "G" : #"env",
      "A" : #"ty",
      "e" : #"exp" "G" "A"
      ----------------------------------------------- ("let eta")
      #"let" "e" (#"ret" #"hd") = "e" : #"exp" "G" "A"
  ] ]}.

Definition let_eta :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 (let_lang ++ exp_subst ++ value_subst) let_eta_def.

Lemma let_eta_wf : wf_lang_ext (let_lang ++ exp_subst ++ value_subst) let_eta.
Proof. compute_wf_lang. Qed.
#[local] Definition let_eta_entry := lang_entry let_eta_wf.
#[export] Hint Resolve let_eta_entry : wf_lang_db.

Definition let_parameterized := parameterize_wrapper let_lang.
Lemma let_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      let_parameterized.
Proof. solve_parameterize_wrapper let_lang. Qed.
#[local] Definition let_parameterized_entry :=
  lang_entry let_parameterized_wf.
#[export] Hint Resolve let_parameterized_entry : wf_lang_db.

Definition let_ty_subst_def := Eval vm_compute in ty_subst_def_maker let_parameterized [].
Derive let_ty_subst
  in (elab_lang_ext (let_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              let_ty_subst_def let_ty_subst)
  as let_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition let_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf let_ty_subst_wf).
#[export] Hint Resolve let_ty_subst_entry : wf_lang_db.

(* NOTE: let_eta adds no new syntax, so (like utlc_bool) it needs no ty_subst lang *)
Definition let_eta_parameterized :=
    let ps := (elab_param "D" (let_eta ++ let_lang ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps let_eta.
Local Definition evp'_let_eta : lang :=
    let ps := (elab_param "D" (let_eta ++ let_lang ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (let_lang ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma let_eta_parameterized_wf
  : wf_lang_ext ((let_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      let_eta_parameterized.
Proof.
  replace (let_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_let_eta.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor
    | now prove_by_lang_db..
    | vm_compute; exact I].
  - cbv; reflexivity.
Qed.
#[local] Definition let_eta_parameterized_entry :=
  lang_entry let_eta_parameterized_wf.
#[export] Hint Resolve let_eta_parameterized_entry : wf_lang_db.
