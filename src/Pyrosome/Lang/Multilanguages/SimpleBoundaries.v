Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
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

Require Coq.derive.Derive.

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC. 
From Pyrosome.Lang Require Import UTLC. 
From Pyrosome.Lang Require Import BoolType. 
From Pyrosome.Lang Require Import SimpleVProd.


(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilers. (* for parameterizing existing languages*)
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
    | now prove_from_known_elabs..
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
  SuchThat (elab_lang_ext (typed_bool_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              typed_bool_ty_subst_def typed_bool_ty_subst)
  As typed_bool_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition typed_bool_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf typed_bool_ty_subst_wf).
#[export] Hint Resolve typed_bool_ty_subst_entry : wf_lang_db.

Definition stlc_ty_subst_def := Eval vm_compute in ty_subst_def_maker stlc_parameterized [].
Derive stlc_ty_subst
  SuchThat (elab_lang_ext (stlc_parameterized ++
                             exp_param_substs ++ exp_ty_subst ++
                             val_param_substs ++ val_ty_subst ++
                             env_ty_subst ++ ty_subst_lang ++
                             exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              stlc_ty_subst_def stlc_ty_subst)
  As stlc_ty_subst_wf.
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
  SuchThat (elab_lang_ext (star_type_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              star_type_ty_subst_def star_type_ty_subst)
  As star_type_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition star_type_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf star_type_ty_subst_wf).
#[export] Hint Resolve star_type_ty_subst_entry : wf_lang_db.

Definition error_t_ty_subst_def := Eval vm_compute in ty_subst_def_maker error_t_parameterized [].
Derive error_t_ty_subst
  SuchThat (elab_lang_ext (error_t_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              error_t_ty_subst_def error_t_ty_subst)
  As error_t_ty_subst_wf.
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
    | now prove_from_known_elabs..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition utlc_parameterized_entry :=
  lang_entry utlc_parameterized_wf.
#[export] Hint Resolve utlc_parameterized_entry : wf_lang_db.

Definition utlc_ty_subst_def := Eval vm_compute in ty_subst_def_maker utlc_parameterized (star_type_parameterized ++ error_t_parameterized). 
Derive utlc_ty_subst
  SuchThat (elab_lang_ext (
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
  As utlc_ty_subst_wf.
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
    | now prove_from_known_elabs..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition untyped_bool_parameterized_entry :=
  lang_entry untyped_bool_parameterized_wf.
#[export] Hint Resolve untyped_bool_parameterized_entry : wf_lang_db.

Definition untyped_bool_ty_subst_def := Eval vm_compute in ty_subst_def_maker untyped_bool_parameterized (star_type_parameterized ++ error_t_parameterized). 
Derive untyped_bool_ty_subst
  SuchThat (elab_lang_ext (
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
  As untyped_bool_ty_subst_wf.
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
    | now prove_from_known_elabs..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition boolhuh_parameterized_entry :=
  lang_entry boolhuh_parameterized_wf.
#[export] Hint Resolve boolhuh_parameterized_entry : wf_lang_db.

Definition boolhuh_ty_subst_def := Eval vm_compute in ty_subst_def_maker boolhuh_parameterized (untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized).
Derive boolhuh_ty_subst
  SuchThat (elab_lang_ext ( (* add all dependencies with their ty_subst versions and the current parameterized lang *)
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
  As boolhuh_ty_subst_wf. 
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
    | now prove_from_known_elabs..
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
    | now prove_from_known_elabs..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition mif_parameterized_entry :=
  lang_entry mif_parameterized_wf.
#[export] Hint Resolve mif_parameterized_entry : wf_lang_db.

Definition mif_ty_subst_def := Eval vm_compute in ty_subst_def_maker mif_parameterized (untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized).
Derive mif_ty_subst
  SuchThat (elab_lang_ext ( (* add all dependencies with their ty_subst versions and the current parameterized lang *)
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
  As mif_ty_subst_wf. 
Proof. auto_elab. Qed. 
#[local] Definition mif_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf mif_ty_subst_wf).
#[export] Hint Resolve mif_ty_subst_entry : wf_lang_db.

(* NOTE: this makes the compiler take forever. why? name stuff? unfolding everything doesn't make it work
Definition simple_typed_fragment := typed_bool ++ stlc.
Hint Unfold simple_typed_fragment : auto_elab. 

Definition simple_untyped_fragment := mif ++ utlc_bool ++ boolhuh ++ untyped_bool ++ utlc ++ error_t ++ star_type.
Hint Unfold simple_untyped_fragment : auto_elab. 

Definition simple_interoperating_langs :=
  simple_untyped_fragment ++
    simple_typed_fragment ++
    exp_subst ++ value_subst.
Hint Unfold simple_interoperating_langs : auto_elab. 

Definition polymorphic_typed_fragment :=
  typed_bool_ty_subst ++ typed_bool_parameterized ++
    stlc_ty_subst ++ stlc_parameterized.
Hint Unfold polymorphic_typed_fragment : auto_elab. 

Definition polymorphic_untyped_fragment :=
  boolhuh_ty_subst ++ boolhuh_parameterized ++
      utlc_bool_parameterized ++
      utlc_ty_subst ++ utlc_parameterized ++
      untyped_bool_ty_subst ++ untyped_bool_parameterized ++
      star_type_ty_subst ++ error_t_ty_subst ++
      star_type_parameterized ++ error_t_parameterized.
Hint Unfold polymorphic_untyped_fragment : auto_elab. 

Definition polymorphic_interoperating_langs :=
  polymorphic_typed_fragment ++
    polymorphic_untyped_fragment ++
    exp_param_substs ++
    exp_ty_subst ++
    val_param_substs ++
    val_ty_subst ++
    env_ty_subst ++
    ty_subst_lang ++
    exp_parameterized ++ val_parameterized ++ ty_env_lang.
Hint Unfold polymorphic_interoperating_langs : auto_elab.
*)


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
        SuchThat (elab_preserving_compiler 
                    []
                    polymorphic_interoperating_langs
                    interoperating_langs_compiler_def
                    interoperating_langs_compiler
                    simple_interoperating_langs) 
        As interoperating_langs_compiler_preserving. 
Proof. auto_elab_compiler. Qed.
#[local] Definition interoperating_langs_entry :=
  cmp_entry (elab_compiler_implies_preserving interoperating_langs_compiler_preserving).
#[export] Hint Resolve interoperating_langs_entry : preserving_db.



(* Now the multilanguages *)

(* First, we define the boundaries fragment. To me, it seems like this is the natural embedding. TODO: see if you can, as Dustin said, simulate the lump embedding. *)
Definition boundaries_def : lang :=
  {[l/subst [exp_subst++value_subst] 
    [:| "G" : #"env",
        "A" : #"ty",
        "e" : #"exp" "G" "A"
        -----------------------------------------------
        #"ttd" "A" "e" : #"exp" "G" #"*"
    ];
    [:| "G" : #"env",
        "A" : #"ty",
        "e" : #"exp" "G" #"*"
        -----------------------------------------------
        #"dtt" "A" "e" : #"exp" "G" "A"
    ];
    [:= "G" : #"env",
        "e" : #"exp" "G" #"*"
        ----------------------------------------------- ("dtt star")
        #"dtt" #"*" "e" =
        "e" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "e" : #"exp" "G" #"*"
        ----------------------------------------------- ("ttd star")
        #"ttd" #"*" "e" =
        "e" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt True")
        #"dtt" #"bool" (#"ret" #"uT") =
        #"ret" #"T" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt False")
        #"dtt" #"bool" (#"ret" #"uF") =
        #"ret" #"F" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd True")
        #"ttd" #"bool" (#"ret" #"T") =
        #"ret" #"uT" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd False")
        #"ttd" #"bool" (#"ret" #"F") =
        #"ret" #"uF" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("dtt func")
        #"dtt" (#"->" "A" "B") (#"ret" "v") =
        #"ret" (#"lambda" "A" (#"dtt" "B" (#"uapp" (#"ret" (#"val_subst" #"wkn" "v")) (#"ttd" "A" (#"ret" #"hd"))))) :
        #"exp" "G" (#"->" "A" "B")
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" (#"->" "A" "B")
        ----------------------------------------------- ("ttd func")
        #"ttd" (#"->" "A" "B") (#"ret" "v") =
        #"ret" (#"ulambda" (#"ttd" "B" (#"app" (#"ret" (#"val_subst" #"wkn" "v")) (#"dtt" "A" (#"ret" #"hd"))))) :
        #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "e" : #"exp" (#"ext" "G" #"*") #"*"
        ----------------------------------------------- ("dtt ulambda mismatch")
        #"dtt" #"bool" (#"ret" (#"ulambda" "e")) =
        #"Error" #"bool" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty"
        ----------------------------------------------- ("dtt uT mismatch")
        #"dtt" (#"->" "A" "B") (#"ret" #"uT") =
        #"Error" (#"->" "A" "B") : #"exp" "G" (#"->" "A" "B")
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty"
        ----------------------------------------------- ("dtt uF mismatch")
        #"dtt" (#"->" "A" "B") (#"ret" #"uF") =
        #"Error" (#"->" "A" "B") : #"exp" "G" (#"->" "A" "B")
    ]
  ]}.
Derive boundaries
        SuchThat (elab_lang_ext (utlc ++ 
                                stlc ++ 
                                typed_bool ++
                                untyped_bool ++
                                error_t ++ star_type ++
                                exp_subst++value_subst) 
                boundaries_def boundaries)
        As boundaries_wf.
Proof. auto_elab. Qed.
#[local] Definition boundaries_entry :=
  lang_entry (elab_lang_implies_wf boundaries_wf).
#[export] Hint Resolve boundaries_entry : wf_lang_db.

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
  SuchThat (elab_lang_ext (
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
        As type_casing_wf.
Proof. auto_elab. Qed. 
#[local] Definition type_casing_entry :=
  lang_entry (elab_lang_implies_wf type_casing_wf).
#[export] Hint Resolve type_casing_entry : wf_lang_db.

Definition source_multilanguage := 
            boundaries ++ simple_interoperating_langs.
Hint Unfold source_multilanguage : auto_elab. 

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
  SuchThat (elab_lang_ext (prod_parameterized ++
                                exp_param_substs ++ exp_ty_subst ++
                                val_param_substs ++ val_ty_subst ++
                                env_ty_subst ++ ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              prod_ty_subst_def prod_ty_subst)
  As prod_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition prod_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf prod_ty_subst_wf).
#[export] Hint Resolve prod_ty_subst_entry : wf_lang_db.

Definition target_multilanguage :=
  prod_ty_subst ++ prod_parameterized ++
    type_casing ++
    polymorphic_interoperating_langs.
Hint Unfold target_multilanguage : auto_elab.



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
Proof. solve_elab_term_or_sort target_multilanguage. Qed. (* used to be derive_elab_term *)

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
Proof. solve_elab_term_or_sort target_multilanguage. Qed. (* used to be derive_elab_term *)

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
Proof. solve_elab_term_or_sort target_multilanguage. Qed. (* used to be derive_elab_term *)

Definition trec_func_case_unelab :=
  {{e #"ret" (#"Lam" (#"ret" (#"lambda" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0})) (#"ret" (#"Lam" (#"ret" (#"lambda" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0})) (#"pair" (#"ret" (#"lambda" (#"->" {ty_ovar 1} {ty_ovar 0}) (#"ret" (#"ulambda" (#"app" (#".1" (#"ret" {ovar 2})) (#"app" (#"ret" {ovar 1}) (#"app" (#".2" (#"ret" {ovar 3})) (#"ret" {ovar 0})))))))) (#"ret" (#"lambda" #"*" (#"ret" (#"lambda" {ty_ovar 1} (#"app" (#".2" (#"ret" {ovar 2})) (#"uapp" (#"ret" {ovar 1}) (#"app" (#".1" (#"ret" {ovar 3})) (#"ret" {ovar 0})))) ) ))))))))))) }}.
Derive trec_func_case
  in ( elab_term target_multilanguage
         [("G", {{s #"env" #"ty_emp"}})]
         trec_func_case_unelab
         trec_func_case
         trec_func_case_sort
     ) as trec_func_case_wf.
Proof. solve_elab_term_or_sort target_multilanguage. Qed. 

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
Proof. solve_elab_term_or_sort target_multilanguage. Qed.



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
  unshelve (Automation.by_reduction);
  match goal with
  | |- wf_term _ _ _ _ => compute_term_wf
  | |- _ => solve_wf_ctx
  end.

Derive simple_multilang_compiler 
  SuchThat (elab_preserving_compiler 
              interoperating_langs_compiler
              target_multilanguage
              simple_multilang_compiler_def
              simple_multilang_compiler
              boundaries) 
  As simple_multilang_compiler_preserving. 
Proof. solve_multilang_compiler. Qed. 

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



(* partial evaluator to get rid of type casing. *)
Definition func_partial_eval_ctx' :=
  Eval vm_compute in Rule.get_ctx (named_list_lookup default target_multilanguage "typerec func").

Definition comp_t1_type := {{s #"exp" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") "t1") "sigma") }}.

Definition comp_t2_type := {{s #"exp" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") "t2") "sigma") }}.

Definition func_partial_eval_ctx := Eval vm_compute in [("comp_t2", comp_t2_type); ("comp_t1", comp_t1_type); ("e3", named_list_lookup default func_partial_eval_ctx' "e3"); ("t2", named_list_lookup default func_partial_eval_ctx' "t2"); ("t1", named_list_lookup default func_partial_eval_ctx' "t1"); ("sigma", named_list_lookup default func_partial_eval_ctx' "sigma"); ("G", named_list_lookup default func_partial_eval_ctx' "G"); ("D", named_list_lookup default func_partial_eval_ctx' "D")]. 

Definition func_partial_eval_term_def := (* comp_t1 ie computation of type t1. cf substitution in meta_typerec *)
  {{e #"app" (#"@" (#"app" (#"@" "e3" "t1") "comp_t1") "t2") "comp_t2" }}.

Derive func_partial_eval_term
  in ( elab_term target_multilanguage
         func_partial_eval_ctx
         func_partial_eval_term_def
         func_partial_eval_term
         {{s #"exp" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") (#"->" "D" "t1" "t2")) "sigma") }}
     ) as func_partial_eval_term_wf. 
Proof. solve_elab_term_or_sort target_multilanguage. Qed.

Fixpoint meta_typerec (D G mu sigma e1 e2 e3 : term) : term :=
  match mu with
  | {{e #"*" {_} }} => e1
  | {{e #"bool" {_} }} => e2
  | {{e #"->" {_} {t1} {t2} }} =>
      func_partial_eval_term [/ [ ("e3", e3);
                                  ("t1", t1);
                                  ("comp_t1", meta_typerec D G t1 sigma e1 e2 e3);
                                  ("t2", t2);
                                  ("comp_t2", meta_typerec D G t2 sigma e1 e2 e3);
                                  ("G", G);
                                  ("D", D) ] /]
  | _ => mu
  end.

Fixpoint elim_typerec (program : term) : term :=
  match program with
  | {{e #"typerec" {D} {G} {mu} {sigma} {e1} {e2} {e3} }} => meta_typerec D G mu sigma (elim_typerec e1) (elim_typerec e2) (elim_typerec e3)
  | con n s => con n (map elim_typerec s)
  | var n => var n
  end.

Fixpoint is_simple_type (mu : term) : Prop :=
  match mu with
  | {{e #"*" {_} }} => True
  | {{e #"bool" {_} }} => True
  | {{e #"->" {_} {t1} {t2} }} => is_simple_type t1 /\ is_simple_type t2
  | _ => False
  end.

Fixpoint all_typerecs_simple (program : term) : Prop :=
  match program with
  | {{e #"typerec" {D} {G} {mu} {sigma} {e1} {e2} {e3} }} =>
      is_simple_type mu /\
        all_typerecs_simple e1 /\ all_typerecs_simple e2 /\ all_typerecs_simple e3
  | con _ s => all all_typerecs_simple s
  | var _ => True
  end.

From Pyrosome.Theory Require Import WfCutElim CutFreeInd.

Ltac invert_wf_args :=
        match goal with
        | H : ComputeWf.wf_args _ _ _ _ |- _ => inversion H; clear H
        end.

Lemma no_sort_eqns_in_sml : Is_true (no_sort_eqns source_multilanguage).
Proof. apply I. Qed. 
Check sort_names_equal.

Lemma source_multilanguage_wf : wf_lang source_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition source_multilanguage_entry :=
  lang_entry source_multilanguage_wf.
#[export] Hint Resolve source_multilanguage_entry : wf_lang_db.

Lemma ty_eq_sort_lemma : forall (t : sort), Core.wf_sort source_multilanguage [] t -> eq_sort source_multilanguage [] t {{s #"ty"}} <-> t = {{s #"ty" }}.
Proof.
  intros; inversion H;
    repeat (simpl in H0; destruct H0;
            [> first [ solve [ injection H0; intros HF; inversion HF ]
                     | solve [ apply conj; inversion H0; intros;
                               [ subst; apply (sort_names_equal source_multilanguage_wf no_sort_eqns_in_sml wf_ctx_nil) in H4; inversion H4
                               | discriminate ] ]
                     | solve [ apply conj; intros; inversion H0; rewrite <- H7 in H1; inversion H1;
                               [ reflexivity
                               | pose proof source_multilanguage_wf; sort_cong ] ] ]
            | .. ]); 
    destruct H0.
Qed.

Lemma ty_inversion_lemma' : forall (t : sort) (e : term),
    Core.wf_sort source_multilanguage [] t -> Core.wf_term source_multilanguage [] e t -> t = {{s #"ty" }} -> e = {{e #"*" }}  \/ e = {{e #"bool" }} \/ (exists a b, Core.wf_term source_multilanguage [] a {{s #"ty" }} /\ Core.wf_term source_multilanguage [] b {{s #"ty" }} /\ e = {{e #"->" {a} {b} }} ).
Proof.
  induction 2 using wf_term_cut_ind.
  - unshelve (repeat (destruct H0;
                      [> first [ solve [ injection H0; intros HF; inversion HF ]
                               | solve [ inversion H0; intros Ht; inversion Ht ]
                               | shelve ] | .. ]); destruct H0).
    + inversion H0; intros Ht; rewrite <- H5 in H1; repeat invert_wf_args. eauto. 
    + inversion H0; intros Ht; rewrite <- H5 in H1; repeat invert_wf_args. eauto. 
    + inversion H0; intros Ht; rewrite <- H5 in H1; repeat invert_wf_args. 
      rewrite <- H5 in H2; subst; destruct H2; repeat destruct H1.
      right. right. eauto. 
  - inversion H0.
  - intros Ht; rewrite Ht in H1.
    apply IHwf_term. 
    + rewrite <- Ht in H1. apply eq_sort_sym in H1. apply ty_eq_sort_lemma in Ht;
        [ eapply (eq_sort_wf_r source_multilanguage_wf wf_ctx_nil); apply H1 | apply H ]. 
    + apply ty_eq_sort_lemma;
        [ eapply (eq_sort_wf_l source_multilanguage_wf wf_ctx_nil); apply H1 | apply H1 ]. 
Qed.

Lemma ty_inversion_lemma : forall (e : term),
    Core.wf_term source_multilanguage [] e {{s #"ty" }} -> e = {{e #"*" }}  \/ e = {{e #"bool" }} \/ (exists a b, Core.wf_term source_multilanguage [] a {{s #"ty" }} /\ Core.wf_term source_multilanguage [] b {{s #"ty" }} /\ e = {{e #"->" {a} {b} }} ).
Proof.
  intros. eapply ty_inversion_lemma'.
  - assert (Core.wf_sort source_multilanguage {{c }} {{s #"ty" }});
      [ pose proof source_multilanguage_wf; compute_sort_wf | apply H0 ]. 
  - apply H.
  - reflexivity.
Qed.

Lemma compiled_types_are_simple :
  forall (t : sort) (e : term),
    Core.wf_term source_multilanguage [] e t -> t = {{s #"ty" }} ->
    is_simple_type (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e).
Proof.
  induction 1 using wf_term_cut_ind.
  - unshelve (repeat (destruct H;
                      [> first [ solve [ injection H; intros HF; inversion HF ]
                               | solve [ inversion H; intros Ht; inversion Ht ]
                               | shelve ] | .. ]); destruct H).
    + inversion H; intros Ht; rewrite <- H4 in H0; repeat invert_wf_args; vm_compute; apply I. 
    + inversion H; intros Ht; rewrite <- H4 in H0; repeat invert_wf_args; vm_compute; apply I. 
    + inversion H. intros Ht. rewrite <- H4 in H0. repeat invert_wf_args. subst. destruct H1;  repeat destruct H0. simpl in Ht.
      cbv [apply_subst] in H2; simpl in H2; cbv [apply_subst] in H1; simpl in H1.
      apply H1 in Ht.
      assert (Ht2 : {{s #"ty"}} = {{s #"ty"}}) by reflexivity. 
      apply H2 in Ht2. 
      simpl. apply conj; assumption.
  - inversion H.
  - intros Ht; rewrite Ht in H0. apply ty_eq_sort_lemma in H0.
    + apply IHwf_term in H0. apply H0.
    + eapply (eq_sort_wf_l source_multilanguage_wf wf_ctx_nil). apply H0.
Qed.

Ltac compute_match t :=
  let v := eval vm_compute in t in
    replace t with v by (vm_compute; reflexivity).

Theorem can_eliminate_typerec :
  forall (t: sort) (e : term),
    Core.wf_term source_multilanguage [] e t ->
    all_typerecs_simple (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e). 
Proof.
  induction 1 using wf_term_cut_ind.
  - unshelve (repeat (destruct H;
                      [> first [ solve [ injection H; intros HF; inversion HF ]
                               | injection H; intros H6 H5 H4 H3; rewrite <- H4 in H1; rewrite <- H4 in H0; cbn [compile]; compute_match (named_list_lookup_err (simple_multilang_compiler ++ interoperating_langs_compiler) name); rewrite <- H3; repeat invert_wf_args; subst; destruct H1; repeat destruct H0; cbn [map combine_r_padded] ]
                      | .. ]); destruct H).
    1-2: simpl in H14; apply ty_inversion_lemma in H14; try reflexivity;
    destruct H14 as [ HStar | [ HBool | HArrow ]];
        [ rewrite HStar; replace (compile (simple_multilang_compiler ++ interoperating_langs_compiler) {{e #"*"}}) with {{e #"*" #"ty_emp" }} by (vm_compute; reflexivity); cbn -[compile simple_multilang_compiler interoperating_langs_compiler]; repeat apply conj; apply I || assumption
        | rewrite HBool; replace (compile (simple_multilang_compiler ++ interoperating_langs_compiler) {{e #"bool"}}) with {{e #"bool" #"ty_emp" }} by (vm_compute; reflexivity); cbn -[compile simple_multilang_compiler interoperating_langs_compiler]; repeat apply conj; apply I || assumption
        | destruct HArrow as [ A [ B [ WfA [ WfB EAB ]]]]; cbn -[compile simple_multilang_compiler interoperating_langs_compiler]; apply compiled_types_are_simple in WfA; try reflexivity; apply compiled_types_are_simple in WfB; try reflexivity; repeat apply conj; try (apply I || assumption || rewrite EAB; apply conj; assumption) ].
    all: repeat apply conj; try assumption; apply I. Unshelve.
  - inversion H.
  - apply IHwf_term.
Qed.

Theorem partial_eval_preserves_equality :
  forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    Core.eq_term target_multilanguage [] t e (elim_typerec e).
Proof. Admitted.

Definition target_multilanguage_without_typerec :=
  prod_ty_subst ++ prod_parameterized ++ (* can we also get rid of these? idt we partially evaluate that away but I think we could *)
    polymorphic_interoperating_langs.

Lemma target_multilanguage_without_typerec_wf : wf_lang target_multilanguage_without_typerec.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_without_typerec_entry :=
  lang_entry target_multilanguage_without_typerec_wf.
#[export] Hint Resolve target_multilanguage_without_typerec_entry : wf_lang_db.

Theorem partial_eval_wf_in_no_typerec_lang : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    Core.wf_term
      target_multilanguage_without_typerec
      []
      (elim_typerec e)
      t.
Proof. Admitted.

