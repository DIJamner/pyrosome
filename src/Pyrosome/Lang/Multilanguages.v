Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
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

(* imports for compilers *)
(* copied from LinearCPS.v *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for `match # from high_level_multilanguage with` *)
(* CompilerDefs, for preserving_compiler_ext, is already imported. Prolly through something else. *)

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
                                usubst ++
                                exp_subst++value_subst) 
                boundaries_def boundaries)
        As boundaries_wf.
Proof. auto_elab. Qed.
#[local] Definition boundaries_entry :=
  lang_entry (elab_lang_implies_wf boundaries_wf).
#[export] Hint Resolve boundaries_entry : wf_lang_db.









(* NOTE: the following is abstracted from the definition of stlc_parameterized in PolyCompilers.v *)
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

Definition typed_bool_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
    (exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
    (hide_lang_implicits (typed_bool_parameterized ++
                            exp_param_substs ++
                            exp_ty_subst ++
                            val_param_substs ++
                            val_ty_subst ++
                            env_ty_subst ++
                            ty_subst_lang ++
                            exp_parameterized ++ val_parameterized ++ ty_env_lang
       )
       typed_bool_parameterized)).
Derive typed_bool_ty_subst
  SuchThat (elab_lang_ext (typed_bool_parameterized ++
                                exp_param_substs ++
                                exp_ty_subst ++
                                val_param_substs ++
                                val_ty_subst ++
                                env_ty_subst ++
                                ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              typed_bool_ty_subst_def typed_bool_ty_subst)
  As typed_bool_ty_subst_wf.
Proof. auto_elab. Qed. 
#[local] Definition typed_bool_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf typed_bool_ty_subst_wf).
#[export] Hint Resolve typed_bool_ty_subst_entry : wf_lang_db.

Definition stlc_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
    (exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
    (hide_lang_implicits (stlc_parameterized ++
                            exp_param_substs ++
                            exp_ty_subst ++
                            val_param_substs ++
                            val_ty_subst ++
                            env_ty_subst ++
                            ty_subst_lang ++
                            exp_parameterized ++ val_parameterized ++ ty_env_lang
       )
       stlc_parameterized)).
Derive stlc_ty_subst
  SuchThat (elab_lang_ext (stlc_parameterized ++
                             exp_param_substs ++
                             exp_ty_subst ++
                             val_param_substs ++
                             val_ty_subst ++
                             env_ty_subst ++
                             ty_subst_lang ++
                             exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              stlc_ty_subst_def stlc_ty_subst)
  As stlc_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition stlc_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf stlc_ty_subst_wf).
#[export] Hint Resolve stlc_ty_subst_entry : wf_lang_db.

Definition usubst_parameterized := parameterize_wrapper usubst. 

Lemma usubst_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      usubst_parameterized.
Proof. solve_parameterize_wrapper usubst. Qed.
#[local] Definition usubst_parameterized_entry :=
  lang_entry usubst_parameterized_wf.
#[export] Hint Resolve usubst_parameterized_entry : wf_lang_db.

Definition usubst_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
    (exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
    (hide_lang_implicits (usubst_parameterized ++
                            exp_param_substs ++
                            exp_ty_subst ++
                            val_param_substs ++
                            val_ty_subst ++
                            env_ty_subst ++
                            ty_subst_lang ++
                            exp_parameterized ++ val_parameterized ++ ty_env_lang
       )
       usubst_parameterized)).
Derive usubst_ty_subst
  SuchThat (elab_lang_ext (usubst_parameterized ++
                                exp_param_substs ++
                                exp_ty_subst ++
                                val_param_substs ++
                                val_ty_subst ++
                                env_ty_subst ++
                                ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              usubst_ty_subst_def usubst_ty_subst)
  As usubst_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition usubst_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf usubst_ty_subst_wf).
#[export] Hint Resolve usubst_ty_subst_entry : wf_lang_db.


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

Definition A_var := {{e #"ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" (#"ty_snoc" #"ty_id" "t1")) #"ty_hd") (#"->" (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {ty_ovar 0}) "sigma") (#"ty_subst" (#"ty_snoc" {ty_wkn_n 2} (#"->" {ty_ovar 1} {ty_ovar 0})) "sigma")) }}.

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
                  usubst_ty_subst ++
                  typed_bool_parameterized ++
                  stlc_parameterized ++
                  usubst_parameterized ++
                  poly ++ (* needed for #"All" *)
                  (* below are the things needed for polymorphic languages *)
                  exp_param_substs ++
                  exp_ty_subst ++
                  val_param_substs ++
                  val_ty_subst ++
                  env_ty_subst ++
                  ty_subst_lang ++
                  exp_parameterized ++ val_parameterized ++ ty_env_lang
              ) 
                type_casing_def type_casing)
        As type_casing_wf.
Proof. 
  auto_elab.
Qed. 
#[local] Definition type_casing_entry :=
  lang_entry (elab_lang_implies_wf type_casing_wf).
#[export] Hint Resolve type_casing_entry : wf_lang_db.

(* 
TODO:
- simple to poly compiler
  - convoy for simple to poly compiler
  - remaining langs parameterized (ultc_bool, mif, uif, boolhuh)
- poly to poly compiler
  - parameterize boundaries (* STARTED, not done *)
  - convoy for poly to poly compiler
*)


(* The actual multilanguages *)
(* QUESTION: if the target language has polymorphism, can we still define a shared fragment? *)
(* correct. need to redo this to basically just insert empty environment anywhere *)
(* with Dustin notation, so long as differing metavars are just implicit, then writing no rules will work. worst you will have to do is the A variable stuff *)

Definition utlc_parameterized := 
    let ps := (elab_param "D" (utlc ++ usubst ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps utlc.

Local Definition evp'_utlc : lang := 
    let ps := (elab_param "D" (utlc ++ usubst ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (usubst ++ exp_ret ++ exp_subst_base ++ value_subst).

Lemma utlc_parameterized_wf
  : wf_lang_ext ((usubst_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      utlc_parameterized.
Proof.
  replace (usubst_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_utlc.
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

Definition utlc_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
  ( usubst_ty_subst ++ (* add all dependencies with their ty_subst versions *)
    usubst_parameterized ++
    exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
  (hide_lang_implicits (
       utlc_parameterized ++
                          usubst_ty_subst ++
       usubst_parameterized ++
       exp_param_substs ++
       exp_ty_subst ++
       val_param_substs ++
       val_ty_subst ++
       env_ty_subst ++
       ty_subst_lang ++
       exp_parameterized ++ val_parameterized ++ ty_env_lang
     )
     utlc_parameterized)).
Derive utlc_ty_subst
  SuchThat (elab_lang_ext (
                utlc_parameterized ++
                  usubst_ty_subst ++
                  usubst_parameterized ++
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
    let ps := (elab_param "D" (untyped_bool ++ usubst ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps untyped_bool.

Local Definition evp'_untyped_bool : lang := 
    let ps := (elab_param "D" (untyped_bool ++ usubst ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (usubst ++ exp_ret ++ exp_subst_base ++ value_subst).

Lemma untyped_bool_parameterized_wf
  : wf_lang_ext ((usubst_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      untyped_bool_parameterized.
Proof. 
  replace (usubst_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_untyped_bool.
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


Definition untyped_bool_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
  ( usubst_ty_subst ++ (* add all dependencies with their ty_subst versions *)
    usubst_parameterized ++
    exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
  (hide_lang_implicits (
       untyped_bool_parameterized ++ (* I think I don't need ty_subst versions here because the operation here is sytnactic *)
                                  (* but you do need the actual language here (for this example, untyped_bool_parameterized *)
                                  usubst_ty_subst ++
         usubst_parameterized ++
       exp_param_substs ++
       exp_ty_subst ++
       val_param_substs ++
       val_ty_subst ++
       env_ty_subst ++
       ty_subst_lang ++
       exp_parameterized ++ val_parameterized ++ ty_env_lang
     )
     untyped_bool_parameterized)).
Derive untyped_bool_ty_subst
  SuchThat (elab_lang_ext (
                untyped_bool_parameterized ++
                  usubst_ty_subst ++
                  usubst_parameterized ++
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
    let ps := (elab_param "D" (boolhuh ++ untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps boolhuh.

Local Definition evp'_boolhuh : lang := 
    let ps := (elab_param "D" (boolhuh ++ untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst).

Lemma boolhuh_parameterized_wf
  : wf_lang_ext ((untyped_bool_parameterized ++ utlc_parameterized ++ usubst_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      boolhuh_parameterized.
Proof. 
  replace (untyped_bool_parameterized ++ utlc_parameterized ++ usubst_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_boolhuh.
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

Compute boolhuh_parameterized. 

(*


Definition boolhuh_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
  ( (* add all dependencies with their ty_subst versions *)
    untyped_bool_ty_subst ++
    untyped_bool_parameterized ++
    utlc_ty_subst ++
    utlc_parameterized ++
    usubst_ty_subst ++ 
    usubst_parameterized ++
    exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
  (hide_lang_implicits ( (* add previously depending parameterized languages (and the current one) *)
       boolhuh_parameterized ++
         untyped_bool_ty_subst ++
    untyped_bool_parameterized ++
    utlc_ty_subst ++
    utlc_parameterized ++
    usubst_ty_subst ++ 
    usubst_parameterized ++
    exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
       )
     boolhuh_parameterized)). (* change this line to the current parameterized langauge working on *)


(* Definition boolhuh_ty_subst_def : lang :=
  {[l
      [:= "D" : #"ty_env",
           "D'" : #"ty_env",
             "G" : #"env" "D",
               "d" : #"ty_sub" "D'" "D",
            "e" : #"exp" "D" "G" #"*"
            ----------------------------------------------- ("exp_ty_subst bool?")
            #"exp_ty_subst" "d" (#"bool?" "e") = #"bool?" (#"exp_ty_subst" "d" "e")
             : #"exp" "D'" (#"env_ty_subst" "d" "G") (#"ty_subst" "d" #"*")
        ]
  ]}. *)

Compute boolhuh_ty_subst_def. 

Derive boolhuh_ty_subst
  SuchThat (elab_lang_ext ( (* add all dependencies with their ty_subst versions and the current parameterized lang *)
                boolhuh_parameterized ++
                untyped_bool_ty_subst ++
                untyped_bool_parameterized ++
                utlc_ty_subst ++
                utlc_parameterized ++
                usubst_ty_subst ++ 
                usubst_parameterized ++
                exp_param_substs ++
                exp_ty_subst ++
                val_param_substs ++
                val_ty_subst ++
                env_ty_subst ++
                ty_subst_lang ++
                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              boolhuh_ty_subst_def boolhuh_ty_subst) (* remember to change this *)
  As boolhuh_ty_subst_wf. (* and remember to change this *)
Proof. 
auto_elab. Qed. 
#[export] Hint Resolve boolhuh_ty_subst_wf : elab_pfs. (* and remember to change this *)


*)














(* NOTE: utlc_bool does not need a ty_subst lang because there are no new syntactic constructs in utlc_bool *)
Definition utlc_bool_parameterized := 
    let ps := (elab_param "D" (utlc_bool ++ untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps utlc_bool.

Local Definition evp'_utlc_bool : lang := 
    let ps := (elab_param "D" (utlc_bool ++ untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst).

Lemma utlc_bool_parameterized_wf
  : wf_lang_ext ((untyped_bool_parameterized ++ utlc_parameterized ++ usubst_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      utlc_bool_parameterized.
Proof. 
  replace (untyped_bool_parameterized ++ utlc_parameterized ++ usubst_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_utlc_bool.
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



Definition simple_shared_fragment :=
  boolhuh ++ 
    utlc_bool ++ 
    utlc ++ 
    untyped_bool ++ 
    usubst ++ 
    typed_bool ++ 
    stlc ++ 
    exp_subst ++ 
    value_subst.

Definition polymorphic_shared_fragment :=
    boolhuh_parameterized ++  (* NOTE: MISSING BOOLHUH_TY_SUBST *)
      utlc_bool_parameterized ++
      utlc_ty_subst ++
    utlc_parameterized ++
    untyped_bool_ty_subst ++
    untyped_bool_parameterized ++
    usubst_ty_subst ++
    usubst_parameterized ++
    typed_bool_ty_subst ++
    typed_bool_parameterized ++
    stlc_ty_subst ++
    stlc_parameterized ++
    (* all polymorphic langs stuff *) 
    exp_param_substs ++
    exp_ty_subst ++
    val_param_substs ++
    val_ty_subst ++
    env_ty_subst ++
    ty_subst_lang ++
    exp_parameterized ++ val_parameterized ++ ty_env_lang.

Local Notation compiler := (compiler string).

Definition shared_fragment_compiler_def : compiler :=
  match # from simple_shared_fragment with
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
  end.

Derive shared_fragment_compiler 
        SuchThat (elab_preserving_compiler 
                    []
                    polymorphic_shared_fragment
                    shared_fragment_compiler_def
                    shared_fragment_compiler
                    simple_shared_fragment) 
        As shared_fragment_compiler_preserving. 
Proof.
  auto_elab_compiler.
Qed.
#[local] Definition shared_fragment_entry :=
  cmp_entry (elab_compiler_implies_preserving shared_fragment_compiler_preserving).
#[export] Hint Resolve shared_fragment_entry : preserving_db.

Definition source_multilanguage := 
            boundaries ++ uif ++ simple_shared_fragment.
Hint Unfold source_multilanguage : auto_elab. 

Definition mif_parameterized := 
    let ps := (elab_param "D" (mif ++ untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps mif.

Local Definition evp'_mif : lang := 
    let ps := (elab_param "D" (mif ++ untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (untyped_bool ++ utlc ++ usubst ++ exp_ret ++ exp_subst_base ++ value_subst).

Lemma mif_parameterized_wf
  : wf_lang_ext ((untyped_bool_parameterized ++ utlc_parameterized ++ usubst_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      mif_parameterized.
Proof. 
  replace (untyped_bool_parameterized ++ utlc_parameterized ++ usubst_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_mif.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | now prove_from_known_elabs..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition mif_parameterized_entry :=
  lang_entry mif_parameterized_wf.
#[export] Hint Resolve mif_parameterized_entry : wf_lang_db.


(*

Definition mif_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
  ( (* add all dependencies with their ty_subst versions *)
    untyped_bool_ty_subst ++
    untyped_bool_parameterized ++
    utlc_ty_subst ++
    utlc_parameterized ++
    usubst_ty_subst ++ 
    usubst_parameterized ++
    exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
  (hide_lang_implicits ( (* add previously depending parameterized languages (and the current one) *)
       mif_parameterized ++
         untyped_bool_ty_subst ++
    untyped_bool_parameterized ++
    utlc_ty_subst ++
    utlc_parameterized ++
    usubst_ty_subst ++ 
    usubst_parameterized ++
    exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
       )
     mif_parameterized)). (* change this line to the current parameterized langauge working on *)
Derive mif_ty_subst
  SuchThat (elab_lang_ext ( (* add all dependencies with their ty_subst versions and the current parameterized lang *)
                mif_parameterized ++
                untyped_bool_ty_subst ++
                untyped_bool_parameterized ++
                utlc_ty_subst ++
                utlc_parameterized ++
                usubst_ty_subst ++ 
                usubst_parameterized ++
                exp_param_substs ++
                exp_ty_subst ++
                val_param_substs ++
                val_ty_subst ++
                env_ty_subst ++
                ty_subst_lang ++
                exp_parameterized ++ val_parameterized ++ ty_env_lang
              )
              mif_ty_subst_def mif_ty_subst) (* remember to change this *)
  As mif_ty_subst_wf. (* and remember to change this *)
Proof. 
auto_elab. Qed. 
#[export] Hint Resolve mif_ty_subst_wf : elab_pfs. (* and remember to change this *)

*)

Definition prod_parameterized := parameterize_wrapper prod. 

Lemma prod_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      prod_parameterized.
Proof. solve_parameterize_wrapper prod. Qed. 
#[local] Definition prod_parameterized_entry :=
  lang_entry prod_parameterized_wf.
#[export] Hint Resolve prod_parameterized_entry : wf_lang_db.

Definition prod_ty_subst_def := Eval vm_compute in (eqn_rules
  type_subst_mode
    (exp_param_substs ++
     exp_ty_subst ++
     val_param_substs ++
     val_ty_subst ++
     env_ty_subst ++
     ty_subst_lang ++
     exp_parameterized ++ val_parameterized ++ ty_env_lang
    )
    (hide_lang_implicits (prod_parameterized ++
                            exp_param_substs ++
                            exp_ty_subst ++
                            val_param_substs ++
                            val_ty_subst ++
                            env_ty_subst ++
                            ty_subst_lang ++
                            exp_parameterized ++ val_parameterized ++ ty_env_lang
       )
       prod_parameterized)).
Derive prod_ty_subst
  SuchThat (elab_lang_ext (prod_parameterized ++
                                exp_param_substs ++
                                exp_ty_subst ++
                                val_param_substs ++
                                val_ty_subst ++
                                env_ty_subst ++
                                ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                )
              prod_ty_subst_def prod_ty_subst)
  As prod_ty_subst_wf.
Proof. auto_elab. Qed.
#[local] Definition prod_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf prod_ty_subst_wf).
#[export] Hint Resolve prod_ty_subst_entry : wf_lang_db.


Definition target_multilanguage :=
  prod_ty_subst ++
    prod_parameterized ++
    mif_parameterized ++ (* NOTE: MISSING MIF_TY_SUBST *)
    type_casing ++
    poly ++
    polymorphic_shared_fragment.
Hint Unfold target_multilanguage : auto_elab.

Axiom todo_2 : wf_lang target_multilanguage.

Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | 1 => {{e #"wkn"}}
  | S n' =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Definition ovar n :=
    {{e #"val_subst" {wkn_n n} #"hd" }}.  

Fixpoint vwkn_n n e :=
  match n with
  | 0 => e
  | S n' =>
    {{e #"val_subst" #"wkn" {vwkn_n n' e} }}
  end.

(*
Definition ttd_fun t1 (x : t1 -> dyn) t2 (y : t2 -> dyn) : (t1 -> t2) -> dyn :=
  fun input =>
    ufun z =>
    y (input (dtt t1 z))
.
Definition ttd t : t -> dyn :=
  match t with
  | dyn => fun x => x
  | bool => fun x =>  if x then utrue else ufalse
  | t1 -> t2 => fun t1 (x : t1 -> dyn) t2 (y : t2 -> dyn) => fun input => (* x is NOT _this_ dtt! which is why the type is flipped *)
    ufun z =>
      y (input (dtt t1 z))
  end.

Definition dtt t : dyn -> t :=
  match t with
  | dyn => fun x => x
  | bool => fun x =>  mif x then true else false
  | t1 -> t2 => fun t1 (x : dyn -> t1) t2 (y : dyn -> t2) => ufun input =>
    fun z =>
      y (input (ttd t1 z))
  end.

Definition boundaries t : (t -> dyn) * (dyn -> t) :=
  match t with
  | dyn => (fun x => x, fun x => x)
  | bool => (fun x =>  if x then utrue else ufalse, fun x =>  mif x then true else false)
  | t1 -> t2 => fun t1 (x : (t1 -> dyn) * (dyn -> t1)) t2 (y : (t2 -> dyn) * (dyn -> t2)) =>
                  (
                    fun input =>
    ufun z =>
      (fst y) (input ((snd x) z))
                    , (* above is ttd, below is dtt *)
                    ufun input =>
    fun z =>
      (snd y) (input ((fst x) z))
                    )
  end. (* in the first case, the first thing is first of y bc we want to get the same direction, and in the second one its second *)
(* then we reverse evertyihng in the other one *)
*)
(* so the way this is gonna work is that we're gonna have a typerec that has as its three cases the three things in the boundaries func *)

(*
 Ltac t' :=
  match goal with
  | [|- fresh _ _ ]=> compute_fresh
  | [|- sublist _ _ ]=> apply (use_sublistb); vm_compute; reflexivity
  | |- In _ _ => solve [solve_in | simpl; intuition fail]
  | |- Model.wf_term _ _ _ => cbn [Model.wf_term core_model]
  | |- wf_term ?l ?c ?e ?t =>
        let c' := eval vm_compute in c in
        let e' := eval vm_compute in e in
        let t' := eval vm_compute in t in
            change_no_check (wf_term l c' e' t');
    tryif first [has_evar c'| has_evar e' | has_evar t']
    then assumption || eapply wf_term_var || eapply wf_term_by'
    else compute_noconv_term_wf
  | [|-wf_args _ _ _ _] => simple apply wf_args_nil
                           || simple eapply wf_args_cons2
                           || simple eapply wf_args_cons
  | [|-wf_subst _ _ _] => constructor
  | |- wf_ctx (Model:= ?m) ?c =>
    let c' := eval vm_compute in c in
        change_no_check (wf_ctx (Model:= m) c');
    tryif has_evar c'
    then assumption || constructor
    else solve_wf_ctx
  | |- wf_sort ?l ?c ?t =>
        let c' := eval vm_compute in c in
        let t' := eval vm_compute in t in
        change_no_check (wf_sort l c' t'); eapply wf_sort_by
  | [|- wf_lang _] => solve[Tools.Resolution.prove_by_lang_db]
  (*Don't use vm_compute here*)
  | [|- _ = _] => compute; reflexivity
  end.
*)

Ltac derive_elab_term :=
  pose proof todo_2;
  unshelve (repeat t); t'. (* repeat t then unshelve; then on the unshelved do t'. *)

Derive bool_test
  in (elab_term target_multilanguage
                [("G", {{s #"env" #"ty_emp"}})]
         {{e #"lambda" #"bool" (#"ret" #"T") }}
         bool_test
         {{s #"exp" #"ty_emp" "G"
                (#"->" #"ty_emp" (#"bool" #"ty_emp") (#"bool" #"ty_emp"))
         }}
     ) as bool_test_wf.
Proof.
  pose proof todo_2.
  repeat t.
  1: solve_in.
  
  1: solve [ solve_in | simpl; intuition fail ]. 


Definition trec_star_case_unelab :=
  {{e
      #"pair"
      (#"ret" (#"lambda" #"*" (#"ret" #"hd")))
      (#"ret" (#"lambda" #"*" (#"ret" #"hd")))
  }}.
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
Proof.
  pose proof todo_2.
  repeat t. 
  unshelve (repeat t).
  Print Matches.t'. 
  all: try apply default.
  Print t'.
  1: solve_in. 
  1: solve [ solve_in | simpl; intuition fail ].
  Print t'. 
  18: t'. 
  
  all: try t'. 

  derive_elab_term. Qed.

Definition trec_bool_case_unelab :=
  {{e
      #"pair"
      (#"ret" (#"lambda" #"bool" (#"if" (#"ret" #"hd") (#"ret" #"uT") (#"ret" #"uF"))))
      (#"ret" (#"lambda" #"*" (#"mif" (#"ret" #"hd") (#"ret" #"T") (#"ret" #"F"))))
  }}. 
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
Proof. derive_elab_term. Qed.

Ltac quick_goal_match :=
  lazymatch goal with
  | |- elab_term _ _ (con ?s _) (con ?s _) _ =>
      idtac "can go further"
  | |- elab_term _ _ (con ?s _) (con ?s' _) _ =>
      fail "cannot go further"
  | |- _  => idtac "neither case"
  end.

(*
Definition trec_func_case'_unelab :=
  {{e
      #"pair"
         (#"ret"
            (#"lambda" (#"->" "t1" "t2")
               (#"ret"
                  (#"ulambda"
                     (#"app" (#".1" (#"ret" "v2")) (#"app" (#"ret" {ovar 1}) (#"app" (#".2" (#"ret" "v3")) (#"ret" {ovar 0}))))
                  )
               )
            )
         )
         (#"ret"
            (#"lambda" #"*"
               (#"ret"
                  (#"lambda" "t1"
                     (#"app" (#".2" (#"ret" "v2")) (#"uapp" (#"ret" {ovar 1}) (#"app" (#".1" (#"ret" "v3")) (#"ret" {ovar 0}))))
                  )
               )
            )
         )
  }}.

Definition two_var_env := {{e #"ty_ext" (#"ty_ext" #"ty_emp") }}.
Derive trec_func_case'_sort
  in (elab_sort target_multilanguage
        [
           ("G", {{s #"env" #"ty_emp"}});
           ("t1", {{s #"ty" (#"ty_ext" #"ty_emp") "G"}});
           ("t2", {{s #"ty" (#"ty_ext" (#"ty_ext" #"ty_emp")) "G"}});
           ("v2", {{s #"val" {two_var_env} "G"
                      (#"prod" {two_var_env}
                         (#"->" {two_var_env} "t2" (#"*" {two_var_env}))
                         (#"->" {two_var_env} (#"*" {two_var_env}) "t2")
                      )
           }});
           ("v3", {{s #"val" {two_var_env} "G"
                      (#"prod" {two_var_env}
                         (#"->" {two_var_env} "t1" (#"*" {two_var_env}))
                         (#"->" {two_var_env} (#"*" {two_var_env}) "t1")
                      )
           }})
         ]
        {{s #"exp" #"ty_emp" "G"
             (#"All" 
                (#"->" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
                   (#"All"
                      (#"->" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
                             (#"prod" (#"->" (#"->" {ty_ovar 1} {ty_ovar 0}) #"*") (#"->" #"*" (#"->" {ty_ovar 1} {ty_ovar 0})))
                      )
                   )
                )
             )
        }}
        trec_func_case'_sort
 
     )
    as trec_func_case_sort_wf.
Proof.
  pose proof todo_2.
  repeat t.
  all: t'.
  Abort. 


Derive trec_func_case'
  in ( elab_term target_multilanguage
         [
           ("G", {{s #"env" #"ty_emp"}});
           ("t1", {{s #"ty" (#"ty_ext" #"ty_emp") "G"}});
           ("t2", {{s #"ty" (#"ty_ext" (#"ty_ext" #"ty_emp")) "G"}});
           ("v2", {{s #"val" {two_var_env} "G"
                      (#"prod" {two_var_env}
                         (#"->" {two_var_env} "t2" (#"*" {two_var_env}))
                         (#"->" {two_var_env} (#"*" {two_var_env}) "t2")
                      )
           }});
           ("v3", {{s #"val" {two_var_env} "G"
                      (#"prod" {two_var_env}
                         (#"->" {two_var_env} "t1" (#"*" {two_var_env}))
                         (#"->" {two_var_env} (#"*" {two_var_env}) "t1")
                      )
           }})
         ]
         trec_func_case'_unelab
         trec_func_case'
         {{s #"exp" #"ty_emp" "G"
                             (#"prod" (#"->" (#"->" "t1" "t2") #"*") (#"->" #"*" (#"->" "t1" "t2")))
         }}
     ) as trec_func_case_wf.
Proof.
  pose proof todo_2.
  repeat t.
  Abort. 
*)




Derive trec_func_case_sort
  in (elab_sort target_multilanguage
        [("G", {{s #"env" #"ty_emp"}})]
        {{s #"exp" #"ty_emp" "G"
             (#"All" 
                (#"->" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
                   (#"All"
                      (#"->" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
                             (#"prod" (#"->" (#"->" {ty_ovar 1} {ty_ovar 0}) #"*") (#"->" #"*" (#"->" {ty_ovar 1} {ty_ovar 0})))
                      )
                   )
                )
             )
        }}
        trec_func_case_sort
     )
    as trec_func_case_sort_wf.
Proof. derive_elab_term. Qed.

Print trec_func_case_sort.

Definition trec_func_case_unelab :=
  {{e
      #"ret"
      (#"Lam"
         (#"ret"
            (#"lambda" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
               (#"ret"
                  (#"Lam"
                     (#"ret"
                        (#"lambda" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))

                           (#"pair"
         (#"ret"
            (#"lambda" (#"->" {ty_ovar 1} {ty_ovar 0})
               (#"ret"
                  (#"ulambda"
                     (#"app" (#".1" (#"ret" {ovar 2})) (#"app" (#"ret" {ovar 1}) (#"app" (#".2" (#"ret" {ovar 3})) (#"ret" {ovar 0}))))
                  )
               )
            )
         )
         (#"ret"
            (#"lambda" #"*"
               (#"ret"
                  (#"lambda" {ty_ovar 1}
                     (#"app" (#".2" (#"ret" {ovar 2})) (#"uapp" (#"ret" {ovar 1}) (#"app" (#".1" (#"ret" {ovar 3})) (#"ret" {ovar 0}))))
                  )
               )
            )
         )
      )
                        )
                     )
                  )
               )
            )
         )
      )
  }}.







Definition evar := {{e #"ty_emp" }}.
Definition evar2 := {{e "G" }}. 
Definition lhs := 
{{s #"exp" (#"ty_ext" (#"ty_ext" {evar})) (#"ext" (#"ty_ext" (#"ty_ext" {evar})) {
                                                    evar2} (#"prod" (#"ty_ext" (#"ty_ext" {evar})) (
                                                                  #"->" (
                                                                        #"ty_ext" (#"ty_ext" {evar})) (
                                                                        #"ty_subst" 
                                                                        (
                                                                        #"ty_ext" (#"ty_ext" {evar})) (
                                                                        #"ty_ext" 
                                                                        {evar}) (
                                                                        #"ty_wkn" 
                                                                        (#"ty_ext" {evar})) (
                                                                        #"ty_hd" 
                                                                        {evar})) (
                                                                        #"*" 
                                                                        (
                                                                        #"ty_ext" (#"ty_ext" {evar})))) (
                                                                  #"->" (
                                                                        #"ty_ext" (#"ty_ext" {evar})) (
                                                                        #"*" 
                                                                        (
                                                                        #"ty_ext" (#"ty_ext" {evar}))) (
                                                                        #"ty_subst" 
                                                                        (
                                                                        #"ty_ext" (#"ty_ext" {evar})) (
                                                                        #"ty_ext" 
                                                                        {evar}) (
                                                                        #"ty_wkn" 
                                                                        (#"ty_ext" {evar})) (
                                                                        #"ty_hd" 
                                                                        {evar}))))) (
             #"->" (#"ty_ext" (#"ty_ext" {evar})) (#"prod" (#"ty_ext" (#"ty_ext" {evar})) (
                                                           #"->" (#"ty_ext" (#"ty_ext" {evar})) (
                                                                 #"ty_hd" 
                                                                 (#"ty_ext" {evar})) (
                                                                 #"*" (#"ty_ext" (#"ty_ext" {evar})))) (
                                                           #"->" (#"ty_ext" (#"ty_ext" {evar})) (
                                                                 #"*" (#"ty_ext" (#"ty_ext" {evar}))) (
                                                                 #"ty_hd" 
                                                                 (#"ty_ext" {evar})))) (
                   #"prod" (#"ty_ext" (#"ty_ext" {evar})) (#"->" (#"ty_ext" (#"ty_ext" {evar})) (
                                                                 #"->" (#"ty_ext" (#"ty_ext" {evar})) (
                                                                       #"ty_subst" 
                                                                       (#"ty_ext" (#"ty_ext" {evar})) (
                                                                       #"ty_ext" 
                                                                       {evar}) (
                                                                       #"ty_wkn" 
                                                                       (#"ty_ext" {evar})) (
                                                                       #"ty_hd" 
                                                                       {evar})) (
                                                                       #"ty_hd" 
                                                                       (#"ty_ext" {evar}))) (
                                                                 #"*" (#"ty_ext" (#"ty_ext" {evar})))) (
                           #"->" (#"ty_ext" (#"ty_ext" {evar})) (#"*" (#"ty_ext" (#"ty_ext" {evar}))) (
                                 #"->" (#"ty_ext" (#"ty_ext" {evar})) (#"ty_subst" 
                                                                       (#"ty_ext" (#"ty_ext" {evar})) (
                                                                       #"ty_ext" 
                                                                       {evar}) (
                                                                       #"ty_wkn" 
                                                                       (#"ty_ext" {evar})) (
                                                                       #"ty_hd" 
                                                                       {evar})) (
                                     #"ty_hd" (#"ty_ext" {evar}))))))}}.

Definition rhs := {{s #"exp" (#"ty_ext" (#"ty_ext" #"ty_emp")) (#"env_ty_subst" (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                                #"ty_ext" 
                                                                #"ty_emp") (
                                                                #"ty_wkn" 
                                                                (#"ty_ext" #"ty_emp")) (
                                                                #"ext" (#"ty_ext" #"ty_emp") (
                                                                       #"env_ty_subst" 
                                                                       (#"ty_ext" #"ty_emp") #"ty_emp" (
                                                                       #"ty_wkn" 
                                                                       #"ty_emp") "G") (
                                                                       #"prod" 
                                                                       (#"ty_ext" #"ty_emp") (
                                                                       #"->" 
                                                                       (#"ty_ext" #"ty_emp") (
                                                                       #"ty_hd" 
                                                                       #"ty_emp") (
                                                                       #"*" 
                                                                       (#"ty_ext" #"ty_emp"))) (
                                                                       #"->" 
                                                                       (#"ty_ext" #"ty_emp") (
                                                                       #"*" 
                                                                       (#"ty_ext" #"ty_emp")) (
                                                                       #"ty_hd" 
                                                                       #"ty_emp"))))) (
             #"->" (#"ty_ext" (#"ty_ext" #"ty_emp")) (#"prod" (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                              #"->" (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                                    #"ty_hd" 
                                                                    (#"ty_ext" #"ty_emp")) (
                                                                    #"*" 
                                                                    (#"ty_ext" (#"ty_ext" #"ty_emp")))) (
                                                              #"->" (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                                    #"*" 
                                                                    (#"ty_ext" (#"ty_ext" #"ty_emp"))) (
                                                                    #"ty_hd" 
                                                                    (#"ty_ext" #"ty_emp")))) (
                   #"prod" (#"ty_ext" (#"ty_ext" #"ty_emp")) (#"->" (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                                    #"->" 
                                                                    (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                                    #"ty_subst" 
                                                                    (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                                    #"ty_ext" 
                                                                    #"ty_emp") (
                                                                    #"ty_wkn" 
                                                                    (#"ty_ext" #"ty_emp")) (
                                                                    #"ty_hd" 
                                                                    #"ty_emp")) (
                                                                    #"ty_hd" 
                                                                    (#"ty_ext" #"ty_emp"))) (
                                                                    #"*" 
                                                                    (#"ty_ext" (#"ty_ext" #"ty_emp")))) (
                           #"->" (#"ty_ext" (#"ty_ext" #"ty_emp")) (#"*" 
                                                                    (#"ty_ext" (#"ty_ext" #"ty_emp"))) (
                                 #"->" (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                       #"ty_subst" (#"ty_ext" (#"ty_ext" #"ty_emp")) (
                                                   #"ty_ext" #"ty_emp") (
                                                   #"ty_wkn" (#"ty_ext" #"ty_emp")) (
                                                   #"ty_hd" #"ty_emp")) (
                                     #"ty_hd" (#"ty_ext" #"ty_emp"))))))}}.

Check eq_sort.

Ltac hide_implicits_custom :=
  lazymatch goal with
  | |- Model.eq_sort ?l ?c ?s1 ?s2 =>
        let c' := eval compute in (hide_ctx_implicits l c) in
        let s1' := eval compute in (hide_sort_implicits l s1) in
        let s2' := eval compute in (hide_sort_implicits l s2) in
        change (Model.eq_sort l (!! as_ctx c') (!! s1') (!! s2'))
  end.


Theorem problem_case : eq_sort
                         target_multilanguage
                         {{c "G" : #"env" #"ty_emp" }}
                         lhs
                         rhs.
Proof.
  pose proof todo_2. 
  compute.
  
  sort_cong.
  1: by_reduction.
  2: by_reduction.
  (* there's one goal left, and it's a env_ty_subst on one side and an ext on the other side *)
  Abort. 
  





Derive trec_func_case
  in ( elab_term target_multilanguage
         [("G", {{s #"env" #"ty_emp"}})]
         trec_func_case_unelab
         trec_func_case
         trec_func_case_sort
     ) as trec_func_case_wf.
Proof.
  pose proof todo_2.
  repeat t.
  right.
  compute_eq_compilation.
  sort_cong.
  1: term_refl.
  1: compute_eq_compilation.
  1: reduce.
  1: term_cong.
  1: term_refl.
  1: reduce.
  1: term_refl.
  1: by_reduction.
  1: compute_eq_compilation.
  term_cong.
  1: term_refl.
  1: compute_eq_compilation.
  1: term_cong.
  1: term_refl.
  1: term_refl.
  1: term_refl.
  compute_eq_compilation.
  term_refl.
  Unshelve.
  all: t'.
Qed.



Definition trec_boundaries_unelab :=
  {{e
      #"typerec" "A" (#"prod" (#"->" {ty_ovar 0} #"*") (#"->" #"*" {ty_ovar 0}))
      {trec_star_case_unelab}
      {trec_bool_case_unelab}
      {trec_func_case_unelab}
  }}.

Derive trec_boundaries
         in ( elab_term target_multilanguage
                [("e", {{s #"exp" #"ty_emp" "G" "A"}}); ("A", {{s #"ty" #"ty_emp"}});

                 ("G", {{s #"env" #"ty_emp"}})]
                trec_boundaries_unelab
                trec_boundaries
                {{s #"exp" #"ty_emp" "G"
                    (#"prod" #"ty_emp"
                       (#"->" #"ty_emp" "A" (#"*" #"ty_emp"))
                       (#"->" #"ty_emp" (#"*" #"ty_emp") "A")
                    )
                }}
            ) as trec_boundaries_wf.
Proof.
Abort.
(* 
  derive_elab_term. 
  t.
  2: t. 2: t. 2: t.
  3: t. 3: t. 3: t.
  4: t. 4: t. 4: t.
  5: t. 5: t. 5: t.
  6: t. 6: t. 6: t.
  7: t. 7: t. 7: t.
  8: t. 8: t. 8: t.
  9: t. 9: t. 9: t.
  10: t. 10: t. 10: t.
  11: t. 11: t. 11: t.
  12: t. 12: t. 12: t.
  13: t. 13: t. 13: t.
  14: t. 14: t. 14: t.
  15: t. 15: t. 15: t.
  16: t. 16: t. 16: t.
  17: t. 17: t. 17: t.
  18: t.

  Compute target_multilanguage. 
  18: t. 18: t.
  19: t. 19: t. 19: t.
  20: t. 20: t. 20: t.
  21: t. 21: t. 21: t.
  22: t. 22: t. 22: t.
  23: t. 23: t. 23: t.
  24: t. 24: t. 24: t.
  25: t. 25: t. 25: t.
  26: t. 26: t. 26: t.
  27: t. 27: t. 27: t.
  28: t. 28: t. 28: t.
  29: t. 29: t. 29: t.

  repeat Matches.t.
  Qed. 
  Matches.t. 1: Matches.t. 2: shelve. t. 1: repeat t. 2: t. 2: repeat t. 3: repeat t.
  all: cycle 1. 1: t.
  Compute prod_parameterized. 
  1: solve_in.
  1: t. 1: repeat t. 2: repeat t. 
  all: try (left; reflexivity).
 *)  


(*
(* simple to poly compiler *)
Definition multilang_compiler_def : compiler :=
    match # from (boundaries ++ uif) with
    | {{e #"uif" "G" "c" "thn" "els"}} => {{e @"mif" @("D" := #"ty_emp") "c" "thn" "els" }}
    | {{e #"dtt" "G" "A" "e"}} => {{e #"app" (#".2" {trec_boundaries {{e "A"}}}) "e" }}
    | {{e #"ttd" "G" "A" "e"}} => {{e #"app" (#".1" {trec_boundaries {{e "A"}}}) "e" }}
    (* order of implicit vars is order of context vars *)
    end.

Derive multilang_compiler 
        SuchThat (elab_preserving_compiler 
                    shared_fragment_compiler
                    target_multilanguage
                    multilang_compiler_def
                    multilang_compiler
                    (boundaries ++ uif)
                    ) 
        As multilang_compiler_preserving. 
Proof.
  assert (wf_lang target_multilanguage) by apply todo_2.
  setup_elab_compiler.
  { repeat Matches.t.  }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { Compute (compile_ctx (nth_tail 2 multilang_compiler ++ shared_fragment_compiler)
               {{c "G" : #"env", "A" : #"ty", "e" : #"exp" "G" "A"}}).
    Compute (compile_sort (nth_tail 2 multilang_compiler ++ shared_fragment_compiler)
       {{s #"exp" "G" #"*"}}).



      repeat Matches.t. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  { by_reduction. }
  3: { compute_eq_compilation. by_reduction.  }.
   repeat
    ([>repeat Matches.t; cleanup_elab_after
        try (try decompose_sort_eq; (solve [ by_reduction ]))
     | .. ])


  Print auto_elab_compiler. 
  auto_elab_compiler.
  Check eq_term.
  Print boundaries. 
  setup_elab_compiler.
   repeat
    ([>repeat Matches.t; cleanup_elab_after
        try (try decompose_sort_eq; (solve [ by_reduction ]))
     | .. ])


(* in case needed, defined in Tools.Matches, Elab.ElabCompilers *)
(* semantic properties are in SemanticsPreservingDefs.v *)

(* Locate elab_preserving_compiler. 
Locate auto_elab_compiler.  *)

Derive multilang_compiler 
        SuchThat (elab_preserving_compiler 
                    shared_fragment_compiler
                    target_multilanguage
                    multilang_compiler_def
                    multilang_compiler
                    (boundaries ++ uif)
                    ) 
        As multilang_compiler_preserving. 
Proof. 
Abort. 








Local Notation preserving_compiler_ext tgt cmp_pre cmp src := (* copied from Paramaterizer, 2523 *)
(preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).

Definition polymorphic_shared_fragment_compiler := id_compiler polymorphic_shared_fragment. 

Lemma polymorphic_shared_fragment_identity_compiler_preserving : preserving_compiler_ext polymorphic_shared_fragment [] polymorphic_shared_fragment_compiler polymorphic_shared_fragment.
Proof. Abort.
(*
    (* OLD TACTICS (for some reason this doesn't work now?) *)
    unfold polymorphic_shared_fragment. 
    apply id_compiler_preserving; prove_from_known_elabs. 
    typeclasses eauto.
Qed.
Hint Resolve polymorphic_shared_fragment_identity_compiler_preserving : auto_elab.
*)

Definition boundaries_parameterized_def : lang :=
  {[l
    [:| "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D", (* 'source' type *)
        "e" : #"exp" "D" "G" "A"
        -----------------------------------------------
        #"ttd" "A" "e" : #"exp" "D" "G" #"*"
    ];
    [:| "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D", (* 'target' type *)
        "e" : #"exp" "D" "G" "A"
        -----------------------------------------------
        #"dtt" "A" "e" : #"exp" "D" "G" "A"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "e" : #"exp" "D" "G" #"*"
        ----------------------------------------------- ("dtt star")
        #"dtt" #"*" "e" = "e" : #"exp" "D" "G" #"*"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "e" : #"exp" "D" "G" #"*"
        ----------------------------------------------- ("ttd star")
        #"ttd" #"*" "e" = "e" : #"exp" "D" "G" #"*"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D"
        ----------------------------------------------- ("dtt True")
        #"dtt" #"bool" (#"ret" #"uT") = #"ret" #"T" : #"exp" "D" "G" #"bool"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D"
        ----------------------------------------------- ("dtt False")
        #"dtt" #"bool" (#"ret" #"uF") = #"ret" #"F" : #"exp" "D" "G" #"bool"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D"
        ----------------------------------------------- ("ttd True")
        #"ttd" #"bool" (#"ret" #"T") = #"ret" #"uT" : #"exp" "D" "G" #"*"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D"
        ----------------------------------------------- ("ttd False")
        #"ttd" #"bool" (#"ret" #"F") = #"ret" #"uF" : #"exp" "D" "G" #"*"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D",
        "B" : #"ty" "D",
        "v" : #"val" "D" "G" #"*"
        ----------------------------------------------- ("dtt func") (* NOTE: NOT DONE *)
        #"dtt" (#"->" "A" "B") (#"ret" "v") =
        #"ret" (#"lambda" "A" (#"dtt" "B" (#"uapp" (#"ret" (#"val_subst" #"wkn" "v")) (#"ttd" "A" (#"ret" #"hd"))))) :
        #"exp" "G" (#"->" "A" "B")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D",
        "B" : #"ty" "D",
        "v" : #"val" "D" "G" (#"->" "A" "B")
        ----------------------------------------------- ("ttd func") (* NOTE: NOT DONE *)
        #"ttd" (#"->" "A" "B") (#"ret" "v") =
        #"ret" (#"ulambda" (#"ttd" "B" (#"app" (#"ret" (#"val_subst" #"wkn" "v")) (#"dtt" "A" (#"ret" #"hd"))))) :
        #"exp" "G" #"*"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "e" : #"exp" "D" (#"ext" "G" #"*") #"*"
        ----------------------------------------------- ("dtt ulambda mismatch")
        #"dtt" #"bool" (#"ret" (#"ulambda" "e")) =
        #"Error" #"bool" : #"exp" "D" "G" #"bool"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D",
        "B" : #"ty" "D"
        ----------------------------------------------- ("dtt uT mismatch")
        #"dtt" (#"->" "A" "B") (#"ret" #"uT") =
        #"Error" (#"->" "A" "B") : #"exp" "D" "G" (#"->" "A" "B")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D",
        "B" : #"ty" "D"
        ----------------------------------------------- ("dtt uF mismatch")
        #"dtt" (#"->" "A" "B") (#"ret" #"uF") =
        #"Error" (#"->" "A" "B") : #"exp" "D" "G" (#"->" "A" "B")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D",
        "e" : #"exp" "D" "G" "A",
        "G'" : #"env" "D" "G",
        "g" : #"sub" "D" "G" "G'"
        ----------------------------------------------- ("exp_subst dtt")
        #"exp_subst" "g" (#"dtt" "A" "e") = 
        #"dtt" "A" (#"exp_subst" "g" "e"): #"exp" "G" "A"
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" "D",
        "e" : #"exp" "D" "G" "A",
        "G'" : #"env" "D" "G",
        "g" : #"sub" "D" "G" "G'"
        ----------------------------------------------- ("exp_subst ttd")
        #"exp_subst" "g" (#"ttd" "A" "e") = 
        #"ttd" "A" (#"exp_subst" "g" "e") : #"exp" "G" "A"
    ];
    [:= "D" : #"ty_env",
        "D'" : #"ty_env",
        "G" : #"env" "D",
        "g" : #"ty_sub" "D" "D'",
        "A" : #"ty" "D",
        "e" : #"exp" "D" "G" "A"
        ----------------------------------------------- ("ty_subst dtt")
        #"exp_ty_subst" "g" (#"dtt" "A" "e")
        = #"dtt" (#"ty_subst" "g" "A") (#"exp_ty_subst" "g" "e") : #"exp" "G" "A"
    ];
    [:= "D" : #"ty_env",
        "D'" : #"ty_env",
        "G" : #"env" "D",
        "g" : #"ty_sub" "D" "D'",
        "A" : #"ty" "D",
        "e" : #"exp" "D" "G" "A"
        ----------------------------------------------- ("ty_subst ttd")
        #"exp_ty_subst" "g" (#"ttd" "A" "e")
        = #"ttd" (#"ty_subst" "g" "A") (#"exp_ty_subst" "g" "e") : #"exp" "G" "A"
    ]
  ]}.
Derive boundaries_parameterized  (* need polymorphic versions of all these *)
        SuchThat (elab_lang_ext (utlc ++
                                untyped_bool ++
                                stlc ++ 
                                typed_bool ++ 
                                usubst ++
                                exp_subst++value_subst) 
                boundaries_parameterized_def boundaries_parameterized)
        As boundaries_parameterized_wf.
Proof. Abort. 
(* #[export] Hint Resolve boundaries_parameterized_wf : elab_pfs. *)











(* proof mirrors language proof *)
(* Derive h2l
       SuchThat (elab_preserving_compiler [] (* compiler root: for base language *)
                                          low_level_multilanguage (* target language—ALL of it *)
                                          h2l_def
                                          h2l
                                          high_level_multilanguage) (* source  *) 
                                          (* ideally, only boundaries ++ uif *)
       As h2l_preserving.
Proof. unfold low_level_multilanguage. unfold high_level_multilanguage. 
        unfold shared_fragment. 
        auto_elab_compiler. 
        lazymatch goal with 
        | |- ?G => idtac G
        end. 
Admitted. 
#[export] Hint Resolve h2l_preserving : elab_pfs. *)

(* accompanying story: boundaries aren't really necessary to do multilanguages
because they can be expressed in terms of more primitive features, but we can do mif *)

(* story: we have the uif, and then we can just compile to mif *)

(* so make new language with these below in the object language. That's gonna be the boundary language *)
(* equations will look a lot like matthews and findler eqns. Start with lump embedding stuff *)
(* lump embedding is 12:5, says like boundaries cancel *)
(* only rule for expression boundary is boundary_e ret is same as ret boundary_v *)
(* for value boundary, say that cancel if types are the same *)
(* what to do with not matched boundary? raise error (see paper notes) *)

(* compiler will be type case—doing a case on the type—looks similar to the below but in the object language *)

(* high level multilanguage which has boundaries—has set of eqns that fully describe the boundaries *)
(* low level multilanguage which has type cases—this is the one with mif *)

(* 
(* everytyhig will be v boudnaries (evantuaully) *)
Definition dtt_e {G : term} (x : term) (Ty : term) : Ty :=
  match Ty with
  | {{e #"*"}} => x (* this is how you put pyrosome things in gallina *)
  | {{e #"bool"}} => match x with
                     | {{e #"ret" {v} }} => {{e #"ret" {dtt_v v Ty} }} (* THATS IT FOR e boundreis *)
                     | _ => {{e #"if" {dtt_e x Ty} #"ret" #"T" #"ret" #"F" }}
                     end
  (* OL if/else, with x as condition *)
  | {{e #"->" {A} {B} }} => {{e #"ret" #"lambda" {A} {dtt_e {{e #"uapp" (#"val_subst" #"wkn" {x}) {ttd_e {{e #"hd"}} A} }} B} }}
  (* {#"lambda" A (dyn_to_typed (#"app" (#"val_subst" #"wkn" x) (typed_to_dyn #"hd" A)) B)} *)
  end. 


Definition ttd_e {G : term} (x : term) (T : term) : T :=
  match T with
  | {{e #"*"}} => x
  | {{e #"bool"}} => match x with
                     | {{e #"ret" {v} }} => {{e #"ret" {ttd_v v Ty} }}
                     | _ => {{e #"uif" {ttd_e x Ty} #"ret" #"uT" #"ret" #"uF" }}
                     end
  | {{e #"->" {A} {B} }} => {{e #"ret" #"ulambda" {ttd_e {{e #"app" (#"val_subst" #"wkn" {x}) {dtt_e {{e #"hd"}} A} }} B} }}
  end. 

Definition dtt_v {G : term} (x : term) (Ty : term) : Ty :=
  match Ty with
  | {{e #"*"}} => x
  | {{e #"bool"}} => match x with
                            (* these go in the high level multilanguage. mismatches will all be errors *)
                            (* error will be in high level multilanguage and low level multilanguage *)
                     | {{e #"uT"}} => {{e #"T"}}
                     | {{e #"uF"}} => {{e #"F"}}
                     | _           => {{e #"F"}}
                     end
  | {{e #"->" {A} {B} }} => {{e #"lambda" {A} {dtt_e {{e #"uapp" (#"val_subst" #"wkn" #"ret" {x}) {ttd_e {{e #"hd"}} A} }} B} }}
  end. 

Definition ttd_v {G : term} (x : term) (Ty : term) : Ty :=
  match Ty with
  | {{e #"*"}} => x
  | {{e #"bool"}} => match x with
                     | {{e #"T"}} => {{e #"uT"}}
                     | {{e #"F"}} => {{e #"uF"}}
                     | _          => {{e #"uF"}}
                     end
  | {{e #"->" {A} {B} }} => {{e #"ulambda" {ttd_e {{e #"app" (#"val_subst" #"wkn" #"ret" {x}) {dtt_e {{e #"hd"}} A} }} B} }}
  end.  *)

 *)
