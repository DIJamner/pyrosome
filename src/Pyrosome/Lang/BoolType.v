Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for `match # from high_level_multilanguage with` *)

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

Require Coq.derive.Derive.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst SimpleVSTLC.
From Pyrosome.Lang Require Import UTLC. 

From Pyrosome.Compilers Require Import Parameterizer. (* for id_compiler *)


Definition typed_bool_def : lang :=
  {[l/subst [exp_subst++value_subst] (* for subst rule generation *)
  [:| 
      -----------------------------------------------
      #"bool" : #"ty"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"T" : #"val" "G" #"bool"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"F" : #"val" "G" #"bool"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "cond" : #"exp" "G" #"bool",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      -----------------------------------------------
      #"if" "cond" "e2" "e3" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      ----------------------------------------------- ("if-true")
      #"if" (#"ret" #"T") "e2" "e3" 
      = "e2" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      ----------------------------------------------- ("if-false")
      #"if" (#"ret" #"F") "e2" "e3" 
      = "e3" : #"exp" "G" "A"
  ]
  ]}.

Derive typed_bool
       SuchThat (elab_lang_ext (exp_subst++value_subst) typed_bool_def typed_bool)
       As typed_bool_wf.
Proof. auto_elab. Qed.
#[local] Definition typed_bool_entry :=
  lang_entry (elab_lang_implies_wf typed_bool_wf).
#[export] Hint Resolve typed_bool_entry : wf_lang_db.

Definition untyped_bool_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env"
      -----------------------------------------------
      #"uT" : #"val" "G" #"*"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"uF" : #"val" "G" #"*"
  ]
  ]}.

Derive untyped_bool
       SuchThat (elab_lang_ext (star_type ++ exp_subst++value_subst) untyped_bool_def untyped_bool)
       As untyped_bool_wf.
Proof. auto_elab. Qed. 
#[local] Definition untyped_bool_entry :=
  lang_entry (elab_lang_implies_wf untyped_bool_wf).
#[export] Hint Resolve untyped_bool_entry : wf_lang_db.


(* Compute value_subst_def. 
Locate term.  *)
Definition boolhuh_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env",
      "e" : #"exp" "G" #"*"
      -----------------------------------------------
      #"bool?" "e" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env"
      ----------------------------------------------- ("bool?-true")
      #"bool?" (#"ret" #"uT") 
      = #"ret" #"uT" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env"
      ----------------------------------------------- ("bool?-false")
      #"bool?" (#"ret" #"uF") 
      = #"ret" #"uT" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*"
      ----------------------------------------------- ("bool?-func")
      #"bool?" (#"ret" (#"ulambda" "e")) 
      = #"ret" #"uF" : #"exp" "G" #"*"
  ]
  ]}.

Derive boolhuh
       SuchThat (elab_lang_ext (utlc ++ untyped_bool ++ star_type ++ exp_subst++value_subst) boolhuh_def boolhuh)
       As boolhuh_wf.
Proof. auto_elab. Qed.
#[local] Definition boolhuh_entry :=
  lang_entry (elab_lang_implies_wf boolhuh_wf).
#[export] Hint Resolve boolhuh_entry : wf_lang_db.


Definition utlc_bool_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:= "G" : #"env",
      "e" : #"exp" "G" #"*"
      ----------------------------------------------- ("uT uapp")
      #"uapp" (#"ret" #"uT") "e" =
      #"Error" #"*" : #"exp" "G" #"*"
  ];
  (* for eventually contexts, Estlc_def in SimpleEvalCtx.v *)
  [:= "G" : #"env",
      "e" : #"exp" "G" #"*"
      ----------------------------------------------- ("uF uapp")
      #"uapp" (#"ret" #"uF") "e" =
      #"Error" #"*" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env"
      ----------------------------------------------- ("uT ulambda")
      #"ret" (#"ulambda" (#"ret" #"uT")) = 
      #"Error" #"*" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env"
      ----------------------------------------------- ("uF ulambda")
      #"ret" (#"ulambda" (#"ret" #"uF")) =
      #"Error" #"*" : #"exp" "G" #"*"
  ]
  ]}.

Derive utlc_bool
       SuchThat (elab_lang_ext (utlc ++ untyped_bool ++ error_t ++ star_type ++ exp_subst++value_subst) utlc_bool_def utlc_bool)
       As utlc_bool_wf.
Proof. auto_elab. Qed.
#[local] Definition utlc_bool_entry :=
  lang_entry (elab_lang_implies_wf utlc_bool_wf).
#[export] Hint Resolve utlc_bool_entry : wf_lang_db.


Definition uif_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env", 
      "e1" : #"exp" "G" #"*",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      -----------------------------------------------
      #"uif" "e1" "e2" "e3" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      ----------------------------------------------- ("uif true")
      #"uif" (#"ret" #"uT") "e2" "e3" 
      = "e2" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      ----------------------------------------------- ("uif false")
      #"uif" (#"ret" #"uF") "e2" "e3" 
      = "e3" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      ----------------------------------------------- ("uif func")
      #"uif" (#"ret" (#"ulambda" "e")) "e2" "e3" 
      = #"Error" #"*" : #"exp" "G" #"*" 
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      ----------------------------------------------- ("uif Error")
      #"uif" (#"Error" #"*") "e2" "e3"
      = #"Error" #"*" : #"exp" "G" #"*" 
  ]
  ]}.

Derive uif
       SuchThat (elab_lang_ext (utlc ++ untyped_bool ++ error_t ++ star_type ++exp_subst++value_subst) uif_def uif)
       As uif_wf. (* leftmost is newest *)
Proof. auto_elab. Qed.
#[local] Definition uif_entry :=
  lang_entry (elab_lang_implies_wf uif_wf).
#[export] Hint Resolve uif_entry : wf_lang_db.

Definition mif_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env", 
      "A" : #"ty",
      "e1" : #"exp" "G" #"*",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      -----------------------------------------------
      #"mif" "e1" "e2" "e3" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      ----------------------------------------------- ("mif true")
      #"mif" (#"ret" #"uT") "e2" "e3" 
      = "e2" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      ----------------------------------------------- ("mif false")
      #"mif" (#"ret" #"uF") "e2" "e3" 
      = "e3" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      ----------------------------------------------- ("mif func")
      #"mif" (#"ret" (#"ulambda" "e")) "e2" "e3" 
      = #"Error" "A" : #"exp" "G" "A" 
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      ----------------------------------------------- ("mif Error")
      #"mif" (#"Error" #"*") "e2" "e3"
      = #"Error" "A" : #"exp" "G" "A" 
  ]
  ]}.
Derive mif
       SuchThat (elab_lang_ext (utlc ++ untyped_bool ++ error_t ++ star_type ++exp_subst++value_subst) mif_def mif)
       As mif_wf.
Proof. auto_elab. Qed.
#[local] Definition mif_entry :=
  lang_entry (elab_lang_implies_wf mif_wf).
#[export] Hint Resolve mif_entry : wf_lang_db.

Definition dyn_lang_no_conditional := boolhuh ++ utlc_bool ++ untyped_bool ++ utlc ++ error_t ++ star_type ++ exp_subst ++ value_subst.
Hint Unfold dyn_lang_no_conditional : auto_elab.

(* NOTE: commenting out to see if it's ever necessary *)
(* Lemma dyn_lang_no_conditional_wf : wf_lang dyn_lang_no_conditional.
Proof. prove_by_lang_db. Qed.
#[local] Definition dyn_lang_no_conditional_entry :=
  lang_entry dyn_lang_no_conditional_wf.
#[export] Hint Resolve dyn_lang_no_conditional_entry : wf_lang_db. *)

Local Notation compiler := (compiler string).

Local Notation preserving_compiler_ext tgt cmp_pre cmp src := (* copied from Paramaterizer, 2523 *)
(preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).

Definition dynamic_id_compiler := id_compiler dyn_lang_no_conditional.

Lemma dyn_lang_no_conditional_id_compiler_preserving : preserving_compiler_ext dyn_lang_no_conditional [] dynamic_id_compiler dyn_lang_no_conditional.
Proof.
  apply id_compiler_preserving. 2: prove_by_lang_db. typeclasses eauto.
Qed.
#[local] Definition dyn_lang_no_conditional_id_compiler_entry :=
  cmp_entry dyn_lang_no_conditional_id_compiler_preserving.
#[export] Hint Resolve dyn_lang_no_conditional_id_compiler_entry : preserving_db.

Definition simple_dynamic_lang_uif := uif ++ utlc_bool ++ boolhuh ++ untyped_bool ++ utlc ++ error_t ++ star_type ++ exp_subst ++ value_subst. 

Definition simple_dynamic_lang_mif := mif ++ utlc_bool ++ boolhuh ++ untyped_bool ++ utlc ++ error_t ++ star_type ++ exp_subst ++ value_subst.


Definition uif_to_mif_compiler_def : compiler :=
    match # from uif with
    | {{e #"uif" "G" "c" "thn" "els"}} => {{e #"mif" "c" "thn" "els" }}
    end.
Derive uif_to_mif_compiler 
        SuchThat (elab_preserving_compiler 
                    dynamic_id_compiler
                    simple_dynamic_lang_mif
                    uif_to_mif_compiler_def
                    uif_to_mif_compiler
                    uif
                    ) 
        As uif_to_mif_compiler_preserving. 
Proof. auto_elab_compiler. Qed.
#[local] Definition uif_to_mif_compiler_entry :=
  cmp_entry (elab_compiler_implies_preserving uif_to_mif_compiler_preserving).
#[export] Hint Resolve uif_to_mif_compiler_entry : preserving_db.

(* Now, we don't need to have uif at all in the Multilanguages.v file! *)
