Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
Import Core.Notations.

From Stdlib Require derive.Derive.

Definition usubst_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| 
      -----------------------------------------------
      #"*" : #"ty"
  ];
  [:| "G" : #"env",
      "t" : #"ty"
      -----------------------------------------------
      #"Error" "t" : #"exp" "G" "t"
  ]
  ]}.

Derive usubst
       in (elab_lang_ext (exp_subst++value_subst) usubst_def usubst)
       as usubst_wf.
Proof. auto_elab. Qed.
#[local] Definition usubst_entry :=
  lang_entry (elab_lang_implies_wf usubst_wf).
#[export] Hint Resolve usubst_entry : wf_lang_db.

Definition utlc_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*"
      -----------------------------------------------
      #"ulambda" "e" : #"val" "G" (#"*")
  ];
  [:| "G" : #"env",
      "e" : #"exp" "G" #"*", 
      "e'" : #"exp" "G" #"*"
      -----------------------------------------------
      #"uapp" "e" "e'" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "v" : #"val" "G" #"*"
      ----------------------------------------------- ("UTLC-beta")
      #"uapp" (#"ret" (#"ulambda" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" "G" #"*"
  ]
  ]}.

Derive utlc
       in (elab_lang_ext (usubst++exp_subst++value_subst) utlc_def utlc)
       as utlc_wf.
Proof. auto_elab. Qed.
#[local] Definition utlc_entry :=
  lang_entry (elab_lang_implies_wf utlc_wf).
#[export] Hint Resolve utlc_entry : wf_lang_db.
