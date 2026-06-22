Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition star_type_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| 
      -----------------------------------------------
      #"*" : #"ty"
  ]
  ]}.
Derive star_type
       SuchThat (elab_lang_ext (exp_subst++value_subst) star_type_def star_type)
       As star_type_wf.
Proof. auto_elab. Qed.
#[local] Definition star_type_entry :=
  lang_entry (elab_lang_implies_wf star_type_wf).
#[export] Hint Resolve star_type_entry : wf_lang_db.

Definition error_t_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| "G" : #"env",
      "t" : #"ty"
      -----------------------------------------------
      #"Error" "t" : #"exp" "G" "t"
  ]
  ]}.
Derive error_t
       SuchThat (elab_lang_ext (exp_subst++value_subst) error_t_def error_t)
       As error_t_wf.
Proof. auto_elab. Qed.
#[local] Definition error_t_entry :=
  lang_entry (elab_lang_implies_wf error_t_wf).
#[export] Hint Resolve error_t_entry : wf_lang_db.

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
       SuchThat (elab_lang_ext (star_type ++ exp_subst ++ value_subst) utlc_def utlc)
       As utlc_wf.
Proof. auto_elab. Qed.
#[local] Definition utlc_entry :=
  lang_entry (elab_lang_implies_wf utlc_wf).
#[export] Hint Resolve utlc_entry : wf_lang_db.
