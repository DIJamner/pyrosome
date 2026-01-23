Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.
From Pyrosome.Lang Require Import SimpleVSTLC. 
From Pyrosome.Lang Require Import UTLC. 

Definition utf_def : lang :=
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

Derive utf
       SuchThat (elab_lang_ext (usubst++exp_subst++value_subst) utf_def utf)
       As utf_wf.
Proof. auto_elab. Qed. 
#[export] Hint Resolve utf_wf : elab_pfs.


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
       SuchThat (elab_lang_ext (utf++utlc++usubst++exp_subst++value_subst) boolhuh_def boolhuh)
       As boolhuh_wf.
Proof. auto_elab. Qed. 
#[export] Hint Resolve boolhuh_wf : elab_pfs.


Definition utf_uapp_ulambda_def : lang :=
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

Derive utf_uapp_ulambda
       SuchThat (elab_lang_ext (utlc++utf++usubst++exp_subst++value_subst) utf_uapp_ulambda_def utf_uapp_ulambda)
       As utf_uapp_ulambda_wf.
Proof. auto_elab. Qed. 
#[export] Hint Resolve utf_uapp_ulambda_wf : elab_pfs.


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
       SuchThat (elab_lang_ext (utlc++utf++usubst++exp_subst++value_subst) uif_def uif)
       As uif_wf. (* leftmost is newest *)
Proof. auto_elab. Qed.
#[export] Hint Resolve uif_wf : elab_pfs.


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
       SuchThat (elab_lang_ext (utlc++utf++usubst++exp_subst++value_subst) mif_def mif)
       As mif_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve mif_wf : elab_pfs.