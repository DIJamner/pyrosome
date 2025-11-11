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

(* Compute value_subst_def. 
Locate term.  *)
Definition utlc_only_boolha_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env"
      -----------------------------------------------
      #"uT" : #"val" "G" #"*"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"uF" : #"val" "G" #"*"
  ];
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
      #"bool?" (#"ulambda" "e") 
      = #"ret" #"uF" : #"exp" "G" #"*"
  ]
  ]}.

Derive utlc_only_boolha
       SuchThat (elab_lang_ext (utlc++exp_subst++value_subst) utlc_only_boolha_def utlc_only_boolha)
       As utlc_only_boolha_wf.
Proof. auto_elab. Admitted. 
#[export] Hint Resolve utlc_only_boolha_wf : elab_pfs.


Definition utlc_bool_uif_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env",
      "t" : #"ty"
      -----------------------------------------------
      #"Error" : #"exp" "G" "t"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      ----------------------------------------------- ("uif-true")
      #"uif" (#"ret" #"uT") "e2" "e3" 
      = "e2" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      ----------------------------------------------- ("uif-false")
      #"uif" (#"ret" #"uF") "e2" "e3" 
      = "e3" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      ----------------------------------------------- ("uif-func")
      #"uif" (#"ret" (#"ulambda" "e")) "e2" "e3" 
      = #"Error" : #"exp" "G" #"*" 
  ]
  ]}.

Derive utlc_bool_uif
       SuchThat (elab_lang_ext (utlc_only_boolha++exp_subst++value_subst) utlc_bool_uif_def utlc_bool_uif)
       As utlc_bool_uif_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve utlc_bool_uif_wf : elab_pfs.


Definition utlc_bool_mif_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env",
      "t" : #"ty"
      -----------------------------------------------
      #"Error" : #"exp" "G" "t"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      ----------------------------------------------- ("mif-true")
      #"uif" (#"ret" #"uT") "e2" "e3" 
      = "e2" : #"exp" "G" "t"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      ----------------------------------------------- ("mif-false")
      #"uif" (#"ret" #"uF") "e2" "e3" 
      = "e3" : #"exp" "G" "t"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      ----------------------------------------------- ("mif-func")
      #"uif" (#"ret" (#"ulambda" "e")) "e2" "e3" 
      = #"Error" : #"exp" "G" "t" 
  ]
  ]}.

Derive utlc_bool_mif
       SuchThat (elab_lang_ext (utlc_only_boolha++exp_subst++value_subst) utlc_bool_mif_def utlc_bool_mif)
       As utlc_bool_mif_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve utlc_bool_mif_wf : elab_pfs.