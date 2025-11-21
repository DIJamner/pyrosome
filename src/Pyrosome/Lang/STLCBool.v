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


Definition stlc_bool_def : lang :=
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

Derive stlc_bool
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_bool_def stlc_bool)
       As stlc_bool_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_bool_wf : elab_pfs.


