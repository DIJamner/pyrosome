Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.


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
      "cond" : #"exp" "G" #"bool",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      -----------------------------------------------
      #"if" "cond" "e2" "e3" : #"exp" "G" "t"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      ----------------------------------------------- ("if-true")
      #"if" (#"ret" #"T") "e2" "e3" 
      = "e2" : #"exp" "G" "t"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      ----------------------------------------------- ("if-false")
      #"if" (#"ret" #"F") "e2" "e3" 
      = "e3" : #"exp" "G" "t"
  ]
  ]}.

Derive stlc_bool
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_bool_def stlc)
       As stlc_bool_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_bool_wf : elab_pfs.


