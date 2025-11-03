Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.


Definition stlc_def : lang :=
(* Is there a way to import STLC and only list the new rules? *)
  {[l/subst [stlc++exp_subst++value_subst]
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
      "cond" : #"val" "G" #"bool",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      -----------------------------------------------
      #"if" "cond" "e2" "e3" : #"exp" "G" "t"
  ];
  [:| "G" : #"env",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      -----------------------------------------------
      #"if" #"T" "e2" "e3" = "e2"
  ];
  [:| "G" : #"env",
      "e2" : #"exp" "G" "t",
      "e3" : #"exp" "G" "t"
      -----------------------------------------------
      #"if" #"F" "e2" "e3" = "e3"
  ];
  ]}.

Derive stlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_def stlc)
       As stlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_wf : elab_pfs.


