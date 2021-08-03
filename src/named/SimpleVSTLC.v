Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Matches SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition stlc_def : lang :=
  {[l
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" "G" "A") "B"
       -----------------------------------------------
       #"lambda" "A" "e" : #"val" "G" (#"->" "A" "B")
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"->" "A" "B"),
       "e'" : #"exp" "G" "A"
       -----------------------------------------------
       #"app" "e" "e'" : #"exp" "G" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("STLC_beta")
      #"app" (#"ret" (#"lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"exp" "G" (#"->" "A" "B"),
      "e'" : #"exp" "G" "A",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("app_subst")
      #"exp_subst" "g" (#"app" "e" "e'")
      = #"app" (#"exp_subst" "g" "e") (#"exp_subst" "g" "e'")
      : #"exp" "G'" "B"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("lambda_subst")
      #"val_subst" "g" (#"lambda" "A" "e")
      = #"lambda" "A" (#"exp_subst" (#"snoc" (#"cmp" #"wkn" "g") #"hd") "e")
      : #"val" "G'" (#"->" "A" "B")
  ]
  ]}.

Derive stlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_def stlc)
       As stlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_wf : elab_pfs.

