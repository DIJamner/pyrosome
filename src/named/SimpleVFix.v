Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Matches SimpleVSubst.
From Named Require ElabWithPrefix.
Module Pre := ElabWithPrefix.
Import Core.Notations.

Require Coq.derive.Derive.

Definition fix_def : lang :=
  {[l
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" (#"ext" "G" (#"->" "A" "B")) "A") "B"
       -----------------------------------------------
       #"fix" "A" "e" : #"val" "G" (#"->" "A" "B")
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
      "e" : #"exp" (#"ext" (#"ext" "G" (#"->" "A" "B")) "A") "B",
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("fix_beta")
      #"app" (#"ret" (#"fix" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" (#"snoc" #"id" (#"fix" "A" "e")) "v") "e"
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
      "e" : #"exp" (#"ext" (#"ext" "G" (#"->" "A" "B")) "A") "B",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("fix_subst")
      #"val_subst" "g" (#"fix" "A" "e")
      = #"fix" "A" (#"exp_subst" (#"snoc" (#"cmp" #"wkn" (#"snoc" (#"cmp" #"wkn" "g") #"hd")) #"hd") "e")
      : #"val" "G'" (#"->" "A" "B")
  ]
  ]}.

Derive fix_lang
       SuchThat (Pre.elab_lang (exp_subst++value_subst) fix_def fix_lang)
       As fix_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve fix_wf : elab_pfs.

