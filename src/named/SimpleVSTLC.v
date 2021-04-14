Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.


Definition stlc :=
  [[:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el" (#"ext" %"G" %"A") %"B",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("lambda_subst")
      #"val_subst" %"g" (#"lambda" %"A" %"e")
      = #"lambda" %"A" (#"el_subst" (#"snoc" (#"cmp" #"wkn" %"g") #"hd") %"e")
      : #"val" %"G'" (#"->" %"A" %"B")
  ];
  [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el"%"G" (#"->" %"A" %"B"),
      "e'" : #"el" %"G" %"A",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("app_subst")
      #"el_subst" %"g" (#"app" %"e" %"e'")
      = #"app" (#"el_subst" %"g" %"e") (#"el_subst" %"g" %"e'")
      : #"el" %"G'" %"B"
  ];
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"el" (#"ext" %"G" %"A") %"B",
      "v" : #"val" %"G" %"A"
      ----------------------------------------------- ("STLC_beta")
      #"app" (#"ret" (#"lambda" %"A" %"e")) (#"ret" %"v")
      = #"el_subst" (#"snoc" #"id" %"v") %"e"
      : #"el" %"G" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"el" %"G" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A"
       -----------------------------------------------
       #"app" "e" "e'" : #"el" %"G" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"el" (#"ext" %"G" %"A") %"B"
       -----------------------------------------------
       #"lambda" "A" "e" : #"val" %"G" (#"->" %"A" %"B")
  ];
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty"
  ]]%arule++subst_lang.


Derive stlc_elab
       SuchThat (elab_lang stlc stlc_elab)
       As stlc_wf.
Proof.
  auto_elab.
  Unshelve.
  all: cleanup_auto_elab.
Qed.

