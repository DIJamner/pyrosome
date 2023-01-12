Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleSubst Matches.
Import Core.Notations.

Require Coq.derive.Derive.

(*TODO: flip rule*)
Definition prod_lang :=
  [
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B"),
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("proj_2_subst")
      #"subst" "g" (#".2" "e")
      = #".2" (#"subst" "g" "e")
      : #"exp" "G'" "B"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B"),
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("proj_1_subst")
      #"subst" "g" (#".1" "e")
      = #".1" (#"subst" "g" "e")
      : #"exp" "G'" "A"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"exp" "G" "A",
      "e'" : #"exp" "G" "B",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("pair_subst")
      #"subst" "g" (#"pair" "e" "e'")
      = #"pair" (#"subst" "g" "e") (#"subst" "g" "e'")
      : #"exp" "G'" (#"prod" "A" "B")
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"exp" "G" (#"prod" "A" "B")
      ----------------------------------------------- ("prod_eta")
      #"pair" (#".1" "v") (#".2" "v") = "v"
      : #"exp" "G" (#"prod" "A" "B")
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"exp" "G" "A",
      "v2" : #"exp" "G" "B"
      ----------------------------------------------- ("project 2")
      #".2" (#"pair" "v1" "v2") = "v2"
      : #"exp" "G" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"exp" "G" "A",
      "v2" : #"exp" "G" "B"
      ----------------------------------------------- ("project 1")
      #".1" (#"pair" "v1" "v2") = "v1"
      : #"exp" "G" "A"
  ];
    [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".2" "e" : #"exp" "G" "B"
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".1" "e" : #"exp" "G" "A"
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e1" : #"exp" "G" "A",
      "e2" : #"exp" "G" "B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"exp" "G" (#"prod" "A" "B")
   ];
  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"prod" "A" "B" : #"ty"
  ]]%rule.

Derive prod_elab
       SuchThat (Pre.elab_lang subst_elab prod_lang prod_elab)
       As prod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_wf : elab_pfs.
