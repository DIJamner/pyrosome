Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst Matches.
Import Core.Notations.

Require Coq.derive.Derive.

Definition prod_lang :=
  [
     [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" %"G" %"A",
      "v'" : #"val" %"G" %"B"
      ----------------------------------------------- ("ret_pair")
      #"pair" (#"ret" %"v") (#"ret" %"v'")
      = #"ret" (#"pair_val" %"v" %"v'")
      : #"el" %"G" (#"prod" %"A" %"B")
  ]; 
  [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el" %"G" (#"prod" %"A" %"B"),
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("proj_2_subst")
      #"el_subst" %"g" (#".2" %"e")
      = #".2" (#"el_subst" %"g" %"e")
      : #"el" %"G'" %"B"
  ];
  [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el" %"G" (#"prod" %"A" %"B"),
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("proj_1_subst")
      #"el_subst" %"g" (#".1" %"e")
      = #".1" (#"el_subst" %"g" %"e")
      : #"el" %"G'" %"A"
  ];
  [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"val" %"G" %"A",
      "e'" : #"val" %"G" %"B",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("pair_val_subst")
      #"val_subst" %"g" (#"pair_val" %"e" %"e'")
      = #"pair_val" (#"val_subst" %"g" %"e") (#"val_subst" %"g" %"e'")
      : #"val" %"G'" (#"prod" %"A" %"B")
  ];
  [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el" %"G" %"A",
      "e'" : #"el" %"G" %"B",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("pair_subst")
      #"el_subst" %"g" (#"pair" %"e" %"e'")
      = #"pair" (#"el_subst" %"g" %"e") (#"el_subst" %"g" %"e'")
      : #"el" %"G'" (#"prod" %"A" %"B")
  ];
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" %"G" %"A",
      "v2" : #"val" %"G" %"B"
      ----------------------------------------------- ("project 2")
      #".2" (#"ret" (#"pair_val" %"v1" %"v2"))
      = #"ret" %"v2"
      : #"el" %"G" %"B"
  ];
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" %"G" %"A",
      "v2" : #"val" %"G" %"B"
      ----------------------------------------------- ("project 1")
      #".1" (#"ret" (#"pair_val" %"v1" %"v2"))
      = #"ret" %"v1"
      : #"el" %"G" %"A"
  ];
    [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"el" %"G" (#"prod" %"A" %"B")
      -----------------------------------------------
      #".2" "e" : #"el" %"G" %"B"
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"el" %"G" (#"prod" %"A" %"B")
      -----------------------------------------------
      #".1" "e" : #"el" %"G" %"A"
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e1" : #"el" %"G" %"A",
      "e2" : #"el" %"G" %"B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"el" %"G" (#"prod" %"A" %"B")
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" %"G" %"A",
      "v2" : #"val" %"G" %"B"
      -----------------------------------------------
      #"pair_val" "v1" "v2" : #"val" %"G" (#"prod" %"A" %"B")
    ];
  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"prod" "A" "B" : #"ty"
  ]]%arule.


Derive prod_elab
       SuchThat (Pre.elab_lang subst_elab prod_lang prod_elab)
       As prod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_wf : elab_pfs.

(*Note that because the projections aren't values,
  we can't put the eta law directly at the value level
*)
Definition prod_eta :=
  [
     [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" %"G" (#"prod" %"A" %"B")
      ----------------------------------------------- ("prod_eta")
      #"ret" %"v"
      = #"pair" (#".1" (#"ret" %"v")) (#".2" (#"ret" %"v"))
      : #"el" %"G" (#"prod" %"A" %"B")
  ]]%arule.


Derive prod_eta_elab
       SuchThat (Pre.elab_lang (prod_elab ++ subst_elab) prod_eta prod_eta_elab)
       As prod_eta_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_eta_wf : elab_pfs.
