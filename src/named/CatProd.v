Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Cat Matches.
Import Core.Notations.

Require Coq.derive.Derive.

Definition prod_lang : lang :=
  {[l
  [:| "A" : #"ob", "B": #"ob"
      -----------------------------------------------
      #"prod" "A" "B" : #"ob"
  ];
  [:| "G" : #"ob",
      "A" : #"ob",
      "B" : #"ob",
      "e1" : #"arr" "G" "A",
      "e2" : #"arr" "G" "B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"arr" "G" (#"prod" "A" "B")
  ];
  [:| "G" : #"ob",
      "A" : #"ob",
      "B" : #"ob",
      "e" : #"arr" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".1" "e" : #"arr" "G" "A"
  ];
  [:| "G" : #"ob",
      "A" : #"ob",
      "B" : #"ob",
      "e" : #"arr" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".2" "e" : #"arr" "G" "B"
   ];
  [:= "G" : #"ob",
      "A" : #"ob",
      "B" : #"ob",
      "v1" : #"arr" "G" "A",
      "v2" : #"arr" "G" "B"
      ----------------------------------------------- ("project 1")
      #".1" (#"pair" "v1" "v2") = "v1"
      : #"arr" "G" "A"
  ];
  [:= "G" : #"ob",
      "A" : #"ob",
      "B" : #"ob",
      "v1" : #"arr" "G" "A",
      "v2" : #"arr" "G" "B"
      ----------------------------------------------- ("project 2")
      #".2" (#"pair" "v1" "v2") = "v2"
      : #"arr" "G" "B"
  ];   
    [:= "G" : #"ob", "A" : #"ob", "B" : #"ob",
      "v" : #"arr" "G" (#"prod" "A" "B")
      ----------------------------------------------- ("prod_eta")
      #"pair" (#".1" "v") (#".2" "v") = "v"
      : #"arr" "G" (#"prod" "A" "B")
  ]
  ]}.

Derive prod_elab
       SuchThat (Pre.elab_lang cat_elab prod_lang prod_elab)
       As prod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_wf : elab_pfs.
