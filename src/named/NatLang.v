Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab
     SimpleVSubst SimpleUnit Matches.
Import Core.Notations.

Require Coq.derive.Derive.

Definition nat_lang_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"natural" srt
  ];
  [:|  
       -----------------------------------------------
       #"0" : #"natural"
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"1+" "n" : #"natural"
  ];
  [:|
       "a" : #"natural",
       "b" : #"natural" 
       -----------------------------------------------
       #"plus" "a" "b" : #"natural"
  ];
  [:=
       "a" : #"natural"
       ----------------------------------------------- ("plus_0")
       #"plus" "a" #"0" = "a" : #"natural"
  ];
  [:=
       "a" : #"natural",
       "b" : #"natural"
       ----------------------------------------------- ("plus_1+")
       #"plus" "a" (#"1+" "b") = #"plus" (#"1+" "a") "b" : #"natural"
  ]


  (* [s|  "n": #"natural", "m": #"natural" *)
  (*      ----------------------------------------------- *)
  (*      #"neq" "n" "m" srt *)
  (* ]; *)
  (* [:|  "n": #"natural" *)
  (*      ----------------------------------------------- *)
  (*      #"neq_0_l" : #"neq" #"0" (#"1+" "n") *)
  (* ]; *)
  (* [:|  "n": #"natural" *)
  (*      ----------------------------------------------- *)
  (*      #"neq_0_r" : #"neq" (#"1+" "n") #"0" *)
  (* ]; *)
  (* [:|  "n": #"natural", "m": #"natural", *)
  (*      "p" : #"neq" "n" "m" *)
  (*      ----------------------------------------------- *)
  (*      #"neq_1+" "p" : #"neq" (#"1+" "n") (#"1+" "m") *)
  (* ] *)
  ]}.


Derive nat_lang
       SuchThat (elab_lang_ext [] nat_lang_def nat_lang)
       As nat_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve nat_lang_wf : elab_pfs.



