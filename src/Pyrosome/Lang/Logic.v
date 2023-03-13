Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches.
Import Core.Notations.

Require Coq.derive.Derive.


Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).


Definition intuitionistic_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"env" srt
  ];
  [s| "G" : #"env", "G'" : #"env"
      -----------------------------------------------
      #"sub" "G" "G'" srt
  ];
  [:| "G" : #"env"
       -----------------------------------------------
       #"id" : #"sub" "G" "G"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" "G1" "G3"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
      ----------------------------------------------- ("id_right")
      #"cmp" "f" #"id" = "f" : #"sub" "G" "G'"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" "f" = "f" : #"sub" "G" "G'"
  ];
   [:= "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" "G1" "G2",
         "g" : #"sub" "G2" "G3",
         "h" : #"sub" "G3" "G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" "f" (#"cmp" "g" "h") = #"cmp" (#"cmp" "f" "g") "h" : #"sub" "G1" "G4"
  ];
  [s| "G" : #"env"
      -----------------------------------------------
      #"prop" "G" srt
  ];

  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"prop" "G'"
       -----------------------------------------------
       #"prop_subst" "g" "A" : #"prop" "G"
  ];
  [:= "G" : #"env", "A" : #"prop" "G"
       ----------------------------------------------- ("prop_subst_id")
       #"prop_subst" #"id" "A" = "A" : #"prop" "G"
  ];
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"prop" "G3"
       ----------------------------------------------- ("prop_subst_cmp")
       #"prop_subst" "f" (#"prop_subst" "g" "A")
       = #"prop_subst" (#"cmp" "f" "g") "A"
       : #"prop" "G1"
  ];




  [:|
      -----------------------------------------------
      #"emp" : #"env"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"forget" : #"sub" "G" #"emp"
  ];
  [:= "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" "g" #"forget" = #"forget" : #"sub" "G" #"emp"
  ];
  [:=
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ];
  [:| "G" : #"env", "A": #"prop" "G"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ];
  [:| "G" : #"env", "A" : #"prop" "G"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" "G" "A") "G"
  ]












  ]}.