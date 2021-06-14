Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Matches.
Import Core.Notations.

Require Coq.derive.Derive.

(*TODO: flip rule order*)
Definition subst_lang : lang :=
   [[:= "G" : #"env", "A" : #"ty"
       ----------------------------------------------- ("snoc_wkn_hd")
        #"snoc" #"wkn" #"hd" = #"id" : #"sub" (#"ext" "G" "A") (#"ext" "G" "A")
   ];
   [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3",
       "A" : #"ty",
       "e" : #"exp" "G2" "A"
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" "f" (#"snoc" "g" "e")
       = #"snoc" (#"cmp" "f" "g") (#"subst" "f" "e")
       : #"sub" "G1" (#"ext" "G3" "A")
   ];
   [:= "G" : #"env", "G'" : #"env",
       "g" : #"sub" "G" "G'",
       "A" : #"ty",
       "e" : #"exp" "G" "A"
       ----------------------------------------------- ("snoc_hd")
       #"subst" (#"snoc" "g" "e") #"hd" = "e"
       : #"exp" "G" "A"
  ];
  [:= "G" : #"env", "G'" : #"env",
      "g" : #"sub" "G" "G'",
      "A" : #"ty",
      "e" : #"exp" "G" "A"
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" "g" "e") #"wkn" = "g" : #"sub" "G" "G'"
  ];
  [:| "G" : #"env", "A" : #"ty"
       -----------------------------------------------
       #"hd" : #"exp" (#"ext" "G" "A") "A"
  ];
  [:| "G" : #"env", "A" : #"ty"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" "G" "A") "G"
  ];
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty",
      "g" : #"sub" "G" "G'",
      "e" : #"exp" "G" "A"
       -----------------------------------------------
       #"snoc" "g" "e" : #"sub" "G" (#"ext" "G'" "A")
  ];
  [:| "G" : #"env", "A": #"ty"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ];
  [:= 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ];
  [:= "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" "g" #"forget" = #"forget" : #"sub" "G" #"emp"
  ];
  [:| "G" : #"env" 
      -----------------------------------------------
      #"forget" : #"sub" "G" #"emp"
  ];
  [:| 
      -----------------------------------------------
      #"emp" : #"env"
  ];
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty", "e" : #"exp" "G3" "A"
       ----------------------------------------------- ("subst_cmp")
       #"subst" "f" (#"subst" "g" "e")
       = #"subst" (#"cmp" "f" "g") "e"
       : #"exp" "G1" "A"
  ]; 
  [:= "G" : #"env", "A" : #"ty", "e" : #"exp" "G" "A"
       ----------------------------------------------- ("subst_id")
       #"subst" #"id" "e" = "e" : #"exp" "G" "A"
  ]; 
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty", "e" : #"exp" "G'" "A"
       -----------------------------------------------
       #"subst" "g" "e" : #"exp" "G" "A"
  ];
  [s| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"exp" "G" "A" srt
  ];
  [s|  
      -----------------------------------------------
      #"ty" srt
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
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" "f" = "f" : #"sub" "G" "G'"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
      ----------------------------------------------- ("id_right")
      #"cmp" "f" #"id" = "f" : #"sub" "G" "G'"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" "G1" "G3"
  ];
  [:| "G" : #"env" 
       -----------------------------------------------
       #"id" : #"sub" "G" "G"
  ];
  [s| "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      #"sub" "G" "G'" srt                     
  ];
  [s|
      -----------------------------------------------
      #"env" srt
   ]]%rule.

(*TODO: separate cat lang and share amongst var. users *)
Derive subst_elab
       SuchThat (Pre.elab_lang [] subst_lang subst_elab)
       As subst_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve subst_lang_wf : elab_pfs.
