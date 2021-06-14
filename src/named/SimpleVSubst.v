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


Definition value_subst_def : lang :=
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
  [s|  
      -----------------------------------------------
      #"ty" srt
  ];
  [s| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"val" "G" "A" srt
  ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty", "v" : #"val" "G'" "A"
       -----------------------------------------------
       #"val_subst" "g" "v" : #"val" "G" "A"
  ];
  [:= "G" : #"env", "A" : #"ty", "e" : #"val" "G" "A"
       ----------------------------------------------- ("val_subst_id")
       #"val_subst" #"id" "e" = "e" : #"val" "G" "A"
  ]; 
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty", "v" : #"val" "G3" "A"
       ----------------------------------------------- ("val_subst_cmp")
       #"val_subst" "f" (#"val_subst" "g" "v")
       = #"val_subst" (#"cmp" "f" "g") "v"
       : #"val" "G1" "A"
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
  [:| "G" : #"env", "A": #"ty"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ];
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty",
      "g" : #"sub" "G" "G'",
      "v" : #"val" "G" "A" (*we restrict substitutions to values *)
       -----------------------------------------------
       #"snoc" "g" "v" : #"sub" "G" (#"ext" "G'" "A")
  ];
  [:| "G" : #"env", "A" : #"ty"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" "G" "A") "G"
  ];
  [:| "G" : #"env", "A" : #"ty"
       -----------------------------------------------
       #"hd" : #"val" (#"ext" "G" "A") "A"
  ];
   [:= "G" : #"env", "G'" : #"env",
      "g" : #"sub" "G" "G'",
      "A" : #"ty",
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" "g" "v") #"wkn" = "g" : #"sub" "G" "G'"
  ];
   [:= "G" : #"env", "G'" : #"env",
       "g" : #"sub" "G" "G'",
       "A" : #"ty",
       "v" : #"val" "G" "A"
       ----------------------------------------------- ("snoc_hd")
       #"val_subst" (#"snoc" "g" "v") #"hd" = "v"
       : #"val" "G" "A"
  ];
   [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3",
       "A" : #"ty",
       "v" : #"val" "G2" "A"
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" "f" (#"snoc" "g" "v")
       = #"snoc" (#"cmp" "f" "g") (#"val_subst" "f" "v")
       : #"sub" "G1" (#"ext" "G3" "A")
   ];
      [:= "G" : #"env", "A" : #"ty"
       ----------------------------------------------- ("snoc_wkn_hd")
        #"snoc" #"wkn" #"hd" = #"id" : #"sub" (#"ext" "G" "A") (#"ext" "G" "A")
   ]
   ]}.


Derive value_subst
       SuchThat (Pre.elab_lang [] value_subst_def value_subst)
       As value_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve value_subst_wf : elab_pfs.


Definition exp_subst_def : lang :=
  {[l
      [s| "G" : #"env", "A" : #"ty"
          -----------------------------------------------
          #"exp" "G" "A" srt
      ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty", "e" : #"exp" "G'" "A"
       -----------------------------------------------
       #"exp_subst" "g" "e" : #"exp" "G" "A"
  ];
  [:= "G" : #"env", "A" : #"ty", "e" : #"exp" "G" "A"
       ----------------------------------------------- ("exp_subst_id")
       #"exp_subst" #"id" "e" = "e" : #"exp" "G" "A"
  ]; 
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty", "e" : #"exp" "G3" "A"
       ----------------------------------------------- ("exp_subst_cmp")
       #"exp_subst" "f" (#"exp_subst" "g" "e")
       = #"exp_subst" (#"cmp" "f" "g") "e"
       : #"exp" "G1" "A"
  ];    
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"exp" "G" "A"
  ];
  [:= "G1" : #"env", "G2" : #"env",
       "g" : #"sub" "G1" "G2",
       "A" : #"ty", "v" : #"val" "G2" "A"
       ----------------------------------------------- ("exp_subst_ret")
       #"exp_subst" "g" (#"ret" "v")
       = #"ret" (#"val_subst" "g" "v")
       : #"exp" "G1" "A"
  ]
  ]}.


Derive exp_subst
       SuchThat (Pre.elab_lang value_subst exp_subst_def exp_subst)
       As exp_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_subst_wf : elab_pfs.
