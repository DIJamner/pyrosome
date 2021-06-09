Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix SimpleVSubst SimpleVCPS Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Definition value_cc_subst_def : lang :=
  [[l
      
  [s|  
      -----------------------------------------------
      #"ty" srt
  ];
  [s| "G" : #"ty", "A" : #"ty"
      -----------------------------------------------
      #"val" "G" "A" srt
  ];
  [:| "G" : #"ty" 
       -----------------------------------------------
       #"id" : #"val" %"G" %"G"
  ];
  [:| "G" : #"ty", "G'" : #"ty", "g" : #"val" %"G" %"G'",
       "A" : #"ty", "v" : #"val" %"G'" %"A"
       -----------------------------------------------
       #"val_subst" "g" "v" : #"val" %"G" %"A"
  ];
   
  [:> "G" : #"ty", "A" : #"ty", "e" : #"val" %"G" %"A"
       ----------------------------------------------- ("id_left")
       #"val_subst" #"id" %"e" = %"e" : #"val" %"G" %"A"
  ]; 
  [:> "G" : #"ty", "A" : #"ty", "e" : #"val" %"G" %"A"
       ----------------------------------------------- ("id_right")
       #"val_subst" %"e" #"id" = %"e" : #"val" %"G" %"A"
  ]; 
   [:> "G1" : #"ty",
         "G2" : #"ty",
         "G3" : #"ty",
         "G4" : #"ty",
         "f" : #"val" %"G1" %"G2",
         "g" : #"val" %"G2" %"G3",
         "h" : #"val"%"G3" %"G4"
         ----------------------------------------------- ("val_subst_assoc")
         #"val_subst" %"f" (#"val_subst" %"g" %"h") = #"val_subst" (#"val_subst" %"f" %"g") %"h" : #"val" %"G1" %"G4"
  ] ]].


Derive value_cc_subst
       SuchThat (Pre.elab_lang []
                               value_cc_subst_def
                               value_cc_subst)
       As value_cc_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve value_cc_subst_wf : elab_pfs.

Definition prod_cc_def : lang :=
  [[l

  [:| 
      -----------------------------------------------
      #"unit" : #"ty"
  ];
  [:| "G" : #"ty" 
      -----------------------------------------------
      #"tt" : #"val" %"G" #"unit"
  ];
  [:> "G" : #"ty", "G'" : #"ty", "g" : #"val" %"G" %"G'"
       ----------------------------------------------- ("subst_tt")
       #"val_subst" %"g" #"tt" = #"tt" : #"val" %"G" #"unit"
  ];
  [:> 
      ----------------------------------------------- ("tt_id_eta")
      #"id" = #"tt" : #"val" #"unit" #"unit"
  ];
  [:| "G" : #"ty", "A": #"ty"
       -----------------------------------------------
       #"prod" "G" "A" : #"ty"
  ];
  [:| "G" : #"ty", "G'" : #"ty", "A" : #"ty",
      "g" : #"val" %"G" %"G'",
      "v" : #"val" %"G" %"A"
       -----------------------------------------------
       #"pair" "g" "v" : #"val" %"G" (#"prod" %"G'" %"A")
  ];
  [:| "G" : #"ty", "A" : #"ty"
       -----------------------------------------------
       #".1" : #"val" (#"prod" %"G" %"A") %"G"
  ];
  [:| "G" : #"ty", "A" : #"ty"
       -----------------------------------------------
       #".2" : #"val" (#"prod" %"G" %"A") %"A"
  ];
   [:> "G" : #"ty", "G'" : #"ty",
      "g" : #"val" %"G" %"G'",
      "A" : #"ty",
      "v" : #"val" %"G" %"A"
      ----------------------------------------------- ("proj 1")
      #"val_subst" (#"pair" %"g" %"v") #".1" = %"g" : #"val" %"G" %"G'"
  ];
   [:> "G" : #"ty", "G'" : #"ty",
       "g" : #"val" %"G" %"G'",
       "A" : #"ty",
       "v" : #"val" %"G" %"A"
       ----------------------------------------------- ("proj 2")
       #"val_subst" (#"pair" %"g" %"v") #".2" = %"v"
       : #"val" %"G" %"A"
  ];
   [:> "G1" : #"ty", "G2" : #"ty", "G3" : #"ty",
       "f" : #"val" %"G1" %"G2",
       "g" : #"val" %"G2" %"G3",
       "A" : #"ty",
       "v" : #"val" %"G2" %"A"
       ----------------------------------------------- ("subst pair")
       #"val_subst" %"f" (#"pair" %"g" %"v")
       = #"pair" (#"val_subst" %"f" %"g") (#"val_subst" %"f" %"v")
       : #"val" %"G1" (#"prod" %"G3" %"A")
   ];
      [:> "G" : #"ty", "A" : #"ty"
       ----------------------------------------------- ("pair eta")
        #"pair" #".1" #".2" = #"id" : #"val" (#"prod" %"G" %"A") (#"prod" %"G" %"A")
   ]
  ]].


Derive prod_cc
       SuchThat (Pre.elab_lang value_cc_subst prod_cc_def prod_cc)
       As prod_cc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_cc_wf : elab_pfs.

(*TODO: use same def for here and for VCPS
  via CompilerForExt
*)
Definition block_cc_subst_def : lang :=
  [[l
      [s| "G" : #"ty"
          -----------------------------------------------
          #"blk" "G" srt
      ];
  [:| "G" : #"ty", "G'" : #"ty", "g" : #"val" %"G" %"G'",
      "e" : #"blk" %"G'"
       -----------------------------------------------
       #"blk_subst" "g" "e" : #"blk" %"G"
  ];
  [:> "G" : #"ty", "e" : #"blk" %"G"
       ----------------------------------------------- ("blk_subst_id")
       #"blk_subst" #"id" %"e" = %"e" : #"blk" %"G"
  ]; 
  [:> "G1" : #"ty", "G2" : #"ty", "G3" : #"ty",
       "f" : #"val" %"G1" %"G2", "g" : #"val" %"G2" %"G3",
       "e" : #"blk" %"G3"
       ----------------------------------------------- ("blk_subst_val_subst")
       #"blk_subst" %"f" (#"blk_subst" %"g" %"e")
       = #"blk_subst" (#"val_subst" %"f" %"g") %"e"
       : #"blk" %"G1"
  ]
  ]].

Derive block_cc_subst
       SuchThat (Pre.elab_lang value_cc_subst block_cc_subst_def block_cc_subst)
       As block_cc_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_cc_subst_wf : elab_pfs.

Definition cc_lang_def : lang :=
  [[l
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
  [:| "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"prod" %"A" %"B"),
      "v" : #"val" %"G" %"A"
      -----------------------------------------------
      #"closure" "B" "e" "v" : #"val" %"G" (#"neg" %"B")
   ];
   [:| "G" : #"ty",
       "A" : #"ty",
       "v1" : #"val" %"G" (#"neg" %"A"),
       "v2" : #"val" %"G" %"A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" %"G"
   ];
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"prod" %"A" %"B"),
      "v" : #"val" %"G" %"A",
      "v'" : #"val" %"G" %"B"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"closure" %"B" %"e" %"v") %"v'"
      = #"blk_subst" (#"pair" %"v" %"v'") %"e"
      : #"blk" %"G"
  ];
  [:> "G" : #"ty", "A" : #"ty",
      "v1" : #"val" %"G" (#"neg" %"A"),
      "v2" : #"val" %"G" %"A",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("jmp_subst")
      #"blk_subst" %"g" (#"jmp" %"v1" %"v2")
      = #"jmp" (#"val_subst" %"g" %"v1") (#"val_subst" %"g" %"v2")
      : #"blk" %"G'"
  ];  
  [:> "G" : #"ty", "A" : #"ty", "B" : #"ty",
      "e" : #"blk" (#"prod" %"A" %"B"),
      "v" : #"val" %"G" %"A",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("clo_subst")
      #"val_subst" %"g" (#"closure" %"B" %"e" %"v")
      = #"closure" %"B" %"e" (#"val_subst" %"g" %"v")
      : #"val" %"G'" (#"neg" %"B")
  ]
  ]].


Derive cc_lang
       SuchThat (Pre.elab_lang (block_cc_subst ++ prod_cc ++ value_cc_subst)
                               cc_lang_def
                               cc_lang)
       As cc_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cc_lang_wf : elab_pfs.


Definition value_cc_def : compiler :=
  match # from (value_cc_subst) with
    
  end.


(*TODO: put in hoisting file*)
Definition hoist_lang_def : lang :=
  [[l
      [s| "A" : #"ty"
          -----------------------------------------------
          #"program" "A" srt
      ];
   [:| "ht" : #"heapty",
       "H" : #"heap" %"HT",
       "A" : #"ty",
       "e" : #"blk" %"HT" "A"             
       -----------------------------------------------
       #"prog" "H" "e" : #"program" %"A"
      ];
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
   
  [:| "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "l" : #"val" %"G" (#"label" (#"prod" %"A" %"B")),
      "v" : #"val" %"G" %"A"
      -----------------------------------------------
      #"closure" "A" "l" "v" : #"val" %"G" (#"neg" %"B")
   ];
   [:| "G" : #"env",
       "A" : #"ty",
       "v1" : #"val" %"G" (#"neg" %"A"),
       "v2" : #"val" %"G" %"A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" %"G"
   ];
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"prod" %"A" %"B"),
      "v" : #"val" %"G" %"A",
      "v'" : #"val" %"G" %"B"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"closure" %"A" %"e" %"v") %"v'"
      = #"blk_subst" (#"pair" %"v" %"v'") %"e"
      : #"blk" %"G"
  ];
  [:> "G" : #"ty", "A" : #"ty",
      "v1" : #"val" %"G" (#"neg" %"A"),
      "v2" : #"val" %"G" %"A",
      "G'" : #"ty",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("jmp_subst")
      #"blk_subst" %"g" (#"jmp" %"v1" %"v2")
      = #"jmp" (#"val_subst" %"g" %"v1") (#"val_subst" %"g" %"v2")
      : #"blk" %"G'"
  ];  
  [:> "G" : #"ty", "A" : #"ty", "B" : #"ty",
      "e" : #"blk" (#"prod" %"A" %"B"),
      "v" : #"val" (#"ext" %"G" %"A"),
      "G'" : #"ty",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("clo_subst")
      #"val_subst" %"g" (#"closure" %"B" %"e" %"v")
      = #"closure" %"B" %"e" (#"val_subst" %"g" %"e")
      : #"val" %"G'" (#"neg" %"B")
  ]
  ]].
