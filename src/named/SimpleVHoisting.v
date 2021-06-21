Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers
     ElabCompilersWithPrefix SimpleVSubst SimpleVCC Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Definition text_segment_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"ty" srt
  ];
  [s| 
      -----------------------------------------------
      #"textty" srt
  ];
  [s| "TT" : #"textty"
      -----------------------------------------------
      #"text" "TT" srt
  ];
  [s| "TT" : #"textty", "A" : #"ty"
      -----------------------------------------------
      #"blk" "TT" "A" srt
  ];
  [:| 
      -----------------------------------------------
      #"Temp_ty" : #"textty"
  ];
  [:| 
      -----------------------------------------------
      #"Temp" : #"text" #"Temp_ty"
  ];
  [:| "TT" : #"textty", "A" : #"ty"
      -----------------------------------------------
      #"Tcons_ty" "TT" "A" : #"textty"
  ];
  [:| "TT" : #"textty", "T" : #"text" "TT",
      "A" : #"ty", "e" : #"blk" "TT" "A"
      -----------------------------------------------
      #"Tcons" "T" "e" : #"text" (#"Tcons_ty" "TT" "A")
  ];
  [s| "A" : #"ty"
      -----------------------------------------------
      #"program" "A" srt
  ];
  [:| "TT" : #"textty",
      "T" : #"text" "TT",
      "A" : #"ty",
      "e" : #"blk" "TT" "A"             
      -----------------------------------------------
      #"prog" "T" "e" : #"program" "A"
  ]
  ]}.

Derive text_segment
       SuchThat (Pre.elab_lang []
                               text_segment_def
                               text_segment)
       As text_segment_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve text_segment_wf : elab_pfs.

Definition hoisted_value_def : lang :=
  {[l
  [s| "TT" : #"textty", "G" : #"ty", "A" : #"ty"
      -----------------------------------------------
      #"val" "TT" "G" "A" srt
  ];
  [:| "TT" : #"textty", "G" : #"ty" 
      -----------------------------------------------
      #"id" : #"val" "TT" "G" "G"
  ];
  [:| "TT" : #"textty",
      "G" : #"ty", "G'" : #"ty", "g" : #"val" "TT" "G" "G'",
      "A" : #"ty", "v" : #"val" "TT" "G'" "A"
      -----------------------------------------------
      #"val_subst" "g" "v" : #"val" "TT" "G" "A"
  ];
  [:= "TT" : #"textty", "G" : #"ty",
      "A" : #"ty", "e" : #"val" "TT" "G" "A"
      ----------------------------------------------- ("id_left")
      #"val_subst" #"id" "e" = "e" : #"val" "TT" "G" "A"
  ]; 
  [:= "TT" : #"textty", "G" : #"ty",
      "A" : #"ty", "e" : #"val" "TT" "G" "A"
      ----------------------------------------------- ("id_right")
      #"val_subst" "e" #"id" = "e" : #"val" "TT" "G" "A"
  ]; 
  [:= "TT" : #"textty",
      "G1" : #"ty",
      "G2" : #"ty",
      "G3" : #"ty",
      "G4" : #"ty",
      "f" : #"val" "TT" "G1" "G2",
      "g" : #"val" "TT" "G2" "G3",
      "h" : #"val" "TT" "G3" "G4"
      ----------------------------------------------- ("val_subst_assoc")
      #"val_subst" "f" (#"val_subst" "g" "h")
      = #"val_subst" (#"val_subst" "f" "g") "h"
      : #"val" "TT" "G1" "G4"
  ];
  [:| "TT" : #"textty",
      "G" : #"ty", "G'" : #"ty", "g" : #"val" "TT" "G" "G'",
      "e" : #"blk" "TT" "G'"
      -----------------------------------------------
      #"blk_subst" "g" "e" : #"blk" "TT" "G"
  ];
  [:= "TT" : #"textty", "G" : #"ty",
      "e" : #"blk" "TT" "G"
      ----------------------------------------------- ("blk_id_left")
      #"blk_subst" #"id" "e" = "e" : #"blk" "TT" "G"
  ];
  [:= "TT" : #"textty",
      "G1" : #"ty",
      "G2" : #"ty",
      "G3" : #"ty",
      "f" : #"val" "TT" "G1" "G2",
      "g" : #"val" "TT" "G2" "G3",
      "e" : #"blk" "TT" "G3"
      ----------------------------------------------- ("blk_subst_assoc")
      #"blk_subst" "f" (#"blk_subst" "g" "e")
      = #"blk_subst" (#"val_subst" "f" "g") "e"
      : #"blk" "TT" "G1"
  ]  ]}.

Derive hoisted_value
       SuchThat (Pre.elab_lang text_segment
                               hoisted_value_def
                               hoisted_value)
       As hoisted_value_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve hoisted_value_wf : elab_pfs.

Definition hoisted_labels_def : lang :=
  {[l
  [s| "TT" : #"textty", "A" : #"ty"
      -----------------------------------------------
      #"label" "TT" "A" srt
  ];
  [:| "TT" : #"textty",
      "A" : #"ty"
      -----------------------------------------------
      #"l0" : #"label" (#"Tcons_ty" "TT" "A") "A"
   ];
  [:| "TT" : #"textty",
      "A" : #"ty",
      "l" : #"label" "TT" "A",
      "B" : #"ty"
      -----------------------------------------------
      #"l+" "l" : #"label" (#"Tcons_ty" "TT" "B") "A"
  ];
  [:| "TT" : #"textty",
      "A" : #"ty",
      "T" : #"text" "TT",
      "l" : #"label" "TT" "A"
      -----------------------------------------------
      #"lookup" "T" "l" : #"blk" "TT" "A"
  ];
  [:| "TT" : #"textty",
      "A" : #"ty",
      "C" : #"ty",
      "v" : #"val" "TT" "A" "C",
      "B" : #"ty"
      -----------------------------------------------
      #"txt_wkn_val" "v" : #"val" (#"Tcons_ty" "TT" "B") "A" "C"
  ]; 
  [:| "TT" : #"textty",
      "A" : #"ty",
      "e" : #"blk" "TT" "A",
      "B" : #"ty"
      -----------------------------------------------
      #"txt_wkn_blk" "e" : #"blk" (#"Tcons_ty" "TT" "B") "A"
  ]; 
  [:= "TT" : #"textty",
      "A" : #"ty",
      "C" : #"ty",
      "v" : #"val" "TT" "A" "C",
      "G" : #"ty",
      "g" : #"val" "TT" "G" "A",
      "B" : #"ty"
      ----------------------------------------------- ("txt_wkn_val_subst")
      #"txt_wkn_val" (#"val_subst" "g" "v")
      = #"val_subst" (#"txt_wkn_val" "g") (#"txt_wkn_val" "v")
      : #"val" (#"Tcons_ty" "TT" "B") "G" "C"
  ]; 
  [:= "TT" : #"textty",
      "A" : #"ty",
      "e" : #"blk" "TT" "A",
      "G" : #"ty",
      "g" : #"val" "TT" "G" "A",
      "B" : #"ty"
      ----------------------------------------------- ("txt_wkn_blk_subst")
      #"txt_wkn_blk" (#"blk_subst" "g" "e")
      = #"blk_subst" (#"txt_wkn_val" "g") (#"txt_wkn_blk" "e")
      : #"blk" (#"Tcons_ty" "TT" "B") "G"
  ]; 
  [:= "TT" : #"textty",
      "A" : #"ty",
      "T" : #"text" "TT",
      "e" : #"blk" "TT" "A"
      ----------------------------------------------- ("lookup head")
      #"lookup" (#"Tcons" "T" "e") #"l0"
      = #"txt_wkn_blk" "e"
      : #"blk" (#"Tcons_ty" "TT" "A") "A"
  ];
  [:= "TT" : #"textty",
      "A" : #"ty",
      "B" : #"ty",
      "T" : #"text" "TT",
      "e" : #"blk" "TT" "A",
      "l" : #"label" "TT" "B"
      ----------------------------------------------- ("lookup tail")
      #"lookup" (#"Tcons" "T" "e") (#"l+" "l")
      = #"txt_wkn_blk" (#"lookup" "T" "l")
      : #"blk" (#"Tcons_ty" "TT" "A") "B"
  ]
  ]}.


Derive hoisted_labels
       SuchThat (Pre.elab_lang (hoisted_value ++ text_segment)
                               hoisted_labels_def
                               hoisted_labels)
       As hoisted_labels_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve hoisted_labels_wf : elab_pfs.


(*TODO: tt wkn rules*)
Definition prod_hoisted_def : lang :=
  {[l

  [:| 
      -----------------------------------------------
      #"unit" : #"ty"
  ];
  [:| "TT" : #"textty",
      "G" : #"ty" 
      -----------------------------------------------
      #"tt" : #"val" "TT" "G" #"unit"
  ];
  [:= "TT" : #"textty",
      "G" : #"ty", "G'" : #"ty", "g" : #"val" "TT" "G" "G'"
       ----------------------------------------------- ("subst_tt")
       #"val_subst" "g" #"tt" = #"tt" : #"val" "TT" "G" #"unit"
  ];
  [:= "TT" : #"textty"
      ----------------------------------------------- ("tt_id_eta")
      #"id" = #"tt" : #"val" "TT" #"unit" #"unit"
  ];
  [:| "G" : #"ty", "A": #"ty"
       -----------------------------------------------
       #"prod" "G" "A" : #"ty"
  ];
  [:| "TT" : #"textty",
      "G" : #"ty", "G'" : #"ty", "A" : #"ty",
      "g" : #"val" "TT" "G" "G'",
      "v" : #"val" "TT" "G" "A"
       -----------------------------------------------
       #"pair" "g" "v" : #"val" "TT" "G" (#"prod" "G'" "A")
  ];
  [:| "TT" : #"textty",
      "G" : #"ty", "A" : #"ty"
       -----------------------------------------------
       #".1" : #"val" "TT" (#"prod" "G" "A") "G"
  ];
  [:| "TT" : #"textty",
      "G" : #"ty", "A" : #"ty"
       -----------------------------------------------
       #".2" : #"val" "TT" (#"prod" "G" "A") "A"
  ];
  [:= "TT" : #"textty",
      "G" : #"ty", "G'" : #"ty",
      "g" : #"val" "TT" "G" "G'",
      "A" : #"ty",
      "v" : #"val" "TT" "G" "A"
      ----------------------------------------------- ("proj 1")
      #"val_subst" (#"pair" "g" "v") #".1" = "g" : #"val" "TT" "G" "G'"
  ];
  [:= "TT" : #"textty",
      "G" : #"ty", "G'" : #"ty",
      "g" : #"val" "TT" "G" "G'",
      "A" : #"ty",
      "v" : #"val" "TT" "G" "A"
      ----------------------------------------------- ("proj 2")
      #"val_subst" (#"pair" "g" "v") #".2" = "v"
      : #"val" "TT" "G" "A"
  ];
  [:= "TT" : #"textty",
      "G1" : #"ty", "G2" : #"ty", "G3" : #"ty",
      "f" : #"val" "TT" "G1" "G2",
      "g" : #"val" "TT" "G2" "G3",
      "A" : #"ty",
      "v" : #"val" "TT" "G2" "A"
      ----------------------------------------------- ("subst pair")
      #"val_subst" "f" (#"pair" "g" "v")
      = #"pair" (#"val_subst" "f" "g") (#"val_subst" "f" "v")
      : #"val" "TT" "G1" (#"prod" "G3" "A")
  ];
  [:= "TT" : #"textty",
      "G" : #"ty", "A" : #"ty"
      ----------------------------------------------- ("pair eta")
      #"pair" #".1" #".2" = #"id" : #"val" "TT" (#"prod" "G" "A") (#"prod" "G" "A")
  ]
  ]}.

Derive prod_hoisted
       SuchThat (Pre.elab_lang (hoisted_value ++ text_segment) prod_hoisted_def prod_hoisted)
       As prod_hoisted_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_hoisted_wf : elab_pfs.


(*TODO: tt wkn rules*)
(*TODO: relies on product type*)
Definition hoisted_closure_def : lang :=
  {[l
  [:| "A" : #"ty"
      -----------------------------------------------
      #"neg" "A" : #"ty"
  ];
  [:| "TT" : #"textty",
      "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "l" : #"label" "TT" (#"prod" "A" "B"),
      "v" : #"val" "TT" "G" "A"
      -----------------------------------------------
      #"closure" "B" "l" "v" : #"val" "TT" "G" (#"neg" "B")
  ];
  [:| "TT" : #"textty",
      "G" : #"ty",
      "A" : #"ty",
      "v1" : #"val" "TT" "G" (#"neg" "A"),
      "v2" : #"val" "TT" "G" "A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" "TT" "G"
  ];
  [:= "TT" : #"textty",
      "T" : #"text" "TT",
      "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "l" : #"label" "TT" (#"prod" "A" "B"),
      "v" : #"val" "TT" "G" "A",
      "v'" : #"val" "TT" "G" "B"
      ----------------------------------------------- ("jmp_beta")
      #"prog" "T" (#"jmp" (#"closure" "B" "l" "v") "v'")
      = #"prog" "T" (#"blk_subst" (#"pair" "v" "v'") (#"lookup" "T" "l"))
      : #"program" "G"
  ];
  [:= "TT" : #"textty",
      "G" : #"ty", "A" : #"ty",
      "v1" : #"val" "TT" "G" (#"neg" "A"),
      "v2" : #"val" "TT" "G" "A",
      "G'" : #"ty",
      "g" : #"val" "TT" "G'" "G"
      ----------------------------------------------- ("jmp_subst")
      #"blk_subst" "g" (#"jmp" "v1" "v2")
      = #"jmp" (#"val_subst" "g" "v1") (#"val_subst" "g" "v2")
      : #"blk" "TT" "G'"
  ];  
  [:= "TT" : #"textty",
      "G" : #"ty", "A" : #"ty", "B" : #"ty",
      "l" : #"label" "TT" (#"prod" "A" "B"),
      "v" : #"val" "TT" "G" "A",
      "G'" : #"ty",
      "g" : #"val" "TT" "G'" "G"
      ----------------------------------------------- ("clo_subst")
      #"val_subst" "g" (#"closure" "B" "l" "v")
      = #"closure" "B" "l" (#"val_subst" "g" "v")
      : #"val" "TT" "G'" (#"neg" "B")
  ]]}.


Derive hoisted_closure
       SuchThat (Pre.elab_lang (prod_hoisted ++ hoisted_labels ++ hoisted_value ++ text_segment)
                               hoisted_closure_def
                               hoisted_closure)
       As hoisted_closure_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve hoisted_closure_wf : elab_pfs.
