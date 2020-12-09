Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils.
From Named Require Import Exp ARule.
From Named Require Import IExp IRule ICore Tactics.
Require Import String.

Require Import Named.Recognizers.
Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".




(*Notation ob := (con 0 [::]).
Notation hom a b := (con 1 [:: b; a]%exp_scope).
Notation id a := (con 2 [:: a]%exp_scope).
Notation cmp a b c f g := (con 3 [:: f; g; c; b; a]%exp_scope).*)       

(* syntax of categories *)
Definition cat_lang : lang :=
  [::
     [:> "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" %"G1" %"G2",
         "g" : #"sub" %"G2" %"G3",
         "h" : #"sub"%"G3" %"G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" %"f" (#"cmp" %"g" %"h") = #"cmp" (#"cmp" %"f" %"g") %"h" : #"sub" %"G1" %"G4"
  ];  
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" %"f" = %"f" : #"sub" %"G"%"G'"
  ];
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
      ----------------------------------------------- ("id_right")
      #"cmp" %"f" #"id" = %"f" : #"sub" %"G" %"G'"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3"
       -----------------------------------------------
       "cmp" "f" "g" : #"sub" %"G1" %"G3"
  ];
  [:| "G" : #"env" 
       -----------------------------------------------
       "id" : #"sub" %"G" %"G"
  ];
  [s| "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      "sub" "G" "G'" srt                     
  ];
  [s| (:)
      -----------------------------------------------
      "env" srt
  ]
  ].


Derive elab_cat_lang
       SuchThat (elab_lang cat_lang elab_cat_lang)
       As elab_cat_lang_pf.
Proof.
  repeat (simpl;step_elab()); repeat (elab_term_by()).
Qed. 

Instance elab_cat_lang_inst : Elaborated cat_lang :=
  {
  elaboration := elab_cat_lang;
  elab_pf := elab_cat_lang_pf;
  }.


Definition subst_lang' : lang :=
 [:> (:)
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ]::
  [:> "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" %"g" #"forget" = #"forget" : #"sub" %"G" #"emp"
  ]::
  [:| "G" : #"env" 
      -----------------------------------------------
      "forget" : #"sub" %"G" #"emp"
  ]::
  [:| (:)
      -----------------------------------------------
      "emp" : #"env"
  ]::
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3", "e" : #"el" %"G3" %"A"
       ----------------------------------------------- ("el_subst_cmp")
       #"el_subst" (#"cmp" %"f" %"g") %"e"
       = #"el_subst" %"f" (#"el_subst" %"g" %"e")
       : #"el" %"G1" (#"ty_subst" (#"cmp" %"f" %"g") %"A")
  ]:: 
  [:> "G" : #"env", "A" : #"ty" %"G", "e" : #"el" %"G" %"A"
       ----------------------------------------------- ("el_subst_id")
       #"el_subst" #"id" %"e" = %"e" : #"el" %"G" %"A"
  ]::
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3"
       ----------------------------------------------- ("ty_subst_cmp")
       #"ty_subst" (#"cmp" %"f" %"g") %"A"
       = #"ty_subst" %"f" (#"ty_subst" %"g" %"A")
       : #"ty" %"G1"
  ]::              
  [:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("ty_subst_id")
       #"ty_subst" #"id" %"A" = %"A" : #"ty" %"G"
  ]::
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'", "e" : #"el" %"G'" %"A"
       -----------------------------------------------
       "el_subst" "g" "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
  ]::
  [s| "G" : #"env", "A" : #"ty"(%"G")
      -----------------------------------------------
      "el" "G" "A" srt
  ]::
  [:| "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'"
       -----------------------------------------------
       "ty_subst" "g" "A" : #"ty" %"G"
  ]::
  [s| "G" : #"env" 
      -----------------------------------------------
      "ty" "G" srt
  ]::cat_lang.

Derive elab_subst_lang'
       SuchThat (elab_lang subst_lang' elab_subst_lang')
       As elab_subst_lang'_pf.
Proof.
  (repeat (simpl; step_elab()));
    try (solve[repeat (simpl; step_elab())
              | repeat(elab_term_by())]).
  {
    eapply elab_term_conv.
    elab_term_by().
    elab_term_by().
    solve [repeat (simpl;step_elab())].
    solve [repeat (simpl;step_elab())].
    
    eapply Core.le_sort_refl'; repeat (simpl; step_elab()).
    reflexivity.
    eapply (Core.le_term_by' "ty_subst_id"%string); repeat (simpl;step_elab()).
    reflexivity.
    reflexivity.
  }
  {
    eapply elab_term_conv; 
    repeat (simpl;step_elab()).
    elab_term_by().
    elab_term_by().
    elab_term_by().
    solve [repeat (simpl;step_elab())].
    solve [repeat (simpl;step_elab())].
    
    eapply Core.le_sort_refl'; repeat (cbn; step_elab()).
    reflexivity.
    reflexivity.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn;step_elab()); auto;reflexivity.
  }
Qed.

Instance elab_subst_lang'_inst : Elaborated subst_lang' :=
  {
  elaboration := elab_subst_lang';
  elab_pf := elab_subst_lang'_pf;
  }.

Definition subst_lang : lang :=
   [:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("snoc_wkn_hd")
       #"id" = #"snoc" #"wkn" #"hd" : #"sub" (#"ext" %"G" %"A") (#"ext" %"G" %"A")
   ]::
   [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3",
       "e" : #"el" %"G2" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" %"f" (#"snoc" %"g" %"e")
       = #"snoc" (#"cmp" %"f" %"g") (#"el_subst" %"f" %"e")
       : #"sub" %"G1" (#"ext" %"G3" %"A")
   ]::
   [:> "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'",
       "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("snoc_hd")
       #"el_subst" (#"snoc" %"g" %"e") #"hd" = %"e"
       : #"el" %"G" (#"ty_subst" %"g" %"A")
  ]::
  [:> "G" : #"env", "G'" : #"env",
      "g" : #"sub" %"G" %"G'",
      "A" : #"ty" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" %"g" %"e") #"wkn" = %"g" : #"sub" %"G" %"G'"
  ]::
  [:| "G" : #"env", "A" : #"ty"(%"G")
       -----------------------------------------------
       "hd" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"A")
  ]::
  [:| "G" : #"env", "A" : #"ty" %"G"
       -----------------------------------------------
       "wkn" : #"sub" (#"ext" %"G" %"A") %"G"
  ]::
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty" %"G'",
      "g" : #"sub" %"G" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       -----------------------------------------------
       "snoc" "g" "e" : #"sub" %"G" (#"ext" %"G'" %"A")
  ]::
  [:| "G" : #"env", "A": #"ty" %"G"
       -----------------------------------------------
       "ext" "G" "A" : #"env"
  ]::subst_lang'.


Derive elab_subst_lang
       SuchThat (elab_lang subst_lang elab_subst_lang)
       As elab_subst_lang_pf.
Proof.
  repeat (simpl; step_elab());
    try (solve[repeat (simpl; step_elab())
        | repeat(elab_term_by())]).
  { repeat (elab_term_by()). }
  {
    elab_term_by().
    elab_term_by().
    apply (@elab_term_var' "A"%string); reflexivity.
    repeat (elab_term_by()).
    repeat (elab_term_by()).
  }    
  {
    eapply elab_term_conv.
    elab_term_by().
    elab_term_by().

    apply (@elab_term_var' "A"%string); simpl; solve_in().    
    progress (repeat (simpl;step_elab())).
    elab_term_by().
    elab_term_by().
    elab_term_by().
    elab_term_by().
    elab_term_by().
    progress (repeat (cbn;step_elab())).
    progress (repeat (cbn;step_elab())).

    
    eapply Core.le_sort_refl'; repeat (cbn;step_elab()); try reflexivity.

    eapply Core.le_term_trans.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string);repeat (simpl;step_elab());
    reflexivity.
    eapply Core.le_term_refl';repeat (cbn;step_elab()); try reflexivity.
  }
  {
    elab_term_by().
    eapply elab_term_conv.
    solve[repeat(elab_term_by())].
    progress (repeat (simpl;step_elab())).

    eapply Core.le_sort_refl'; repeat(cbn;step_elab());try reflexivity.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string);repeat (cbn;step_elab());
      reflexivity.
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  { repeat (elab_term_by()). }
Qed.
 
    
Instance elab_subst_lang_inst : Elaborated subst_lang :=
  {
  elaboration := elab_subst_lang;
  elab_pf := elab_subst_lang_pf;
  }.
