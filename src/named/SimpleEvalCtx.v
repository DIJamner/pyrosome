Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst SimpleVSTLC Matches.
Import Core.Notations.

Require Coq.derive.Derive.


Definition subst_eval_ctx :=
  [(* TODO: do I want a substitution eval ctx? I think no
         [:> "G1" : #"env", "G2" : #"env", "G3" : #"env", "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3", "A" : #"ty", "e" : #"el" %"G3" %"A"
        ----------------------------------------------- ("el_subst_cmp")
        #"el_subst" %"f" (#"el_subst" %"g" %"e") = #"el_subst" (#"cmp" %"f" %"g") %"e" : #"el" %"G1" %"A"
    ]%arule;
  [:> "G" : #"env", "A" : #"ty", "B": #"ty", "E" : #"Ectx" %"G'" %"A" %"B"
        ----------------------------------------------- ("E_subst_id")
        #"E_subst" #"id" %"E" = %"E" : #"Ectx" %"G'" %"A" %"B"
    ]%arule;
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
      "A" : #"ty", "B" : #"ty", "E" : #"Ectx" %"G" %"A" %"B"
        -----------------------------------------------
        #"E_subst" "g" "E" : #"Ectx" %"G'" %"A" %"B"
    ];*)
     [:> "G" : #"env", "A" : #"ty",
         "e" : #"el" %"G" %"A"
        ----------------------------------------------- ("plug hole")
        #"plug" #"[ ]" %"e" = %"e" : #"el" %"G" %"A"
     ];
     [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
         "E" : #"Ectx" %"G" %"A" %"B",
         "e" : #"el" %"G" %"A"
        -----------------------------------------------
        #"plug" "E" "e" : #"el" %"G" %"B"
     ];
     [:| "G" : #"env", "A" : #"ty"
        -----------------------------------------------
        #"[ ]" : #"Ectx" %"G" %"A" %"A"
     ];
     [s| "G" : #"env", "A" : #"ty", "B" : #"ty"
        -----------------------------------------------
        #"Ectx" "G" "A" "B" srt
     ]
  ]%arule.

Derive eval_ctx_elab
       SuchThat (Pre.elab_lang subst_elab subst_eval_ctx eval_ctx_elab)
       As eval_ctx_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve eval_ctx_wf : elab_pfs.


Definition Estlc :=  
  [
     [:> "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" %"A",
       "v" : #"val" %"G" (#"->" %"A" %"B"),
       "e" : #"el" %"G" %"C"
       ----------------------------------------------- ("plug app_r")
       #"plug" (#"Eapp_r" %"v" %"E") %"e"
       = #"app" (#"ret" %"v") (#"plug" %"E" %"e")
      : #"el" %"G" %"B"
  ];
     [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "v" : #"val" %"G" (#"->" %"A" %"B"),
       "E" : #"Ectx" %"G" %"C" %"A"
       -----------------------------------------------
       #"Eapp_r" "v" "E" : #"Ectx" %"G" %"C" %"B"
  ];
     [:> "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A",
       "e" : #"el" %"G" %"C"
       ----------------------------------------------- ("plug app_l")
       #"plug" (#"Eapp_l" %"E" %"e'") %"e"
       = #"app" (#"plug" %"E" %"e") %"e'"
      : #"el" %"G" %"B"
  ];
     [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A"
       -----------------------------------------------
       #"Eapp_l" "E" "e'" : #"Ectx" %"G" %"C" %"B"
  ]]%arule.

Derive Estlc_elab
       SuchThat (Pre.elab_lang (eval_ctx_elab ++ stlc_elab ++ subst_elab) Estlc Estlc_elab)
       As Estlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve Estlc_wf : elab_pfs.
 
