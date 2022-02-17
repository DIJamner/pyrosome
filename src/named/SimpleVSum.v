Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst Matches Linter.
Import Core.Notations.

Require Coq.derive.Derive.

(* TODO: change the rules of this language to look like the rules
   for the sum type in TAPL.
*)
Definition sum_def : lang :=
  {[l/subst

  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"sum" "A" "B" : #"ty"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" "A"
      -----------------------------------------------
      #"inl" "e" : #"exp" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" "B"
      -----------------------------------------------
      #"inr" "e" : #"exp" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" "A"
      -----------------------------------------------
      #"inl_val" "v" : #"val" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" "B"
      -----------------------------------------------
      #"inr_val" "v" : #"val" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "case_l" : #"exp" (#"SOMETHING" "G" (#"SOMETHING" "a" "A")) "C",
      "case_r" : #"exp" (#"SOMETHING" "G" (#"SOMETHING" "b" "B")) "C",
      "e" : #"exp" "G" (#"sum" "A" "B")
      -----------------------------------------------
      #"case" "e" "a" "case_l" "b" "case_r" : #"exp" "G" "C"
  ];     
     (*TODO: autogenerate somehow *)
     [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("retl")
      #"inl" (#"ret" "v")
      = #"ret" (#"inl_val" "v" )
      : #"exp" "G" (#"sum" "A" "B")
     ]; 
     [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" "B"
      ----------------------------------------------- ("retr")
      #"inr" (#"ret" "v")
      = #"ret" (#"inr_val" "v" )
      : #"exp" "G" (#"sum" "A" "B")
     ]; 
  [:="G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      ----------------------------------------------- ("project 1")
      #".1" (#"ret" (#"pair_val" "v1" "v2"))
      = #"ret" "v1"
      : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      ----------------------------------------------- ("project 2")
      #".2" (#"ret" (#"pair_val" "v1" "v2"))
      = #"ret" "v2"
      : #"exp" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
      ----------------------------------------------- ("prod_eta")
      #"ret" "v"
      = #"pair" (#".1" (#"ret" "v")) (#".2" (#"ret" "v"))
      : #"exp" "G" (#"prod" "A" "B")
     ]
    ]}.


Derive sum
       SuchThat (elab_lang_ext (exp_subst++value_subst) sum_def sum)
       As sum_wf.
Proof.

  (* Replace all these tactics with `auto_elab.` when all goals goa through.
     Each goal corresponds to one rule above.
     If a goal doesn't go through, you can either try breaking down the tactics
     and applying them piece by piece, or just looking at the rule
     to see what's wrong.
     Make sure to check variable and constructor names, it's easy to typo them.
   *)
  setup_elab_lang.
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
  - solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ].
Qed.
#[export] Hint Resolve sum_wf : elab_pfs.

(*Note that because the projections aren't values,
  we can't put the eta law directly at the value level
*)
