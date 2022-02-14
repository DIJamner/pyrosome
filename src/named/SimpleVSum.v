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
      #"prod" "A" "B" : #"ty"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e1" : #"exp" "G" "A",
      "e2" : #"exp" "G" "B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"exp" "G" (#"prod" "A" "C" "B")
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      -----------------------------------------------
      #"pair_val" "v1" "v2" : #"val" "G" (#"prod" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".1" "e" : #"exp" "G" "A"
   ];     
    [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".2" "e" : #"exp" "G" "B"
    ];
     (*TODO: autogenerate somehow *)
     [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" "A",
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("ret_pair")
      #"pair" (#"ret" "v") (#"ret" "v'")
      = #"ret" (#"pair_val" "v" "v'")
      : #"exp" "G" (#"prod" "A" "B")
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
