Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

(* TODO: change the rules of this language to look like the rules
   for the sum type in TAPL.
*)
Definition sum_def : lang :=
  {[l/subst [exp_subst++value_subst]

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
      "e" : #"exp" "G" (#"sum" "A" "B"),
      "case_l" : #"exp" (#"ext" "G" "A") "C",
      "case_r" : #"exp" (#"ext" "G" "B") "C"
      -----------------------------------------------
      #"case" "e" "case_l" "case_r" : #"exp" "G" "C"
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
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "v" : #"val" "G" "A",
      "case_l" : #"exp" (#"ext" "G" "A") "C",
      "case_r" : #"exp" (#"ext" "G" "B") "C"
      ----------------------------------------------- ("case_l ret")
      #"case" (#"ret" (#"inl_val" "v")) "case_l" "case_r"
      = #"exp_subst" (#"snoc" #"id" "v") "case_l"
      : #"exp" "G" "C"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "v" : #"val" "G" "B",
      "case_l" : #"exp" (#"ext" "G" "A") "C",
      "case_r" : #"exp" (#"ext" "G" "B") "C"
      ----------------------------------------------- ("case_r ret")
      #"case" (#"ret" (#"inr_val" "v")) "case_l" "case_r"
      = #"exp_subst" (#"snoc" #"id" "v") "case_r"
      : #"exp" "G" "C"
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
  auto_elab.
Qed.
#[export] Hint Resolve sum_wf : elab_pfs.

(*Note that because the projections aren't values,
  we can't put the eta law directly at the value level
*)
