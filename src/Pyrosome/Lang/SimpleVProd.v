Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition prod_def : lang :=
  {[l/subst [exp_subst++value_subst]

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
      #"pair" "e1" "e2" : #"exp" "G" (#"prod" "A" "B")
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


Derive prod
       SuchThat (elab_lang_ext (exp_subst++value_subst) prod_def prod)
       As prod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_wf : elab_pfs.

(*Note that because the projections aren't values,
  we can't put the eta law directly at the value level
*)
