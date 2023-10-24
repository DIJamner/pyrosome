Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.LinearSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition linear_stlc_def : lang :=
  {[l/lin_subst
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"lolli" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" "G" "A") "B"
       -----------------------------------------------
       #"linear_lambda" "A" "e" : #"val" "G" (#"lolli" "A" "B")
  ];
  [:| "G" : #"env",
      "H" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"lolli" "A" "B"),
       "e'" : #"exp" "H" "A"
       -----------------------------------------------
       #"linear_app" "e" "e'" : #"exp" (#"conc" "G" "H") "B"
  ];
  [:= "G" : #"env",
      "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("Linear-STLC-beta")
      #"linear_app" (#"ret" (#"linear_lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"csub" (#"id" "G") (#"vsub" "v")) "e"
      : #"exp" (#"conc" "G" "H") "B"
  ]
  ]}.

#[export] Hint Resolve (inst_for_db "lolli") : injective_con.

(*
Definition linear_stlc_def : lang :=
  {[l (* /lin_subst *)
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"lolli" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" "G" "A") "B"
       -----------------------------------------------
       #"linear_lambda" "A" "e" : #"val" "G" (#"lolli" "A" "B")
  ];
  [:| "G" : #"env",
      "H" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"lolli" "A" "B"),
       "e'" : #"exp" "H" "A"
       -----------------------------------------------
       #"linear_app" "e" "e'" : #"exp" (#"conc" "G" "H") "B"
  ];
  [:= "G" : #"env",
      "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("Linear-STLC-beta")
      #"linear_app" (#"ret" (#"linear_lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" (#"conc" "G" "H") "B"
  ];

  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"lolli" "A" "B"),
      "e'" : #"exp" "H" "A",
      "G'" : #"env", "H'" : #"env",
      "g" : #"sub" "G'" "G",
      "h" : #"sub" "H'" "H"
      ----------------------------------------------- ("linear_app-subst")
      #"exp_subst" (#"csub" "g" "h") (#"linear_app" "e" "e'")
       = #"linear_app" (#"exp_subst" "g" "e") (#"exp_subst" "h" "e'")
       : #"exp" (#"conc" "G'" "H'") "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("linear_lambda-subst")
      #"val_subst" "g" (#"linear_lambda" "A" "e")
      = #"linear_lambda" "A" (#"exp_subst" (#"snoc" "g" #"hd") "e")
      : #"val" "G'" (#"lolli" "A" "B")
  ]
  ]}.
*)

Compute linear_stlc_def.

Derive linear_stlc
       SuchThat (elab_lang_ext (linear_exp_subst++linear_value_subst) linear_stlc_def linear_stlc)
       As linear_stlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve linear_stlc_wf : elab_pfs.
