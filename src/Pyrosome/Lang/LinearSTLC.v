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
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" (#"conc" "G" "H") "B"
  ]
  ]}.

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

Derive linear_stlc
       SuchThat (elab_lang_ext (linear_exp_subst++linear_value_subst) linear_stlc_def linear_stlc)
       As linear_stlc_wf.
Proof.
  setup_elab_lang.
  - (first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  - (first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -  break_elab_rule.
  all: try now term_refl.
  unfold Model.eq_term; compute_eq_compilation.
  by_reduction. (*TODO: why isn't this solved by automation?*)
  
  - (first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  - (first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  - (first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
     cleanup_auto_elab ]).
    Unshelve.
    all: repeat t'.
Qed.
#[export] Hint Resolve linear_stlc_wf : elab_pfs.
