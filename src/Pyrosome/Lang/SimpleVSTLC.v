Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.


Definition stlc_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" "G" "A") "B"
       -----------------------------------------------
       #"lambda" "A" "e" : #"val" "G" (#"->" "A" "B")
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"->" "A" "B"),
       "e'" : #"exp" "G" "A"
       -----------------------------------------------
       #"app" "e" "e'" : #"exp" "G" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("STLC-beta")
      #"app" (#"ret" (#"lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" "G" "B"
  ]
  ]}.

Compute stlc_def.

Derive stlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_def stlc)
       As stlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_wf : elab_pfs.


