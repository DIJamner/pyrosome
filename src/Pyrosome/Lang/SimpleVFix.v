Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Lang.SimpleVSTLC.
Import Core.Notations.

Require Coq.derive.Derive.

Definition fix_def : lang :=
  {[l/subst [stlc++exp_subst++value_subst]
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" (#"ext" "G" (#"->" "A" "B")) "A") "B"
       -----------------------------------------------
       #"fix" "A" "e" : #"val" "G" (#"->" "A" "B")
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" (#"ext" "G" (#"->" "A" "B")) "A") "B",
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("fix_beta")
      #"app" (#"ret" (#"fix" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" (#"snoc" #"id" (#"fix" "A" "e")) "v") "e"
      : #"exp" "G" "B"
  ]
  ]}.

Derive fix_lang
       SuchThat (elab_lang_ext (stlc++exp_subst++value_subst) fix_def fix_lang)
       As fix_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve fix_wf : elab_pfs.

