Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst Matches.
Import Core.Notations.

Require Coq.derive.Derive.

Definition unit_lang_def : lang :=
  {[l
  [:|
     -----------------------------------------------
      #"unit" : #"ty"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"tt" : #"val" "G" #"unit"
    ];
  [:= "G" : #"env",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("tt_subst")
      #"val_subst" "g" #"tt" = #"tt"
      : #"val" "G'" #"unit"
  ]
  ]}.


Derive unit_lang
       SuchThat (Pre.elab_lang value_subst unit_lang_def unit_lang)
       As unit_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_wf : elab_pfs.

Definition unit_eta_def :lang :=
  {[l [:= "G" : #"env",
       "v" : #"val" "G" #"unit"
      ----------------------------------------------- ("unit eta")
      "v" = #"tt"
      : #"val" "G" #"unit"
  ] ]}.


Derive unit_eta
       SuchThat (Pre.elab_lang (unit_lang ++ value_subst) unit_eta_def unit_eta)
       As unit_eta_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_eta_wf : elab_pfs.
