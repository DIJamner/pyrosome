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
  {[l/subst
  [:|
     -----------------------------------------------
      #"unit" : #"ty"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"tt" : #"val" "G" #"unit"
    ]
  ]}.

Derive unit_lang
       SuchThat (elab_lang_ext value_subst unit_lang_def unit_lang)
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
       SuchThat (elab_lang_ext (unit_lang ++ value_subst) unit_eta_def unit_eta)
       As unit_eta_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_eta_wf : elab_pfs.
