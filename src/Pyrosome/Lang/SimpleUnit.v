Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition unit_lang_def : lang :=
  {[l/subst [value_subst]
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
