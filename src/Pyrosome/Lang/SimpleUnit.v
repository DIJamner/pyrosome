Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Tools.EGraph.TypeInference.
Import Core.Notations.

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

Definition unit_injectivity := [("tt", ["G"])].

Definition unit_lang :=
  Eval vm_compute in
    (infer_lang_ext (exp_subst++value_subst) unit_lang_def
       (unit_injectivity++exp_subst_injectivity++value_subst_injectivity)).

Lemma unit_wf : elab_lang_ext value_subst unit_lang_def unit_lang.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_wf : elab_pfs.

Definition unit_eta_def :lang :=
  {[l [:= "G" : #"env",
       "v" : #"val" "G" #"unit"
      ----------------------------------------------- ("unit eta")
      "v" = #"tt"
      : #"val" "G" #"unit"
  ] ]}.


Definition unit_eta :=
  Eval vm_compute in
    (infer_lang_ext (unit_lang++exp_subst++value_subst) unit_eta_def
       (unit_injectivity++exp_subst_injectivity++value_subst_injectivity)).


Lemma unit_eta_wf : elab_lang_ext (unit_lang ++ value_subst) unit_eta_def unit_eta.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_eta_wf : elab_pfs.
