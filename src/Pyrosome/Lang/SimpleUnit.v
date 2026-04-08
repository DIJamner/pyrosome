Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Resolution Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
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
    (infer_lang_ext_simple (exp_subst++value_subst) unit_lang_def
       (unit_injectivity++exp_subst_injectivity++value_subst_injectivity)).

Lemma unit_wf : wf_lang_ext value_subst unit_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition unit_entry := lang_entry unit_wf.
#[export] Hint Resolve unit_entry : wf_lang_db.

Definition unit_eta_def :lang :=
  {[l [:= "G" : #"env",
       "v" : #"val" "G" #"unit"
      ----------------------------------------------- ("unit eta")
      "v" = #"tt"
      : #"val" "G" #"unit"
  ] ]}.


Definition unit_eta :=
  Eval vm_compute in
    (infer_lang_ext_simple (unit_lang++exp_subst++value_subst) unit_eta_def
       (unit_injectivity++exp_subst_injectivity++value_subst_injectivity)).


Lemma unit_eta_wf : wf_lang_ext (unit_lang ++ value_subst) unit_eta.
Proof. compute_wf_lang. Qed.
#[local] Definition unit_eta_entry := lang_entry unit_eta_wf.
#[export] Hint Resolve unit_eta_entry : wf_lang_db.
