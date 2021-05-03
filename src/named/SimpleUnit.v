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

Definition unit_lang :=
  [
  [:> "G" : #"env",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("tt_subst")
      #"val_subst" %"g" #"tt" = #"tt"
      : #"val" %"G'" #"unit"
  ];
  (*TODO: design choice: I could add an alalogous expression,
    and I might autogenerate one at some point, 
    but it would be equal to ret tt, so I won't for now
   *)
  [:| "G" : #"env"
      -----------------------------------------------
      #"tt" : #"val" %"G" #"unit"
    ];
  [:|
     -----------------------------------------------
      #"unit" : #"ty"
  ]]%arule.


Derive unit_elab
       SuchThat (Pre.elab_lang subst_elab unit_lang unit_elab)
       As unit_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_wf : elab_pfs.

Definition unit_eta :=
  [[:> "G" : #"env",
       "v" : #"val" %"G" #"unit"
      ----------------------------------------------- ("unit eta")
      %"v" = #"tt"
      : #"val" %"G" #"unit"
  ]]%arule.


Derive unit_eta_elab
       SuchThat (Pre.elab_lang (unit_elab ++ subst_elab) unit_eta unit_eta_elab)
       As unit_eta_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_eta_wf : elab_pfs.
