
Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst SimpleVSTLC.
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

Definition fix_injectivity :=
  [("fix", ["B"; "A"; "G"])].

Definition fix_lang :=
  Eval vm_compute in
    (infer_lang_ext_simple (stlc++exp_subst++value_subst) fix_def
       (fix_injectivity++stlc_injectivity
          ++exp_subst_injectivity++value_subst_injectivity)).

Lemma fix_wf : wf_lang_ext (stlc++exp_subst++value_subst) fix_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition fix_entry := lang_entry fix_wf.
#[export] Hint Resolve fix_entry : wf_lang_db.

