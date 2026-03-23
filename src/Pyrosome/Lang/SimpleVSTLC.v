Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
Import Core.Notations.

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

Definition stlc_injectivity :=
  [("app", ["B"; "G"]); ("lambda", ["e";"B"; "A"; "G"]); ("->", ["t'"; "t"])].

Definition stlc :=
  Eval vm_compute in
    (infer_lang_ext_simple (exp_subst++value_subst) stlc_def
       (stlc_injectivity++exp_subst_injectivity++value_subst_injectivity)).

Lemma stlc_wf : wf_lang_ext (exp_subst++value_subst) stlc.
Proof. compute_wf_lang. Qed.

#[local] Definition stlc_entry :=
  lang_entry stlc_wf.
#[export] Hint Resolve stlc_entry : wf_lang_db.
