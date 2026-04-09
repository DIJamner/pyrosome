Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.Resolution Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
Import Core.Notations.

(* TODO: change the rules of this language to look like the rules
   for the sum type in TAPL.
*)
Definition sum_def : lang :=
  {[l/subst [exp_subst++value_subst]

  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"sum" "A" "B" : #"ty"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" "A"
      -----------------------------------------------
      #"inl" "e" : #"exp" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" "B"
      -----------------------------------------------
      #"inr" "e" : #"exp" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" "A"
      -----------------------------------------------
      #"inl_val" "v" : #"val" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" "B"
      -----------------------------------------------
      #"inr_val" "v" : #"val" "G" (#"sum" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "e" : #"exp" "G" (#"sum" "A" "B"),
      "case_l" : #"exp" (#"ext" "G" "A") "C",
      "case_r" : #"exp" (#"ext" "G" "B") "C"
      -----------------------------------------------
      #"case" "e" "case_l" "case_r" : #"exp" "G" "C"
  ];
     (*TODO: autogenerate somehow *)
     [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("retl")
      #"inl" (#"ret" "v")
      = #"ret" (#"inl_val" "v" )
      : #"exp" "G" (#"sum" "A" "B")
     ]; 
     [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" "B"
      ----------------------------------------------- ("retr")
      #"inr" (#"ret" "v")
      = #"ret" (#"inr_val" "v" )
      : #"exp" "G" (#"sum" "A" "B")
     ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "v" : #"val" "G" "A",
      "case_l" : #"exp" (#"ext" "G" "A") "C",
      "case_r" : #"exp" (#"ext" "G" "B") "C"
      ----------------------------------------------- ("case_l ret")
      #"case" (#"ret" (#"inl_val" "v")) "case_l" "case_r"
      = #"exp_subst" (#"snoc" #"id" "v") "case_l"
      : #"exp" "G" "C"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "v" : #"val" "G" "B",
      "case_l" : #"exp" (#"ext" "G" "A") "C",
      "case_r" : #"exp" (#"ext" "G" "B") "C"
      ----------------------------------------------- ("case_r ret")
      #"case" (#"ret" (#"inr_val" "v")) "case_l" "case_r"
      = #"exp_subst" (#"snoc" #"id" "v") "case_r"
      : #"exp" "G" "C"
  ]
  ]}.

Definition sum_injectivity :=
  [("case",["C";"G"]);
   ("inr_val",["v";"B";"A";"G"]);("inl_val",["v";"B";"A";"G"]);
   ("inr",["e";"B";"A";"G"]);("inl",["e";"B";"A";"G"]);("sum", ["B"; "A"])].

Definition sum :=
  Eval vm_compute in
    (infer_lang_ext_simple (exp_subst++value_subst) sum_def
       (sum_injectivity++exp_subst_injectivity++value_subst_injectivity)).

Lemma sum_wf : wf_lang_ext (exp_subst++value_subst) sum.
Proof. compute_wf_lang. Qed.
#[local] Definition sum_entry := lang_entry sum_wf.
#[export] Hint Resolve sum_entry : wf_lang_db.

(*Note that because the projections aren't values,
  we can't put the eta law directly at the value level
*)

