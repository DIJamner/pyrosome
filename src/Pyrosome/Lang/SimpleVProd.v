Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.Resolution Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference Tools.EGraph.InjRuleGen
  Tools.EGraph.Automation.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
Import Core.Notations.

From Stdlib Require derive.Derive.

Definition prod_def : lang :=
  {[l/subst [exp_subst++value_subst]

  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"prod" "A" "B" : #"ty"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e1" : #"exp" "G" "A",
      "e2" : #"exp" "G" "B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"exp" "G" (#"prod" "A" "B")
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      -----------------------------------------------
      #"pair_val" "v1" "v2" : #"val" "G" (#"prod" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".1" "e" : #"exp" "G" "A"
   ];     
    [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".2" "e" : #"exp" "G" "B"
    ];
     (*TODO: autogenerate somehow *)
     [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" "A",
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("ret_pair")
      #"pair" (#"ret" "v") (#"ret" "v'")
      = #"ret" (#"pair_val" "v" "v'")
      : #"exp" "G" (#"prod" "A" "B")
     ]; 
  [:="G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      ----------------------------------------------- ("project 1")
      #".1" (#"ret" (#"pair_val" "v1" "v2"))
      = #"ret" "v1"
      : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      ----------------------------------------------- ("project 2")
      #".2" (#"ret" (#"pair_val" "v1" "v2"))
      = #"ret" "v2"
      : #"exp" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
      ----------------------------------------------- ("prod_eta")
      #"ret" "v"
      = #"pair" (#".1" (#"ret" "v")) (#".2" (#"ret" "v"))
      : #"exp" "G" (#"prod" "A" "B")
     ]
    ]}.

Definition prod_injectivity :=
  [("snoc", ["v"; "A"; "g"; "G'"; "G"]); (".2", ["e"; "B"; "A"; "G"]);
   ("exp_subst", ["A"; "G"]); ("pair", ["e2"; "e1"; "B"; "A"; "G"]);
   ("wkn", ["A"; "G"]); ("forget", ["G"]); ("val", ["A"; "G"]);
   ("exp", ["A"; "G"]); ("val_subst", ["A"; "G"]);
   ("ext", ["A"; "G"]); ("ret", ["v"; "A"; "G"]);
   ("id", ["G"]); ("pair_val", ["v2"; "v1"; "B"; "A"; "G"]);
   ("prod", ["B"; "A"]); (".1", ["e"; "B"; "A"; "G"]);
   ("hd", ["A"; "G"]); ("sub", ["G'"; "G"]);
   ("cmp", ["G3"; "G1"])].

Definition prod :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 (exp_subst++value_subst) prod_def.

Lemma prod_wf : wf_lang_ext (exp_subst++value_subst) prod.
Proof. compute_wf_lang. Qed.
#[local] Definition prod_entry := lang_entry prod_wf.
#[export] Hint Resolve prod_entry : wf_lang_db.

(*Note that because the projections aren't values,
  we can't put the eta law directly at the value level
*)
