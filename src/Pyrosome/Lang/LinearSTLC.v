Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches Tools.Resolution
  Tools.EGraph.TypeInference Tools.EGraph.InjRuleGen
  Tools.EGraph.ComputeWf
  Lang.LinearSubst.
Import Core.Notations.

From Stdlib Require derive.Derive.

Local Notation "'ext' e t" := ({{e #"conc" {e} (#"only" {t} )}})
    (in custom term at level 40, e custom arg at level 0, t custom arg at level 0).

Definition linear_stlc_def : lang :=
  {[l/lin_subst
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"lolli" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (ext "G" "A") "B"
       -----------------------------------------------
       #"linear_lambda" "A" "e" : #"val" "G" (#"lolli" "A" "B")
  ];
  [:| "G" : #"env",
      "H" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"lolli" "A" "B"),
       "e'" : #"exp" "H" "A"
       -----------------------------------------------
       #"linear_app" "e" "e'" : #"exp" (#"conc" "G" "H") "B"
  ];
  [:= "G" : #"env",
      "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (ext "G" "A") "B",
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("LSTLC-beta")
      #"linear_app" (#"ret" (#"linear_lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"csub" (#"id" "G") (#"vsub" "v")) "e"
      : #"exp" (#"conc" "G" "H") "B"
  ]
  ]}.


#[local] Definition lolli_inst_for_db := inst_for_db "lolli".
#[export] Hint Resolve lolli_inst_for_db : injective_con.

(*
Definition linear_stlc_def : lang :=
  {[l (* /lin_subst *)
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"lolli" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" "G" "A") "B"
       -----------------------------------------------
       #"linear_lambda" "A" "e" : #"val" "G" (#"lolli" "A" "B")
  ];
  [:| "G" : #"env",
      "H" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"lolli" "A" "B"),
       "e'" : #"exp" "H" "A"
       -----------------------------------------------
       #"linear_app" "e" "e'" : #"exp" (#"conc" "G" "H") "B"
  ];
  [:= "G" : #"env",
      "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("Linear-STLC-beta")
      #"linear_app" (#"ret" (#"linear_lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" (#"conc" "G" "H") "B"
  ];

  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"lolli" "A" "B"),
      "e'" : #"exp" "H" "A",
      "G'" : #"env", "H'" : #"env",
      "g" : #"sub" "G'" "G",
      "h" : #"sub" "H'" "H"
      ----------------------------------------------- ("linear_app-subst")
      #"exp_subst" (#"csub" "g" "h") (#"linear_app" "e" "e'")
       = #"linear_app" (#"exp_subst" "g" "e") (#"exp_subst" "h" "e'")
       : #"exp" (#"conc" "G'" "H'") "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("linear_lambda-subst")
      #"val_subst" "g" (#"linear_lambda" "A" "e")
      = #"linear_lambda" "A" (#"exp_subst" (#"snoc" "g" #"hd") "e")
      : #"val" "G'" (#"lolli" "A" "B")
  ]
  ]}.
*)

(*
Definition linear_stlc_injectivity :=
  [("only", ["A"]); ("linear_lambda", ["e"; "B"; "A"; "G"]); ("cmp", ["G3"; "G1"]);
   ("id", ["G"]); ("exp_subst", ["A"; "G"]); ("linear_app", ["e'"; "e"; "B"; "A"; "H"; "G"]);
   ("ret", ["v"; "A"; "G"]); ("val_subst", ["A"; "G"]); ("exp", ["A"; "G"]);
   ("exch", ["H"; "G"]); ("vsub", ["v"; "A"; "G"]); ("val", ["A"; "G"]);
   ("sub", ["G'"; "G"]); ("lolli", ["t'"; "t"]); ("hd", ["A"])].*)


(* TODO: can't include the language's rules while debugging the language.
   I actually want this to be incrementally expanded/computed with the language.
 *)
Definition linear_gen_schemas :=
  Eval vm_compute in
    gen_fundep_schemas 10 (linear_exp_subst ++ linear_value_subst).

Definition linear_stlc :=
  Eval vm_compute in
    (infer_lang_ext_simple_gen (linear_exp_subst++linear_value_subst) linear_stlc_def
       (build_general_injection_rules linear_gen_schemas)).

Lemma linear_stlc_wf : wf_lang_ext (linear_exp_subst++linear_value_subst) linear_stlc.
Proof. compute_wf_lang. Qed.
#[local] Definition linear_stlc_entry := lang_entry linear_stlc_wf.
#[export] Hint Resolve linear_stlc_entry : wf_lang_db.
