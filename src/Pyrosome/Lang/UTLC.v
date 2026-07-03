Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition star_type_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| 
      -----------------------------------------------
      #"*" : #"ty"
  ]
  ]}.
Definition star_type_injectivity :=
  [("exp", ["A"; "G"]); ("wkn", ["A"; "G"]); ("forget", ["G"]);
   ("exp_subst", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]);
   ("sub", ["G'"; "G"]); ("val_subst", ["A"; "G"]); ("cmp", ["G3"; "G1"]);
   ("val", ["A"; "G"]); ("hd", ["A"; "G"]); ("ret", ["v"; "A"; "G"]);
   ("ext", ["A"; "G"]); ("id", ["G"])].

Definition star_type :=
  Eval vm_compute in
    (infer_lang_ext_simple (exp_subst++value_subst) star_type_def
       star_type_injectivity).

Lemma star_type_wf : wf_lang_ext (exp_subst++value_subst) star_type.
Proof. compute_wf_lang. Qed.
#[local] Definition star_type_entry := lang_entry star_type_wf.
#[export] Hint Resolve star_type_entry : wf_lang_db.

Definition error_t_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| "G" : #"env",
      "t" : #"ty"
      -----------------------------------------------
      #"Error" "t" : #"exp" "G" "t"
  ]
  ]}.
Definition error_t_injectivity :=
  [("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("exp", ["A"; "G"]);
   ("wkn", ["A"; "G"]); ("forget", ["G"]); ("Error", ["t"; "G"]);
   ("val_subst", ["A"; "G"]); ("val", ["A"; "G"]); ("ext", ["A"; "G"]);
   ("exp_subst", ["A"; "G"]); ("id", ["G"]); ("sub", ["G'"; "G"]);
   ("hd", ["A"; "G"]); ("cmp", ["G3"; "G1"]); ("ret", ["v"; "A"; "G"])].

Definition error_t :=
  Eval vm_compute in
    (infer_lang_ext_simple (exp_subst++value_subst) error_t_def
       error_t_injectivity).

Lemma error_t_wf : wf_lang_ext (exp_subst++value_subst) error_t.
Proof. compute_wf_lang. Qed.
#[local] Definition error_t_entry := lang_entry error_t_wf.
#[export] Hint Resolve error_t_entry : wf_lang_db.

Definition utlc_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*"
      -----------------------------------------------
      #"ulambda" "e" : #"val" "G" (#"*")
  ];
  [:| "G" : #"env",
      "e" : #"exp" "G" #"*", 
      "e'" : #"exp" "G" #"*"
      -----------------------------------------------
      #"uapp" "e" "e'" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "v" : #"val" "G" #"*"
      ----------------------------------------------- ("UTLC-beta")
      #"uapp" (#"ret" (#"ulambda" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" "G" #"*"
  ]
  ]}.

Definition utlc_injectivity :=
  [("exp", ["A"; "G"]); ("exp_subst", ["A"; "G"]); ("hd", ["A"; "G"]);
   ("ulambda", ["e"; "G"]); ("id", ["G"]); ("cmp", ["G3"; "G1"]);
   ("forget", ["G"]); ("ext", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]);
   ("val_subst", ["A"; "G"]); ("ret", ["v"; "A"; "G"]); ("sub", ["G'"; "G"]);
   ("val", ["A"; "G"]); ("uapp", ["e'"; "e"; "G"]); ("wkn", ["A"; "G"])].

Definition utlc :=
  Eval vm_compute in
    (infer_lang_ext_simple (star_type ++ exp_subst ++ value_subst) utlc_def
       utlc_injectivity).

Lemma utlc_wf : wf_lang_ext (star_type ++ exp_subst ++ value_subst) utlc.
Proof. compute_wf_lang. Qed.
#[local] Definition utlc_entry := lang_entry utlc_wf.
#[export] Hint Resolve utlc_entry : wf_lang_db.
