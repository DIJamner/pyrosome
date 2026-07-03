From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils GallinaHintDb.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVCPS.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.

Notation compiler := (compiler string).

Definition let_lang_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" "A",
      "e'" : #"exp" (#"ext" "G" "A") "B"
      -----------------------------------------------
      #"let" "e" "e'" : #"exp" "G" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" "A",
      "e" : #"exp" (#"ext" "G" "A") "B"
      ----------------------------------------------- ("eval let")
      #"let" (#"ret" "v") "e"
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" "G" "B"
  ] ]}.

Definition let_lang_injectivity :=
  [("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("wkn", ["A"; "G"]);
   ("forget", ["G"]); ("sub", ["G'"; "G"]); ("ext", ["A"; "G"]);
   ("let", ["e'"; "e"; "B"; "A"; "G"]); ("exp", ["A"; "G"]); ("id", ["G"]);
   ("hd", ["A"; "G"]); ("val_subst", ["A"; "G"]); ("ret", ["v"; "A"; "G"]);
   ("val", ["A"; "G"]); ("cmp", ["G3"; "G1"]); ("exp_subst", ["A"; "G"])].

Definition let_lang :=
  Eval vm_compute in
    (infer_lang_ext_simple (exp_subst++value_subst) let_lang_def
       let_lang_injectivity).

Lemma let_lang_wf : wf_lang_ext (exp_subst++value_subst) let_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition let_entry := lang_entry let_lang_wf.
#[export] Hint Resolve let_entry : wf_lang_db.

Definition let_cps_def : compiler :=
  match # from (let_lang) with
  | {{e #"let" "G" "A" "B" "e" "e'"}} =>
    bind_k 1 (var "e") (var "A")
    {{e#"blk_subst" (#"snoc" (#"snoc" {wkn_n 2} #"hd") {ovar 1}) "e'"}}
  end.

Derive let_cps
       in (elab_preserving_compiler cps_subst
                                          (cps_lang ++ block_subst ++ value_subst)
                                          let_cps_def
                                          let_cps
                                          let_lang)
       as let_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition let_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving let_cps_preserving).
#[export] Hint Resolve let_cps_entry : preserving_db.
