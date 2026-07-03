From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleUnit.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.


Notation compiler := (compiler string).

Definition prod_cc_def : lang :=
  {[l/subst [cps_prod_lang ++ block_subst ++value_subst]
  [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
       -----------------------------------------------
       #".1" "v" : #"val" "G" "A"
  ];
  [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
       -----------------------------------------------
       #".2" "v" : #"val" "G" "B"
  ];
   [:= "G" : #"env", "A" : #"ty",
      "g" : #"val" "G" "A",
      "B" : #"ty",
      "v" : #"val" "G" "B"
      ----------------------------------------------- ("proj 1")
      #".1" (#"pair" "g" "v") = "g" : #"val" "G" "A"
  ];
  [:= "G" : #"env", "A" : #"ty",
      "g" : #"val" "G" "A",
      "B" : #"ty",
      "v" : #"val" "G" "B"
      ----------------------------------------------- ("proj 2")
      #".2" (#"pair" "g" "v") = "v" : #"val" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
      ----------------------------------------------- ("negative pair eta")
      #"pair" (#".1" "v") (#".2" "v") = "v" : #"val" "G" (#"prod" "A" "B")
  ]]}.


Definition prod_cc_injectivity :=
  [("pm_pair", ["e"; "v"; "B"; "A"; "G"]); ("blk", ["G"]); (".1", ["v"; "B"; "A"; "G"]); ("wkn", ["A"; "G"]);
   ("val_subst", ["A"; "G"]); ("forget", ["G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("hd", ["A"; "G"]); ("val", ["A"; "G"]);
   ("blk_subst", ["G"]); ("ext", ["A"; "G"]); (".2", ["v"; "B"; "A"; "G"]); ("id", ["G"]); ("sub", ["G'"; "G"]);
   ("prod", ["B"; "A"]); ("pair", ["e2"; "e1"; "B"; "A"; "G"]); ("cmp", ["G3"; "G1"])].

Definition prod_cc :=
  Eval vm_compute in
    (infer_lang_ext_simple (cps_prod_lang ++ block_subst ++value_subst) prod_cc_def prod_cc_injectivity).

Lemma prod_cc_wf : wf_lang_ext (cps_prod_lang ++ block_subst ++value_subst) prod_cc.
Proof. compute_wf_lang. Qed.
#[local] Definition prod_cc_entry := lang_entry prod_cc_wf.
#[export] Hint Resolve prod_cc_entry : wf_lang_db.

Definition cc_lang_def : lang :=
  {[l/subst [prod_cc++cps_prod_lang ++ block_subst ++value_subst]
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"ext" #"emp" (#"prod" "A" "B")),
      "v" : #"val" "G" "A"
      -----------------------------------------------
      #"closure" "B" "e" "v" : #"val" "G" (#"neg" "B")
   ];
   [:| "G" : #"env",
       "A" : #"ty",
       "v1" : #"val" "G" (#"neg" "A"),
       "v2" : #"val" "G" "A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" "G"
   ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"ext" #"emp" (#"prod" "A" "B")),
      "v" : #"val" "G" "A",
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"closure" "B" "e" "v") "v'"
      = #"blk_subst" (#"snoc" #"forget" (#"pair" "v" "v'")) "e"
      : #"blk" "G"
  ];
  [:= "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" (#"ext" #"emp" "A") (#"neg" "B")
      ----------------------------------------------- ("clo_eta")
      #"closure" "B"
        (#"jmp" (#"val_subst" (#"snoc" #"wkn" (#".1" #"hd")) "v") (#".2" #"hd"))
        #"hd"
      = "v"
      : #"val" (#"ext" #"emp" "A") (#"neg" "B")
  ]]}.

Definition cc_lang_injectivity :=
  [("neg", ["A"]); ("val", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("prod", ["B"; "A"]); ("blk_subst", ["G"]);
   ("pm_pair", ["e"; "v"; "B"; "A"; "G"]); ("cmp", ["G3"; "G1"]); (".1", ["v"; "B"; "A"; "G"]); ("pair", ["e2"; "e1"; "B"; "A"; "G"]);
   ("jmp", ["v2"; "v1"; "A"; "G"]); ("ext", ["A"; "G"]); ("wkn", ["A"; "G"]); ("sub", ["G'"; "G"]); ("blk", ["G"]);
   ("hd", ["A"; "G"]); ("forget", ["G"]); ("id", ["G"]); ("closure", ["v"; "e"; "B"; "A"; "G"]); (".2", ["v"; "B"; "A"; "G"]);
   ("val_subst", ["A"; "G"])].

Definition cc_lang :=
  Eval vm_compute in
    (infer_lang_ext_simple (prod_cc ++ cps_prod_lang
                             ++ block_subst ++value_subst)
                               cc_lang_def
                               cc_lang_injectivity).

Lemma cc_lang_wf : wf_lang_ext (prod_cc ++ cps_prod_lang
                             ++ block_subst ++value_subst) cc_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition cc_entry := lang_entry cc_lang_wf.
#[export] Hint Resolve cc_entry : wf_lang_db.

Definition subst_cc_def : compiler :=
  match # from (block_subst ++ value_subst) with
  | {{s #"env" }} => {{s #"ty"}}
  | {{s #"val" "G" "B"}} => {{s #"val" (#"ext" #"emp" "G") "B"}}
  | {{s #"blk" "G"}} => {{s #"blk" (#"ext" #"emp" "G")}}
  | {{s #"sub" "G" "G'"}} => {{s #"val" (#"ext" #"emp" "G") "G'"}}
  | {{e #"cmp" "G" "G'" "A" "g" "g'"}} =>
    {{e #"val_subst" (#"snoc" #"wkn" "g") "g'"}}
  | {{e #"emp"}} => {{e#"unit"}}
  | {{e #"forget"}} => {{e# "tt"}}
  | {{e #"ext" "A" "B" }} => {{e #"prod" "A" "B"}}
  | {{e #"snoc" "G" "G'""g" "A" "v"}} =>
    {{e #"pair" "g" "v"}}
  | {{e #"id" "G"}} => {{e #"hd"}}
  | {{e #"hd" "G" "A"}} => {{e #".2" #"hd"}}
  | {{e #"wkn" "G" "A"}} => {{e #".1" #"hd"}}
  | {{e #"val_subst" "G" "G'" "g" "A" "v"}} =>
    {{e #"val_subst" (#"snoc" #"wkn" "g") "v"}}
  | {{e #"blk_subst" "G" "G'" "g" "e"}} =>
    {{e #"blk_subst" (#"snoc" #"wkn" "g") "e"}}
  end.

Derive subst_cc
       in (elab_preserving_compiler []
                                          (unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          subst_cc_def
                                          subst_cc
                                          (block_subst++value_subst))
       as subst_cc_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition subst_cc_entry :=
  cmp_entry (elab_compiler_implies_preserving subst_cc_preserving).
#[export] Hint Resolve subst_cc_entry : preserving_db.

(*TODO: redo for positive products *)
Definition prod_cc_compile_def : compiler :=
  match # from cps_prod_lang with
  | {{e #"pm_pair" "G" "A" "B" "v" "e"}} =>
    {{e #"blk_subst"
        (#"snoc" #"wkn" (#"pair" (#"pair" {ovar 0} (#".1" "v")) (#".2" "v")))
        "e"}}
  end.


(*TODO: move to value_subst? could conflict w/ cmp_forget
  not currently used
*)
(*TODO: generalize? reverse for tactics?*)
Definition forget_eq_wkn_def : lang :=
  {[l
      [:= "A" : #"ty"
         ----------------------------------------------- ("wkn_emp_forget")
         #"forget" = #"wkn"
         : #"sub" (#"ext" #"emp" "A") #"emp"
      ]
  ]}.
Definition forget_eq_wkn_injectivity :=
  [("wkn", ["A"; "G"]); ("cmp", ["G3"; "G1"]); ("ext", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("val", ["A"; "G"]);
   ("forget", ["G"]); ("id", ["G"]); ("hd", ["A"; "G"]); ("sub", ["G'"; "G"]); ("val_subst", ["A"; "G"])].

Definition forget_eq_wkn :=
  Eval vm_compute in
    (infer_lang_ext_simple value_subst forget_eq_wkn_def forget_eq_wkn_injectivity).

Lemma forget_eq_wkn_wf : wf_lang_ext value_subst forget_eq_wkn.
Proof. compute_wf_lang. Qed.
#[local] Definition forget_eq_wkn_entry :=
  lang_entry forget_eq_wkn_wf.
#[export] Hint Resolve forget_eq_wkn_entry : wf_lang_db.

Definition cc_bidirectional_rules :=
  ["forget_eq_wkn"; "clo_eta"; "id_emp_forget"; "cmp_snoc"].

Derive prod_cc_compile
       in (elab_preserving_compiler subst_cc
                                          ( unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          prod_cc_compile_def
                                          prod_cc_compile
                                          cps_prod_lang)
       as prod_cc_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition prod_cc_cmp_entry :=
  cmp_entry (elab_compiler_implies_preserving prod_cc_preserving).
#[export] Hint Resolve prod_cc_cmp_entry : preserving_db.

Definition cc_def : compiler :=
  match # from (cps_lang) with
  | {{e #"neg" "A" }} => {{e #"neg" "A"}}
  | {{e #"cont" "G" "A" "e"}} =>
    {{e #"closure" "A" "e" #"hd"}}
  | {{e #"jmp" "G" "A" "v1" "v2"}} =>
    {{e #"jmp" "v1" "v2" }}
  end.
 
Derive cc
       in (elab_preserving_compiler (prod_cc_compile++subst_cc)
                                          (cc_lang
                                             ++ forget_eq_wkn
                                             ++ unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          cc_def
                                          cc
                                          cps_lang)
       as cc_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition cc_cmp_entry :=
  cmp_entry (elab_compiler_implies_preserving cc_preserving).
#[export] Hint Resolve cc_cmp_entry : preserving_db.

