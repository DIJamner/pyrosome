From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.InjRuleGen
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.

Notation compiler := (compiler string).

Definition fix_cps_lang_def : lang :=
  {[l/subst [cps_lang ++ block_subst ++ value_subst]
  [:| "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" (#"ext" (#"ext" "G" (#"neg" "A")) "A")
      -----------------------------------------------
      #"fix" "A" "e" : #"val" "G" (#"neg" "A")
   ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" (#"ext" (#"ext" "G" (#"neg" "A")) "A"),
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("fix_beta")
      #"jmp" (#"fix" "A" "e") "v"
      = #"blk_subst" (#"snoc" (#"snoc" #"id" (#"fix" "A" "e")) "v") "e"
      : #"blk" "G"
  ] ]}.

Definition fix_cps_lang_injectivity :=
  [("ext", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("wkn", ["A"; "G"]);
   ("sub", ["G'"; "G"]); ("jmp", ["v2"; "v1"; "A"; "G"]); ("val_subst", ["A"; "G"]);
   ("neg", ["A"]); ("id", ["G"]); ("hd", ["A"; "G"]); ("cont", ["e"; "A"; "G"]);
   ("val", ["A"; "G"]); ("fix", ["e"; "A"; "G"]); ("forget", ["G"]); ("blk", ["G"]);
   ("cmp", ["G3"; "G1"]); ("blk_subst", ["G"])].

(* Saturation fuel 2: on this base (cps_lang ++ block_subst ++ value_subst) the
   injectivity e-graph explodes at fuel >= 3 (OOM ~6GB); fuel 2 already yields
   every schema of the explicit [fix_cps_lang_injectivity] list. *)
Definition fix_cps_lang :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 2 100 (cps_lang ++ block_subst ++ value_subst)
      fix_cps_lang_def.

Lemma fix_wf : wf_lang_ext (cps_lang ++ block_subst ++ value_subst) fix_cps_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition fix_cps_entry := lang_entry fix_wf.
#[export] Hint Resolve fix_cps_entry : wf_lang_db.

Definition fix_cps_def : compiler :=
  match # from (fix_lang) with
  | {{e #"fix" "G" "A" "B" "e"}} =>
    {{e #"fix" (#"prod" "A" (#"neg" "B"))
        (#"pm_pair" #"hd"
          (#"blk_subst" {under (under {{e #"wkn"}})} "e"))}}
  end.

Derive fix_cps
       in (elab_preserving_compiler (cps++cps_subst)
                                          (fix_cps_lang
                                              ++ cps_prod_lang
                                             ++ cps_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          fix_cps_def
                                          fix_cps
                                          fix_lang)
       as fix_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition fix_cps_cmp_entry :=
  cmp_entry (elab_compiler_implies_preserving fix_cps_preserving).
#[export] Hint Resolve fix_cps_cmp_entry : preserving_db.
