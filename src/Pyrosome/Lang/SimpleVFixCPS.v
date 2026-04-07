Require Import Datatypes.String Lists.List.
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
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

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

Derive fix_cps_lang
       SuchThat (elab_lang_ext (cps_lang ++ block_subst ++ value_subst) fix_cps_lang_def fix_cps_lang)
       As fix_wf.
Proof. auto_elab. Qed.
#[local] Definition fix_cps_entry := lang_entry (elab_lang_implies_wf fix_wf).
#[export] Hint Resolve fix_cps_entry : wf_lang_db.

Definition fix_cps_def : compiler :=
  match # from (fix_lang) with
  | {{e #"fix" "G" "A" "B" "e"}} =>
    {{e #"fix" (#"prod" "A" (#"neg" "B"))
        (#"pm_pair" #"hd"
          (#"blk_subst" {under (under {{e #"wkn"}})} "e"))}}
  end.

Derive fix_cps
       SuchThat (elab_preserving_compiler (cps++cps_subst)
                                          (fix_cps_lang
                                              ++ cps_prod_lang
                                             ++ cps_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          fix_cps_def
                                          fix_cps
                                          fix_lang)
       As fix_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition fix_cps_cmp_entry :=
  cmp_entry (elab_compiler_implies_preserving fix_cps_preserving).
#[export] Hint Resolve fix_cps_cmp_entry : preserving_db.
