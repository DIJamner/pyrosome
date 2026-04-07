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
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS SimpleVCC SimpleUnit.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Definition fix_cc_lang_def : lang :=
  {[l/subst [(cc_lang++prod_cc ++ cps_prod_lang ++ block_subst ++value_subst)]
  [:| "G" : #"env",
      "B" : #"ty",
      "vf" : #"val" "G" (#"neg" (#"prod" (#"neg" "B") "B"))
      -----------------------------------------------
      #"fix" "vf" : #"val" "G" (#"neg" "B")
   ];
  [:= "G" : #"env",
      "B" : #"ty",
      "v" : #"val" "G" (#"neg" (#"prod" (#"neg" "B") "B")),
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("fix_beta")
      #"jmp" (#"fix" "v") "v'"
      = #"jmp" "v" (#"pair" (#"fix" "v") "v'")
      : #"blk" "G"
  ]]}.

Derive fix_cc_lang
       SuchThat (elab_lang_ext (cc_lang++prod_cc ++ cps_prod_lang ++ block_subst ++value_subst)
                               fix_cc_lang_def
                               fix_cc_lang)
       As fix_cc_wf.
Proof. auto_elab. Qed.
#[local] Definition fix_cc_entry := lang_entry (elab_lang_implies_wf fix_cc_wf).
#[export] Hint Resolve fix_cc_entry : wf_lang_db.

Definition fix_cc_def : compiler :=
  match # from (fix_cps_lang) with
  | {{e #"fix" "G" "A" "e"}} =>
    {{e #"fix" (#"closure" (#"prod" (#"neg" "A") "A")
                 (#"blk_subst" (#"snoc" #"forget"
                                 (#"pair"
                                   (#"pair" (#".1" #"hd")
                                     (#".1" (#".2" #"hd")))
                                   (#".2" (#".2" #"hd"))))
                                 "e") #"hd")}}
  end.

Derive fix_cc
       SuchThat (elab_preserving_compiler (cc++prod_cc_compile++subst_cc)
                                          (fix_cc_lang
                                             ++ cc_lang
                                             ++ forget_eq_wkn
                                             ++ unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          fix_cc_def
                                          fix_cc
                                          fix_cps_lang)
       As fix_cc_preserving.
Proof.
  auto_elab_compiler' (rule_named_in cc_bidirectional_rules) empty_inj_rules.
Qed.
#[local] Definition fix_cc_cmp_entry :=
  cmp_entry (elab_compiler_implies_preserving fix_cc_preserving).
#[export] Hint Resolve fix_cc_cmp_entry : preserving_db.
