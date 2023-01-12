Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers Tools.Matches.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Notation compiler := (compiler string).


Definition fix_cps_lang_def : lang :=
  {[l/subst
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
#[export] Hint Resolve fix_wf : elab_pfs.



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
#[export] Hint Resolve fix_cps_preserving : elab_pfs.
