Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix
     SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS SimpleVCC Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Definition fix_cc_lang_def : lang :=
  {[l
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"ext" #"emp" (#"prod" (#"prod" "A" (#"neg" "B")) "B")),
      "v" : #"val" "G" "A"
      -----------------------------------------------
      #"fix_clo" "B" "e" "v": #"val" "G" (#"neg" "B")
   ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"ext" #"emp" (#"prod" (#"prod" "A" (#"neg" "B")) "B")),
      "v" : #"val" "G" "A",
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("fix_beta")
      #"jmp" (#"fix_clo" "B" "e" "v") "v'"
      = #"blk_subst" (#"snoc" #"forget" (#"pair" (#"pair" "v" (#"fix_clo" "B" "e" "v")) "v'")) "e"
      : #"blk" "G"
  ];
  [:= "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" (#"ext" #"emp" "A") (#"neg" "B")
      ----------------------------------------------- ("fix_clo_eta")
      #"fix_clo" "B"
        (#"jmp" (#"val_subst" (#"snoc" #"wkn" (#".1" (#".1" #"hd"))) "v") (#".2" #"hd"))
        #"hd"
      = "v"
      : #"val" (#"ext" #"emp" "A") (#"neg" "B")
  ];
  [:= "G" : #"env",
     "A" : #"ty",
     "B" : #"ty",
     "e" : #"blk" (#"ext" #"emp" (#"prod" (#"prod" "A" (#"neg" "B")) "B")),
     "v" : #"val" "G" "A",
     "G'" : #"env",
     "g" : #"sub" "G'" "G"
     ----------------------------------------------- ("fix_clo_subst")
     #"val_subst" "g" (#"fix_clo" "B" "e" "v") = #"fix_clo" "B" "e" (#"val_subst" "g" "v")
      : #"val" "G'" (#"neg" "B")
  ]
  ]}.

Derive fix_cc_lang
       SuchThat (Pre.elab_lang (cc_lang++prod_cc ++ cps_prod_lang ++ block_subst ++value_subst)
                               fix_cc_lang_def
                               fix_cc_lang)
       As fix_cc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve fix_cc_wf : elab_pfs.




Definition fix_cc_def : compiler :=
  match # from (fix_cps_lang) with
  | {{e #"fix" "G" "A" "e"}} =>
    {{e #"fix_clo" "A" "e" #"hd"}}
  end.

Require Import SimpleUnit.
 
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
  auto_elab_compiler.
  {
    reduce.
    eapply eq_term_trans.
    eapply eq_term_sym.
    eredex_steps_with fix_cc_lang "fix_clo_eta".
    reduce.
    term_cong.
    term_refl.
    term_refl.
    term_refl.
    {
      compute_eq_compilation.
      term_cong; try term_refl.
      term_cong; try term_refl.
      term_cong; try term_refl.
      term_cong; try term_refl.
      TODO: eta issue: have "fix..." on one side and "hd" on the other
      term_cong; try term_refl.
      term_refl.
    
  cleanup_elab_after
  (reduce;
   eapply eq_term_trans;  
   [eapply eq_term_sym;
   eredex_steps_with cc_lang "fix_clo_eta"|];
   by_reduction).
Qed.
#[export] Hint Resolve cc_preserving : elab_pfs.

Definition fix_cc_def : compiler :=
  match # from (fix_lang) with
  | {{e #"fix" "G" "A" "e"}} =>
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
