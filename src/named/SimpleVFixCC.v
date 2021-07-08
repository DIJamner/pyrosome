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
  ];
  (*
  [:= "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" (#"ext" #"emp" "A") (#"neg" "B")
      ----------------------------------------------- ("fix_clo_eta")
      #"fix_clo" "B"
        (#"jmp" (#"val_subst" (#"snoc" #"wkn" (#".1" (#".1" #"hd"))) "v") (#".2" #"hd"))
        #"hd"
      = "v"
      : #"val" (#"ext" #"emp" "A") (#"neg" "B")
  ];*)
  [:= "G" : #"env",
      "B" : #"ty",
      "v" : #"val" "G" (#"neg" (#"prod" (#"neg" "B") "B")),
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("fix_subst")
      #"val_subst" "g" (#"fix" "v")
      = #"fix" (#"val_subst" "g" "v")
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
    {{e #"fix" (#"closure" (#"prod" (#"neg" "A") "A")
                 (#"blk_subst" (#"snoc" #"forget"
                                 (#"pair"
                                   (#"pair" (#".1" #"hd")
                                     (#".1" (#".2" #"hd")))
                                   (#".2" (#".2" #"hd"))))
                                 "e") #"hd")}}
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
  cleanup_elab_after
    (reduce;
     term_cong; try term_refl;
     eapply eq_term_trans;
     [eapply eq_term_sym;
      eredex_steps_with cc_lang "clo_eta"|];
     by_reduction).
Qed.
#[export] Hint Resolve fix_cc_preserving : elab_pfs.