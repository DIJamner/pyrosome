Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Elab.ElabCompilers Tools.Matches.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS SimpleVCC SimpleUnit.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Definition fix_cc_lang_def : lang :=
  {[l/subst
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


(*
Lemma term_rw_lhs_nth {V} `{Eqb V} (l : Rule.lang V) c t t'' s1 e e1 e2 s1_pre s1_post name
  : wf_lang l ->
    s1 = s1_pre ++ e1::s1_post ->
    eq_term l c t'' e1 e2 ->
    eq_term l c t (con name (s1_pre ++ e2::s1_post)) e ->
    eq_term l c t (con name s1) e.
Proof.
  intros; subst.
  eapply eq_term_trans; eauto.
  (*TODO: conv-stable inversion*)
Admitted.
 *)

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
     unfold Model.eq_term;
     eapply eq_term_trans;
     [eapply eq_term_sym;
      eredex_steps_with cc_lang "clo_eta"|];
     by_reduction).
Qed.
#[export] Hint Resolve fix_cc_preserving : elab_pfs.
