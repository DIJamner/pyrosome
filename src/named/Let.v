Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers
      SimpleVSubst SimpleVCPS Matches.
Import Core.Notations.
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Let svar := @var string.
Coercion svar : string >-> term.

Notation compiler := (compiler string).

Definition let_lang_def : lang :=
  {[l/subst
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

Derive let_lang
       SuchThat (elab_lang_ext (exp_subst++value_subst) let_lang_def let_lang)
       As let_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve let_lang_wf : elab_pfs.

Definition let_cps_def : compiler :=
  match # from (let_lang) with
  | {{e #"let" "G" "A" "B" "e" "e'"}} =>
    bind_k 1 "e" "A"
    {{e#"blk_subst" (#"snoc" (#"snoc" {wkn_n 2} #"hd") {ovar 1}) "e'"}}
  end.

Derive let_cps
       SuchThat (elab_preserving_compiler cps_subst
                                          (cps_lang ++ block_subst ++ value_subst)
                                          let_cps_def
                                          let_cps
                                          let_lang)
       As let_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve let_cps_preserving : elab_pfs.
