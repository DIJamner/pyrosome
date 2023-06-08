Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers Tools.Matches.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVCPS SimpleUnit.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Notation compiler := (compiler string).

Definition prod_cc_def : lang :=
  {[l/subst
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


Derive prod_cc
       SuchThat (elab_lang_ext (cps_prod_lang ++ block_subst ++value_subst) prod_cc_def prod_cc)
       As prod_cc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_cc_wf : elab_pfs.

Definition cc_lang_def : lang :=
  {[l/subst
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


Derive cc_lang
       SuchThat (elab_lang_ext (prod_cc ++ cps_prod_lang ++ block_subst ++value_subst)
                               cc_lang_def
                               cc_lang)
       As cc_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cc_lang_wf : elab_pfs.


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
       SuchThat (elab_preserving_compiler []
                                          (unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          subst_cc_def
                                          subst_cc
                                          (block_subst++value_subst))
       As subst_cc_preserving.
Proof.
  auto_elab_compiler.
  cleanup_elab_after
    (reduce; eredex_steps_with unit_eta "unit eta").
Qed.
#[export] Hint Resolve subst_cc_preserving : elab_pfs.


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
Derive forget_eq_wkn
       SuchThat (elab_lang_ext value_subst
                               forget_eq_wkn_def
                               forget_eq_wkn)
       As forget_eq_wkn_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve forget_eq_wkn_wf : elab_pfs.


Derive prod_cc_compile
       SuchThat (elab_preserving_compiler subst_cc
                                          ( unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          prod_cc_compile_def
                                          prod_cc_compile
                                          cps_prod_lang)
       As prod_cc_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve prod_cc_preserving : elab_pfs.


Definition cc_def : compiler :=
  match # from (cps_lang) with
  | {{e #"neg" "A" }} => {{e #"neg" "A"}}
  | {{e #"cont" "G" "A" "e"}} =>
    {{e #"closure" "A" "e" #"hd"}}
  | {{e #"jmp" "G" "A" "v1" "v2"}} =>
    {{e #"jmp" "v1" "v2" }}
  end.

 
Derive cc
       SuchThat (elab_preserving_compiler (prod_cc_compile++subst_cc)
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
       As cc_preserving.
Proof.
  auto_elab_compiler.
  cleanup_elab_after
  (reduce;
   eapply eq_term_trans;  
   [eapply eq_term_sym;
   eredex_steps_with cc_lang "clo_eta"|];
   by_reduction).
Qed.
#[export] Hint Resolve cc_preserving : elab_pfs.

