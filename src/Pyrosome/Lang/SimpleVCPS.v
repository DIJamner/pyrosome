Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Lang.SimpleVSubst Lang.SimpleVSTLC Tools.Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Local Notation compiler := (compiler string).


Definition cps_lang_def : lang :=
  {[l/subst
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
  [:| "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" (#"ext" "G" "A")
      -----------------------------------------------
      #"cont" "A" "e" : #"val" "G" (#"neg" "A")
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
      "e" : #"blk" (#"ext" "G" "A"),
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"cont" "A" "e") "v"
      = #"blk_subst" (#"snoc" #"id" "v") "e"
      : #"blk" "G"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" (#"neg" "A")
      ----------------------------------------------- ("cont_eta")
      #"cont" "A" (#"jmp" (#"val_subst" #"wkn" "v") #"hd")
      = "v"
      : #"val" "G" (#"neg" "A")
  ]
  ]}.

Derive cps_lang
       SuchThat (elab_lang_ext (block_subst ++ value_subst)
                               cps_lang_def
                               cps_lang)
       As cps_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cps_lang_wf : elab_pfs.


Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | 1 => {{e #"wkn"}}
  | S n' =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Definition ovar n :=
    {{e #"val_subst" {wkn_n n} #"hd" }}.  

Fixpoint vwkn_n n e :=
  match n with
  | 0 => e
  | S n' =>
    {{e #"val_subst" #"wkn" {vwkn_n n' e} }}
  end.

(*g is the necessary weakening of e *)
Definition bind_k n e A k :=
  {{e #"blk_subst" (#"snoc" {wkn_n n} (#"cont" {A} {k})) {e} }}.
Arguments bind_k n e A k/.

(*TODO: extract the identity compiler for vals*)
(*TODO: depends on products*)
Definition cps_subst_def : compiler :=
  match # from (exp_subst ++ value_subst) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (#"ext" "G" (#"neg" "A")) }}
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" (#"snoc" (#"cmp" #"wkn" "g") #"hd") "e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"jmp" #"hd" (#"val_subst" #"wkn" "v")}}
  end.

Derive cps_subst
       SuchThat (elab_preserving_compiler []
                                          (cps_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          cps_subst_def
                                          cps_subst
                                          (exp_subst ++ value_subst))
       As cps_subst_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve cps_subst_preserving : elab_pfs.

(*TODO: separate file?*)
Definition cps_prod_lang_def : lang :=
  {[l/subst
      
  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"prod" "A" "B" : #"ty"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e1" : #"val" "G" "A",
      "e2" : #"val" "G" "B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"val" "G" (#"prod" "A" "B")
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B"),
      "e" : #"blk" (#"ext" (#"ext" "G" "A") "B")
      -----------------------------------------------
      #"pm_pair" "v" "e" : #"blk" "G"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B",
      "e" : #"blk" (#"ext" (#"ext" "G" "A") "B")
      ----------------------------------------------- ("eval pm_pair")
      #"pm_pair" (#"pair" "v1" "v2") "e"
      = #"blk_subst" (#"snoc" (#"snoc" #"id" "v1") "v2") "e"
      : #"blk" "G"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B"),
      "e" : #"blk" (#"ext" "G" (#"prod" "A" "B"))
      ----------------------------------------------- ("prod_eta")
      #"pm_pair" "v" (#"blk_subst" (#"snoc" (#"cmp" #"wkn" #"wkn") (#"pair" {ovar 1} {ovar 0})) "e")
      = #"blk_subst" (#"snoc" #"id" "v") "e"
      : #"blk" "G"
  ] ]}.


    
Derive cps_prod_lang
       SuchThat (elab_lang_ext (block_subst ++value_subst) cps_prod_lang_def cps_prod_lang)
       As cps_prod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cps_prod_wf : elab_pfs.

Definition under s :=
  {{e #"snoc" (#"cmp" #"wkn" {s}) #"hd"}}.
  
Definition cps_def : compiler :=
  match # from (stlc) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (#"ext" "G" (#"neg" "A")) }}
  | {{e #"->" "A" "B"}} =>
    {{e #"neg" (#"prod" "A" (#"neg" "B")) }}
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    {{e #"cont" (#"prod" "A" (#"neg" "B"))
        (#"pm_pair" #"hd"
          (#"blk_subst" {under (under {{e #"wkn"}})} "e"))}}
  | {{e #"app" "G" "A" "B" "e" "e'"}} =>
    bind_k 1 (var "e") {{e #"neg" (#"prod" "A" (#"neg" "B"))}}
    (bind_k 2 (var "e'") (var "A")
    {{e #"jmp" {ovar 1} (#"pair" {ovar 0} {ovar 2}) }})
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" (#"snoc" (#"cmp" #"wkn" "g") #"hd") "e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"jmp" #"hd" (#"val_subst" #"wkn" "v")}}
  end.

Derive cps
       SuchThat (elab_preserving_compiler cps_subst
                                          (cps_prod_lang
                                             ++ cps_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          cps_def
                                          cps
                                          stlc)
       As cps_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve cps_preserving : elab_pfs.
