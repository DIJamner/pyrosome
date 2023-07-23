Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Lang.LinearSubst (* Lang.LinearSTLC *) Tools.Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Local Notation compiler := (compiler string).


Definition linear_cps_lang_def : lang :=
  {[l/lin_subst (* [linear_blk_subst ++ linear_value_subst] *)
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
   [:| "G" : #"env", "H" : #"env",
       "A" : #"ty",
       "v1" : #"val" "G" (#"neg" "A"),
       "v2" : #"val" "H" "A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" (#"conc" "G" "H")
   ];
  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "e" : #"blk" (#"ext" "G" "A"),
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"cont" "A" "e") "v"
      = #"blk_subst" (#"snoc" #"id" "v") "e"
      : #"blk" (#"conc" "G" "H")
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" (#"neg" "A")
      ----------------------------------------------- ("cont_eta")
      #"cont" "A" (#"jmp" "v" #"hd") = "v"
      : #"val" "G" (#"neg" "A")
  ]
  ]}.

Derive linear_cps_lang
       SuchThat (elab_lang_ext (linear_block_subst ++ linear_value_subst)
                               linear_cps_lang_def
                               linear_cps_lang)
       As cps_lang_wf.
Proof. Abort.

(* #[export] Hint Resolve cps_lang_wf : elab_pfs.

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
    {{e #"blk_subst" (#"snoc" "g" #"hd") "e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"jmp" #"hd" "v"}}
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
  {[l/subst [linear_block_subst++linear_value_subst]

  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"prod" "A" "B" : #"ty"
  ];
  [:| "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e1" : #"val" "G" "A",
      "e2" : #"val" "H" "B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"val" (#"conc" "G" "H") (#"prod" "A" "B")
  ];
  [:| "G" : #"env", "H" : #"env"
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "H" (#"prod" "A" "B"),
      "e" : #"blk" (#"ext" (#"ext" "G" "A") "B")
      -----------------------------------------------
      #"pm_pair" "v" "e" : #"blk" (#"conc" "G" "H")
  ];
  [:= "G" : #"env", "H" : #"env", "K" : #"env"
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "H" "B",
      "e" : #"blk" (#"ext" (#"ext" "K" "A") "B")
      ----------------------------------------------- ("eval pm_pair")
      #"pm_pair" (#"pair" "v1" "v2") "e"
      = #"blk_subst" (#"snoc" (#"snoc" #"id" "v1") "v2") "e"
      : #"blk" (#"conc" "K" (#"conc" "G" "H"))
  ];
  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty", "B" : #"ty",
      "v" : #"val" "H" (#"prod" "A" "B"),
      "e" : #"blk" (#"ext" "G" (#"prod" "A" "B"))
      ----------------------------------------------- ("prod_eta")
      #"pm_pair" "v" (#"blk_subst" (#"snoc" #"id" (#"pair" #"hd" #"hd")) "e")
      = #"blk_subst" (#"snoc" #"id" "v") "e"
      : #"blk" "G"
  ] ]}.



Derive cps_prod_lang
       SuchThat (elab_lang_ext (block_subst ++value_subst) cps_prod_lang_def cps_prod_lang)
       As cps_prod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cps_prod_wf : elab_pfs.
*)

Definition under s :=
  {{e #"snoc" s #"hd"}}.

Definition bind e A k :=
  {{e #"blk_subst" (#"snoc" #"id" (#"cont" {A} {k})) {e} }}.
Arguments bind e A k/.

(*
Definition cps_def : compiler :=
  match # from (linear_stlc) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (#"ext" "G" (#"neg" "A")) }}
  | {{e #"lolli" "A" "B"}} =>
    {{e #"neg" (#"prod" "A" (#"neg" "B")) }}
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    {{e #"cont" (#"prod" "A" (#"neg" "B"))
        (#"pm_pair" #"hd" "e")}}
  | {{e #"app" "G" "H" "A" "B" "e" "e'"}} =>
    (* blk (G; H), ~B = blk G; (H, ~B) *)
    bind (var "e") {{e #"neg" (#"prod" "A" (#"neg" "B"))}}
    ( (* blk H, ~B, ~(A * ~B) = blk H; ({}, ~B, ~(A * ~B)) *)
      bind (var "e'") (var "A")
      ( (* blk {}, ~B, ~(A * ~B), A = blk {}; ({}, ~B); ({}, ~(A * ~B)); ({}, A) *)
        {{e #"blk_subst" (#"exch" #"emp"
                                  (#"ext" #"emp" (#"neg" "B"))
                                  (#"ext" #"emp" (#"neg" (#"prod" "A" (#"neg" "B"))))
                                  (#"ext" #"emp" "A"))
          (* blk {}; ({}, ~(A * ~B)); ({}, ~B); ({}, A) = blk ({}, ~(A * ~B)); ({}, ~B, A) *)
          (#"jmp" #"hd"
            (* val ({}, ~B, A) (A * ~B) = val {}; ({}, ~B); ({}, A); {} *)
            (#"val_subst" (#"exch" #"emp"
                                   (#"ext" #"emp" (#"neg" "B"))
                                   (#"ext" #"emp" "A")
                                   #"emp")
              (#"pair" #"hd" #"hd")))
        }}

      )
    )
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" (#"snoc" "g" #"hd") "e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"jmp" #"hd" "v"}}
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

*)