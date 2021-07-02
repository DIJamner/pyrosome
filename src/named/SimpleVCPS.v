Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix SimpleVSubst SimpleVSTLC Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Definition block_subst_def : lang :=
  {[l
      [s| "G" : #"env"
          -----------------------------------------------
          #"blk" "G" srt
      ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
      "e" : #"blk" "G'"
       -----------------------------------------------
       #"blk_subst" "g" "e" : #"blk" "G"
  ];
  [:= "G" : #"env", "e" : #"blk" "G"
       ----------------------------------------------- ("blk_subst_id")
       #"blk_subst" #"id" "e" = "e" : #"blk" "G"
  ]; 
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "e" : #"blk" "G3"
       ----------------------------------------------- ("blk_subst_cmp")
       #"blk_subst" "f" (#"blk_subst" "g" "e")
       = #"blk_subst" (#"cmp" "f" "g") "e"
       : #"blk" "G1"
  ]
  (*TODO: any reason to add halt?
  [:| "G" : #"env", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"blk" "G" "A"
  ];
   
  [:= "G1" : #"env", "G2" : #"env",
       "g" : #"sub" "G1" "G2",
       "A" : #"ty", "v" : #"val" "G2" "A"
       ----------------------------------------------- ("blk_subst_ret")
       #"blk_subst" "g" (#"ret" "v")
       = #"ret" (#"val_subst" "g" "v")
       : #"blk" "G1" "A"
  ]*)
  ]}.

Derive block_subst
       SuchThat (Pre.elab_lang value_subst block_subst_def block_subst)
       As block_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_subst_wf : elab_pfs.


Definition cps_lang_def : lang :=
  {[l
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
  ];
  [:= "G" : #"env", "A" : #"ty",
      "v1" : #"val" "G" (#"neg" "A"),
      "v2" : #"val" "G" "A",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("jmp_subst")
      #"blk_subst" "g" (#"jmp" "v1" "v2")
      = #"jmp" (#"val_subst" "g" "v1") (#"val_subst" "g" "v2")
      : #"blk" "G'"
  ];  
  [:= "G" : #"env", "A" : #"ty",
      "e" : #"blk" (#"ext" "G" "A"),
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("cont_subst")
      #"val_subst" "g" (#"cont" "A" "e")
      = #"cont" "A" (#"blk_subst"
                       (#"snoc" (#"cmp" #"wkn" "g") #"hd") "e")
      : #"val" "G'" (#"neg" "A")
  ]
  ]}.


Derive cps_lang
       SuchThat (Pre.elab_lang (block_subst ++ value_subst)
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

(*TODO: separate file*)
Definition val_prod_lang_def : lang :=
  {[l
      
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
      "e" : #"val" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".1" "e" : #"val" "G" "A"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"val" "G" (#"prod" "A" "B")
      -----------------------------------------------
      #".2" "e" : #"val" "G" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      ----------------------------------------------- ("project 1")
      #".1" (#"pair" "v1" "v2") = "v1"
      : #"val" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "G" "B"
      ----------------------------------------------- ("project 2")
      #".2" (#"pair" "v1" "v2") = "v2"
      : #"val" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
      ----------------------------------------------- ("prod_eta")
      #"pair" (#".1" "v") (#".2" "v") = "v"
      : #"val" "G" (#"prod" "A" "B")
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"val" "G" "A",
      "e'" : #"val" "G" "B",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("pair_subst")
      #"val_subst" "g" (#"pair" "e" "e'")
      = #"pair" (#"val_subst" "g" "e") (#"val_subst" "g" "e'")
      : #"val" "G'" (#"prod" "A" "B")
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"val" "G" (#"prod" "A" "B"),
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("proj_1_subst")
      #"val_subst" "g" (#".1" "e")
      = #".1" (#"val_subst" "g" "e")
      : #"val" "G'" "A"
  ];
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"val" "G" (#"prod" "A" "B"),
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("proj_2_subst")
      #"val_subst" "g" (#".2" "e")
      = #".2" (#"val_subst" "g" "e")
      : #"val" "G'" "B"
  ]
  ]}.


    
Derive val_prod_lang
       SuchThat (Pre.elab_lang value_subst val_prod_lang_def val_prod_lang)
       As val_prod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve val_prod_wf : elab_pfs.


Definition cps_def : compiler :=
  match # from (stlc) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (#"ext" "G" (#"neg" "A")) }}
  | {{e #"->" "A" "B"}} =>
    {{e #"neg" (#"prod" "A" (#"neg" "B")) }}
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    (*TODO: use value product or exp-projection product?*)
    {{e #"cont" (#"prod" "A" (#"neg" "B"))
        (#"blk_subst" (#"snoc" (#"snoc" #"wkn" (#".1" #"hd")) (#".2" #"hd")) "e") }}
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
                                          (val_prod_lang
                                             ++ cps_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          cps_def
                                          cps
                                          stlc)
       As cps_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve cps_preserving : elab_pfs.
