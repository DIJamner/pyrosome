Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst SimpleVSTLC Matches.
Import Core.Notations.

Require Coq.derive.Derive.


Definition subst_eval_ctx_def : lang :=
  {[l
  [s| "G" : #"env", "A" : #"ty", "B" : #"ty"
      -----------------------------------------------
      #"Ectx" "G" "A" "B" srt
  ];
  [:| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"[ ]" : #"Ectx" "G" "A" "A"
  ];       
  [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
      "E" : #"Ectx" "G" "A" "B",
      "e" : #"exp" "G" "A"
      -----------------------------------------------
      #"plug" "E" "e" : #"exp" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty",
      "e" : #"exp" "G" "A"
      ----------------------------------------------- ("plug hole")
      #"plug" #"[ ]" "e" = "e" : #"exp" "G" "A"
  ]]}.
       
Derive eval_ctx
       SuchThat (Pre.elab_lang (exp_subst ++ value_subst) subst_eval_ctx_def eval_ctx)
       As eval_ctx_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve eval_ctx_wf : elab_pfs.


Definition Estlc_def :lang :=  
  {[l
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "E" : #"Ectx" "G" "C" (#"->" "A" "B"),
      "e'" : #"exp" "G" "A"
      -----------------------------------------------
      #"Eapp_l" "E" "e'" : #"Ectx" "G" "C" "B"
  ];
  [:= "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" "G" "C" (#"->" "A" "B"),
       "e'" : #"exp" "G" "A",
       "e" : #"exp" "G" "C"
       ----------------------------------------------- ("plug app_l")
       #"plug" (#"Eapp_l" "E" "e'") "e"
       = #"app" (#"plug" "E" "e") "e'"
      : #"exp" "G" "B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "v" : #"val" "G" (#"->" "A" "B"),
       "E" : #"Ectx" "G" "C" "A"
       -----------------------------------------------
       #"Eapp_r" "v" "E" : #"Ectx" "G" "C" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "E" : #"Ectx" "G" "C" "A",
      "v" : #"val" "G" (#"->" "A" "B"),
      "e" : #"exp" "G" "C"
      ----------------------------------------------- ("plug app_r")
      #"plug" (#"Eapp_r" "v" "E") "e"
      = #"app" (#"ret" "v") (#"plug" "E" "e")
      : #"exp" "G" "B"
  ]]}.


Derive Estlc
       SuchThat (Pre.elab_lang (eval_ctx ++ stlc ++ exp_subst++ value_subst) Estlc_def Estlc)
       As Estlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve Estlc_wf : elab_pfs.
 
