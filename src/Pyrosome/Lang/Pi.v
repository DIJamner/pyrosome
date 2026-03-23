Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import
  Theory.Core Elab.Elab
  Elab.PreRule
  Tools.Resolution Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference
  Tools.Interactive
  Lang.Subst
  Lang.SubstEqnGen.

Require Coq.derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* TODO: delcare interactively, register in DB *)
Definition pi_injectivity :=
  [("app", ["G"]); ("lambda", ["e";"B"; "A"; "G"]); ("Pi", ["B"; "A"; "G"])].

Derive pi
       SuchThat (wf_lang_ext subst_lang pi)
       As pi_wf.
Proof.
  setup_lang_interactive.

  elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A")
      -----------------------------------------------
      #"Pi" "A" "B" : #"ty" "G"
    ]}%prerule
    (pi_injectivity++subst_injectivity).
  gen_subst.
  elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" (#"ext" "G" "A") "B"
      -----------------------------------------------
      #"lambda" "A" "e" : #"exp" "G" (#"Pi" "A" "B")
  ]}%prerule
   (pi_injectivity++subst_injectivity).
  gen_subst.
  elab_rule {[r "G" : #"env",
          "A" : #"ty" "G",
          "B": #"ty" (#"ext" "G" "A"),
          (*TODO: why is this annotation needed? *)
          "e" : #"exp" "G" (#"Pi" ["G":="G"] "A" "B"), 
          "e'" : #"exp" "G" "A"
          -----------------------------------------------
          #"app" "e" "e'" : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e'") "B")
   ]}%prerule
    (pi_injectivity++subst_injectivity).
   gen_subst.
  elab_rule{[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" (#"ext" "G" "A") "B",
      "e'" : #"exp" "G" "A"
      ----------------------------------------------- ("Pi beta")
      #"app" (#"lambda" "A" "e") "e'"
      = #"exp_subst" (#"snoc" #"id" "e'") "e"
      : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e'") "B")
  ]}%prerule
    (pi_injectivity++subst_injectivity).
elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" "G" (#"Pi" ["G":="G"] "A" "B")
      ----------------------------------------------- ("Pi eta")
      #"lambda" "A" (#"app" ["B":= #"ty_subst" {inr (under' {{pe#"wkn"}}) } "B"]
                       (*TODO: check this type *)
                       (#"exp_subst" #"wkn" "e")
                        #"hd")
      = "e"
      : #"exp" "G" (#"Pi" "A" "B")
  ]}%prerule
  (pi_injectivity++subst_injectivity).
apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition pi_entry := lang_entry pi_wf.
#[export] Hint Resolve pi_entry : wf_lang_db.

