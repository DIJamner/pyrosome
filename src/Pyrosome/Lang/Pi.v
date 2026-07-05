From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
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

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* TODO: delcare interactively, register in DB *)
Definition pi_injectivity :=
  [("app", ["G"]); ("lambda", ["e";"B"; "A"; "G"]); ("Pi", ["B"; "A"; "G"])].

Derive pi
       in (wf_lang_ext subst_lang pi)
       as pi_wf.
Proof.
  setup_lang_interactive.

  elab_rule_auto {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A")
      -----------------------------------------------
      #"Pi" "A" "B" : #"ty" "G"
    ]}%prerule 5.
  gen_subst.
  elab_rule_auto {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" (#"ext" "G" "A") "B"
      -----------------------------------------------
      #"lambda" "A" "e" : #"exp" "G" (#"Pi" "A" "B")
  ]}%prerule 5.
  gen_subst.
  elab_rule_auto {[r "G" : #"env",
          "A" : #"ty" "G",
          "B": #"ty" (#"ext" "G" "A"),
          (*TODO: why is this annotation needed? *)
          "e" : #"exp" "G" (#"Pi" ["G":="G"] "A" "B"), 
          "e'" : #"exp" "G" "A"
          -----------------------------------------------
          #"app" "e" "e'" : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e'") "B")
   ]}%prerule 5.
   gen_subst.
  elab_rule_auto{[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" (#"ext" "G" "A") "B",
      "e'" : #"exp" "G" "A"
      ----------------------------------------------- ("Pi beta")
      #"app" (#"lambda" "A" "e") "e'"
      = #"exp_subst" (#"snoc" #"id" "e'") "e"
      : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e'") "B")
  ]}%prerule 5.
(* NOTE: kept on the explicit schema list: the auto-generated ruleset includes
   composition-cancellation schemas (cmp f1 g = cmp f2 g |- f1 = f2) that the
   bounded counterexample search cannot refute but that are semantically
   unjustified; they merge (under' wkn) with wkn (both compose with wkn to the
   double weakening), mis-elaborating the "B" annotation below into
   (ty_subst wkn B), and the deferred wf-check of that ill-formed rule then
   diverges at Qed. *)
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

