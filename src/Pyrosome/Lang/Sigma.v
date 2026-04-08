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
(* Note: sigma injectivity is a bit complicated,
   but this doesn't have to be correct, it'll just yield
   a slightly incomplete process.
 *)
Definition sigma_injectivity :=
  [("proj2", ["G"]);("proj1", ["A";"G"]); ("ex", ["e2";"B"; "e1"; "A"; "G"]);
   ("Sig", ["B"; "A"; "G"])].

Derive sigma
       SuchThat (wf_lang_ext subst_lang sigma)
       As sigma_wf.
Proof.
  setup_lang_interactive.

  elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A")
      -----------------------------------------------
      #"Sig" "A" "B" : #"ty" "G"
    ]}%prerule
    (sigma_injectivity++subst_injectivity).
  gen_subst.
  elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "e1" : #"exp" "G" "A",
      "B": #"ty" (#"ext" "G" "A"),
      "e2" : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e1") "B")
      -----------------------------------------------
      #"ex" "e1" "e2" : #"exp" "G" (#"Sig" "A" "B")
  ]}%prerule
   (sigma_injectivity++subst_injectivity).
  gen_subst.
  elab_rule {[r "G" : #"env",
          "A" : #"ty" "G",
          "B": #"ty" (#"ext" "G" "A"),
          (*TODO: why is this annotation needed? *)
          "e" : #"exp" "G" (#"Sig" ["G":="G"] "A" "B")
          -----------------------------------------------
          #"proj1" "e" : #"exp" "G" "A"
   ]}%prerule
    (sigma_injectivity++subst_injectivity).
  gen_subst.
  elab_rule {[r "G" : #"env",
          "A" : #"ty" "G",
          "B": #"ty" (#"ext" "G" "A"),
          "e" : #"exp" "G" (#"Sig" "A" "B")
          -----------------------------------------------
          #"proj2" "e"
          : #"exp" "G" (#"ty_subst" (#"snoc" #"id" (#"proj1" "e")) "B")
   ]}%prerule
    (sigma_injectivity++subst_injectivity).
  gen_subst.
  elab_rule{[r "G" : #"env",
      "A" : #"ty" "G",
      "e1" : #"exp" "G" "A",
      "B": #"ty" (#"ext" "G" "A"),
      "e2" : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e1") "B")
      ----------------------------------------------- ("proj1 beta")
      #"proj1" ["B":="B"] (#"ex" "e1" "e2") = "e1"
      : #"exp" "G" "A"
  ]}%prerule
    (sigma_injectivity++subst_injectivity).
  elab_rule{[r "G" : #"env",
      "A" : #"ty" "G",
      "e1" : #"exp" "G" "A",
      "B": #"ty" (#"ext" "G" "A"),
      "e2" : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e1") "B")
      ----------------------------------------------- ("proj2 beta")
      #"proj2" ["B":="B"] (#"ex" "e1" "e2") = "e2"
      : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e1") "B")
  ]}%prerule
    (sigma_injectivity++subst_injectivity).
elab_rule {[r "G" : #"env",
          "A" : #"ty" "G",
          "B": #"ty" (#"ext" "G" "A"),
          "e" : #"exp" "G" (#"Sig" "A" "B")
      ----------------------------------------------- ("ex eta")
      #"ex" (#"proj1" "e") (#"proj2" "e") = "e"
          (*TODO: why is this annotation needed? *)
      : #"exp" "G" (#"Sig" ["G":="G"]  "A" "B")
  ]}%prerule
  (sigma_injectivity++subst_injectivity).
apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition sigma_entry := lang_entry sigma_wf.
#[export] Hint Resolve sigma_entry : wf_lang_db.


