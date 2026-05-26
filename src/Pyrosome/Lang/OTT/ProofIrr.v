From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import
  Theory.Core Elab.Elab
  Elab.PreRule
  Tools.ComputeWf
  Tools.Matches
  Tools.Resolution
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.EGraph.Automation
  Tools.Interactive.

From Pyrosome.Compilers Require Import Parameterizer.

From Pyrosome.Lang Require Import
  Subst SubstEqnGen.
From Pyrosome.Lang.OTT Require Import Base.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ====================================================================== *)
(* Definitional proof irrelevance (Agda Typed.agda:222-225):              *)
(* any two terms of a proof-irrelevant type [%, l] are equal.  This is    *)
(* former-agnostic and subsumes the η/equality of all SProp inhabitants   *)
(* (∃, Id, Pi_irr, …).                                                    *)
(* ====================================================================== *)

Derive ott_proofirr
       in (wf_lang_ext (ott_base ++ subst_ott ++ ott_info) ott_proofirr)
       as ott_proofirr_wf.
Proof.
  setup_lang_interactive.

  elab_rule {[r "G" : #"env", "l" : #"tlvl",
          "A" : #"ty" "G" (#"info" #"irr" "l"),
          "t" : #"exp" "G" (#"info" #"irr" "l") "A",
          "u" : #"exp" "G" (#"info" #"irr" "l") "A"
      ----------------------------------------------- ("proof irrelevance")
      "t" = "u" : #"exp" "G" (#"info" #"irr" "l") "A"
    ]}%prerule
    (ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_proofirr_entry := lang_entry ott_proofirr_wf.
#[export] Hint Resolve ott_proofirr_entry : wf_lang_db.
