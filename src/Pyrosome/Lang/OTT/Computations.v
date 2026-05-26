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
From Pyrosome.Lang.OTT Require Import Base Nat Pi Id.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ====================================================================== *)
(* Cross-former computation rules that need several sub-languages at once  *)
(* (e.g. Id-ℕ-00 = sUnit needs Π; Id-Π needs Π + application).            *)
(* First: confirm the concatenated base is provable by the wf db.          *)
(* ====================================================================== *)

Derive ott_comp
       in (wf_lang_ext (ott_id ++ ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info) ott_comp)
       as ott_comp_wf.
Proof.
  setup_lang_interactive.

  (* Id ℕ 0 0 = sUnit = (Π sEmpty ▹ sEmpty), a proof-irrelevant unit.
     (Agda Typed.agda Id-ℕ-00.) *)
  elab_rule {[r "G" : #"env"
      ----------------------------------------------- ("Id-Nat-00")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) #"zero" #"zero"
        = #"Pi_irr" #"irr" #"L0" (#"Empty" ["G" := "G"])
            (#"Empty" ["G" := #"ext" "G" (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Empty" ["G" := "G"]))])
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (pi_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_comp_entry := lang_entry ott_comp_wf.
#[export] Hint Resolve ott_comp_entry : wf_lang_db.
