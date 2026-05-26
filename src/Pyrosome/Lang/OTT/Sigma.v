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
(* Proof-irrelevant dependent pairs (∃).  Everything lives in SProp =     *)
(* U_{%,⁰}, so this former is uniform in relevance/level (all [%, ι⁰]).   *)
(* (Agda Typed.agda:50-53, 71-86.)                                        *)
(* ====================================================================== *)

Definition sigma_injectivity :=
  [("snd", ["e"; "B"; "F"; "G"]); ("fst", ["e"; "B"; "F"; "G"]);
   ("pair", ["t2"; "t1"; "B"; "F"; "G"]); ("Sig", ["B"; "F"; "G"])].

Derive ott_sigma
       in (wf_lang_ext (ott_base ++ subst_ott ++ ott_info) ott_sigma)
       as ott_sigma_wf.
Proof.
  setup_lang_interactive.

  (* ∃ F ▹ B : a code in SProp; F and B are codes in SProp. *)
  elab_rule {[r "G" : #"env",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0")
      -----------------------------------------------
      #"Sig" "F" "B" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* substitution commutes with ∃ (binder: codomain lifted via under'). *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "F" : #"exp" "G'" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G'"] #"irr" #"L0"),
          "B" : #"exp" (#"ext" "G'" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G'" (#"El" "F")] #"irr" #"L0")
      ----------------------------------------------- ("Sig subst")
      #"exp_subst" "g" (#"Sig" "F" "B")
        = #"Sig" (#"exp_subst" "g" "F") (#"exp_subst" {inr (under' {{pe "g"}}) } "B")
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* fst : ∃ F B → F *)
  elab_rule {[r "G" : #"env",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0"),
          "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Sig" ["G" := "G"] "F" "B"))
      -----------------------------------------------
      #"fst" "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0")) (#"El" "F")
    ]}%prerule
    (sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* snd : (e : ∃ F B) → B[fst e] *)
  elab_rule {[r "G" : #"env",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0"),
          "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Sig" ["G" := "G"] "F" "B"))
      -----------------------------------------------
      #"snd" "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                   (#"ty_subst" (#"snoc" #"id" (#"fst" "e")) (#"El" "B"))
    ]}%prerule
    (sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* pair ⦅F,B, t1, t2⦆ : ∃ F B *)
  elab_rule {[r "G" : #"env",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0"),
          "t1" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0")) (#"El" "F"),
          "t2" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                        (#"ty_subst" (#"snoc" #"id" "t1") (#"El" "B"))
      -----------------------------------------------
      #"pair" "t1" "t2" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                          (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Sig" ["G" := "G"] "F" "B"))
    ]}%prerule
    (sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* β rules *)
  elab_rule {[r "G" : #"env",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0"),
          "t1" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0")) (#"El" "F"),
          "t2" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                        (#"ty_subst" (#"snoc" #"id" "t1") (#"El" "B"))
      ----------------------------------------------- ("fst beta")
      #"fst" ["B" := "B"] (#"pair" "t1" "t2") = "t1"
      : #"exp" "G" (#"info" #"irr" (#"iota" #"L0")) (#"El" "F")
    ]}%prerule
    (sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  (* NOTE: "snd beta" deferred — its conclusion type ty_subst(snoc id t1)(El B)
     currently defeats the e-graph sort inference (leaves @sort_of on B/t2). *)

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_sigma_entry := lang_entry ott_sigma_wf.
#[export] Hint Resolve ott_sigma_entry : wf_lang_db.
