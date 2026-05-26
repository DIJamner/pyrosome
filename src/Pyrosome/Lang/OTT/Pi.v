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
(* Dependent products Π, split by RESULT relevance (Agda Typed.agda:44-49 *)
(* and the side-conditions r≡!→…, r≡%→lG≡⁰∧l≡⁰).                          *)
(*   Pi_rel : result in U_{!,lG}   (domain rF/lF free, result level = lG)  *)
(*   Pi_irr : result in SProp=U_{%,⁰}   (domain rF/lF free)               *)
(* Level side-conditions (lF≤l etc.) simplified: result level = codomain   *)
(* level; no cumulativity witnesses.                                       *)
(* ====================================================================== *)

Definition pi_injectivity :=
  [("Pi_rel", ["B"; "F"; "lG"; "lF"; "rF"; "G"]);
   ("Pi_irr", ["B"; "F"; "lF"; "rF"; "G"]);
   ("lam_rel", ["t"; "B"; "F"; "lG"; "lF"; "rF"; "G"]);
   ("lam_irr", ["t"; "B"; "F"; "lF"; "rF"; "G"]);
   ("app_rel", ["a"; "f"; "B"; "F"; "lG"; "lF"; "rF"; "G"]);
   ("app_irr", ["a"; "f"; "B"; "F"; "lF"; "rF"; "G"])].

Derive ott_pi
       in (wf_lang_ext (ott_base ++ subst_ott ++ ott_info) ott_pi)
       as ott_pi_wf.
Proof.
  setup_lang_interactive.

  (* proof-relevant Π : (x : F_{rF,lF}) → B_{!,lG}, a code in U_{!,lG}. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG")
      -----------------------------------------------
      #"Pi_rel" "rF" "lF" "lG" "F" "B"
        : #"exp" "G" (#"info" #"rel" (#"next" "lG")) (#"U" ["G" := "G"] #"rel" "lG")
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* proof-irrelevant Π : (x : F_{rF,lF}) → B_{%,⁰}, a code in SProp. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0")
      -----------------------------------------------
      #"Pi_irr" "rF" "lF" "F" "B"
        : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* substitution commutes with Π (binder codomain lifted via under'). *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G'" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G'"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G'" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G'" (#"El" "F")] #"rel" "lG")
      ----------------------------------------------- ("Pi_rel subst")
      #"exp_subst" "g" (#"Pi_rel" "rF" "lF" "lG" "F" "B")
        = #"Pi_rel" "rF" "lF" "lG" (#"exp_subst" "g" "F") (#"exp_subst" {inr (under' {{pe "g"}}) } "B")
      : #"exp" "G" (#"info" #"rel" (#"next" "lG")) (#"U" ["G" := "G"] #"rel" "lG")
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G'" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G'"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G'" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G'" (#"El" "F")] #"irr" #"L0")
      ----------------------------------------------- ("Pi_irr subst")
      #"exp_subst" "g" (#"Pi_irr" "rF" "lF" "F" "B")
        = #"Pi_irr" "rF" "lF" (#"exp_subst" "g" "F") (#"exp_subst" {inr (under' {{pe "g"}}) } "B")
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* λ for the proof-relevant Π. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG"),
          "t" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"iota" "lG")) (#"El" "B")
      -----------------------------------------------
      #"lam_rel" "rF" "lF" "lG" "F" "B" "t"
        : #"exp" "G" (#"info" #"rel" (#"iota" "lG"))
          (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "lG"] (#"Pi_rel" ["G" := "G"] "rF" "lF" "lG" "F" "B"))
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* λ for the proof-irrelevant Π. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0"),
          "t" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"irr" (#"iota" #"L0")) (#"El" "B")
      -----------------------------------------------
      #"lam_irr" "rF" "lF" "F" "B" "t"
        : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
          (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Pi_irr" ["G" := "G"] "rF" "lF" "F" "B"))
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* application for the proof-relevant Π : (f : Π F B)(a : F) → B[a]. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG"),
          "f" : #"exp" "G" (#"info" #"rel" (#"iota" "lG"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "lG"] (#"Pi_rel" ["G" := "G"] "rF" "lF" "lG" "F" "B")),
          "a" : #"exp" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      -----------------------------------------------
      #"app_rel" "rF" "lF" "lG" "F" "B" "f" "a"
        : #"exp" "G" (#"info" #"rel" (#"iota" "lG")) (#"ty_subst" (#"snoc" #"id" "a") (#"El" "B"))
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* application for the proof-irrelevant Π. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0"),
          "f" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Pi_irr" ["G" := "G"] "rF" "lF" "F" "B")),
          "a" : #"exp" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      -----------------------------------------------
      #"app_irr" "rF" "lF" "F" "B" "f" "a"
        : #"exp" "G" (#"info" #"irr" (#"iota" #"L0")) (#"ty_subst" (#"snoc" #"id" "a") (#"El" "B"))
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* β for the proof-relevant Π. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG"),
          "t" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"iota" "lG")) (#"El" "B"),
          "a" : #"exp" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      ----------------------------------------------- ("Pi_rel beta")
      #"app_rel" "rF" "lF" "lG" "F" "B" (#"lam_rel" "rF" "lF" "lG" "F" "B" "t") "a"
        = #"exp_subst" (#"snoc" #"id" "a") "t"
      : #"exp" "G" (#"info" #"rel" (#"iota" "lG")) (#"ty_subst" (#"snoc" #"id" "a") (#"El" "B"))
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* β for the proof-irrelevant Π. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"irr" #"L0"),
          "t" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"irr" (#"iota" #"L0")) (#"El" "B"),
          "a" : #"exp" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      ----------------------------------------------- ("Pi_irr beta")
      #"app_irr" "rF" "lF" "F" "B" (#"lam_irr" "rF" "lF" "F" "B" "t") "a"
        = #"exp_subst" (#"snoc" #"id" "a") "t"
      : #"exp" "G" (#"info" #"irr" (#"iota" #"L0")) (#"ty_subst" (#"snoc" #"id" "a") (#"El" "B"))
    ]}%prerule
    (pi_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_pi_entry := lang_entry ott_pi_wf.
#[export] Hint Resolve ott_pi_entry : wf_lang_db.
