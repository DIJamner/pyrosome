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
(* Natural numbers (and the proof-irrelevant Empty type).                 *)
(* ℕ ∷ U⁰ (info [!,ι¹]=[!,next⁰]); zero/suc ∷ ℕ (info [!,ι⁰]).            *)
(* (Agda Typed.agda:42,87-98 ; Empty 43,99-100.)                          *)
(* ====================================================================== *)

Definition nat_injectivity :=
  [("suc", ["G"]); ("zero", ["G"]); ("Empty", ["G"]); ("Nat", ["G"]);
   ("Emptyrec", ["e"; "A"; "lA"; "rA"; "G"])].

Derive ott_nat
       in (wf_lang_ext (ott_base ++ subst_ott ++ ott_info) ott_nat)
       as ott_nat_wf.
Proof.
  setup_lang_interactive.

  (* ℕ : a code in U_{!,⁰}. *)
  elab_rule {[r "G" : #"env"
      -----------------------------------------------
      #"Nat" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"rel" #"L0")
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'"
      ----------------------------------------------- ("Nat subst")
      #"exp_subst" "g" (#"Nat") = #"Nat"
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"rel" #"L0")
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* zero : ℕ  (info [!,ι⁰]) *)
  elab_rule {[r "G" : #"env"
      -----------------------------------------------
      #"zero" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'"
      ----------------------------------------------- ("zero subst")
      #"exp_subst" "g" (#"zero") = #"zero"
      : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* suc : ℕ → ℕ *)
  elab_rule {[r "G" : #"env",
          "n" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      -----------------------------------------------
      #"suc" "n" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "n" : #"exp" "G'" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G'"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G'"]))
      ----------------------------------------------- ("suc subst")
      #"exp_subst" "g" (#"suc" "n") = #"suc" (#"exp_subst" "g" "n")
      : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Empty (sEmpty) : a code in SProp = U_{%,⁰}. *)
  elab_rule {[r "G" : #"env"
      -----------------------------------------------
      #"Empty" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'"
      ----------------------------------------------- ("Empty subst")
      #"exp_subst" "g" (#"Empty") = #"Empty"
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Emptyrec : from a proof of Empty, get any type A_{rA,lA}. *)
  elab_rule {[r "G" : #"env", "rA" : #"relevance", "lA" : #"lvl",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" "lA")) (#"U" ["G" := "G"] "rA" "lA"),
          "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Empty" ["G" := "G"]))
      -----------------------------------------------
      #"Emptyrec" "A" "e" : #"exp" "G" (#"info" "rA" (#"iota" "lA")) (#"El" "A")
    ]}%prerule
    (nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_nat_entry := lang_entry ott_nat_wf.
#[export] Hint Resolve ott_nat_entry : wf_lang_db.
