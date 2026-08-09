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
From Pyrosome.Lang.OTT Require Import Base Nat Pi Sigma Id Cast.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ====================================================================== *)
(* Universe / type-equality layer for the heterogeneous Id.               *)
(*                                                                        *)
(* Here A = B = (u0 rel) : U_{!,1}, so the "elements" t,u : El(u0 rel) =   *)
(* U_{!,⁰} are themselves level-⁰ type CODES.  Id (u0 rel)(u0 rel) A B is  *)
(* thus the observational TYPE equality A ~ B (Pujet–Tabareau TTobs),      *)
(* computing structurally on the heads of A,B:                            *)
(*   ℕ ~ ℕ            ↝ sUnit                                             *)
(*   ℕ ~ Π  / Π ~ ℕ    ↝ Empty          (head clash)                      *)
(*   Π ~ Π            ↝ Σ(...)          (structural — DEFERRED, below)     *)
(* Plus the head clash between the universe code (u0) and Π at level ¹.    *)
(* ====================================================================== *)

Derive ott_id_univ
       in (wf_lang_ext (ott_cast ++ ott_id ++ ott_pi ++ ott_sigma ++ ott_nat
                         ++ ott_base ++ subst_ott ++ ott_info) ott_id_univ)
       as ott_id_univ_wf.
Proof.
  setup_lang_interactive.

  (* ℕ ~ ℕ ↝ sUnit = (Π sEmpty ▹ sEmpty). *)
  elab_rule {[r "G" : #"env"
      ----------------------------------------------- ("Id-U-Nat-Nat")
      #"Id" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] #"rel") (#"u0" ["G" := "G"] #"rel")
            (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"])
        = #"Pi_irr" #"irr" #"L0" (#"Empty" ["G" := "G"])
            (#"Empty" ["G" := #"ext" "G" (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Empty" ["G" := "G"]))])
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (cast_injectivity ++ pi_injectivity ++ id_injectivity ++ nat_injectivity
     ++ sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* ℕ ~ Π ↝ Empty  (type-level head clash at level ⁰). *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" #"L0")
      ----------------------------------------------- ("Id-U-Nat-Pi")
      #"Id" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] #"rel") (#"u0" ["G" := "G"] #"rel")
            (#"Nat" ["G" := "G"]) (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L0" "F" "B")
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (cast_injectivity ++ pi_injectivity ++ id_injectivity ++ nat_injectivity
     ++ sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  (* Π ~ ℕ ↝ Empty. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" #"L0")
      ----------------------------------------------- ("Id-U-Pi-Nat")
      #"Id" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] #"rel") (#"u0" ["G" := "G"] #"rel")
            (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L0" "F" "B") (#"Nat" ["G" := "G"])
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (cast_injectivity ++ pi_injectivity ++ id_injectivity ++ nat_injectivity
     ++ sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Head clash between the universe code (u0) and Π at level ¹.
     A = u0 r : U_{!,1}, B = Π at result level ¹; distinct heads ↝ Empty. *)
  elab_rule {[r "G" : #"env", "r" : #"relevance", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L1"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" #"L1"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L1"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L1"] (#"u0" ["G" := "G"] "r")),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" #"L1"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L1"] (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L1" "F" "B"))
      ----------------------------------------------- ("Id-u0-Pi")
      #"Id" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] "r") (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L1" "F" "B") "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (cast_injectivity ++ pi_injectivity ++ id_injectivity ++ nat_injectivity
     ++ sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "r" : #"relevance", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L1"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" #"L1"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L1"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L1"] (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L1" "F" "B")),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" #"L1"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L1"] (#"u0" ["G" := "G"] "r"))
      ----------------------------------------------- ("Id-Pi-u0")
      #"Id" ["G" := "G"] ["l" := #"L1"] (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L1" "F" "B") (#"u0" ["G" := "G"] "r") "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (cast_injectivity ++ pi_injectivity ++ id_injectivity ++ nat_injectivity
     ++ sigma_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Π ~ Π at the universe (Id-U-ΠΠ, Typed.agda:251-261) ↝ a Σ pairing the
     domain equality with the codomain equality under it:
       Id_U (Π F1 B1) (Π F2 B2)
         ↝ Sig (Id_U F1 F2) (Id_U B1[..] B2[..])
     DEFERRED: this is the structural universe rule the notes flag as strictly
     harder than Id-Π — it additionally needs Idsym (built from the deferred
     transp) to state the codomain equality, and the deeply-nested binder +
     substitution term OOMs the e-graph wf/inference pass on this machine
     (same wall as transp / Id-Π).  Its computational content is subsumed by
     proof irrelevance once the endpoints are known equal. *)

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_id_univ_entry := lang_entry ott_id_univ_wf.
#[export] Hint Resolve ott_id_univ_entry : wf_lang_db.
