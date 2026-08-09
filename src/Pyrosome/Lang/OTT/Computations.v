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
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) #"zero" #"zero"
        = #"Pi_irr" #"irr" #"L0" (#"Empty" ["G" := "G"])
            (#"Empty" ["G" := #"ext" "G" (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Empty" ["G" := "G"]))])
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (pi_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Head clash ℕ vs Π at level ⁰: heterogeneous Id between codes with distinct
     head constructors reduces to the empty proposition (OTT "clash" rule).
     Both codes sit at level ⁰, so the Π result level lG is fixed to L0. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" #"L0"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"])),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L0" "F" "B"))
      ----------------------------------------------- ("Id-Nat-Pi")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L0" "F" "B") "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (pi_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" #"L0"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L0" "F" "B")),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Pi-Nat")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Pi_rel" ["G" := "G"] "rF" "lF" #"L0" "F" "B") (#"Nat" ["G" := "G"]) "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (pi_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Id-Π — the same-head STRUCTURAL rule for two Π codes (funext,
     Typed.agda:231-240) — remains DEFERRED.  The intended reduction is the
     heterogeneous function extensionality
       Id (Π F1 B1) (Π F2 B2) f g
         ↝ Π(a1:F1) Π(a2:F2) (Id F1 F2 a1 a2) ⇒ Id (B1[a1]) (B2[a2]) (f·a1) (g·a2)
     as a triple-nested Pi_irr.  Two obstacles, both real:
       (1) SEMANTIC.  Id requires its two type arguments at a COMMON level and
           relevance rel (see the Id former).  So the inner Id F1 F2 a1 a2 only
           typechecks when the domains F1,F2 share level/relevance; the general
           case (distinct domains) must instead cast a1 across F1~F2, which needs
           Idsym/transp — themselves deferred (see Id.v).
       (2) COST.  Even the restricted same-shape-domain form OOMs: it is the
           deeply-nested binder + substitution + application term whose e-graph
           wf/inference pass does not finish in practical time (killed >500s),
           the same wall hit by transp.
     The head-CLASH rules above (Id-Nat-Pi / Id-Pi-Nat) are the tractable part of
     the Π fragment and are done.  cast-Π (:300-312) and the universe-level
     Id-U-ΠΠ (:251-261, see IdUniv.v) are strictly harder for the same reasons. *)

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_comp_entry := lang_entry ott_comp_wf.
#[export] Hint Resolve ott_comp_entry : wf_lang_db.
