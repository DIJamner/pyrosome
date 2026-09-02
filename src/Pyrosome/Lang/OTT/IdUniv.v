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

(* Id-U-Π-Π — the structural universe rule (Typed.agda:251-261): the type
   equality of two Π codes at level ⁰ is a Σ of the domain equality and the
   pointwise codomain equality.  Cast-based single-binder form (Pujet–Tabareau):
     Id_U (Π F1 B1) (Π F2 B2)
       ↝ Σ (ef : Id_U F1 F2).
           Π (a2 : F2). Id_U (B1[cast F2 F1 (Idsym ef) a2]) (B2[a2])
   The argument a2 : F2 is cast CONTRAVARIANTLY to F1 (via Idsym ef) to index B1,
   so this needs exactly the transp/Idsym/cast machinery now in place.  Domains
   are relevant at level ⁰ (forced by Id_U F1 F2 typechecking).  Pre-elaborated +
   push_rule (like Pi.v's `Pi_rel eta` and the funext rule). *)
Definition id_u_pi_pi_rule : string * rule :=
  let iN0   : term := {{e #"info" #"rel" (#"next" #"L0") }} in
  let iI0   : term := {{e #"info" #"rel" (#"iota" #"L0") }} in
  let uG    : term := {{e #"U" "G" #"rel" #"L0" }} in
  let uGirr : term := {{e #"U" "G" #"irr" #"L0" }} in
  let u0r   : term := {{e #"u0" "G" #"rel" }} in
  let pi1   : term := {{e #"Pi_rel" "G" #"rel" #"L0" #"L0" "F1" "B1" }} in
  let pi2   : term := {{e #"Pi_rel" "G" #"rel" #"L0" #"L0" "F2" "B2" }} in
  let idF   : term := {{e #"Id" "G" #"L1" {u0r} {u0r} "F1" "F2" }} in
  let iSig  : term := {{e #"info" #"irr" (#"iota" #"L0") }} in
  let elIdF : term := {{e #"El" "G" #"irr" #"L0" {idF} }} in
  let Gs    : term := {{e #"ext" "G" {iSig} {elIdF} }} in
  let wS    : term := {{e #"wkn" "G" {iSig} {elIdF} }} in
  let F1s   : term := {{e #"exp_subst" {Gs} "G" {wS} {iN0} {uG} "F1" }} in
  let F2s   : term := {{e #"exp_subst" {Gs} "G" {wS} {iN0} {uG} "F2" }} in
  let idFs  : term := {{e #"exp_subst" {Gs} "G" {wS} {iN0} {uGirr} {idF} }} in
  let elIdFs : term := {{e #"El" {Gs} #"irr" #"L0" {idFs} }} in
  let elF2s : term := {{e #"El" {Gs} #"rel" #"L0" {F2s} }} in
  let Gs2   : term := {{e #"ext" {Gs} {iI0} {elF2s} }} in
  let wS2   : term := {{e #"wkn" {Gs} {iI0} {elF2s} }} in
  let a2    : term := {{e #"hd" {Gs} {iI0} {elF2s} }} in
  let ef    : term := {{e #"hd" "G" {iSig} {elIdF} }} in
  let ef2   : term := {{e #"exp_subst" {Gs2} {Gs} {wS2} {iSig} {elIdFs} {ef} }} in
  let uGs   : term := {{e #"U" {Gs} #"rel" #"L0" }} in
  let F1s2  : term := {{e #"exp_subst" {Gs2} {Gs} {wS2} {iN0} {uGs} {F1s} }} in
  let F2s2  : term := {{e #"exp_subst" {Gs2} {Gs} {wS2} {iN0} {uGs} {F2s} }} in
  let u0r2  : term := {{e #"u0" {Gs2} #"rel" }} in
  let symE  : term := {{e #"Idsym" {Gs2} #"L1" {u0r2} {u0r2} {F1s2} {F2s2} {ef2} }} in
  let cst   : term := {{e #"cast" {Gs2} #"rel" {F2s2} {F1s2} {symE} {a2} }} in
  let w     : term := {{e #"cmp" {Gs2} {Gs} "G" {wS2} {wS} }} in
  let elF1  : term := {{e #"El" "G" #"rel" #"L0" "F1" }} in
  let elF2  : term := {{e #"El" "G" #"rel" #"L0" "F2" }} in
  let extF1 : term := {{e #"ext" "G" {iI0} {elF1} }} in
  let extF2 : term := {{e #"ext" "G" {iI0} {elF2} }} in
  let uExtF1 : term := {{e #"U" {extF1} #"rel" #"L0" }} in
  let uExtF2 : term := {{e #"U" {extF2} #"rel" #"L0" }} in
  let snoc1 : term := {{e #"snoc" {Gs2} "G" {iI0} {elF1} {w} {cst} }} in
  let snoc2 : term := {{e #"snoc" {Gs2} "G" {iI0} {elF2} {w} {a2} }} in
  let bod1   : term := {{e #"exp_subst" {Gs2} {extF1} {snoc1} {iN0} {uExtF1} "B1" }} in
  let bod2   : term := {{e #"exp_subst" {Gs2} {extF2} {snoc2} {iN0} {uExtF2} "B2" }} in
  let body  : term := {{e #"Id" {Gs2} #"L1" {u0r2} {u0r2} {bod1} {bod2} }} in
  let cod   : term := {{e #"Pi_irr" {Gs} #"rel" #"L0" {F2s} {body} }} in
  ("Id-U-Pi-Pi",
   term_eq_rule
     [("B2", {{s #"exp" {extF2} {iN0} {uExtF2} }});
      ("F2", {{s #"exp" "G" {iN0} {uG} }});
      ("B1", {{s #"exp" {extF1} {iN0} {uExtF1} }});
      ("F1", {{s #"exp" "G" {iN0} {uG} }});
      ("G", {{s #"env" }})]
     {{e #"Id" "G" #"L1" {u0r} {u0r} {pi1} {pi2} }}
     {{e #"Sig" "G" {idF} {cod} }}
     {{s #"exp" "G" {iN0} {uGirr} }}).

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

  (* Π ~ Π at the universe (Id-U-ΠΠ, Typed.agda:251-261): the term is fully
     authored — see id_u_pi_pi_rule above — but its wf-CHECK is DEFERRED.
     Unlike transp/Idsym/funext (which the perf improvements brought under budget,
     peaking <0.8GB in seconds/minutes), pushing this rule runs the compute_wf_rule
     e-graph saturation for >25min without terminating (memory stays flat ~0.77GB,
     so it is a SATURATION-time wall, not OOM).  It is the deepest term in the
     development: a Σ whose codomain casts its argument CONTRAVARIANTLY across the
     domain equality (cast + Idsym + double codomain instantiation under two
     binders).  To land it, uncomment the push_rule below once the e-graph
     wf-check is faster (or run it with a very large time budget). *)
  (* push_rule id_u_pi_pi_rule. *)

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_id_univ_entry := lang_entry ott_id_univ_wf.
#[export] Hint Resolve ott_id_univ_entry : wf_lang_db.
