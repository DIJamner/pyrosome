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
From Pyrosome.Lang.OTT Require Import Base Nat Pi.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ====================================================================== *)
(* The four substitution-commutation rules missing from                    *)
(*   ott_dtt = ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info.     *)
(*                                                                         *)
(* Without them `g[app_rel F B f a]`, `g[app_irr F B f a]`,                *)
(* `g[lam_irr F B t]` and `g[Emptyrec A e]` are STUCK under an explicit    *)
(* substitution, so normal forms are not stable under weakening and the    *)
(* normalization statement is false for the language as it stands.         *)
(* (`Pi.v` claims "lam_irr subst is subsumed by proof irrelevance" — true  *)
(* in the full theory with Lang/OTT/ProofIrr.v, but ProofIrr is out of     *)
(* scope for the normalization proof, so the rule is genuinely absent      *)
(* there.)                                                                 *)
(*                                                                         *)
(* Kept in a SEPARATE extension so that every already-compiled language    *)
(* (Sigma, Id, Cast, ProofIrr, Computations) is untouched.                 *)
(* ====================================================================== *)

Derive ott_subst_commute
  in (wf_lang_ext (ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info) ott_subst_commute)
  as ott_subst_commute_wf.
Proof.
  setup_lang_interactive.

  (* substitution commutes with Emptyrec (no binder).                      *)
  (* The sort is written in the RIGHT-hand form `El g[A]` rather than the  *)
  (* left-hand `ty_subst g (El A)`; the two are equal by "El subst".        *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "rA" : #"relevance", "lA" : #"lvl",
          "A" : #"exp" "G'" (#"info" #"rel" (#"next" "lA")) (#"U" ["G" := "G'"] "rA" "lA"),
          "e" : #"exp" "G'" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G'"] ["r" := #"irr"] ["l" := #"L0"] (#"Empty" ["G" := "G'"]))
      ----------------------------------------------- ("Emptyrec subst")
      #"exp_subst" "g" (#"Emptyrec" "A" "e")
        = #"Emptyrec" (#"exp_subst" "g" "A") (#"exp_subst" "g" "e")
      : #"exp" "G" (#"info" "rA" (#"iota" "lA")) (#"El" (#"exp_subst" "g" "A"))
    ]}%prerule
    (pi_injectivity ++ nat_injectivity ++ ott_base_injectivity
       ++ ott_info_injectivity ++ subst_ott_injectivity).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_subst_commute_entry := lang_entry ott_subst_commute_wf.
#[export] Hint Resolve ott_subst_commute_entry : wf_lang_db.
