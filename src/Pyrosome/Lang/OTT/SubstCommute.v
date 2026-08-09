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

(* Substitution commutes with the proof-irrelevant λ — the exact mirror of
   "lam_rel subst" in Pi.v (codomain code B and body t both lifted along
   `under' g` = snoc (cmp wkn g) hd).

   Written FULLY PRE-ELABORATED and added with `push_rule` (which runs only
   the automated wf-CHECK, `compute_wf_rule`; ~55s) rather than via
   `elab_rule`.  `elab_rule` DOES succeed on this rule, but it records the
   codomain code B at the info spelling `info rel (iota L1)` — inherited from
   `Pi_irr`, which is the only former mentioned in this rule's conclusion
   sort.  `next L0` and `iota L1` are provably equal (the "next0" rule of
   ott_info) but are not the same term, and ott_pi's own `lam_irr` (and
   `app_irr`) rules store B at `info rel (next L0)`.  Spelling it by hand
   keeps this rule syntactically aligned with the constructor it is about. *)
Definition lam_irr_subst_rule : string * rule :=
  let iF   : term := {{e #"info" "rF" (#"iota" "lF") }} in
  let iuF  : term := {{e #"info" #"rel" (#"next" "lF") }} in
  let iB   : term := {{e #"info" #"rel" (#"next" #"L0") }} in
  let it   : term := {{e #"info" #"irr" (#"iota" #"L0") }} in
  let uF'  : term := {{e #"U" "G'" "rF" "lF" }} in
  let elF' : term := {{e #"El" "G'" "rF" "lF" "F" }} in
  let gext' : term := {{e #"ext" "G'" {iF} {elF'} }} in
  let gF   : term := {{e #"exp_subst" "G" "G'" "g" {iuF} {uF'} "F" }} in
  let elgF : term := {{e #"El" "G" "rF" "lF" {gF} }} in
  let gext : term := {{e #"ext" "G" {iF} {elgF} }} in
  (* under' g : gext -> gext' *)
  let underg : term := {{e #"snoc" {gext} "G'" {iF} {elF'}
                            (#"cmp" {gext} "G" "G'" (#"wkn" "G" {iF} {elgF}) "g")
                            (#"hd" "G" {iF} {elgF}) }} in
  let uB'  : term := {{e #"U" {gext'} #"irr" #"L0" }} in
  let elB' : term := {{e #"El" {gext'} #"irr" #"L0" "B" }} in
  let gB   : term := {{e #"exp_subst" {gext} {gext'} {underg} {iB} {uB'} "B" }} in
  let gt   : term := {{e #"exp_subst" {gext} {gext'} {underg} {it} {elB'} "t" }} in
  let pity : term := {{e #"El" "G'" #"irr" #"L0" (#"Pi_irr" "G'" "rF" "lF" "F" "B") }} in
  ("lam_irr subst",
   term_eq_rule
     [("t", {{s #"exp" {gext'} {it} {elB'} }});
      ("B", {{s #"exp" {gext'} {iB} {uB'} }});
      ("F", {{s #"exp" "G'" {iuF} {uF'} }});
      ("lF", {{s #"lvl" }});
      ("rF", {{s #"relevance" }});
      ("g", {{s #"sub" "G" "G'" }});
      ("G'", {{s #"env" }});
      ("G", {{s #"env" }})]
     {{e #"exp_subst" "G" "G'" "g" {it} {pity} (#"lam_irr" "G'" "rF" "lF" "F" "B" "t") }}
     {{e #"lam_irr" "G" "rF" "lF" {gF} {gB} {gt} }}
     {{s #"exp" "G" {it} (#"ty_subst" "G" "G'" "g" {it} {pity}) }}).

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

  (* substitution commutes with the proof-irrelevant λ; see the comment on   *)
  (* lam_irr_subst_rule above for why this one is pre-elaborated.            *)
  push_rule lam_irr_subst_rule.

  (* substitution commutes with the proof-irrelevant application.            *)
  (*                                                                         *)
  (* The two sides live at DIFFERENT spellings of the same sort:             *)
  (*   LHS  g[app_irr .. f a]           : ty_subst g (ty_subst <id,a> (El B))*)
  (*   RHS  app_irr .. g[f] g[a]        : ty_subst <id,g[a]> (El (g^+)[B])   *)
  (* They are equal (ty_subst_cmp + cmp_snoc + the id laws) and BOTH pass    *)
  (* compute_wf_rule.  We write the RIGHT-hand spelling, because the         *)
  (* left-hand one makes the elaborator record B's context sort with the     *)
  (* `info rel (iota L1)` spelling of the code info, whereas the `app_irr` / *)
  (* `lam_irr` rules of ott_pi use `info rel (next L0)` (the two are equal   *)
  (* by "next0" but are not the same term, so a mismatch would make this     *)
  (* rule fail to apply syntactically).  Note the elaborator normalizes the  *)
  (* CONCLUSION sort back to the left-hand `ty_subst g (ty_subst ...)` form  *)
  (* either way.                                                             *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "rF" : #"relevance", "lF" : #"lvl",
          "F" : #"exp" "G'" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G'"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G'" (#"El" "F")) (#"info" #"rel" (#"next" #"L0"))
                       (#"U" ["G" := #"ext" "G'" (#"El" "F")] #"irr" #"L0"),
          "f" : #"exp" "G'" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G'"] ["r" := #"irr"] ["l" := #"L0"] (#"Pi_irr" ["G" := "G'"] "rF" "lF" "F" "B")),
          "a" : #"exp" "G'" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      ----------------------------------------------- ("app_irr subst")
      #"exp_subst" "g" (#"app_irr" "rF" "lF" "F" "B" "f" "a")
        = #"app_irr" "rF" "lF" (#"exp_subst" "g" "F")
              (#"exp_subst" {inr (under' {{pe "g"}}) } "B")
              (#"exp_subst" "g" "f") (#"exp_subst" "g" "a")
      : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
        (#"ty_subst" (#"snoc" #"id" (#"exp_subst" "g" "a"))
              (#"El" (#"exp_subst" {inr (under' {{pe "g"}}) } "B")))
    ]}%prerule
    (pi_injectivity ++ nat_injectivity ++ ott_base_injectivity
       ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* substitution commutes with the proof-relevant application.  Same sort   *)
  (* situation as "app_irr subst" above; here the codomain level is the      *)
  (* variable "lG", so `next "lG"` has no alternative spelling.              *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G'" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G'"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G'" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G'" (#"El" "F")] #"rel" "lG"),
          "f" : #"exp" "G'" (#"info" #"rel" (#"iota" "lG"))
                       (#"El" ["G" := "G'"] ["r" := #"rel"] ["l" := "lG"] (#"Pi_rel" ["G" := "G'"] "rF" "lF" "lG" "F" "B")),
          "a" : #"exp" "G'" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      ----------------------------------------------- ("app_rel subst")
      #"exp_subst" "g" (#"app_rel" "rF" "lF" "lG" "F" "B" "f" "a")
        = #"app_rel" "rF" "lF" "lG" (#"exp_subst" "g" "F")
              (#"exp_subst" {inr (under' {{pe "g"}}) } "B")
              (#"exp_subst" "g" "f") (#"exp_subst" "g" "a")
      : #"exp" "G" (#"info" #"rel" (#"iota" "lG"))
        (#"ty_subst" (#"snoc" #"id" (#"exp_subst" "g" "a"))
              (#"El" (#"exp_subst" {inr (under' {{pe "g"}}) } "B")))
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
