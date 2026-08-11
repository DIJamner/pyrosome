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
From Pyrosome.Lang.OTT Require Import Base Nat Pi SubstCommute ProofIrr IdCore IdFunextDefs.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ======================================================================= *)
(* The heterogeneous observational identity type, for the language the      *)
(* normalization proof targets (src/Pyrosome/Gluing/Dtt/).                  *)
(*                                                                          *)
(* This is a SEPARATE fragment from Lang/OTT/Id.v.  Id.v is the exploratory *)
(* OTT playground (it also carries Idrefl / Idsym / transp and feeds        *)
(* Cast.v, Computations.v, IdUniv.v, none of which are in ott_dtt); the     *)
(* fragment below is the one added to ott_dtt, and it differs in three      *)
(* deliberate ways.                                                         *)
(*                                                                          *)
(* (1) NO Idrefl.  [Idcong] strictly generalizes it: taking the congruence  *)
(*     of a term that ignores the bound variable, i.e.                      *)
(*       Idcong Nat C[wkn] c[wkn] zero zero triv : Id C C c c,             *)
(*     where [triv] inhabits [Id Nat Nat zero zero], which "Id-Nat-00"      *)
(*     below reduces to the unit proposition.  So reflexivity is DERIVED.   *)
(*                                                                          *)
(* (2) NO equations for Idcong at all -- not the substitution commutation,  *)
(*     not the computation rules that push it under a constructor.  Every   *)
(*     one of them is an equation between two inhabitants of a code at      *)
(*     [U _ irr _], so [ott_proofirr_el] proves it outright.  They are      *)
(*     DERIVED in Gluing/Dtt/Eqns.v instead of posited here; the            *)
(*     normalization proof still rewrites with them exactly as if they      *)
(*     were rules (that is what makes reification at an Id type a           *)
(*     structural recursion on the congruence's body).                      *)
(*                                                                          *)
(* (3) THE COMPUTATION RULES ARE COMPLETE.  An [Id] whose arguments are all *)
(*     canonical always reduces; equivalently, in a closed environment an   *)
(*     Id type never survives, and the only [Id] codes that are normal are  *)
(*     the NEUTRAL ones (stuck on a neutral endpoint or a neutral code).    *)
(*     That is what keeps the extension from adding any normal form beyond  *)
(*     neutrals.                                                            *)
(*                                                                          *)
(* Id is HETEROGENEOUS: [Id A B t u] relates [t : El A] and [u : El B] for  *)
(* two codes A,B of a common level, and it is that generality which lets    *)
(* the function-extensionality rule below quantify over a pair of arguments *)
(* plus a proof that they are equal, rather than casting one argument       *)
(* across a domain equality (which would need [Cast], whose [u0] gives a    *)
(* code for a universe and breaks the code grammar the proof rests on).     *)
(* ======================================================================= *)


(* The 2-binder (irrelevant-domain) funext rule.  Sibling of IdFunextRel.v. *)

Derive ott_id_funext_irr
       in (wf_lang_ext (ott_id_core ++ ott_id_base) ott_id_funext_irr)
       as ott_id_funext_irr_wf.
Proof.
  setup_lang_interactive.
  push_rule id_pi_pi_irr_rule.

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.

#[local] Definition ott_id_funext_irr_entry := lang_entry ott_id_funext_irr_wf.
#[export] Hint Resolve ott_id_funext_irr_entry : wf_lang_db.
