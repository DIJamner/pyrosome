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
From Pyrosome.Lang.OTT Require Import Base Nat Pi SubstCommute ProofIrr.

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

Definition id_cong_injectivity :=
  [("Id", ["u"; "t"; "B"; "A"; "l"; "G"]);
   ("Idcong", ["e"; "u"; "t"; "b"; "B"; "lB"; "A"; "l"; "G"])].

Definition ott_id_base :=
  ott_proofirr_el ++ ott_subst_commute ++ ott_pi ++ ott_nat ++ ott_base
    ++ subst_ott ++ ott_info.

Definition id_inj_all :=
  id_cong_injectivity ++ pi_injectivity ++ nat_injectivity
    ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity.

(* ======================================================================= *)
(* SPLIT INTO FOUR FILES, and the reason is performance.                    *)
(*                                                                          *)
(* [compute_wf_rule] checks each rule against its PREFIX, and its cost      *)
(* grows sharply with that prefix: the 3-binder funext rule was measured at *)
(* 1h55m against a two-rule prefix and had not finished after 2h35m against *)
(* the full one.  Splitting lets each rule be checked against the smallest  *)
(* prefix it actually needs, and the pieces are then concatenated, with     *)
(* [Core.lang_ext_monotonicity] lifting a rule verified against a small     *)
(* prefix to its position in the assembled language.                        *)
(*                                                                          *)
(*   IdCore.v    ott_id_core    Id, Id subst                     (seconds)  *)
(*   IdComp.v    ott_id_comp    Idcong + the computation rules   (~4 min)   *)
(*   IdFunext.v  ott_id_funext  the two funext rules             (~2 h)     *)
(*   IdCong.v    ott_id_cong    = funext ++ comp ++ core, assembled          *)
(*                                                                          *)
(* The payoff is not the first build, it is every later one: editing a      *)
(* computation rule no longer re-triggers the two-hour funext check.        *)
(*                                                                          *)
(* IdComp is derived over [ott_id_core ++ ott_id_base] and NOT over the     *)
(* funext rules, which is also forced: with a funext rule in scope,         *)
(* [infer_rule] re-elaborates "Id-Nat-00" to a DIFFERENT rule (the          *)
(* next L0 <-> iota L1 flip).  Deriving the two extensions over a COMMON    *)
(* base keeps each one's elaboration exactly as it is today.                *)
(* ======================================================================= *)

Derive ott_id_core
       in (wf_lang_ext ott_id_base ott_id_core)
       as ott_id_core_wf.
Proof.
  setup_lang_interactive.
  (* --------------------------------------------------------------- *)
  (* The code.                                                        *)
  (* --------------------------------------------------------------- *)

  (* [Id A B t u] : the heterogeneous equality of [t : El A] and
     [u : El B], a code in SProp = U_{%,0}.  A and B are proof-RELEVANT
     codes at a common level [l]; there is no [Id] between irrelevant
     codes, and none is needed -- proof irrelevance already equates all
     inhabitants of those. *)
  elab_rule {[r "G" : #"env", "l" : #"lvl",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] #"rel" "l"),
          "B" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "B")
      -----------------------------------------------
      #"Id" "A" "B" "t" "u" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.

  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'", "l" : #"lvl",
          "A" : #"exp" "G'" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G'"] #"rel" "l"),
          "B" : #"exp" "G'" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G'"] #"rel" "l"),
          "t" : #"exp" "G'" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "u" : #"exp" "G'" (#"info" #"rel" (#"iota" "l")) (#"El" "B")
      ----------------------------------------------- ("Id subst")
      #"exp_subst" "g" (#"Id" "A" "B" "t" "u")
        = #"Id" (#"exp_subst" "g" "A") (#"exp_subst" "g" "B") (#"exp_subst" "g" "t") (#"exp_subst" "g" "u")
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_id_core_entry := lang_entry ott_id_core_wf.
#[export] Hint Resolve ott_id_core_entry : wf_lang_db.
