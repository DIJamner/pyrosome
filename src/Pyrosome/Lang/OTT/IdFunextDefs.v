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
From Pyrosome.Lang.OTT Require Import Base Nat Pi SubstCommute ProofIrr IdCore.

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


(* DEFINITIONS ONLY -- no Derive, so this file costs seconds.  The two rules are
   checked in IdFunextRel.v and IdFunextIrr.v, which are SIBLINGS over the same
   base: neither rule is in the other's prefix, so neither pays for the other.
   Sequencing them in one Derive cost hours -- the irrelevant rule went from
   ~4 min to >16 min purely from having the relevant one ahead of it. *)
(* Pre-elaborated function-extensionality rules for ott_id_cong.
   To be inserted into src/Pyrosome/Lang/OTT/IdCong.v BEFORE the Derive,
   and pushed with `push_rule` inside the Derive block.

   Con argument orders (read off Gluing/Dtt/Syntax.v, authoritative):
     ext   G i A          wkn G i A        hd G i A
     cmp   G1 G2 G3 f g   (f : sub G1 G2, g : sub G2 G3)
     snoc  G G' i A g v   (g : sub G G', result : sub G (ext G' i A))
     exp_subst G G' g i A v      (A : ty G' i, v : exp G' i A)
     El G r l e           U G r l
     Pi_rel G rF lF lG F B       Pi_irr G rF lF F B
     app_rel G rF lF lG F B f a
     Id G l A B t u
*)

(* ---------------------------------------------------------------- *)
(* IRRELEVANT domains: two binders, no domain-equality premise.       *)
(*                                                                    *)
(*   Id (Pi_rel irr lF l F1 B1) (Pi_rel irr lF l F2 B2) f g           *)
(*     = Pi_irr irr lF F1 (Pi_irr irr lF F2[w1]                       *)
(*         (Id (B1[a1]) (B2[a2]) (f a1) (g a2)))                      *)
(*                                                                    *)
(* Sound WITHOUT the premise because a relevant result cannot depend  *)
(* on an irrelevant argument except through Emptyrec.                 *)
(* ---------------------------------------------------------------- *)
Definition id_pi_pi_irr_rule : string * rule :=
  let iF    : term := {{e #"info" #"irr" (#"iota" "lF") }} in
  let nF    : term := {{e #"info" #"rel" (#"next" "lF") }} in
  let nl    : term := {{e #"info" #"rel" (#"next" "l") }} in
  let il    : term := {{e #"info" #"rel" (#"iota" "l") }} in
  let UGF   : term := {{e #"U" "G" #"irr" "lF" }} in
  let elF1  : term := {{e #"El" "G" #"irr" "lF" "F1" }} in
  let elF2  : term := {{e #"El" "G" #"irr" "lF" "F2" }} in
  let X1    : term := {{e #"ext" "G" {iF} {elF1} }} in
  let X2    : term := {{e #"ext" "G" {iF} {elF2} }} in
  let UX1   : term := {{e #"U" {X1} #"rel" "l" }} in
  let UX2   : term := {{e #"U" {X2} #"rel" "l" }} in
  let pi1   : term := {{e #"Pi_rel" "G" #"irr" "lF" "l" "F1" "B1" }} in
  let pi2   : term := {{e #"Pi_rel" "G" #"irr" "lF" "l" "F2" "B2" }} in
  let elpi1 : term := {{e #"El" "G" #"rel" "l" {pi1} }} in
  let elpi2 : term := {{e #"El" "G" #"rel" "l" {pi2} }} in
  (* binder 1: a1 : El F1, living in X1 *)
  let w1    : term := {{e #"wkn" "G" {iF} {elF1} }} in
  let a1    : term := {{e #"hd" "G" {iF} {elF1} }} in
  let F1w   : term := {{e #"exp_subst" {X1} "G" {w1} {nF} {UGF} "F1" }} in
  let elF1w : term := {{e #"El" {X1} #"irr" "lF" {F1w} }} in
  let F2w   : term := {{e #"exp_subst" {X1} "G" {w1} {nF} {UGF} "F2" }} in
  let elF2w : term := {{e #"El" {X1} #"irr" "lF" {F2w} }} in
  (* binder 2: a2 : El F2[w1], living in Y *)
  let Y     : term := {{e #"ext" {X1} {iF} {elF2w} }} in
  let w2    : term := {{e #"wkn" {X1} {iF} {elF2w} }} in
  let a2    : term := {{e #"hd" {X1} {iF} {elF2w} }} in
  let w21   : term := {{e #"cmp" {Y} {X1} "G" {w2} {w1} }} in
  let a1w   : term := {{e #"exp_subst" {Y} {X1} {w2} {iF} {elF1w} {a1} }} in
  (* the domain codes, weakened all the way to Y *)
  let F1s   : term := {{e #"exp_subst" {Y} "G" {w21} {nF} {UGF} "F1" }} in
  let F2s   : term := {{e #"exp_subst" {Y} "G" {w21} {nF} {UGF} "F2" }} in
  let elF1s : term := {{e #"El" {Y} #"irr" "lF" {F1s} }} in
  let elF2s : term := {{e #"El" {Y} #"irr" "lF" {F2s} }} in
  (* the two codomain instances *)
  let ins1  : term := {{e #"snoc" {Y} "G" {iF} {elF1} {w21} {a1w} }} in
  let ins2  : term := {{e #"snoc" {Y} "G" {iF} {elF2} {w21} {a2} }} in
  let cod1   : term := {{e #"exp_subst" {Y} {X1} {ins1} {nl} {UX1} "B1" }} in
  let cod2   : term := {{e #"exp_subst" {Y} {X2} {ins2} {nl} {UX2} "B2" }} in
  (* the two applications: codomain codes lifted along w21 *)
  let YF1   : term := {{e #"ext" {Y} {iF} {elF1s} }} in
  let YF2   : term := {{e #"ext" {Y} {iF} {elF2s} }} in
  let lift1 : term := {{e #"snoc" {YF1} "G" {iF} {elF1}
                          (#"cmp" {YF1} {Y} "G" (#"wkn" {Y} {iF} {elF1s}) {w21})
                          (#"hd" {Y} {iF} {elF1s}) }} in
  let lift2 : term := {{e #"snoc" {YF2} "G" {iF} {elF2}
                          (#"cmp" {YF2} {Y} "G" (#"wkn" {Y} {iF} {elF2s}) {w21})
                          (#"hd" {Y} {iF} {elF2s}) }} in
  let lifb1   : term := {{e #"exp_subst" {YF1} {X1} {lift1} {nl} {UX1} "B1" }} in
  let lifb2   : term := {{e #"exp_subst" {YF2} {X2} {lift2} {nl} {UX2} "B2" }} in
  let fw    : term := {{e #"exp_subst" {Y} "G" {w21} {il} {elpi1} "f" }} in
  let gw    : term := {{e #"exp_subst" {Y} "G" {w21} {il} {elpi2} "g" }} in
  let app1  : term := {{e #"app_rel" {Y} #"irr" "lF" "l" {F1s} {lifb1} {fw} {a1w} }} in
  let app2  : term := {{e #"app_rel" {Y} #"irr" "lF" "l" {F2s} {lifb2} {gw} {a2} }} in
  let body  : term := {{e #"Id" {Y} "l" {cod1} {cod2} {app1} {app2} }} in
  let inner : term := {{e #"Pi_irr" {X1} #"irr" "lF" {F2w} {body} }} in
  ("Id-Pi-Pi-irr",
   term_eq_rule
     [("g", {{s #"exp" "G" {il} {elpi2} }});
      ("f", {{s #"exp" "G" {il} {elpi1} }});
      ("B2", {{s #"exp" {X2} {nl} {UX2} }});
      ("F2", {{s #"exp" "G" {nF} {UGF} }});
      ("B1", {{s #"exp" {X1} {nl} {UX1} }});
      ("F1", {{s #"exp" "G" {nF} {UGF} }});
      ("l", {{s #"lvl" }});
      ("lF", {{s #"lvl" }});
      ("G", {{s #"env" }})]
     {{e #"Id" "G" "l" {pi1} {pi2} "f" "g" }}
     {{e #"Pi_irr" "G" #"irr" "lF" "F1" {inner} }}
     {{s #"exp" "G" (#"info" #"rel" (#"iota" #"L1")) (#"U" "G" #"irr" #"L0") }}).

(* ---------------------------------------------------------------- *)
(* RELEVANT domains: three binders, with the domain-equality premise. *)
(*                                                                    *)
(*   Id (Pi_rel rel lF l F1 B1) (Pi_rel rel lF l F2 B2) f g           *)
(*     = Pi_irr rel lF F1 (Pi_irr rel lF F2[w1]                       *)
(*         (Pi_irr irr L0 (Id F1 F2 a1 a2)                            *)
(*           (Id (B1[a1]) (B2[a2]) (f a1) (g a2))))                   *)
(* ---------------------------------------------------------------- *)
Definition id_pi_pi_rel_rule : string * rule :=
  let iF    : term := {{e #"info" #"rel" (#"iota" "lF") }} in
  let iP    : term := {{e #"info" #"irr" (#"iota" #"L0") }} in
  let nF    : term := {{e #"info" #"rel" (#"next" "lF") }} in
  let nl    : term := {{e #"info" #"rel" (#"next" "l") }} in
  let il    : term := {{e #"info" #"rel" (#"iota" "l") }} in
  let n0    : term := {{e #"info" #"rel" (#"iota" #"L1") }} in
  let UGF   : term := {{e #"U" "G" #"rel" "lF" }} in
  let elF1  : term := {{e #"El" "G" #"rel" "lF" "F1" }} in
  let elF2  : term := {{e #"El" "G" #"rel" "lF" "F2" }} in
  let X1    : term := {{e #"ext" "G" {iF} {elF1} }} in
  let X2    : term := {{e #"ext" "G" {iF} {elF2} }} in
  let UX1   : term := {{e #"U" {X1} #"rel" "l" }} in
  let UX2   : term := {{e #"U" {X2} #"rel" "l" }} in
  let pi1   : term := {{e #"Pi_rel" "G" #"rel" "lF" "l" "F1" "B1" }} in
  let pi2   : term := {{e #"Pi_rel" "G" #"rel" "lF" "l" "F2" "B2" }} in
  let elpi1 : term := {{e #"El" "G" #"rel" "l" {pi1} }} in
  let elpi2 : term := {{e #"El" "G" #"rel" "l" {pi2} }} in
  (* binder 1: a1 : El F1, in X1 *)
  let w1    : term := {{e #"wkn" "G" {iF} {elF1} }} in
  let a1    : term := {{e #"hd" "G" {iF} {elF1} }} in
  let F1w   : term := {{e #"exp_subst" {X1} "G" {w1} {nF} {UGF} "F1" }} in
  let elF1w : term := {{e #"El" {X1} #"rel" "lF" {F1w} }} in
  let F2w   : term := {{e #"exp_subst" {X1} "G" {w1} {nF} {UGF} "F2" }} in
  let elF2w : term := {{e #"El" {X1} #"rel" "lF" {F2w} }} in
  (* binder 2: a2 : El F2[w1], in Y *)
  let Y     : term := {{e #"ext" {X1} {iF} {elF2w} }} in
  let w2    : term := {{e #"wkn" {X1} {iF} {elF2w} }} in
  let a2    : term := {{e #"hd" {X1} {iF} {elF2w} }} in
  let w21   : term := {{e #"cmp" {Y} {X1} "G" {w2} {w1} }} in
  let a1w   : term := {{e #"exp_subst" {Y} {X1} {w2} {iF} {elF1w} {a1} }} in
  let F1s   : term := {{e #"exp_subst" {Y} "G" {w21} {nF} {UGF} "F1" }} in
  let F2s   : term := {{e #"exp_subst" {Y} "G" {w21} {nF} {UGF} "F2" }} in
  (* binder 3: p : Id F1 F2 a1 a2, in Z *)
  let ieq   : term := {{e #"Id" {Y} "lF" {F1s} {F2s} {a1w} {a2} }} in
  let elieq : term := {{e #"El" {Y} #"irr" #"L0" {ieq} }} in
  let Z     : term := {{e #"ext" {Y} {iP} {elieq} }} in
  let w3    : term := {{e #"wkn" {Y} {iP} {elieq} }} in
  let w3G   : term := {{e #"cmp" {Z} {Y} "G" {w3} {w21} }} in
  (* everything transported from Y to Z *)
  let a1z   : term := {{e #"exp_subst" {Z} {Y} {w3} {iF} (#"El" {Y} #"rel" "lF" {F1s}) {a1w} }} in
  let a2z   : term := {{e #"exp_subst" {Z} {Y} {w3} {iF} (#"El" {Y} #"rel" "lF" {F2s}) {a2} }} in
  let F1z   : term := {{e #"exp_subst" {Z} "G" {w3G} {nF} {UGF} "F1" }} in
  let F2z   : term := {{e #"exp_subst" {Z} "G" {w3G} {nF} {UGF} "F2" }} in
  let elF1z : term := {{e #"El" {Z} #"rel" "lF" {F1z} }} in
  let elF2z : term := {{e #"El" {Z} #"rel" "lF" {F2z} }} in
  (* the two codomain instances, in Z *)
  let ins1  : term := {{e #"snoc" {Z} "G" {iF} {elF1} {w3G} {a1z} }} in
  let ins2  : term := {{e #"snoc" {Z} "G" {iF} {elF2} {w3G} {a2z} }} in
  let cod1   : term := {{e #"exp_subst" {Z} {X1} {ins1} {nl} {UX1} "B1" }} in
  let cod2   : term := {{e #"exp_subst" {Z} {X2} {ins2} {nl} {UX2} "B2" }} in
  (* the two applications, in Z *)
  let ZF1   : term := {{e #"ext" {Z} {iF} {elF1z} }} in
  let ZF2   : term := {{e #"ext" {Z} {iF} {elF2z} }} in
  let lift1 : term := {{e #"snoc" {ZF1} "G" {iF} {elF1}
                          (#"cmp" {ZF1} {Z} "G" (#"wkn" {Z} {iF} {elF1z}) {w3G})
                          (#"hd" {Z} {iF} {elF1z}) }} in
  let lift2 : term := {{e #"snoc" {ZF2} "G" {iF} {elF2}
                          (#"cmp" {ZF2} {Z} "G" (#"wkn" {Z} {iF} {elF2z}) {w3G})
                          (#"hd" {Z} {iF} {elF2z}) }} in
  let lifb1   : term := {{e #"exp_subst" {ZF1} {X1} {lift1} {nl} {UX1} "B1" }} in
  let lifb2   : term := {{e #"exp_subst" {ZF2} {X2} {lift2} {nl} {UX2} "B2" }} in
  let fz    : term := {{e #"exp_subst" {Z} "G" {w3G} {il} {elpi1} "f" }} in
  let gz    : term := {{e #"exp_subst" {Z} "G" {w3G} {il} {elpi2} "g" }} in
  let app1  : term := {{e #"app_rel" {Z} #"rel" "lF" "l" {F1z} {lifb1} {fz} {a1z} }} in
  let app2  : term := {{e #"app_rel" {Z} #"rel" "lF" "l" {F2z} {lifb2} {gz} {a2z} }} in
  let body  : term := {{e #"Id" {Z} "l" {cod1} {cod2} {app1} {app2} }} in
  let mid   : term := {{e #"Pi_irr" {Y} #"irr" #"L0" {ieq} {body} }} in
  let inner : term := {{e #"Pi_irr" {X1} #"rel" "lF" {F2w} {mid} }} in
  ("Id-Pi-Pi-rel",
   term_eq_rule
     [("g", {{s #"exp" "G" {il} {elpi2} }});
      ("f", {{s #"exp" "G" {il} {elpi1} }});
      ("B2", {{s #"exp" {X2} {nl} {UX2} }});
      ("F2", {{s #"exp" "G" {nF} {UGF} }});
      ("B1", {{s #"exp" {X1} {nl} {UX1} }});
      ("F1", {{s #"exp" "G" {nF} {UGF} }});
      ("l", {{s #"lvl" }});
      ("lF", {{s #"lvl" }});
      ("G", {{s #"env" }})]
     {{e #"Id" "G" "l" {pi1} {pi2} "f" "g" }}
     {{e #"Pi_irr" "G" #"rel" "lF" "F1" {inner} }}
     {{s #"exp" "G" {n0} (#"U" "G" #"irr" #"L0") }}).

