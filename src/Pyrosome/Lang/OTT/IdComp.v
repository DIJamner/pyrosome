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

(* The congruence former and the Id computation table.  Derived over
   [ott_id_core ++ ott_id_base] -- deliberately WITHOUT the funext rules in
   scope, since their presence changes how "Id-Nat-00" elaborates (measured:
   the re-inferred rules compare unequal).  [ott_id_base], [id_inj_all] and
   the injectivity table all come from IdCore. *)

Derive ott_id_comp
       in (wf_lang_ext (ott_id_core ++ ott_id_base) ott_id_comp)
       as ott_id_comp_wf.
Proof.
  setup_lang_interactive.
  (* --------------------------------------------------------------- *)
  (* The congruence -- the only proof former, and the generalization   *)
  (* of reflexivity.                                                   *)
  (* --------------------------------------------------------------- *)

  (* [Idcong A B b t u e] : from [e : Id A A t u] and a term [b : El B]
     with one free variable of type [El A], conclude that the two
     instantiations of [b] are (heterogeneously) equal:
        Id (B[t]) (B[u]) (b[t]) (b[u]).
     The codomain code B may itself mention the variable, which is
     exactly why the equality has to be heterogeneous.

     It lives in SProp, so positing it as a term former is coherent by
     proof irrelevance, and no computation rule for it is needed: every
     equation one would write -- pushing it under [suc], under a [lam],
     under a substitution, or bottoming out at the variable ([Idcong] of
     [hd] is [e]) or at a closed subterm (reflexivity) -- is an equation
     between two inhabitants of the same irrelevant code, hence already
     provable.  Gluing/Dtt/Eqns.v derives them. *)
  elab_rule {[r "G" : #"env", "l" : #"lvl", "lB" : #"lvl",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] #"rel" "l"),
          "B" : #"exp" (#"ext" "G" (#"El" "A")) (#"info" #"rel" (#"next" "lB"))
                       (#"U" ["G" := #"ext" "G" (#"El" "A")] #"rel" "lB"),
          "b" : #"exp" (#"ext" "G" (#"El" "A")) (#"info" #"rel" (#"iota" "lB")) (#"El" "B"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"]
                             (#"Id" ["G" := "G"] ["l" := "l"] "A" "A" "t" "u"))
      -----------------------------------------------
      #"Idcong" "A" "B" "b" "t" "u" "e"
        : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
          (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"]
                (#"Id" ["G" := "G"] ["l" := "lB"]
                      (#"exp_subst" (#"snoc" #"id" "t") "B")
                      (#"exp_subst" (#"snoc" #"id" "u") "B")
                      (#"exp_subst" (#"snoc" #"id" "t") "b")
                      (#"exp_subst" (#"snoc" #"id" "u") "b")))
    ]}%prerule
    id_inj_all.

  (* --------------------------------------------------------------- *)
  (* Computation, part 1: both codes are Nat.                          *)
  (*                                                                   *)
  (* The four canonical/canonical cases.  Together with the clashes     *)
  (* below they leave an [Id] at Nat stuck exactly when an ENDPOINT is  *)
  (* neutral, which is what makes the extension add no normal form      *)
  (* beyond neutrals.                                                   *)
  (* --------------------------------------------------------------- *)

  (* 0 = 0 : the unit proposition (Pi_irr Empty Empty). *)
  elab_rule {[r "G" : #"env"
      ----------------------------------------------- ("Id-Nat-00")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) #"zero" #"zero"
        = #"Pi_irr" #"irr" #"L0" (#"Empty" ["G" := "G"])
            (#"Empty" ["G" := #"ext" "G" (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Empty" ["G" := "G"]))])
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.

  (* 0 = suc t, suc t = 0 : the constructors are disjoint. *)
  elab_rule {[r "G" : #"env",
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-0S")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) #"zero" (#"suc" "t")
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.
  elab_rule {[r "G" : #"env",
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-S0")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) (#"suc" "t") #"zero"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.

  (* suc is injective. *)
  elab_rule {[r "G" : #"env",
          "m" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"])),
          "n" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-SS")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) (#"suc" "m") (#"suc" "n")
        = #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) "m" "n"
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.

  (* --------------------------------------------------------------- *)
  (* Computation, part 2: the two codes have different heads.          *)
  (*                                                                   *)
  (* Nat against Pi, and Pi against Nat.  These are TYPE-DIRECTED --    *)
  (* the endpoints t,u are arbitrary -- which is why they cost nothing  *)
  (* structurally.                                                      *)
  (* --------------------------------------------------------------- *)

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
    id_inj_all.
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
    id_inj_all.

  (* --------------------------------------------------------------- *)
  (* Computation, part 3: both codes are Pi, but their DOMAIN INDICES  *)
  (* disagree.                                                         *)
  (*                                                                   *)
  (* [Pi_rel G rF lF lG F B] records the domain's relevance and level   *)
  (* in the code, so two Pi codes whose (rF,lF) differ are as distinct  *)
  (* as a Nat and a Pi: the equality clashes to Empty.  Four rules      *)
  (* cover it -- relevance mismatch either way (levels arbitrary), and  *)
  (* level mismatch either way (relevance shared).  They do NOT overlap -- *)
  (* an earlier version of this comment claimed they did, and that was     *)
  (* wrong.  The relevance-mismatch pair pins the two relevances to the    *)
  (* distinct LITERALS rel/irr, while the level-mismatch pair shares one   *)
  (* relevance METAVARIABLE rF, so the two families are mutually           *)
  (* exclusive and the four transcribe directly as a partition.  That      *)
  (* matters downstream: the value layer's Id table needs a partition for  *)
  (* determinism, and gets one without restructuring.  (Kept for the       *)
  (* record: harmless even if they had overlapped, since all give Empty.)  *)
  (* is harmless: every one of them gives Empty.  The remaining case,   *)
  (* (rF,lF) shared, is genuine function extensionality, below.         *)
  (* --------------------------------------------------------------- *)

  elab_rule {[r "G" : #"env", "l" : #"lvl", "lF1" : #"lvl", "lF2" : #"lvl",
          "F1" : #"exp" "G" (#"info" #"rel" (#"next" "lF1")) (#"U" ["G" := "G"] #"rel" "lF1"),
          "B1" : #"exp" (#"ext" "G" (#"El" "F1")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F1")] #"rel" "l"),
          "F2" : #"exp" "G" (#"info" #"rel" (#"next" "lF2")) (#"U" ["G" := "G"] #"irr" "lF2"),
          "B2" : #"exp" (#"ext" "G" (#"El" "F2")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F2")] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] #"rel" "lF1" "l" "F1" "B1")),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] #"irr" "lF2" "l" "F2" "B2"))
      ----------------------------------------------- ("Id-Pi-Pi-rel-irr")
      #"Id" ["G" := "G"] ["l" := "l"]
            (#"Pi_rel" ["G" := "G"] #"rel" "lF1" "l" "F1" "B1")
            (#"Pi_rel" ["G" := "G"] #"irr" "lF2" "l" "F2" "B2") "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.
  elab_rule {[r "G" : #"env", "l" : #"lvl", "lF1" : #"lvl", "lF2" : #"lvl",
          "F1" : #"exp" "G" (#"info" #"rel" (#"next" "lF1")) (#"U" ["G" := "G"] #"irr" "lF1"),
          "B1" : #"exp" (#"ext" "G" (#"El" "F1")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F1")] #"rel" "l"),
          "F2" : #"exp" "G" (#"info" #"rel" (#"next" "lF2")) (#"U" ["G" := "G"] #"rel" "lF2"),
          "B2" : #"exp" (#"ext" "G" (#"El" "F2")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F2")] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] #"irr" "lF1" "l" "F1" "B1")),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] #"rel" "lF2" "l" "F2" "B2"))
      ----------------------------------------------- ("Id-Pi-Pi-irr-rel")
      #"Id" ["G" := "G"] ["l" := "l"]
            (#"Pi_rel" ["G" := "G"] #"irr" "lF1" "l" "F1" "B1")
            (#"Pi_rel" ["G" := "G"] #"rel" "lF2" "l" "F2" "B2") "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.
  elab_rule {[r "G" : #"env", "l" : #"lvl", "rF" : #"relevance",
          "F1" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] "rF" #"L0"),
          "B1" : #"exp" (#"ext" "G" (#"El" "F1")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F1")] #"rel" "l"),
          "F2" : #"exp" "G" (#"info" #"rel" (#"next" #"L1")) (#"U" ["G" := "G"] "rF" #"L1"),
          "B2" : #"exp" (#"ext" "G" (#"El" "F2")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F2")] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] "rF" #"L0" "l" "F1" "B1")),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] "rF" #"L1" "l" "F2" "B2"))
      ----------------------------------------------- ("Id-Pi-Pi-L0-L1")
      #"Id" ["G" := "G"] ["l" := "l"]
            (#"Pi_rel" ["G" := "G"] "rF" #"L0" "l" "F1" "B1")
            (#"Pi_rel" ["G" := "G"] "rF" #"L1" "l" "F2" "B2") "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.
  elab_rule {[r "G" : #"env", "l" : #"lvl", "rF" : #"relevance",
          "F1" : #"exp" "G" (#"info" #"rel" (#"next" #"L1")) (#"U" ["G" := "G"] "rF" #"L1"),
          "B1" : #"exp" (#"ext" "G" (#"El" "F1")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F1")] #"rel" "l"),
          "F2" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] "rF" #"L0"),
          "B2" : #"exp" (#"ext" "G" (#"El" "F2")) (#"info" #"rel" (#"next" "l"))
                        (#"U" ["G" := #"ext" "G" (#"El" "F2")] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] "rF" #"L1" "l" "F1" "B1")),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "l"] (#"Pi_rel" ["G" := "G"] "rF" #"L0" "l" "F2" "B2"))
      ----------------------------------------------- ("Id-Pi-Pi-L1-L0")
      #"Id" ["G" := "G"] ["l" := "l"]
            (#"Pi_rel" ["G" := "G"] "rF" #"L1" "l" "F1" "B1")
            (#"Pi_rel" ["G" := "G"] "rF" #"L0" "l" "F2" "B2") "t" "u"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    id_inj_all.

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_id_comp_entry := lang_entry ott_id_comp_wf.
#[export] Hint Resolve ott_id_comp_entry : wf_lang_db.
