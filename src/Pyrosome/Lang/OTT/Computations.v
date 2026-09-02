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

(* Id-Π — function extensionality (Typed.agda:231-240), homogeneous form.
   Two functions f,g : Π F B are equal iff they agree pointwise:
     Id (Π F B) (Π F B) f g  ↝  Π(a:F). Id B B (f·a) (g·a)   [a proof-irr Π]
   The inner equality is on the CODOMAIN (rel), so no constraint on the domain
   relevance rF and no cast is needed.  Pre-elaborated (all implicit env/subst
   args explicit) and added with push_rule, exactly like Pi.v's `Pi_rel eta`,
   because the deeply-nested binder+application body defeats elab_rule's
   inference.  The application body reuses the eta rule's wkF/liftB/app_rel
   spelling (so app_rel … : El B by the same conversion). *)
Definition id_pi_funext_rule : string * rule :=
  let iF : term := {{e #"info" "rF" (#"iota" "lF") }} in
  let elF : term := {{e #"El" "G" "rF" "lF" "F" }} in
  let gext : term := {{e #"ext" "G" {iF} {elF} }} in
  let wkn_g : term := {{e #"wkn" "G" {iF} {elF} }} in
  let wkF : term := {{e #"exp_subst" {gext} "G" {wkn_g} (#"info" #"rel" (#"next" "lF")) (#"U" "G" "rF" "lF") "F" }} in
  let elwkF : term := {{e #"El" {gext} "rF" "lF" {wkF} }} in
  let extnew : term := {{e #"ext" {gext} {iF} {elwkF} }} in
  let underwkn : term := {{e #"snoc" {extnew} "G" {iF} {elF}
                              (#"cmp" {extnew} {gext} "G" (#"wkn" {gext} {iF} {elwkF}) {wkn_g})
                              (#"hd" {gext} {iF} {elwkF}) }} in
  let liftB : term := {{e #"exp_subst" {extnew} {gext} {underwkn} (#"info" #"rel" (#"next" "lG")) (#"U" {gext} #"rel" "lG") "B" }} in
  let piFB : term := {{e #"Pi_rel" "G" "rF" "lF" "lG" "F" "B" }} in
  let elpi : term := {{e #"El" "G" #"rel" "lG" {piFB} }} in
  let wkf : term := {{e #"exp_subst" {gext} "G" {wkn_g} (#"info" #"rel" (#"iota" "lG")) {elpi} "f" }} in
  let wkg : term := {{e #"exp_subst" {gext} "G" {wkn_g} (#"info" #"rel" (#"iota" "lG")) {elpi} "g" }} in
  let hd_a : term := {{e #"hd" "G" {iF} {elF} }} in
  let appf : term := {{e #"app_rel" {gext} "rF" "lF" "lG" {wkF} {liftB} {wkf} {hd_a} }} in
  let appg : term := {{e #"app_rel" {gext} "rF" "lF" "lG" {wkF} {liftB} {wkg} {hd_a} }} in
  let bodyId : term := {{e #"Id" {gext} "lG" "B" "B" {appf} {appg} }} in
  ("Id-Pi",
   term_eq_rule
     [("g", {{s #"exp" "G" (#"info" #"rel" (#"iota" "lG")) {elpi} }});
      ("f", {{s #"exp" "G" (#"info" #"rel" (#"iota" "lG")) {elpi} }});
      ("B", {{s #"exp" {gext} (#"info" #"rel" (#"next" "lG")) (#"U" {gext} #"rel" "lG") }});
      ("F", {{s #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" "G" "rF" "lF") }});
      ("lG", {{s #"lvl" }});
      ("lF", {{s #"lvl" }});
      ("rF", {{s #"relevance" }});
      ("G", {{s #"env" }})]
     {{e #"Id" "G" "lG" {piFB} {piFB} "f" "g" }}
     {{e #"Pi_irr" "G" "rF" "lF" "F" {bodyId} }}
     {{s #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" "G" #"irr" #"L0") }}).

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

  (* Id-Π — homogeneous function extensionality (see id_pi_funext_rule above). *)
  push_rule id_pi_funext_rule.

  (* The fully HETEROGENEOUS funext Id (Π F1 B1)(Π F2 B2) f g with DISTINCT
     domains F1≠F2 is still open here: its pointwise clause quantifies over the
     domain equality Id F1 F2 a1 a2, which (since Id needs its type args at a
     common level/relevance) only typechecks when the domains match, else it must
     cast a1 across F1~F2 — needing the domain equality as a hypothesis, i.e. the
     universe rule Id-U-ΠΠ (:251-261, see IdUniv.v).  cast-Π (:300-312) is the
     matching computation for that cast. *)

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_comp_entry := lang_entry ott_comp_wf.
#[export] Hint Resolve ott_comp_entry : wf_lang_db.
