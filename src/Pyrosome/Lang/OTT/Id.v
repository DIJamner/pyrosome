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
From Pyrosome.Lang.OTT Require Import Base Nat.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ====================================================================== *)
(* Identity types (Agda Typed.agda:101-108, 109-116).                     *)
(*   Id A t u : SProp   (A a proof-relevant code in U_{!,l}; t,u : El A)  *)
(*   Idrefl A t : Id A t t                                                *)
(*   transp : transport along a proof-irrelevant predicate                *)
(* Plus the first-order ℕ-computation rules for Id (Typed.agda:241-250).  *)
(* ====================================================================== *)

Definition id_injectivity :=
  [("Id", ["u"; "t"; "A"; "l"; "G"]);
   ("Idrefl", ["t"; "A"; "l"; "G"])].

Derive ott_id
       in (wf_lang_ext (ott_nat ++ ott_base ++ subst_ott ++ ott_info) ott_id)
       as ott_id_wf.
Proof.
  setup_lang_interactive.

  (* Id A t u : a code in SProp. *)
  elab_rule {[r "G" : #"env", "l" : #"lvl",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A")
      -----------------------------------------------
      #"Id" "A" "t" "u" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'", "l" : #"lvl",
          "A" : #"exp" "G'" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G'"] #"rel" "l"),
          "t" : #"exp" "G'" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "u" : #"exp" "G'" (#"info" #"rel" (#"iota" "l")) (#"El" "A")
      ----------------------------------------------- ("Id subst")
      #"exp_subst" "g" (#"Id" "A" "t" "u")
        = #"Id" (#"exp_subst" "g" "A") (#"exp_subst" "g" "t") (#"exp_subst" "g" "u")
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Idrefl A t : Id A t t  (a proof, lives in SProp). *)
  elab_rule {[r "G" : #"env", "l" : #"lvl",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A")
      -----------------------------------------------
      #"Idrefl" "A" "t"
        : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
          (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Id" ["G" := "G"] ["l" := "l"] "A" "t" "t"))
    ]}%prerule
    (id_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* First-order ℕ computations for Id (Typed.agda:241-250, 272-277).
     These equate CODES, so are NOT subsumed by proof irrelevance.
     (Id ℕ 0 0 = sUnit needs Π and lives in Pi-importing follow-up.) *)
  elab_rule {[r "G" : #"env",
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-0S")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) #"zero" (#"suc" "t")
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env",
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-S0")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"suc" "t") #"zero"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env",
          "m" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"])),
          "n" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-SS")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"suc" "m") (#"suc" "n")
        = #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) "m" "n"
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* NOTE: transp (Typed.agda:109-116) deferred. Writing it elaborated-direct
     (push_rule with a fully-explicit [:|...]%rule) DOES get past infer_rule
     (no @sort_of), but compute_wf_rule then fails to verify the rule in
     practical time (killed after 20+ min) — the e-graph wf check blows up on
     the nested ty_subst/snoc/El term. A 20-min-per-build rule is impractical;
     and transp's computation is in any case subsumed by proof irrelevance
     (its result lives in SProp). Deferred pending a faster wf path. *)

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_id_entry := lang_entry ott_id_wf.
#[export] Hint Resolve ott_id_entry : wf_lang_db.
