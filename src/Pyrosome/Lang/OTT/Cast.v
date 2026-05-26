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
From Pyrosome.Lang.OTT Require Import Base Nat Id.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ====================================================================== *)
(* Type casting (Agda Typed.agda:117-126).  cast operates on type CODES,  *)
(* so it needs the universe Univ r ⁰ available AS A CODE.  We give a       *)
(* specialised code  u0 r : Univ r ⁰  living in U_{!,1} (outer level       *)
(* fixed to 1, so no ambiguity), with the coherence  El (u0 r) = U r L0.  *)
(* ====================================================================== *)

Definition cast_injectivity :=
  [("u0", ["r"; "G"]);
   ("cast", ["t"; "e"; "B"; "A"; "r"; "G"]);
   ("castrefl", ["t"; "A"; "G"])].

Derive ott_cast
       in (wf_lang_ext (ott_id ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info) ott_cast)
       as ott_cast_wf.
Proof.
  setup_lang_interactive.

  (* u0 r : the universe Univ r ⁰, as a code in U_{!,1}. *)
  elab_rule {[r "G" : #"env", "r" : #"relevance"
      -----------------------------------------------
      #"u0" "r" : #"exp" "G" (#"info" #"rel" (#"next" #"L1")) (#"U" ["G" := "G"] #"rel" #"L1")
    ]}%prerule
    (cast_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'", "r" : #"relevance"
      ----------------------------------------------- ("u0 subst")
      #"exp_subst" "g" (#"u0" "r") = #"u0" "r"
      : #"exp" "G" (#"info" #"rel" (#"next" #"L1")) (#"U" ["G" := "G"] #"rel" #"L1")
    ]}%prerule
    (cast_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* coherence: decoding the code for Univ r ⁰ gives the universe-type U r L0. *)
  elab_rule {[r "G" : #"env", "r" : #"relevance"
      ----------------------------------------------- ("El u0")
      #"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L1"] (#"u0" "r") = #"U" ["G" := "G"] "r" #"L0"
      : #"ty" "G" (#"info" #"rel" (#"next" #"L0"))
    ]}%prerule
    (cast_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* cast A B e t : transports t : El A to El B along e : Id_{Univ r ⁰} A B.   *)
  (* The proof e relates A,B as elements of the universe Univ r ⁰ (= El(u0 r)   *)
  (* = U r L0 by coherence), so A,B are passed where Id expects El(u0 r).       *)
  elab_rule {[r "G" : #"env", "r" : #"relevance",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] "r" #"L0"),
          "B" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] "r" #"L0"),
          "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"]
                             (#"Id" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] "r") "A" "B")),
          "t" : #"exp" "G" (#"info" "r" (#"iota" #"L0")) (#"El" "A")
      -----------------------------------------------
      #"cast" "A" "B" "e" "t" : #"exp" "G" (#"info" "r" (#"iota" #"L0")) (#"El" "B")
    ]}%prerule
    (cast_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* cast over ℕ computes structurally (Agda Typed.agda:313-323). *)
  elab_rule {[r "G" : #"env",
          "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"]
                             (#"Id" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] #"rel")
                                   (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"])))
      ----------------------------------------------- ("cast-Nat-zero")
      #"cast" ["r" := #"rel"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) "e" #"zero" = #"zero"
      : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    (cast_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env",
          "e" : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
                       (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"]
                             (#"Id" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] #"rel")
                                   (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]))),
          "n" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("cast-Nat-suc")
      #"cast" ["r" := #"rel"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) "e" (#"suc" "n")
        = #"suc" (#"cast" ["r" := #"rel"] (#"Nat" ["G" := "G"]) (#"Nat" ["G" := "G"]) "e" "n")
      : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    (cast_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* castrefl A t : a proof that t equals (cast A A refl t).  (Typed.agda:123-126) *)
  elab_rule {[r "G" : #"env",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"rel" #"L0"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" "A")
      -----------------------------------------------
      #"castrefl" "A" "t"
        : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
          (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"]
            (#"Id" ["G" := "G"] ["l" := #"L0"] "A" "t"
              (#"cast" ["r" := #"rel"] "A" "A"
                (#"Idrefl" ["G" := "G"] ["l" := #"L1"] (#"u0" ["G" := "G"] #"rel") "A") "t")))
    ]}%prerule
    (cast_injectivity ++ id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_cast_entry := lang_entry ott_cast_wf.
#[export] Hint Resolve ott_cast_entry : wf_lang_db.
