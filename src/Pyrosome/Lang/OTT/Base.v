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

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* ====================================================================== *)
(* Part 1 : ott_info — the TypeInfo parameter language.                   *)
(* Mirrors Agda's Relevance / Level / TypeLevel (Untyped.agda:22-103),    *)
(* bundled as TypeInfo = [ r , l ].  Derived interactively exactly like   *)
(* `levels` in Lang/Levels.v.                                             *)
(* ====================================================================== *)

Derive ott_info
       in (wf_lang (ott_info : lang))
       as ott_info_wf.
Proof.
  setup_lang_interactive.

  (* --- Relevance : ! (proof-relevant) / % (proof-irrelevant) --- *)
  elab_rule {[r
      -----------------------------------------------
      #"relevance" srt
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      -----------------------------------------------
      #"rel" : #"relevance"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      -----------------------------------------------
      #"irr" : #"relevance"
    ]}%prerule
    (@nil (string* list string)).

  (* --- Levels : ⁰ / ¹ , with ordering ⁰ < ¹ --- *)
  elab_rule {[r
      -----------------------------------------------
      #"lvl" srt
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      -----------------------------------------------
      #"L0" : #"lvl"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      -----------------------------------------------
      #"L1" : #"lvl"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "a" : #"lvl", "b" : #"lvl"
      -----------------------------------------------
      #"ltl" "a" "b" srt
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      -----------------------------------------------
      #"L0<L1" : #"ltl" #"L0" #"L1"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "a" : #"lvl", "b" : #"lvl",
          "p1" : #"ltl" "a" "b",
          "p2" : #"ltl" "a" "b"
      ----------------------------------------------- ("ltl_irr")
      #"p1" = "p2" : #"ltl" "a" "b"
    ]}%prerule
    (@nil (string* list string)).

  (* --- TypeLevels : ι⁰ , ι¹ , ∞  (iota _ , inf) --- *)
  elab_rule {[r
      -----------------------------------------------
      #"tlvl" srt
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "l" : #"lvl"
      -----------------------------------------------
      #"iota" "l" : #"tlvl"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      -----------------------------------------------
      #"inf" : #"tlvl"
    ]}%prerule
    (@nil (string* list string)).
  (* `next l` = the TypeLevel of the universe holding level-l types       *)
  (* Agda: next ⁰ = ι¹ (U⁰ is a type at [!,ι¹]); next ¹ = ∞.              *)
  elab_rule {[r "l" : #"lvl"
      -----------------------------------------------
      #"next" "l" : #"tlvl"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      ----------------------------------------------- ("next0")
      #"next" #"L0" = #"iota" #"L1" : #"tlvl"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r
      ----------------------------------------------- ("next1")
      #"next" #"L1" = #"inf" : #"tlvl"
    ]}%prerule
    (@nil (string* list string)).

  (* --- The bundle : TypeInfo = [ r , l ] --- *)
  elab_rule {[r
      -----------------------------------------------
      #"tyinfo" srt
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "r" : #"relevance", "l" : #"tlvl"
      -----------------------------------------------
      #"info" "r" "l" : #"tyinfo"
    ]}%prerule
    (@nil (string* list string)).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_info_entry := lang_entry ott_info_wf.
#[export] Hint Resolve ott_info_entry : wf_lang_db.

Definition ott_info_injectivity :=
  [("info", ["l"; "r"]); ("next", ["l"]); ("iota", ["l"]);
   ("ltl", ["b"; "a"]); ("inf", []); ("L1", []); ("L0", []);
   ("irr", []); ("rel", []);
   ("tyinfo", []); ("tlvl", []); ("lvl", []); ("relevance", [])].

(* ====================================================================== *)
(* Part 2 : subst_ott — parameterize the substitution calculus over       *)
(* #"tyinfo".  Clone of Lang/Levels.v:98-125 (param "i" : tyinfo, at      *)
(* ty@0 / exp@1).                                                         *)
(* ====================================================================== *)

#[local] Definition subst_ott' :=
    let ps := (elab_param "i" (subst_lang)
                 [("exp", Some 1);
                  ("ty", Some 0)]) in
  parameterize_lang "i" {{s #"tyinfo"}}
    ps subst_lang.

Definition subst_ott :=
  Eval vm_compute in subst_ott'.

Lemma subst_ott_wf
  : wf_lang_ext ott_info subst_ott.
Proof. compute_wf_lang. Qed.
#[local] Definition subst_ott_entry := lang_entry subst_ott_wf.
#[export] Hint Resolve subst_ott_entry : wf_lang_db.

Definition subst_ott_injectivity :=
  [("hd", ["A"; "i"; "G"]); ("wkn", ["A"; "i"; "G"]);
   ("snoc", ["v"; "A"; "i"; "g"; "G'"; "G"]); ("ext", ["A"; "G"]);
   ("forget", ["G"]); ("emp", []); ("ty", ["i"; "G"]); ("ty_subst", ["i"; "G"]);
   ("exp_subst", ["i"; "G"]); ("exp", ["A"; "i"; "G"]);
   ("cmp", ["G3"; "G1"]); ("id", ["G"]); ("sub", ["G'"; "G"]); ("env", [])].

(* Parameterized sorts (confirmed by inspection):                          *)
(*   types        #"ty"  "G" "i"          (i : #"tyinfo")                   *)
(*   expressions  #"exp" "G" "i" "A"      (A : #"ty" "G" "i")              *)

(* ====================================================================== *)
(* Part 3 : ott_base — the universe, a la Tarski (U + El).                *)
(* Type codes are #"exp" of a universe; #"El" decodes a code to a #"ty".  *)
(* Agda: Uⱼ / univ (Typed.agda:31-41), the univ coercion (Typed.agda:32). *)
(* ====================================================================== *)

Definition ott_base_injectivity :=
  [("El", ["e"; "l"; "r"; "G"]); ("U", ["l"; "r"; "G"])].

Derive ott_base
       in (wf_lang_ext (subst_ott ++ ott_info) ott_base)
       as ott_base_wf.
Proof.
  setup_lang_interactive.

  (* Universe U_{r,l}, viewed as a type, has info [!, next l].            *)
  (* (Agda: U⁰ is a type at [!,ι¹]=next⁰; U¹ at [!,∞]=next¹; SProp=U_%,⁰.) *)
  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl"
      -----------------------------------------------
      #"U" "r" "l" : #"ty" "G" (#"info" #"rel" (#"next" "l"))
    ]}%prerule
    (ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  (* gen_subst mis-handles the tyinfo parameter (it tries to ty_subst the  *)
  (* info annotation); U is a closed code, so write its subst rule by hand. *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "r" : #"relevance", "l" : #"lvl"
      ----------------------------------------------- ("U subst")
      #"ty_subst" "g" (#"U" "r" "l") = #"U" "r" "l"
      : #"ty" "G" (#"info" #"rel" (#"next" "l"))
    ]}%prerule
    (ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* El : decode a universe code (a term of U_{r,l}) into the type it      *)
  (* names, whose info is [r, ι l].  (Agda `univ`, Typed.agda:32-34.)      *)
  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl",
          "e" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] "r" "l")
      -----------------------------------------------
      #"El" "e" : #"ty" "G" (#"info" "r" (#"iota" "l"))
    ]}%prerule
    (ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  (* hand-written subst rule (gen_subst mishandles the info parameter):    *)
  (*   ty_subst g (El e) = El (exp_subst g e)                              *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
          "r" : #"relevance", "l" : #"lvl",
          "e" : #"exp" "G'" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G'"] "r" "l")
      ----------------------------------------------- ("El subst")
      #"ty_subst" "g" (#"El" "e") = #"El" (#"exp_subst" "g" "e")
      : #"ty" "G" (#"info" "r" (#"iota" "l"))
    ]}%prerule
    (ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_base_entry := lang_entry ott_base_wf.
#[export] Hint Resolve ott_base_entry : wf_lang_db.
