(* ====================================================================== *)
(* OTT Normalization via In-Language Normal-Form Extension — Phase 1.       *)
(*                                                                        *)
(* The extension language `ott_nf` over                                    *)
(*   ott := ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info         *)
(* adds OBJECT-LEVEL sorts for de Bruijn variables, neutral/normal exps &   *)
(* types, and nf substitutions/contexts, plus embedding term rules with     *)
(* equations that collapse each onto its base denotation.  All new sorts    *)
(* are indexed by the SAME base `G`/`i`/`A` indices that `exp`/`ty` use      *)
(* (no normal contexts ⇒ no hereditary substitution in the defs).           *)
(*                                                                        *)
(* Eta-LONG gated normals: `nf_ne_at` is admitted only at neutral/base type *)
(* codes (`nf2ty` of a neutral), NEVER at `El (Pi_rel …)`, so the only       *)
(* normal at a Pi code is `nf_lam` ⇒ unique eta-long normal forms.          *)
(* ====================================================================== *)
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
From Pyrosome.Lang Require Import Subst SubstEqnGen.
From Pyrosome.Lang.OTT Require Import Base Nat Pi.
From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* The concrete base OTT language the extension sits on top of (mirrors
   Norm/Pi/FundamentalLemma.v:33). *)
Definition ott :=
  (ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info)%list.

(* Injectivity entries for the new ott_nf constructors.  Grown as the
   fragment grows; combined with the base injectivity lists at each rule. *)
Definition nf_injectivity : list (string * list string) :=
  [("var", ["A"; "i"; "G"]);
   ("vz", ["A"; "i"; "G"]);
   ("vs", ["x"; "B"; "j"; "A"; "i"; "G"]);
   ("ne_exp", ["A"; "i"; "G"]);
   ("nf_exp", ["A"; "i"; "G"]);
   ("ne_ty", ["i"; "G"]);
   ("nf_ty", ["i"; "G"]);
   ("var2exp", ["x"; "A"; "i"; "G"]);
   ("ne2exp", ["m"; "A"; "i"; "G"]);
   ("nf2exp", ["t"; "A"; "i"; "G"]);
   ("nf2ty", ["n"; "i"; "G"]);
   ("ne2ty", ["n"; "i"; "G"]);
   ("ne_var", ["x"; "A"; "i"; "G"]);
   ("ne_El", ["m"; "l"; "r"; "G"]);
   ("nf_El", ["e"; "l"; "r"; "G"]);
   ("nf_U", ["l"; "r"; "G"]);
   ("nf_Nat", ["G"]);
   ("nf_zero", ["G"]);
   ("nf_suc", ["n"; "G"]);
   ("nf_ne_at", ["m"; "n"; "i"; "G"]);
   ("nf_lam", ["t"; "B"; "F"; "lG"; "lF"; "rF"; "G"]);
   ("ne_app", ["a"; "f"; "B"; "F"; "lG"; "lF"; "rF"; "G"]);
   ("nf_sub", ["G'"; "G"]);
   ("nf_ctx", []);
   ("nfsub2sub", ["gn"; "G'"; "G"]);
   ("nfctx2env", ["Gn"]);
   ("nf_forget", ["G"]);
   ("nf_snoc", ["vn"; "A"; "i"; "gn"; "G'"; "G"]);
   ("nf_emp_ctx", []);
   ("nf_ext_ctx", ["An"; "i"; "Gn"])].

Definition ott_base_inj_all :=
  (nf_injectivity ++ pi_injectivity ++ nat_injectivity
     ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity)%list.

(* ====================================================================== *)
(* Phase 1a — de Bruijn variables (intrinsically typed; NO `sub` subterm;   *)
(* the index uses only `ty_subst wkn`, forced by `hd`'s type).             *)
(* ====================================================================== *)

Derive ott_nf
       in (wf_lang_ext ott ott_nf)
       as ott_nf_wf.
Proof.
  setup_lang_interactive.

  (* var G i A : the sort of de Bruijn variables of type A in context G. *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i"
      -----------------------------------------------
      #"var" "G" "i" "A" srt
    ]}%prerule
    ott_base_inj_all.

  (* vz : the most-recent variable. *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i"
      -----------------------------------------------
      #"vz" : #"var" (#"ext" "G" "A") "i" (#"ty_subst" #"wkn" "A")
    ]}%prerule
    ott_base_inj_all.

  (* vs : shift a variable under one extension. *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i",
          "j" : #"tyinfo", "B" : #"ty" "G" "j",
          "x" : #"var" "G" "i" "A"
      -----------------------------------------------
      #"vs" "B" "x" : #"var" (#"ext" "G" "B") "i" (#"ty_subst" #"wkn" "A")
    ]}%prerule
    ott_base_inj_all.

  (* ==================================================================== *)
  (* Phase 1b — neutral / normal sorts, indexed by BASE G,i,A (same as     *)
  (* exp/ty).  No equations among these sorts ⇒ the collapse compiler is    *)
  (* trivial and decidability is syntactic.                                *)
  (* ==================================================================== *)

  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i"
      -----------------------------------------------
      #"ne_exp" "G" "i" "A" srt
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i"
      -----------------------------------------------
      #"nf_exp" "G" "i" "A" srt
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "i" : #"tyinfo"
      -----------------------------------------------
      #"ne_ty" "G" "i" srt
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "i" : #"tyinfo"
      -----------------------------------------------
      #"nf_ty" "G" "i" srt
    ]}%prerule
    ott_base_inj_all.

  (* ==================================================================== *)
  (* Phase 1g (maps only) — the embedding term-rule CONSTRUCTORS into base   *)
  (* syntax.  Declared here (before the neutral/normal constructors) so      *)
  (* indices may mention `nf2exp`/`nf2ty`.  Their collapse EQUATIONS are      *)
  (* added later, once all formers exist.                                    *)
  (* ==================================================================== *)

  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i",
          "x" : #"var" "G" "i" "A"
      -----------------------------------------------
      #"var2exp" "x" : #"exp" "G" "i" "A"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i",
          "m" : #"ne_exp" "G" "i" "A"
      -----------------------------------------------
      #"ne2exp" "m" : #"exp" "G" "i" "A"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i",
          "t" : #"nf_exp" "G" "i" "A"
      -----------------------------------------------
      #"nf2exp" "t" : #"exp" "G" "i" "A"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "i" : #"tyinfo",
          "n" : #"nf_ty" "G" "i"
      -----------------------------------------------
      #"nf2ty" "n" : #"ty" "G" "i"
    ]}%prerule
    ott_base_inj_all.

  (* ==================================================================== *)
  (* Phase 1c/1d/1e (non-Pi) — neutral & normal constructors for variables,  *)
  (* Nat, and the universe/El type codes, plus the eta-positivity gate.      *)
  (* The Pi pieces (ne_app / nf_lam) and Nat's eliminator neutral come next. *)
  (* ==================================================================== *)

  (* ne_var : a variable is a neutral. *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i",
          "x" : #"var" "G" "i" "A"
      -----------------------------------------------
      #"ne_var" "x" : #"ne_exp" "G" "i" "A"
    ]}%prerule
    ott_base_inj_all.

  (* ne2ty : embed a neutral type code into a base type (used by the gate). *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "n" : #"ne_ty" "G" "i"
      -----------------------------------------------
      #"ne2ty" "n" : #"ty" "G" "i"
    ]}%prerule
    ott_base_inj_all.

  (* ne_El : El of a neutral code is a neutral type. *)
  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl",
          "m" : #"ne_exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] "r" "l")
      -----------------------------------------------
      #"ne_El" "m" : #"ne_ty" "G" (#"info" "r" (#"iota" "l"))
    ]}%prerule
    ott_base_inj_all.

  (* nf_El : El of a normal code is a normal type. *)
  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl",
          "e" : #"nf_exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] "r" "l")
      -----------------------------------------------
      #"nf_El" "e" : #"nf_ty" "G" (#"info" "r" (#"iota" "l"))
    ]}%prerule
    ott_base_inj_all.

  (* nf_U : the universe is a normal type. *)
  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl"
      -----------------------------------------------
      #"nf_U" "r" "l" : #"nf_ty" "G" (#"info" #"rel" (#"next" "l"))
    ]}%prerule
    ott_base_inj_all.

  (* nf_Nat : Nat is a normal type. *)
  elab_rule {[r "G" : #"env"
      -----------------------------------------------
      #"nf_Nat" : #"nf_ty" "G" (#"info" #"rel" (#"iota" #"L0"))
    ]}%prerule
    ott_base_inj_all.

  (* nf_zero / nf_suc : Nat normals (eta-trivial base type). *)
  elab_rule {[r "G" : #"env"
      -----------------------------------------------
      #"nf_zero"
        : #"nf_exp" "G" (#"info" #"rel" (#"iota" #"L0"))
            (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env",
          "n" : #"nf_exp" "G" (#"info" #"rel" (#"iota" #"L0"))
                  (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      -----------------------------------------------
      #"nf_suc" "n"
        : #"nf_exp" "G" (#"info" #"rel" (#"iota" #"L0"))
            (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    ott_base_inj_all.

  (* The eta-positivity GATE: a neutral is a normal ONLY at a neutral type    *)
  (* `ne2ty n` (never at El(Pi_rel …), which is not a neutral type) ⇒ unique  *)
  (* eta-long normals at Pi (only nf_lam inhabits a Pi code).                 *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "n" : #"ne_ty" "G" "i",
          "m" : #"ne_exp" "G" "i" (#"ne2ty" "n")
      -----------------------------------------------
      #"nf_ne_at" "n" "m" : #"nf_exp" "G" "i" (#"ne2ty" "n")
    ]}%prerule
    ott_base_inj_all.

  (* ==================================================================== *)
  (* Phase 1c/1d (Pi) — the binder constructors.  nf_lam is the ONLY normal   *)
  (* at a Pi code (eta gate, above); ne_app's head is neutral, arg normal,    *)
  (* result index uses nf2exp to stay in base syntax.  Mirror lam_rel/app_rel.*)
  (* ==================================================================== *)

  (* nf_lam : the unique eta-long normal at a Pi code (body is normal). *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG"),
          "t" : #"nf_exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"iota" "lG")) (#"El" "B")
      -----------------------------------------------
      #"nf_lam" "rF" "lF" "lG" "F" "B" "t"
        : #"nf_exp" "G" (#"info" #"rel" (#"iota" "lG"))
          (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "lG"] (#"Pi_rel" ["G" := "G"] "rF" "lF" "lG" "F" "B"))
    ]}%prerule
    ott_base_inj_all.

  (* ne_app : application of a neutral head to a normal argument. *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG"),
          "f" : #"ne_exp" "G" (#"info" #"rel" (#"iota" "lG"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "lG"] (#"Pi_rel" ["G" := "G"] "rF" "lF" "lG" "F" "B")),
          "a" : #"nf_exp" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      -----------------------------------------------
      #"ne_app" "rF" "lF" "lG" "F" "B" "f" "a"
        : #"ne_exp" "G" (#"info" #"rel" (#"iota" "lG"))
            (#"ty_subst" (#"snoc" #"id" (#"nf2exp" "a")) (#"El" "B"))
    ]}%prerule
    ott_base_inj_all.

  (* ==================================================================== *)
  (* Phase 1f — nf substitutions / contexts (object sorts, list-shaped;       *)
  (* carry normal exps/types, NOT base subs).  No nf_wkn/nf_cmp/nf_id —        *)
  (* those normalize into snoc-lists.  Neutrals never carry a sub.            *)
  (* ==================================================================== *)

  elab_rule {[r "G" : #"env", "G'" : #"env"
      -----------------------------------------------
      #"nf_sub" "G" "G'" srt
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r
      -----------------------------------------------
      #"nf_ctx" srt
    ]}%prerule
    ott_base_inj_all.

  (* maps from the list sorts into base subs / envs. *)
  elab_rule {[r "G" : #"env", "G'" : #"env", "gn" : #"nf_sub" "G" "G'"
      -----------------------------------------------
      #"nfsub2sub" "gn" : #"sub" "G" "G'"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "Gn" : #"nf_ctx"
      -----------------------------------------------
      #"nfctx2env" "Gn" : #"env"
    ]}%prerule
    ott_base_inj_all.

  (* nf_sub constructors: forget + snoc (no wkn/cmp/id). *)
  elab_rule {[r "G" : #"env"
      -----------------------------------------------
      #"nf_forget" : #"nf_sub" "G" #"emp"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "G'" : #"env", "gn" : #"nf_sub" "G" "G'",
          "i" : #"tyinfo", "A" : #"ty" "G'" "i",
          "vn" : #"nf_exp" "G" "i"
                   (#"ty_subst" ["G'" := "G'"] (#"nfsub2sub" ["G" := "G"] ["G'" := "G'"] "gn") "A")
      -----------------------------------------------
      #"nf_snoc" "gn" "vn" : #"nf_sub" "G" (#"ext" "G'" "A")
    ]}%prerule
    ott_base_inj_all.

  (* nf_ctx constructors: emp + ext (carrying a normal type). *)
  elab_rule {[r
      -----------------------------------------------
      #"nf_emp_ctx" : #"nf_ctx"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "Gn" : #"nf_ctx", "i" : #"tyinfo",
          "An" : #"nf_ty" (#"nfctx2env" "Gn") "i"
      -----------------------------------------------
      #"nf_ext_ctx" "Gn" "An" : #"nf_ctx"
    ]}%prerule
    ott_base_inj_all.

  (* ==================================================================== *)
  (* Phase 1g — embedding EQUATIONS.  Each collapses an embedding map onto    *)
  (* its base denotation; every equation concludes at a BASE sort.  Under     *)
  (* the Phase-2 collapse compiler both sides become syntactically identical  *)
  (* base terms ⇒ the preservation obligation closes by reflexivity.          *)
  (* ==================================================================== *)

  (* --- variables --- *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i"
      ----------------------------------------------- ("var2exp_vz")
      #"var2exp" ["G" := #"ext" "G" "A"] ["i" := "i"] ["A" := #"ty_subst" #"wkn" "A"] #"vz"
      = #"hd"
      : #"exp" (#"ext" "G" "A") "i" (#"ty_subst" #"wkn" "A")
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i",
          "j" : #"tyinfo", "B" : #"ty" "G" "j", "x" : #"var" "G" "i" "A"
      ----------------------------------------------- ("var2exp_vs")
      #"var2exp" ["G" := #"ext" "G" "B"] ["i" := "i"] ["A" := #"ty_subst" #"wkn" "A"] (#"vs" "B" "x")
      = #"exp_subst" ["G'" := "G"] #"wkn" (#"var2exp" "x")
      : #"exp" (#"ext" "G" "B") "i" (#"ty_subst" #"wkn" "A")
    ]}%prerule
    ott_base_inj_all.

  (* --- neutrals into exps --- *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "A" : #"ty" "G" "i",
          "x" : #"var" "G" "i" "A"
      ----------------------------------------------- ("ne2exp_var")
      #"ne2exp" (#"ne_var" "x") = #"var2exp" "x" : #"exp" "G" "i" "A"
    ]}%prerule
    ott_base_inj_all.

  (* --- normals into exps : Nat --- *)
  elab_rule {[r "G" : #"env"
      ----------------------------------------------- ("nf2exp_zero")
      #"nf2exp" #"nf_zero" = #"zero"
      : #"exp" "G" (#"info" #"rel" (#"iota" #"L0"))
          (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env",
          "n" : #"nf_exp" "G" (#"info" #"rel" (#"iota" #"L0"))
                  (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("nf2exp_suc")
      #"nf2exp" (#"nf_suc" "n") = #"suc" (#"nf2exp" "n")
      : #"exp" "G" (#"info" #"rel" (#"iota" #"L0"))
          (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
    ]}%prerule
    ott_base_inj_all.

  (* --- the eta gate collapses to the neutral's embedding --- *)
  elab_rule {[r "G" : #"env", "i" : #"tyinfo", "n" : #"ne_ty" "G" "i",
          "m" : #"ne_exp" "G" "i" (#"ne2ty" ["G" := "G"] ["i" := "i"] "n")
      ----------------------------------------------- ("nf2exp_ne_at")
      #"nf2exp" ["G" := "G"] ["i" := "i"] ["A" := #"ne2ty" "n"] (#"nf_ne_at" "n" "m")
      = #"ne2exp" ["G" := "G"] ["i" := "i"] ["A" := #"ne2ty" "n"] "m"
      : #"exp" "G" "i" (#"ne2ty" "n")
    ]}%prerule
    ott_base_inj_all.

  (* --- normal/neutral types --- *)
  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl"
      ----------------------------------------------- ("nf2ty_U")
      #"nf2ty" (#"nf_U" "r" "l") = #"U" ["G" := "G"] "r" "l"
      : #"ty" "G" (#"info" #"rel" (#"next" "l"))
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl",
          "e" : #"nf_exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] "r" "l")
      ----------------------------------------------- ("nf2ty_El")
      #"nf2ty" (#"nf_El" "e") = #"El" (#"nf2exp" "e")
      : #"ty" "G" (#"info" "r" (#"iota" "l"))
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env"
      ----------------------------------------------- ("nf2ty_Nat")
      #"nf2ty" #"nf_Nat"
      = #"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"])
      : #"ty" "G" (#"info" #"rel" (#"iota" #"L0"))
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "r" : #"relevance", "l" : #"lvl",
          "m" : #"ne_exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] "r" "l")
      ----------------------------------------------- ("ne2ty_El")
      #"ne2ty" (#"ne_El" "m") = #"El" (#"ne2exp" "m")
      : #"ty" "G" (#"info" "r" (#"iota" "l"))
    ]}%prerule
    ott_base_inj_all.

  (* --- nf substitutions / contexts --- *)
  elab_rule {[r "G" : #"env"
      ----------------------------------------------- ("nfsub2sub_forget")
      #"nfsub2sub" #"nf_forget" = #"forget" : #"sub" "G" #"emp"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r
      ----------------------------------------------- ("nfctx2env_emp")
      #"nfctx2env" #"nf_emp_ctx" = #"emp" : #"env"
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "Gn" : #"nf_ctx", "i" : #"tyinfo",
          "An" : #"nf_ty" (#"nfctx2env" "Gn") "i"
      ----------------------------------------------- ("nfctx2env_ext")
      #"nfctx2env" (#"nf_ext_ctx" "Gn" "An")
      = #"ext" (#"nfctx2env" "Gn") (#"nf2ty" "An") : #"env"
    ]}%prerule
    ott_base_inj_all.

  (* --- the two dependent / Pi embeddings (most inference-heavy) --- *)
  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG"),
          "t" : #"nf_exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"iota" "lG")) (#"El" "B")
      ----------------------------------------------- ("nf2exp_lam")
      #"nf2exp" (#"nf_lam" "rF" "lF" "lG" "F" "B" "t")
      = #"lam_rel" "rF" "lF" "lG" "F" "B" (#"nf2exp" "t")
      : #"exp" "G" (#"info" #"rel" (#"iota" "lG"))
          (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "lG"] (#"Pi_rel" ["G" := "G"] "rF" "lF" "lG" "F" "B"))
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "rF" : #"relevance", "lF" : #"lvl", "lG" : #"lvl",
          "F" : #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" ["G" := "G"] "rF" "lF"),
          "B" : #"exp" (#"ext" "G" (#"El" "F")) (#"info" #"rel" (#"next" "lG"))
                       (#"U" ["G" := #"ext" "G" (#"El" "F")] #"rel" "lG"),
          "f" : #"ne_exp" "G" (#"info" #"rel" (#"iota" "lG"))
                       (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := "lG"] (#"Pi_rel" ["G" := "G"] "rF" "lF" "lG" "F" "B")),
          "a" : #"nf_exp" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "F")
      ----------------------------------------------- ("ne2exp_app")
      #"ne2exp" (#"ne_app" "rF" "lF" "lG" "F" "B" "f" "a")
      = #"app_rel" "rF" "lF" "lG" "F" "B" (#"ne2exp" "f") (#"nf2exp" "a")
      : #"exp" "G" (#"info" #"rel" (#"iota" "lG"))
          (#"ty_subst" (#"snoc" #"id" (#"nf2exp" "a")) (#"El" "B"))
    ]}%prerule
    ott_base_inj_all.

  elab_rule {[r "G" : #"env", "G'" : #"env", "gn" : #"nf_sub" "G" "G'",
          "i" : #"tyinfo", "A" : #"ty" "G'" "i",
          "vn" : #"nf_exp" "G" "i"
                   (#"ty_subst" ["G'" := "G'"] (#"nfsub2sub" ["G" := "G"] ["G'" := "G'"] "gn") "A")
      ----------------------------------------------- ("nfsub2sub_snoc")
      #"nfsub2sub" (#"nf_snoc" "gn" "vn")
      = #"snoc" (#"nfsub2sub" "gn") (#"nf2exp" "vn")
      : #"sub" "G" (#"ext" "G'" "A")
    ]}%prerule
    ott_base_inj_all.

  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
