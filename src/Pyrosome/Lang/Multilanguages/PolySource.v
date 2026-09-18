(* Stage G': the value-restricted polymorphic source boundaries.

   [PolyBoundaries.v] defines [poly_boundaries], whose "dtt forall" rule
   delays evaluation of the body expression [e] under a [Lam].  That
   formulation is not preserved by a call-by-value compiler.  This file
   defines the value-restricted replacement [poly_boundaries_v] (see
   PLAN-poly.md decision 2) and assembles the new source multilanguage
   [poly_source_multilanguage] (decision 6), without touching any existing
   file. *)

Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* imports for compilers *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for the `match # from _ with` compiler notation *)

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

From Stdlib Require derive.Derive.

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC.
From Pyrosome.Lang Require Import UTLC.
From Pyrosome.Lang Require Import BoolType.
From Pyrosome.Lang Require Import SimpleVProd.
From Pyrosome.Lang.Multilanguages Require Export SimpleBoundaries.

(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers. (* for parameterizing existing languages*)
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.

(* re-export the boundary-generation stage so downstream files get
   everything they need from a single import of this file *)
From Pyrosome.Lang.Multilanguages Require Export PolyBoundaries.

Local Open Scope lang_scope.

(* The value-restricted forall boundary rules (Matthews and Findler figure
   11, page 12:33, restricted to values so that a call-by-value compiler
   preserves them; see PLAN-poly.md decision 2). There are no term rules
   here (only equations between terms already built from #"ret"), so unlike
   [poly_boundaries_def] there is no need for the [{[l/subst ...]}] notation
   that auto-generates substitution rules. *)
Definition poly_boundaries_v_def : lang :=
  {[l
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"), (* tau in Matthews and Findler *)
        "v" : #"val" "D" "G" #"*"
        ----------------------------------------------- ("dtt forall")
        #"dtt" (#"All" "A") (#"ret" "v") =
        #"ret" (#"Lam" (#"dtt" "A" (#"ret" (#"val_ty_subst" #"ty_wkn" "v"))))
        : #"exp" "D" "G" (#"All" "A")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"), (* tau in Matthews and Findler *)
        "v" : #"val" "D" "G" (#"All" "A")
        ----------------------------------------------- ("ttd forall")
        #"ttd" (#"All" "A") (#"ret" "v") =
        #"ttd" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A") (#"@" (#"ret" "v") #"*")
        : #"exp" "D" "G" #"*"
    ]
  ]}.

Derive poly_boundaries_v
  in (elab_lang_ext (boundaries_ty_subst ++
                             boundaries_parameterized ++ polymorphic_interoperating_langs)
                poly_boundaries_v_def poly_boundaries_v)
        as poly_boundaries_v_wf.
Proof. auto_elab. Qed.
#[local] Definition poly_boundaries_v_entry :=
  lang_entry (elab_lang_implies_wf poly_boundaries_v_wf).
#[export] Hint Resolve poly_boundaries_v_entry : wf_lang_db.

Definition poly_source_boundaries :=
  poly_boundaries_v ++ boundaries_ty_subst ++ boundaries_parameterized.
Hint Unfold poly_source_boundaries : auto_elab.

Definition poly_source_multilanguage :=
  poly_source_boundaries ++ polymorphic_interoperating_langs.
Hint Unfold poly_source_multilanguage : auto_elab.

Lemma poly_source_multilanguage_wf : wf_lang poly_source_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition poly_source_multilanguage_entry :=
  lang_entry poly_source_multilanguage_wf.
#[export] Hint Resolve poly_source_multilanguage_entry : wf_lang_db.
