(* The polymorphic extension of [target_multilanguage]:

   - [poly_ty_subst], the type-substitution laws for the [#"Lam"] / [#"@"]
     forms of the [poly] fragment (PolySubst.v declares them as a TODO
     [poly_subst_laws_def] but never adds them to the language);
   - [bAll_cases], the boundary case constant [#"bAll"] for the universal
     quantifier, in the style of [#"bfunc"] (explicit arguments), with its
     substitution laws and its defining equation;
   - [typerec_All], the [#"All"] case of the boundary recursor.

   The [#"All"] case cannot be a generic fourth case of [#"typerec"]: the
   recursive result lives under a type binder (at [#"ty_ext" "D"]) while the
   case has to produce a value at ["D"], which only a higher-kinded type
   variable could express.  So the case is specific to the boundary recursor
   ([trec_boundaries] of TrecTerms.v) and is stated as an equation relating
   that recursor at [#"All" "A"] to [#"bAll"] applied to it at ["A"].

   [target_multilanguage] is a syntactic suffix of the result, so every fact
   already proved about it lifts by language monotonicity.                 *)

Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* Compiler infrastructure. *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations.

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

From Stdlib Require derive.Derive.
From Pyrosome Require Import Tools.EGraph.InjRuleGen.

From Pyrosome.Lang Require Import SimpleVSTLC UTLC BoolType SimpleVProd.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers.
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.
From Pyrosome.Lang.Multilanguages Require Export TrecTerms.


(* ------------------------------------------------------------------ *)
(* Stage 1: the missing type-substitution laws of the [poly] fragment.

   These are exactly the two non-[#"All"] rules of [PolySubst.poly_subst_laws_def]
   (the [#"ty_subst All"] rule of that definition is already part of [poly]);
   they are written out by hand here so that the rule names follow the
   ["ty_subst <constructor>"] convention used by the rest of this folder. *)
Definition poly_ty_subst_def : lang :=
  {[l
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "e" : #"exp" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") "A"
        ----------------------------------------------- ("ty_subst Lam")
        #"val_ty_subst" "g" (#"Lam" "e")
        = #"Lam" (#"exp_ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" "g") #"ty_hd") "e")
        : #"val" "D'" (#"env_ty_subst" "g" "G") (#"ty_subst" "g" (#"All" "A"))
    ];
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "e" : #"exp" "D" "G" (#"All" "A"),
        "B" : #"ty" "D"
        ----------------------------------------------- ("ty_subst @")
        #"exp_ty_subst" "g" (#"@" "e" "B")
        = #"@" (#"exp_ty_subst" "g" "e") (#"ty_subst" "g" "B")
        : #"exp" "D'" (#"env_ty_subst" "g" "G")
            (#"ty_subst" "g" (#"ty_subst" (#"ty_snoc" #"ty_id" "B") "A"))
    ]
  ]}.

Definition poly_ty_subst :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 target_multilanguage poly_ty_subst_def.

Lemma poly_ty_subst_wf : wf_lang_ext target_multilanguage poly_ty_subst.
Proof. compute_wf_lang. Qed.
#[local] Definition poly_ty_subst_entry := lang_entry poly_ty_subst_wf.
#[export] Hint Resolve poly_ty_subst_entry : wf_lang_db.

Definition target_multilanguage_poly_subst :=
  poly_ty_subst ++ target_multilanguage.
Hint Unfold target_multilanguage_poly_subst : auto_elab.

Lemma target_multilanguage_poly_subst_wf : wf_lang target_multilanguage_poly_subst.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_poly_subst_entry :=
  lang_entry target_multilanguage_poly_subst_wf.
#[export] Hint Resolve target_multilanguage_poly_subst_entry : wf_lang_db.


(* ------------------------------------------------------------------ *)
(* Stage 2: the [#"All"] boundary case constant.

   [#"bAll" "A" "c"] is the coercion pair at [#"All" "A"], built from the
   coercion pair ["c"] at ["A"] (which lives one type variable up).  Its
   two components:

   - [#"->" (#"All" "A") #"*"]: instantiate the polymorphic argument at
     [#"*"], let-bind the result, and coerce it with ["c"] instantiated at
     [#"*"].  (The [#"let"] is what makes the quantifier boundary equation
     provable against the let-binding boundary compiler.)
   - [#"->" #"*" (#"All" "A")]: type-abstract with [#"Lam"], then coerce the
     dynamic argument with ["c"] (weakened over the [#"*"] binder).        *)
Definition bAll_body :=
  {{e #"pair_val"
      (#"lambda" (#"All" "A")
         (#"let" (#"@" (#"ret" #"hd") #"*")
                 (#"app" (#".1" (#"ret" (#"val_subst" {wkn_n 2}
                            (#"val_ty_subst" (#"ty_snoc" #"ty_id" #"*") "c"))))
                         (#"ret" #"hd"))))
      (#"lambda" #"*"
         (#"ret" (#"Lam" (#"app" (#".2" (#"ret" (#"val_subst" #"wkn" "c")))
                                 (#"ret" #"hd"))))) }}.

Definition bAll_cases_def : lang :=
  {[l
    [:| "D" : #"ty_env", "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "c" : #"val" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") {P {{e "A"}} }
        -----------------------------------------------
        #"bAll" "A" "c" : #"val" "D" "G" {P {{e #"All" "A"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D", "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G",
        "A" : #"ty" (#"ty_ext" "D"),
        "c" : #"val" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") {P {{e "A"}} }
        ----------------------------------------------- ("val_subst bAll")
        #"val_subst" "g" (#"bAll" "A" "c")
        = #"bAll" "A" (#"val_subst" (#"sub_ty_subst" #"ty_wkn" "g") "c")
        : #"val" "D" "G'" {P {{e #"All" "A"}} }
    ];
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "c" : #"val" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") {P {{e "A"}} }
        ----------------------------------------------- ("ty_subst bAll")
        #"val_ty_subst" "g" (#"bAll" "A" "c")
        = #"bAll" (#"ty_subst" {ty_lift1 {{e "g"}} } "A")
            (#"val_ty_subst" {ty_lift1 {{e "g"}} } "c")
        : #"val" "D'" (#"env_ty_subst" "g" "G")
            {P {{e #"All" (#"ty_subst" {ty_lift1 {{e "g"}} } "A") }} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "c" : #"val" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") {P {{e "A"}} }
        ----------------------------------------------- ("bAll def")
        #"bAll" "A" "c" = {bAll_body} : #"val" "D" "G" {P {{e #"All" "A"}} }
    ]
  ]}.

(* Unlike [boundary_cases], this fragment goes through [auto_elab] rather than
   the computational [infer_lang_ext_simple_incr] pathway: the incremental
   inference engine re-saturates the *whole* base language before elaborating
   any rule, and with [boundary_cases] now part of that base the saturation no
   longer terminates in reasonable time. *)
Derive bAll_cases
  in (elab_lang_ext target_multilanguage_poly_subst bAll_cases_def bAll_cases)
  as bAll_cases_wf.
Proof. auto_elab. Qed.
#[local] Definition bAll_cases_entry :=
  lang_entry (elab_lang_implies_wf bAll_cases_wf).
#[export] Hint Resolve bAll_cases_entry : wf_lang_db.

Definition target_multilanguage_bAll := bAll_cases ++ target_multilanguage_poly_subst.
Hint Unfold target_multilanguage_bAll : auto_elab.

Lemma target_multilanguage_bAll_wf : wf_lang target_multilanguage_bAll.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_bAll_entry :=
  lang_entry target_multilanguage_bAll_wf.
#[export] Hint Resolve target_multilanguage_bAll_entry : wf_lang_db.


(* ------------------------------------------------------------------ *)
(* Stage 3: the [#"All"] case of the boundary recursor.

   The recursor is [trec_boundaries] of TrecTerms.v, i.e. [#"typerec"] at
   [boundary_sigma] with the three boundary case constants; the equation says
   that at [#"All" "A"] it is [#"bAll"] applied to the same recursor at ["A"]
   (which lives at [#"ty_ext" "D"], over [#"env_ty_subst" #"ty_wkn" "G"]). *)
Definition typerec_All_def : lang :=
  {[l
    [:= "D" : #"ty_env", "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D")
        ----------------------------------------------- ("typerec All")
        #"typerec" (#"All" "A") {boundary_sigma} #"bstar" #"bbool"
          (#"bfunc" {tva} {tvb} {ovar 1} {ovar 0})
        = #"bAll" "A" (#"typerec" "A" {boundary_sigma} #"bstar" #"bbool"
          (#"bfunc" {tva} {tvb} {ovar 1} {ovar 0}))
        : #"val" "D" "G" {P {{e #"All" "A"}} }
    ]
  ]}.

Derive typerec_All
  in (elab_lang_ext target_multilanguage_bAll typerec_All_def typerec_All)
  as typerec_All_wf.
Proof. auto_elab. Qed.
#[local] Definition typerec_All_entry :=
  lang_entry (elab_lang_implies_wf typerec_All_wf).
#[export] Hint Resolve typerec_All_entry : wf_lang_db.


(* ------------------------------------------------------------------ *)
(* The polymorphic target multilanguage. *)
Definition poly_target_multilanguage :=
  typerec_All ++ bAll_cases ++ poly_ty_subst ++ target_multilanguage.
Hint Unfold poly_target_multilanguage : auto_elab.

Lemma poly_target_multilanguage_wf : wf_lang poly_target_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition poly_target_multilanguage_entry :=
  lang_entry poly_target_multilanguage_wf.
#[export] Hint Resolve poly_target_multilanguage_entry : wf_lang_db.
