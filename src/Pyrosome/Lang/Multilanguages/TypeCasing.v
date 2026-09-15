Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* imports for compilers *)
(* copied from LinearCPS.v *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for `match # from high_level_multilanguage with` *)
(* CompilerDefs, for preserving_compiler_ext, is already imported. Prolly through something else. *)

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

From Stdlib Require derive.Derive.
From Pyrosome Require Import Tools.EGraph.InjRuleGen.

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC. 
From Pyrosome.Lang Require Import UTLC. 
From Pyrosome.Lang Require Import BoolType. 
From Pyrosome.Lang Require Import SimpleVProd.


(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers. (* for parameterizing existing languages*)
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.
From Pyrosome.Lang.Multilanguages Require Export Boundaries.

(* now we define the type casing fragment for the target multilanguage without boundaries. First, some helpers. *)
Fixpoint ty_wkn_n n :=
  match n with
  | 0 => {{e #"ty_id"}}
  | 1 => {{e #"ty_wkn"}}
  | S n' => {{e #"ty_cmp" #"ty_wkn" {ty_wkn_n n'} }}
  end.

Definition ty_ovar n :=
  match n with 
  | 0 => {{e #"ty_hd"}} (* bc ty_subst ty_id ty_hd is just ty_hd *)
  | S _ => {{e #"ty_subst" {ty_wkn_n n} #"ty_hd" }}
  end.  

(* ------------------------------------------------------------------ *)
(* VALUE-LEVEL typerec (this session's redesign).

   [#"typerec"] now returns a [#"val"], not an [#"exp"], and its function
   case is a *value* built by substituting the two recursive results into a
   single value variable ["v3"] that abstracts over two type variables and
   two term variables.  The old formulation returned an expression and the
   ["typerec func"] rule applied [#"@"]/[#"app"] to the *expressions*
   [#"typerec" "t1" ...]/[#"typerec" "t2" ...]; for a metavariable type
   those are stuck, so [STLC-beta] (which needs [#"ret" "v"]) never fired
   and the compiled boundary equations at type [#"->" "A" "B"] were
   unprovable.                                                            *)

(* [sigma] instantiated at [X] (X : ty D), i.e. sigma[X] *)
Definition Sg X := {{e #"ty_subst" (#"ty_snoc" #"ty_id" {X}) "sigma" }}.
(* [sigma] instantiated at [X], under two extra type variables
   (X : ty (ty_ext (ty_ext D))) *)
Definition S2 X := {{e #"ty_subst" (#"ty_snoc" {ty_wkn_n 2} {X}) "sigma" }}.
(* the two extra type variables *)
Definition tva := Eval compute in ty_ovar 1.
Definition tvb := Eval compute in ty_ovar 0.
(* [G] weakened by the two extra type variables *)
Definition G2 := {{e #"env_ty_subst" {ty_wkn_n 2} "G" }}.
Definition G2' := {{e #"env_ty_subst" {ty_wkn_n 2} "G'" }}.

(* the sort of the function case, [v3] *)
Definition v3_env := {{e #"ext" (#"ext" {G2} {S2 tva}) {S2 tvb} }}.
Definition v3_env' := {{e #"ext" (#"ext" {G2'} {S2 tva}) {S2 tvb} }}.
Definition v3_sort :=
  {{s #"val" (#"ty_ext" (#"ty_ext" "D")) {v3_env}
      {S2 {{e #"->" {tva} {tvb} }} } }}.

(* the two type variables lift of a term substitution "g", then the two
   term-variable lifts *)
Definition g_lift :=
  {{e #"snoc" (#"cmp" #"wkn"
        (#"snoc" (#"cmp" #"wkn" (#"sub_ty_subst" {ty_wkn_n 2} "g")) #"hd")) #"hd" }}.
(* the two type variable lift of a type substitution "g" *)
Definition ty_lift1 g := {{e #"ty_snoc" (#"ty_cmp" #"ty_wkn" {g}) #"ty_hd" }}.
Definition ty_lift2 := Eval compute in ty_lift1 (ty_lift1 {{e "g"}}).

Definition type_casing_rest_def : lang :=
  {[l
    [:| "D" : #"ty_env",
        "G" : #"env" "D",
        "mu" : #"ty" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "v1" : #"val" "D" "G" {Sg {{e #"*"}} },
        "v2" : #"val" "D" "G" {Sg {{e #"bool"}} },
        "v3" : {v3_sort}
        -----------------------------------------------
        #"typerec" "mu" "sigma" "v1" "v2" "v3"
        : #"val" "D" "G" {Sg {{e "mu"}} }
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "v1" : #"val" "D" "G" {Sg {{e #"*"}} },
        "v2" : #"val" "D" "G" {Sg {{e #"bool"}} },
        "v3" : {v3_sort}
        ----------------------------------------------- ("typerec star")
        #"typerec" #"*" "sigma" "v1" "v2" "v3"
        = "v1" : #"val" "D" "G" {Sg {{e #"*"}} }
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "v1" : #"val" "D" "G" {Sg {{e #"*"}} },
        "v2" : #"val" "D" "G" {Sg {{e #"bool"}} },
        "v3" : {v3_sort}
        ----------------------------------------------- ("typerec bool")
        #"typerec" #"bool" "sigma" "v1" "v2" "v3"
        = "v2" : #"val" "D" "G" {Sg {{e #"bool"}} }
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "t1" : #"ty" "D",
        "t2" : #"ty" "D",
        "v1" : #"val" "D" "G" {Sg {{e #"*"}} },
        "v2" : #"val" "D" "G" {Sg {{e #"bool"}} },
        "v3" : {v3_sort}
        ----------------------------------------------- ("typerec func")
        #"typerec" (#"->" "t1" "t2") "sigma" "v1" "v2" "v3"
        = #"val_subst"
            (#"snoc" (#"snoc" #"id" (#"typerec" "t1" "sigma" "v1" "v2" "v3"))
                     (#"typerec" "t2" "sigma" "v1" "v2" "v3"))
            (#"val_ty_subst" (#"ty_snoc" (#"ty_snoc" #"ty_id" "t1") "t2") "v3")
        : #"val" "D" "G" {Sg {{e #"->" "t1" "t2"}} }
    ];
    [:= "D" : #"ty_env",
        "D'" : #"ty_env",
        "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D",
        "mu" : #"ty" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "v1" : #"val" "D" "G" {Sg {{e #"*"}} },
        "v2" : #"val" "D" "G" {Sg {{e #"bool"}} },
        "v3" : {v3_sort}
        ----------------------------------------------- ("ty_subst typerec")
        #"val_ty_subst" "g" (#"typerec" "mu" "sigma" "v1" "v2" "v3")
        = #"typerec" (#"ty_subst" "g" "mu")
            (#"ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" "g") #"ty_hd") "sigma")
            (#"val_ty_subst" "g" "v1") (#"val_ty_subst" "g" "v2")
            (#"val_ty_subst" {ty_lift2} "v3")
        : #"val" "D'" (#"env_ty_subst" "g" "G") (#"ty_subst" "g" {Sg {{e "mu"}} })
    ]
  ]}.


(* The ["val_subst typerec"] rule is elaborated separately: type inference
   leaves the environment of ["v3"] as a hole here (it is only determined
   through the doubly-lifted substitution [g_lift]), so this one rule goes
   through [auto_elab] instead. *)
Definition val_subst_typerec_def : lang :=
  {[l
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G",
        "mu" : #"ty" "D",
        "sigma" : #"ty" (#"ty_ext" "D"),
        "v1" : #"val" "D" "G" {Sg {{e #"*"}} },
        "v2" : #"val" "D" "G" {Sg {{e #"bool"}} },
        "v3" : {v3_sort}
        ----------------------------------------------- ("val_subst typerec")
        #"val_subst" "g" (#"typerec" "mu" "sigma" "v1" "v2" "v3")
        = #"typerec" "mu" "sigma" (#"val_subst" "g" "v1") (#"val_subst" "g" "v2")
            (#"val_subst" {g_lift} "v3")
        : #"val" "D" "G'" {Sg {{e "mu"}} }
    ]
  ]}.
Definition TC_BASE :=
  stlc_ty_subst ++
    typed_bool_ty_subst ++
    star_type_ty_subst ++ error_t_ty_subst ++
    typed_bool_parameterized ++
    stlc_parameterized ++
    star_type_parameterized ++ error_t_parameterized ++
    poly ++ (* needed for #"All" *)
    (* base polymorphic stuff *)
    exp_param_substs ++ exp_ty_subst ++
    val_param_substs ++ val_ty_subst ++
    env_ty_subst ++ ty_subst_lang ++
    exp_parameterized ++ val_parameterized ++ ty_env_lang.

(* NOTE (this session): [auto_elab] OOMs on the whole value-level
   [type_casing] (killed at 11m51s / 7GB), so the five rules that type
   inference gets right are elaborated by the computational pathway, and the
   one rule it does not (["val_subst typerec"], whose ["v3"] environment is
   only determined through the doubly-lifted substitution [g_lift] and comes
   back as a hole) is elaborated by [auto_elab] on its own.               *)
Definition type_casing_rest :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 TC_BASE type_casing_rest_def.

Lemma type_casing_rest_wf : wf_lang_ext TC_BASE type_casing_rest.
Proof. Time compute_wf_lang. Qed.
#[local] Definition type_casing_rest_entry := lang_entry type_casing_rest_wf.
#[export] Hint Resolve type_casing_rest_entry : wf_lang_db.

Derive type_casing_vs
  in (elab_lang_ext (type_casing_rest ++ TC_BASE)
        val_subst_typerec_def type_casing_vs)
  as type_casing_vs_wf.
(* [auto_elab] itself fails here (its [cleanup_auto_elab] is not wrapped in
   [try], and some of the 281 leaves need [by_reduction] instead), so the
   same steps are run with the leaf tactics made total. *)
Proof.
  setup_elab_lang.
  unshelve (eapply eq_term_rule;
    [break_down_elab_ctx | break_elab_sort | try_break_elab_term | try_break_elab_term]).
  all: try (try apply eq_term_refl; try by_reduction; try cleanup_auto_elab).
Qed.
#[local] Definition type_casing_vs_entry :=
  lang_entry (elab_lang_implies_wf type_casing_vs_wf).
#[export] Hint Resolve type_casing_vs_entry : wf_lang_db.

Definition type_casing := type_casing_vs ++ type_casing_rest.

Lemma type_casing_wf : wf_lang_ext TC_BASE type_casing.
Proof.
  apply wf_lang_concat_hd.
  unfold type_casing; rewrite <- app_assoc.
  apply wf_lang_concat.
  { apply wf_lang_concat; [ prove_by_lang_db | exact type_casing_rest_wf ]. }
  { exact (elab_lang_implies_wf type_casing_vs_wf). }
Qed.
#[local] Definition type_casing_entry := lang_entry type_casing_wf.
#[export] Hint Resolve type_casing_entry : wf_lang_db.

Definition source_multilanguage :=
            boundaries ++ simple_interoperating_langs.
Hint Unfold source_multilanguage : auto_elab.

(* The target multilanguage *without* the boundary case constants; the full
   [target_multilanguage] is [boundary_cases ++ target_multilanguage_pre],
   defined in TrecTerms.v. *)
Definition target_multilanguage_pre :=
  let_eta_parameterized ++ let_ty_subst ++ let_parameterized ++
    prod_ty_subst ++ prod_parameterized ++
    type_casing ++
    polymorphic_interoperating_langs.
Hint Unfold target_multilanguage_pre : auto_elab.

Lemma source_multilanguage_wf : wf_lang source_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition source_multilanguage_entry :=
  lang_entry source_multilanguage_wf.
#[export] Hint Resolve source_multilanguage_entry : wf_lang_db.

Lemma target_multilanguage_pre_wf : wf_lang target_multilanguage_pre.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_pre_entry :=
  lang_entry target_multilanguage_pre_wf.
#[export] Hint Resolve target_multilanguage_pre_entry : wf_lang_db.
