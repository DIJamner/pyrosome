Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
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

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC. 
From Pyrosome.Lang Require Import UTLC. 
From Pyrosome.Lang Require Import BoolType. 
From Pyrosome.Lang Require Import SimpleVProd.
From Pyrosome.Lang.Multilanguages Require Import SimpleBoundaries. 


(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers. (* for parameterizing existing languages*)
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.

Definition boundaries_parameterized := 
    let ps := (elab_param "D" (boundaries ++ stlc ++ typed_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps boundaries.
Local Definition evp'_boundaries : lang := 
    let ps := (elab_param "D" (boundaries ++ stlc ++ typed_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (stlc ++ typed_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma boundaries_parameterized_wf (* this is necessary *)
  : wf_lang_ext ((stlc_parameterized ++ typed_bool_parameterized ++ untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      boundaries_parameterized.
Proof. 
  replace (stlc_parameterized ++ typed_bool_parameterized ++ untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_boundaries.
  - Time Timeout 1500 (eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor
    | now prove_by_lang_db..
    | vm_compute; exact I]).
  - Time cbv; reflexivity. 
Qed. 
#[local] Definition boundaries_parameterized_entry :=
  lang_entry boundaries_parameterized_wf.
#[export] Hint Resolve boundaries_parameterized_entry : wf_lang_db.

(* polymorphic_interoperating_langs_wf moved to Stage B (InteropLangs.v) *)

(* Lemma boundaries_parameterized_wf_2 : *)
(*   wf_lang (boundaries_parameterized ++ polymorphic_interoperating_langs). *)
(* Proof. prove_by_lang_db. Qed.  *)

Definition boundaries_ty_subst_def := Eval vm_compute in ty_subst_def_maker boundaries_parameterized (stlc_parameterized ++ typed_bool_parameterized ++ untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized).
Derive boundaries_ty_subst
  in (elab_lang_ext
              (boundaries_parameterized ++ polymorphic_interoperating_langs)
              boundaries_ty_subst_def
              boundaries_ty_subst)
  as boundaries_ty_subst_wf.
Proof. Time Timeout 1500 auto_elab. Time Qed.
#[local] Definition boundaries_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf boundaries_ty_subst_wf).
#[export] Hint Resolve boundaries_ty_subst_entry : wf_lang_db.

Definition poly_boundaries_def : lang := (* Matthews and Findler figure 11, page 12:33 *)
  {[l/subst [exp_subst++value_subst] 
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"), (* tau in Matthews and Findler *)
        "e" : #"exp" "D" "G" #"*"
        ----------------------------------------------- ("dtt forall")
        #"dtt" (#"All" "A") "e" =
        #"ret" (#"Lam" (#"dtt" "A" (#"exp_ty_subst" #"ty_wkn" "e")))
        : #"exp" "D" "G" (#"All" "A")
    ]; 
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"), (* tau in Matthews and Findler *)
        "e" : #"exp" "D" "G" (#"All" "A")
        ----------------------------------------------- ("ttd forall")
        #"ttd" (#"All" "A") "e" =
        #"ttd" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A") (#"@" "e" #"*") : #"exp" "D" "G" #"*"
    ]     
  ]}.

Derive poly_boundaries
  in (elab_lang_ext (boundaries_ty_subst ++
                             boundaries_parameterized ++ polymorphic_interoperating_langs)
                poly_boundaries_def poly_boundaries)
        as poly_boundaries_wf.
Proof. Time Timeout 1500 auto_elab. Time Qed.
#[local] Definition poly_boundaries_entry :=
  lang_entry (elab_lang_implies_wf poly_boundaries_wf).
#[export] Hint Resolve poly_boundaries_entry : wf_lang_db.
(* Aight so the problem you were having had to do with names and prove_by_lang_db. I think the moral solution is to add ty_subst to all the wf proofs for ty_subst langs above. But whatever I did works enough it looks like. *)



(* Matthews and Findler have lump cancellation as a rule. But, we don't need that rule, (I think) because we've collapsed the Lump and TST types! *)
Definition lump_cancellation_term_unelab :=
  {{e #"ttd" #"*" (#"dtt" #"*" "e") }}. 
Derive lump_cancellation_term
  in ( elab_term
         (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
         [("e", {{s #"exp" "D" "G" (#"*" "D")}}); (* the order of these matters! *)
          ("G", {{s #"env" "D"}});
          ("D", {{s #"ty_env"}})]
         lump_cancellation_term_unelab
         lump_cancellation_term
         {{s #"exp" "D" "G" (#"*" "D") }}
     ) as lump_cancellation_term_wf. 
Proof.
  Time Timeout 1500 (solve_elab_term_or_sort (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)).
Time Qed.

Lemma lump_cancellation_holds :
  eq_term
    (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
    [("e", {{s #"exp" "D" "G" (#"*" "D")}}); (* the order of these matters! *)
     ("G", {{s #"env" "D"}});
     ("D", {{s #"ty_env"}})]
    {{s #"exp" "D" "G" (#"*" "D") }}
    {{e "e" }}
    lump_cancellation_term.
Proof.
  assert (wf_lang (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)) by prove_by_lang_db.
  Time Timeout 1500 by_reduction.
Time Qed.



(* Now the compiler. Three parts: base identity compiler, then a first pass partial evaluation to get rid of #"All" in typerecs, and then a second pass to get rid of the boundaries *)
Local Notation compiler := (compiler string).

Local Notation preserving_compiler_ext tgt cmp_pre cmp src := (* copied from Paramaterizer, 2523 *)
  (preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).

Definition polymorphic_interoperating_langs_compiler :=
  id_compiler polymorphic_interoperating_langs.

Lemma polymorphic_interoperating_langs_compiler_preserving :
  preserving_compiler_ext
    polymorphic_interoperating_langs
    []
    polymorphic_interoperating_langs_compiler
    polymorphic_interoperating_langs.
Proof.
  Time Timeout 1500 (apply id_compiler_preserving; [ typeclasses eauto | prove_by_lang_db ]).
Time Qed.
#[local] Definition polymorphic_interoperating_langs_compiler_entry :=
  cmp_entry polymorphic_interoperating_langs_compiler_preserving.
#[export] Hint Resolve polymorphic_interoperating_langs_compiler_entry : preserving_db.

(* begin getting the partial evaluator *)
Definition dtt_forall_partial_eval_ctx :=
  Eval vm_compute in Rule.get_ctx (named_list_lookup default poly_boundaries "dtt forall").

Definition dtt_forall_partial_eval_term_def :=
  {{e #"ret" (#"Lam" (#"dtt" "A" (#"exp_ty_subst" #"ty_wkn" "e"))) }}. 

Derive dtt_forall_partial_eval_term
  in ( elab_term (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
         dtt_forall_partial_eval_ctx
         dtt_forall_partial_eval_term_def
         dtt_forall_partial_eval_term
         {{s #"exp" "D" "G" (#"All" "D" "A") }}
     ) as dtt_forall_partial_eval_term_wf. 
Proof.
  Time Timeout 1500 (solve_elab_term_or_sort (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)).
Time Qed.

Definition ttd_forall_partial_eval_ctx :=
  Eval vm_compute in Rule.get_ctx (named_list_lookup default poly_boundaries "ttd forall").

Definition ttd_forall_partial_eval_term_def :=
  {{e #"ttd" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A") (#"@" "e" #"*") }}.

Derive ttd_forall_partial_eval_term
  in ( elab_term (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
         ttd_forall_partial_eval_ctx
         ttd_forall_partial_eval_term_def
         ttd_forall_partial_eval_term
         {{s #"exp" "D" "G" (#"*" "D") }}
     ) as ttd_forall_partial_eval_term_wf. 
Proof.
  Time Timeout 1500 (solve_elab_term_or_sort (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)).
Time Qed.

Fixpoint forall_partial_eval (program : term) : term :=
  match program with
  | {{e #"dtt" {D} {G} (#"All" {_} {A}) {e} }} =>
      dtt_forall_partial_eval_term [/ [ ("e", e); ("A", A); ("G", G); ("D", D) ] /]
  | {{e #"ttd" {D} {G} (#"All" {_} {A}) {e} }} =>
      ttd_forall_partial_eval_term [/ [ ("e", e); ("A", A); ("G", G); ("D", D) ] /]
  | con n s => con n (map forall_partial_eval s)
  | var n => var n
  end.

(* poly to poly compiler *)
Definition poly_multilang_compiler_def : compiler :=
  match # from boundaries_parameterized with
  | {{e #"dtt" "D" "G" "A" "e"}} => {{e #"app" (#".2" {trec_boundaries_unelab}) "e" }}
  | {{e #"ttd" "D" "G" "A" "e"}} => {{e #"app" (#".1" {trec_boundaries_unelab}) "e" }}
    (* we don't need a type variable case, since it's the same as the old compiler! *)
  end.
(* ------------------------------------------------------------------ *)
(* Stage G: the poly -> poly compiler.

   The source language is [boundaries_parameterized]; its ambient prefix is
   [polymorphic_interoperating_langs] (that is the language
   [boundaries_parameterized_wf] extends, up to the fragments' ty_subst
   rules).  So the prefix compiler is
   [polymorphic_interoperating_langs_compiler], the *identity* compiler on
   [polymorphic_interoperating_langs] -- NOT [interoperating_langs_compiler],
   which has the *simple* (unparameterized) interoperating languages as its
   source and would not typecheck here.  The target is
   [target_multilanguage], which contains [polymorphic_interoperating_langs]
   as a suffix, so the identity prefix compiler is target-valid.

   As in stage F, the two cases are elaborated by hand from the [typerec]
   term; here it has to be re-elaborated at a general type environment "D"
   (the stage-F [trec_boundaries] lives at #"ty_emp").                     *)

Derive trec_boundaries_poly
  in ( elab_term target_multilanguage
         [("A", {{s #"ty" "D"}}); ("G", {{s #"env" "D"}}); ("D", {{s #"ty_env"}})]
         trec_boundaries_unelab
         trec_boundaries_poly
         {{s #"exp" "D" "G"
             (#"prod" "D"
                (#"->" "D" "A" (#"*" "D"))
                (#"->" "D" (#"*" "D") "A")) }}
     ) as trec_boundaries_poly_wf.
Proof. Time Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Time Qed.

Definition poly_dtt_case_tgt :=
  {{e #"app" "D" "G" (#"*" "D") "A"
       (#".2" "D" "G" (#"->" "D" "A" (#"*" "D"))
              (#"->" "D" (#"*" "D") "A") {trec_boundaries_poly})
       "e" }}.

Definition poly_ttd_case_tgt :=
  {{e #"app" "D" "G" "A" (#"*" "D")
       (#".1" "D" "G" (#"->" "D" "A" (#"*" "D"))
              (#"->" "D" (#"*" "D") "A") {trec_boundaries_poly})
       "e" }}.

Definition poly_multilang_compiler
  : @CompilerDefs.compiler string (Term.term string) (Term.sort string) :=
  [("ttd", term_case ["e"; "A"; "G"; "D"] poly_ttd_case_tgt);
   ("dtt", term_case ["e"; "A"; "G"; "D"] poly_dtt_case_tgt)].

Lemma poly_dtt_case_wf
  : wf_term target_multilanguage
      [("e", {{s #"exp" "D" "G" (#"*" "D")}});
       ("A", {{s #"ty" "D"}});
       ("G", {{s #"env" "D"}});
       ("D", {{s #"ty_env"}})]
      poly_dtt_case_tgt {{s #"exp" "D" "G" "A"}}.
Proof. pose proof target_multilanguage_wf. Time Timeout 1500 compute_term_wf. Time Qed.

Lemma poly_ttd_case_wf
  : wf_term target_multilanguage
      [("e", {{s #"exp" "D" "G" "A"}});
       ("A", {{s #"ty" "D"}});
       ("G", {{s #"env" "D"}});
       ("D", {{s #"ty_env"}})]
      poly_ttd_case_tgt {{s #"exp" "D" "G" (#"*" "D")}}.
Proof. pose proof target_multilanguage_wf. Time Timeout 1500 compute_term_wf. Time Qed.

(* ------------------------------------------------------------------ *)
(* Per-equation machinery, exactly as in stage F.                       *)

Ltac ctw_checked :=
  apply ComputeWf.compute_wf_term'_sound with (fuel := 100) (rebuild_fuel := 100)
    (saturation_fuel := 10) (efuel := 100) (red_fuel := 100)
    (filter := Automation.filter_rules) (reversible := fun _ => true)
    (inj_rules := Automation.empty_inj_rules);
  [ assumption | solve_wf_ctx | vm_compute; exact I ].

Ltac by_reduction_checked :=
  pose proof target_multilanguage_wf;
  apply (Automation.egraph_sound 100 100 100 100 Automation.filter_rules
           (fun _ : string * Rule.rule string => true) Automation.empty_inj_rules);
  [ prove_by_lang_db
  | solve_wf_ctx
  | ctw_checked
  | ctw_checked
  | vm_compute; exact I ].

Definition PCMP := poly_multilang_compiler ++ polymorphic_interoperating_langs_compiler.

Definition pbrule (n:string) :=
  named_list_lookup (Rule.sort_rule [] []) boundaries_parameterized n.
Definition pgctx n := match pbrule n with Rule.term_eq_rule c _ _ _ => compile_ctx PCMP c | _ => [] end.
Definition pgsrt n := match pbrule n with Rule.term_eq_rule _ _ _ t => compile_sort PCMP t | _ => default end.
Definition pglhs n := match pbrule n with Rule.term_eq_rule _ e _ _ => compile PCMP e | _ => default end.
Definition pgrhs n := match pbrule n with Rule.term_eq_rule _ _ e _ => compile PCMP e | _ => default end.

(* ------------------------------------------------------------------ *)
(* One [eq_term] lemma per equation of [boundaries_parameterized].       *)

Definition pc_dtt_star := Eval vm_compute in pgctx "dtt star".
Definition ps_dtt_star := Eval vm_compute in pgsrt "dtt star".
Definition pl_dtt_star := Eval vm_compute in pglhs "dtt star".
Definition pr_dtt_star := Eval vm_compute in pgrhs "dtt star".
(* ISSUE: see STATUS.md -- FALSE for the same reason as stage F's "dtt star": the LHS compiles to a beta-redex [#"app" (#"ret" (#"lambda" #"*" (#"ret" #"hd"))) "e"] whose argument is an arbitrary *expression*, while STLC-beta needs a [#"ret" "v"].  `by_reduction_checked` times out at 240s. *)
Lemma peq_dtt_star : eq_term target_multilanguage pc_dtt_star ps_dtt_star pl_dtt_star pr_dtt_star.
Admitted. (* ISSUE: see STATUS.md *)

Definition pc_ttd_star := Eval vm_compute in pgctx "ttd star".
Definition ps_ttd_star := Eval vm_compute in pgsrt "ttd star".
Definition pl_ttd_star := Eval vm_compute in pglhs "ttd star".
Definition pr_ttd_star := Eval vm_compute in pgrhs "ttd star".
(* ISSUE: see STATUS.md -- as "dtt star", through the [#".1"] projection. *)
Lemma peq_ttd_star : eq_term target_multilanguage pc_ttd_star ps_ttd_star pl_ttd_star pr_ttd_star.
Admitted. (* ISSUE: see STATUS.md *)

Definition pc_dtt_True := Eval vm_compute in pgctx "dtt True".
Definition ps_dtt_True := Eval vm_compute in pgsrt "dtt True".
Definition pl_dtt_True := Eval vm_compute in pglhs "dtt True".
Definition pr_dtt_True := Eval vm_compute in pgrhs "dtt True".
Lemma peq_dtt_True : eq_term target_multilanguage pc_dtt_True ps_dtt_True pl_dtt_True pr_dtt_True.
Proof. unfold pc_dtt_True, ps_dtt_True, pl_dtt_True, pr_dtt_True. Time Timeout 1500 by_reduction_checked. Time Qed.

Definition pc_dtt_False := Eval vm_compute in pgctx "dtt False".
Definition ps_dtt_False := Eval vm_compute in pgsrt "dtt False".
Definition pl_dtt_False := Eval vm_compute in pglhs "dtt False".
Definition pr_dtt_False := Eval vm_compute in pgrhs "dtt False".
Lemma peq_dtt_False : eq_term target_multilanguage pc_dtt_False ps_dtt_False pl_dtt_False pr_dtt_False.
Proof. unfold pc_dtt_False, ps_dtt_False, pl_dtt_False, pr_dtt_False. Time Timeout 1500 by_reduction_checked. Time Qed.

Definition pc_ttd_True := Eval vm_compute in pgctx "ttd True".
Definition ps_ttd_True := Eval vm_compute in pgsrt "ttd True".
Definition pl_ttd_True := Eval vm_compute in pglhs "ttd True".
Definition pr_ttd_True := Eval vm_compute in pgrhs "ttd True".
Lemma peq_ttd_True : eq_term target_multilanguage pc_ttd_True ps_ttd_True pl_ttd_True pr_ttd_True.
Proof. unfold pc_ttd_True, ps_ttd_True, pl_ttd_True, pr_ttd_True. Time Timeout 1500 by_reduction_checked. Time Qed.

Definition pc_ttd_False := Eval vm_compute in pgctx "ttd False".
Definition ps_ttd_False := Eval vm_compute in pgsrt "ttd False".
Definition pl_ttd_False := Eval vm_compute in pglhs "ttd False".
Definition pr_ttd_False := Eval vm_compute in pgrhs "ttd False".
Lemma peq_ttd_False : eq_term target_multilanguage pc_ttd_False ps_ttd_False pl_ttd_False pr_ttd_False.
Proof. unfold pc_ttd_False, ps_ttd_False, pl_ttd_False, pr_ttd_False. Time Timeout 1500 by_reduction_checked. Time Qed.

Definition pc_dtt_func := Eval vm_compute in pgctx "dtt func".
Definition ps_dtt_func := Eval vm_compute in pgsrt "dtt func".
Definition pl_dtt_func := Eval vm_compute in pglhs "dtt func".
Definition pr_dtt_func := Eval vm_compute in pgrhs "dtt func".
(* ISSUE: see STATUS.md -- TIMEOUT 240s: needs the "typerec func" rule of [type_casing]; same saturation wall as stage F (which also failed at 900s). *)
Lemma peq_dtt_func : eq_term target_multilanguage pc_dtt_func ps_dtt_func pl_dtt_func pr_dtt_func.
Admitted. (* ISSUE: see STATUS.md *)

Definition pc_ttd_func := Eval vm_compute in pgctx "ttd func".
Definition ps_ttd_func := Eval vm_compute in pgsrt "ttd func".
Definition pl_ttd_func := Eval vm_compute in pglhs "ttd func".
Definition pr_ttd_func := Eval vm_compute in pgrhs "ttd func".
(* ISSUE: see STATUS.md -- as "dtt func". *)
Lemma peq_ttd_func : eq_term target_multilanguage pc_ttd_func ps_ttd_func pl_ttd_func pr_ttd_func.
Admitted. (* ISSUE: see STATUS.md *)

Definition pc_dtt_ulambda_mismatch := Eval vm_compute in pgctx "dtt ulambda mismatch".
Definition ps_dtt_ulambda_mismatch := Eval vm_compute in pgsrt "dtt ulambda mismatch".
Definition pl_dtt_ulambda_mismatch := Eval vm_compute in pglhs "dtt ulambda mismatch".
Definition pr_dtt_ulambda_mismatch := Eval vm_compute in pgrhs "dtt ulambda mismatch".
Lemma peq_dtt_ulambda_mismatch : eq_term target_multilanguage pc_dtt_ulambda_mismatch ps_dtt_ulambda_mismatch pl_dtt_ulambda_mismatch pr_dtt_ulambda_mismatch.
Proof. unfold pc_dtt_ulambda_mismatch, ps_dtt_ulambda_mismatch, pl_dtt_ulambda_mismatch, pr_dtt_ulambda_mismatch. Time Timeout 1500 by_reduction_checked. Time Qed.

Definition pc_dtt_uT_mismatch := Eval vm_compute in pgctx "dtt uT mismatch".
Definition ps_dtt_uT_mismatch := Eval vm_compute in pgsrt "dtt uT mismatch".
Definition pl_dtt_uT_mismatch := Eval vm_compute in pglhs "dtt uT mismatch".
Definition pr_dtt_uT_mismatch := Eval vm_compute in pgrhs "dtt uT mismatch".
(* ISSUE: see STATUS.md -- TIMEOUT 240s: at type [#"->" "A" "B"], so it needs "typerec func". *)
Lemma peq_dtt_uT_mismatch : eq_term target_multilanguage pc_dtt_uT_mismatch ps_dtt_uT_mismatch pl_dtt_uT_mismatch pr_dtt_uT_mismatch.
Admitted. (* ISSUE: see STATUS.md *)

Definition pc_dtt_uF_mismatch := Eval vm_compute in pgctx "dtt uF mismatch".
Definition ps_dtt_uF_mismatch := Eval vm_compute in pgsrt "dtt uF mismatch".
Definition pl_dtt_uF_mismatch := Eval vm_compute in pglhs "dtt uF mismatch".
Definition pr_dtt_uF_mismatch := Eval vm_compute in pgrhs "dtt uF mismatch".
(* ISSUE: see STATUS.md -- as "dtt uT mismatch". *)
Lemma peq_dtt_uF_mismatch : eq_term target_multilanguage pc_dtt_uF_mismatch ps_dtt_uF_mismatch pl_dtt_uF_mismatch pr_dtt_uF_mismatch.
Admitted. (* ISSUE: see STATUS.md *)

Definition pc_exp_subst_dtt := Eval vm_compute in pgctx "exp_subst dtt".
Definition ps_exp_subst_dtt := Eval vm_compute in pgsrt "exp_subst dtt".
Definition pl_exp_subst_dtt := Eval vm_compute in pglhs "exp_subst dtt".
Definition pr_exp_subst_dtt := Eval vm_compute in pgrhs "exp_subst dtt".
(* ISSUE: see STATUS.md -- TIMEOUT 240s: pushing [#"exp_subst"] through the whole [trec_boundaries_poly] term. *)
Lemma peq_exp_subst_dtt : eq_term target_multilanguage pc_exp_subst_dtt ps_exp_subst_dtt pl_exp_subst_dtt pr_exp_subst_dtt.
Admitted. (* ISSUE: see STATUS.md *)

Definition pc_exp_subst_ttd := Eval vm_compute in pgctx "exp_subst ttd".
Definition ps_exp_subst_ttd := Eval vm_compute in pgsrt "exp_subst ttd".
Definition pl_exp_subst_ttd := Eval vm_compute in pglhs "exp_subst ttd".
Definition pr_exp_subst_ttd := Eval vm_compute in pgrhs "exp_subst ttd".
(* ISSUE: see STATUS.md -- as "exp_subst dtt". *)
Lemma peq_exp_subst_ttd : eq_term target_multilanguage pc_exp_subst_ttd ps_exp_subst_ttd pl_exp_subst_ttd pr_exp_subst_ttd.
Admitted. (* ISSUE: see STATUS.md *)

(* ------------------------------------------------------------------ *)
(* ISSUE: see STATUS.md, Stage G.  Exactly as in stage F, 5 of the 13
   equations of [boundaries_parameterized] go through and 8 do not: the two
   [star] equations are believed genuinely FALSE (the compiler produces a
   beta-redex applied to an expression rather than a value), and the six
   [typerec func] / [exp_subst] equations saturate.                       *)
Lemma poly_multilang_compiler_preserving
  : preserving_compiler_ext target_multilanguage
      polymorphic_interoperating_langs_compiler poly_multilang_compiler
      boundaries_parameterized.
Admitted. (* ISSUE: see STATUS.md *)
