Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* imports for compilers *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations.

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

(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers.
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.
From Pyrosome.Lang.Multilanguages Require Export TrecTerms.

Local Notation compiler :=
  (@CompilerDefs.compiler string (Term.term string) (Term.sort string)).

(* ------------------------------------------------------------------ *)
(* The compiler, as originally written (unelaborated).  Kept for
   documentation: the two target terms below are its elaboration.      *)
Definition simple_multilang_compiler_def : compiler :=
    match # from boundaries with
    | {{e #"dtt" "G" "A" "e"}} =>
        {{e #"let" "e" (#"app" (#".2" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                               (#"ret" #"hd")) }}
    | {{e #"ttd" "G" "A" "e"}} =>
        {{e #"let" "e" (#"app" (#".1" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                               (#"ret" #"hd")) }}
    end.

(* ------------------------------------------------------------------ *)
(* The elaborated compiler.

   NOTE (stage F, see STATUS.md): the computational route
   [infer_compiler_simple_autoinj 4 target_multilanguage ...] does NOT work
   here.  So the two cases are elaborated individually, on top of
   [trec_boundaries], the already-elaborated typerec term from TrecTerms.v.

   NOTE (let-binding change): the compiled body binds the source argument
   ["e"] with [#"let"] and applies the boundary function to [#"ret" #"hd"].
   A variable is a value, so [STLC-beta] now fires, which is what makes the
   ["dtt star"]/["ttd star"] equations provable (via the ["let eta"] rule).  *)

Definition dtt_case_unelab :=
  {{e #"let" "e" (#"app" (#".2" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                         (#"ret" #"hd")) }}.

Derive dtt_case_tgt
  in ( elab_term target_multilanguage
         [("e", {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}});
          ("A", {{s #"ty" #"ty_emp"}});
          ("G", {{s #"env" #"ty_emp"}})]
         dtt_case_unelab
         dtt_case_tgt
         {{s #"exp" #"ty_emp" "G" "A"}}
     ) as dtt_case_tgt_wf.
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed.

Definition ttd_case_unelab :=
  {{e #"let" "e" (#"app" (#".1" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                         (#"ret" #"hd")) }}.

Derive ttd_case_tgt
  in ( elab_term target_multilanguage
         [("e", {{s #"exp" #"ty_emp" "G" "A"}});
          ("A", {{s #"ty" #"ty_emp"}});
          ("G", {{s #"env" #"ty_emp"}})]
         ttd_case_unelab
         ttd_case_tgt
         {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}}
     ) as ttd_case_tgt_wf.
Proof. Timeout 1500 (solve_elab_term_or_sort target_multilanguage). Qed.

Definition simple_multilang_compiler : compiler :=
  [("ttd", term_case ["e"; "A"; "G"] ttd_case_tgt);
   ("dtt", term_case ["e"; "A"; "G"] dtt_case_tgt)].

(* ------------------------------------------------------------------ *)
(* The two term-constructor obligations of [preserving_compiler_ext].   *)

Lemma dtt_case_wf
  : wf_term target_multilanguage
      [("e", {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}});
       ("A", {{s #"ty" #"ty_emp"}});
       ("G", {{s #"env" #"ty_emp"}})]
      dtt_case_tgt {{s #"exp" #"ty_emp" "G" "A"}}.
Proof. pose proof target_multilanguage_wf. compute_term_wf. Qed.

Lemma ttd_case_wf
  : wf_term target_multilanguage
      [("e", {{s #"exp" #"ty_emp" "G" "A"}});
       ("A", {{s #"ty" #"ty_emp"}});
       ("G", {{s #"env" #"ty_emp"}})]
      ttd_case_tgt {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}}.
Proof. pose proof target_multilanguage_wf. compute_term_wf. Qed.

(* ------------------------------------------------------------------ *)
(* One [eq_term] lemma per boundary equation.

   [by_reduction_checked] is [Automation.by_reduction] with the e-graph
   computation forced at tactic time (the default [flagged_exact] defers it
   to [Qed]) and with the three well-formedness side conditions discharged,
   so that a failure is reported where it happens.                        *)

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

(* ------------------------------------------------------------------ *)
(* NOTE (value-level typerec): the per-[typerec]-case helper lemmas
   [star_case_subst] / [bool_case_subst] / [func_case_subst] are gone.  The
   three cases are now the value constants [#"bstar"] / [#"bbool"] /
   [#"bfunc"] of [boundary_cases], whose substitution rules are one-step
   rewrites, so the two ["exp_subst"] equations no longer need them.       *)

Definition CMP := simple_multilang_compiler ++ interoperating_langs_compiler.

Definition brule (n:string) := named_list_lookup (Rule.sort_rule [] []) boundaries n.
Definition gctx n := match brule n with Rule.term_eq_rule c _ _ _ => compile_ctx CMP c | _ => [] end.
Definition gsrt n := match brule n with Rule.term_eq_rule _ _ _ t => compile_sort CMP t | _ => default end.
Definition glhs n := match brule n with Rule.term_eq_rule _ e _ _ => compile CMP e | _ => default end.
Definition grhs n := match brule n with Rule.term_eq_rule _ _ e _ => compile CMP e | _ => default end.

Definition c_dtt_star := Eval vm_compute in gctx "dtt star".
Definition s_dtt_star := Eval vm_compute in gsrt "dtt star".
Definition l_dtt_star := Eval vm_compute in glhs "dtt star".
Definition r_dtt_star := Eval vm_compute in grhs "dtt star".
(* Provable since the compiler let-binds "e": the beta-redex now has a value
   (the variable [#"hd"]) as its argument, and ["let eta"] collapses the
   residual [#"let" "e" (#"ret" #"hd")] back to ["e"]. *)
Lemma eq_dtt_star : eq_term target_multilanguage c_dtt_star s_dtt_star l_dtt_star r_dtt_star.
Proof. unfold c_dtt_star, s_dtt_star, l_dtt_star, r_dtt_star. by_reduction_checked. Qed.

Definition c_ttd_star := Eval vm_compute in gctx "ttd star".
Definition s_ttd_star := Eval vm_compute in gsrt "ttd star".
Definition l_ttd_star := Eval vm_compute in glhs "ttd star".
Definition r_ttd_star := Eval vm_compute in grhs "ttd star".
(* As "dtt star", via the other projection. *)
Lemma eq_ttd_star : eq_term target_multilanguage c_ttd_star s_ttd_star l_ttd_star r_ttd_star.
Proof. unfold c_ttd_star, s_ttd_star, l_ttd_star, r_ttd_star. by_reduction_checked. Qed.

Definition c_dtt_True := Eval vm_compute in gctx "dtt True".
Definition s_dtt_True := Eval vm_compute in gsrt "dtt True".
Definition l_dtt_True := Eval vm_compute in glhs "dtt True".
Definition r_dtt_True := Eval vm_compute in grhs "dtt True".
Lemma eq_dtt_True : eq_term target_multilanguage c_dtt_True s_dtt_True l_dtt_True r_dtt_True.
Proof. unfold c_dtt_True, s_dtt_True, l_dtt_True, r_dtt_True. by_reduction_checked. Qed.

Definition c_dtt_False := Eval vm_compute in gctx "dtt False".
Definition s_dtt_False := Eval vm_compute in gsrt "dtt False".
Definition l_dtt_False := Eval vm_compute in glhs "dtt False".
Definition r_dtt_False := Eval vm_compute in grhs "dtt False".
Lemma eq_dtt_False : eq_term target_multilanguage c_dtt_False s_dtt_False l_dtt_False r_dtt_False.
Proof. unfold c_dtt_False, s_dtt_False, l_dtt_False, r_dtt_False. by_reduction_checked. Qed.

Definition c_ttd_True := Eval vm_compute in gctx "ttd True".
Definition s_ttd_True := Eval vm_compute in gsrt "ttd True".
Definition l_ttd_True := Eval vm_compute in glhs "ttd True".
Definition r_ttd_True := Eval vm_compute in grhs "ttd True".
Lemma eq_ttd_True : eq_term target_multilanguage c_ttd_True s_ttd_True l_ttd_True r_ttd_True.
Proof. unfold c_ttd_True, s_ttd_True, l_ttd_True, r_ttd_True. by_reduction_checked. Qed.

Definition c_ttd_False := Eval vm_compute in gctx "ttd False".
Definition s_ttd_False := Eval vm_compute in gsrt "ttd False".
Definition l_ttd_False := Eval vm_compute in glhs "ttd False".
Definition r_ttd_False := Eval vm_compute in grhs "ttd False".
Lemma eq_ttd_False : eq_term target_multilanguage c_ttd_False s_ttd_False l_ttd_False r_ttd_False.
Proof. unfold c_ttd_False, s_ttd_False, l_ttd_False, r_ttd_False. by_reduction_checked. Qed.

Definition c_dtt_func := Eval vm_compute in gctx "dtt func".
Definition s_dtt_func := Eval vm_compute in gsrt "dtt func".
Definition l_dtt_func := Eval vm_compute in glhs "dtt func".
Definition r_dtt_func := Eval vm_compute in grhs "dtt func".
(* ISSUE: see STATUS.md -- the e-graph now TERMINATES (65s) but reports the two
   sides unequal; it no longer saturates forever.  See STATUS.md, stage F. *)
Lemma eq_dtt_func : eq_term target_multilanguage c_dtt_func s_dtt_func l_dtt_func r_dtt_func.
Proof. unfold c_dtt_func, s_dtt_func, l_dtt_func, r_dtt_func. Time by_reduction_checked. Qed.

Definition c_ttd_func := Eval vm_compute in gctx "ttd func".
Definition s_ttd_func := Eval vm_compute in gsrt "ttd func".
Definition l_ttd_func := Eval vm_compute in glhs "ttd func".
Definition r_ttd_func := Eval vm_compute in grhs "ttd func".
(* ISSUE: see STATUS.md -- the e-graph now TERMINATES (65s) but reports the two
   sides unequal; it no longer saturates forever.  See STATUS.md, stage F. *)
Lemma eq_ttd_func : eq_term target_multilanguage c_ttd_func s_ttd_func l_ttd_func r_ttd_func.
Proof. unfold c_ttd_func, s_ttd_func, l_ttd_func, r_ttd_func. Time by_reduction_checked. Qed.

Definition c_dtt_ulambda_mismatch := Eval vm_compute in gctx "dtt ulambda mismatch".
Definition s_dtt_ulambda_mismatch := Eval vm_compute in gsrt "dtt ulambda mismatch".
Definition l_dtt_ulambda_mismatch := Eval vm_compute in glhs "dtt ulambda mismatch".
Definition r_dtt_ulambda_mismatch := Eval vm_compute in grhs "dtt ulambda mismatch".
Lemma eq_dtt_ulambda_mismatch : eq_term target_multilanguage c_dtt_ulambda_mismatch s_dtt_ulambda_mismatch l_dtt_ulambda_mismatch r_dtt_ulambda_mismatch.
Proof. unfold c_dtt_ulambda_mismatch, s_dtt_ulambda_mismatch, l_dtt_ulambda_mismatch, r_dtt_ulambda_mismatch. by_reduction_checked. Qed.

Definition c_dtt_uT_mismatch := Eval vm_compute in gctx "dtt uT mismatch".
Definition s_dtt_uT_mismatch := Eval vm_compute in gsrt "dtt uT mismatch".
Definition l_dtt_uT_mismatch := Eval vm_compute in glhs "dtt uT mismatch".
Definition r_dtt_uT_mismatch := Eval vm_compute in grhs "dtt uT mismatch".
(* ISSUE: see STATUS.md -- TIMEOUT: by_reduction times out at 300s and at 900s (needs the "typerec func" rule). *)
Lemma eq_dtt_uT_mismatch : eq_term target_multilanguage c_dtt_uT_mismatch s_dtt_uT_mismatch l_dtt_uT_mismatch r_dtt_uT_mismatch.
Proof. unfold c_dtt_uT_mismatch, s_dtt_uT_mismatch, l_dtt_uT_mismatch, r_dtt_uT_mismatch. Time by_reduction_checked. Qed.

Definition c_dtt_uF_mismatch := Eval vm_compute in gctx "dtt uF mismatch".
Definition s_dtt_uF_mismatch := Eval vm_compute in gsrt "dtt uF mismatch".
Definition l_dtt_uF_mismatch := Eval vm_compute in glhs "dtt uF mismatch".
Definition r_dtt_uF_mismatch := Eval vm_compute in grhs "dtt uF mismatch".
(* ISSUE: see STATUS.md -- TIMEOUT: by_reduction times out at 300s (900s run interrupted; same shape as "dtt uT mismatch"). *)
Lemma eq_dtt_uF_mismatch : eq_term target_multilanguage c_dtt_uF_mismatch s_dtt_uF_mismatch l_dtt_uF_mismatch r_dtt_uF_mismatch.
Proof. unfold c_dtt_uF_mismatch, s_dtt_uF_mismatch, l_dtt_uF_mismatch, r_dtt_uF_mismatch. Time by_reduction_checked. Qed.

Definition c_exp_subst_dtt := Eval vm_compute in gctx "exp_subst dtt".
Definition s_exp_subst_dtt := Eval vm_compute in gsrt "exp_subst dtt".
Definition l_exp_subst_dtt := Eval vm_compute in glhs "exp_subst dtt".
Definition r_exp_subst_dtt := Eval vm_compute in grhs "exp_subst dtt".
(* ISSUE: see STATUS.md -- localized to [func_case_subst] above (the [#"->"]
   case of the typerec); the [#"*"] and [#"bool"] cases are proved above. *)
Lemma eq_exp_subst_dtt : eq_term target_multilanguage c_exp_subst_dtt s_exp_subst_dtt l_exp_subst_dtt r_exp_subst_dtt.
Proof. unfold c_exp_subst_dtt, s_exp_subst_dtt, l_exp_subst_dtt, r_exp_subst_dtt. Time by_reduction_checked. Qed.

Definition c_exp_subst_ttd := Eval vm_compute in gctx "exp_subst ttd".
Definition s_exp_subst_ttd := Eval vm_compute in gsrt "exp_subst ttd".
Definition l_exp_subst_ttd := Eval vm_compute in glhs "exp_subst ttd".
Definition r_exp_subst_ttd := Eval vm_compute in grhs "exp_subst ttd".
(* ISSUE: see STATUS.md -- localized to [func_case_subst] above, as "exp_subst dtt". *)
Lemma eq_exp_subst_ttd : eq_term target_multilanguage c_exp_subst_ttd s_exp_subst_ttd l_exp_subst_ttd r_exp_subst_ttd.
Proof. unfold c_exp_subst_ttd, s_exp_subst_ttd, l_exp_subst_ttd, r_exp_subst_ttd. Time by_reduction_checked. Qed.

(* ------------------------------------------------------------------ *)
(* ISSUE: see STATUS.md, Stage F.  6 of the 13 boundary equations are not
   discharged: the six [typerec func] / [exp_subst] equations still time out
   (re-measured at 400s after the let-binding change).  "dtt star" and
   "ttd star", previously believed false, are now Qed thanks to the
   let-binding in the compiler plus the "let eta" rule.  The theorem is
   therefore still admitted; the seven equations that do go through are
   proved above.                                                         *)
Lemma simple_multilang_compiler_preserving
  : preserving_compiler_ext (tgt_Model := core_model target_multilanguage)
      interoperating_langs_compiler simple_multilang_compiler boundaries.
Proof. Time compute_preserving_compiler simple_interoperating_langs. Time Qed.

#[local] Definition simple_multilang_compiler_entry :=
  cmp_entry simple_multilang_compiler_preserving.
#[export] Hint Resolve simple_multilang_compiler_entry : preserving_db.
