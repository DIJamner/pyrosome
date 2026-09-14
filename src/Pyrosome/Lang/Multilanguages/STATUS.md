# Multilanguages status / issue report

One row per definition. `Result` is one of: `Qed` (proved), `TIMEOUT <s>` (gave up
after that many seconds), `FAIL` (tactic/inference error), `ADMITTED` (left
admitted, see Issue column), `PENDING`. Times are wall-clock for the proof step
alone, on the 7GB build box with no other Coq process running.

## Stage A: ParamFragments.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| typed_bool_parameterized_wf | solve_parameterize_wrapper | 4.0s | Qed | |
| typed_bool_ty_subst | auto_elab | 20.3s | Qed |  |
| stlc_ty_subst | auto_elab | 13.3s | Qed |  |
| star_type_parameterized_wf | solve_parameterize_wrapper | 2.5s | Qed |  |
| error_t_parameterized_wf | solve_parameterize_wrapper | 2.4s | Qed |  |
| star_type_ty_subst | auto_elab | 1.1s | Qed |  |
| error_t_ty_subst | auto_elab | 3.5s | Qed |  |
| utlc_parameterized_wf | parameterize_lang_preserving+compute | 5.6s | Qed |  |
| utlc_ty_subst | auto_elab | 22.3s | Qed |  |
| untyped_bool_parameterized_wf | parameterize_lang_preserving+compute | 4.0s | Qed |  |
| untyped_bool_ty_subst | auto_elab | 7.1s | Qed |  |
| boolhuh_parameterized_wf | parameterize_lang_preserving+compute | 11.4s | Qed |  |
| boolhuh_ty_subst | auto_elab | 11.3s | Qed |  |
| utlc_bool_parameterized_wf | parameterize_lang_preserving+compute | 10.8s | Qed |  |
| mif_parameterized_wf | parameterize_lang_preserving+compute | 12.5s | Qed |  |
| mif_ty_subst | auto_elab | 16.8s | Qed |  |
| prod_parameterized_wf | solve_parameterize_wrapper | 6.0s | Qed |  |
| prod_ty_subst | auto_elab | 33.2s | Qed |  |

## Stage B: InteropLangs.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| simple_interoperating_langs_wf | prove_by_lang_db | 2.0s | Qed | |
| polymorphic_interoperating_langs_wf | prove_by_lang_db | 4.9s | Qed | |
| interoperating_langs_compiler_preserving | auto_elab_compiler | 129.0s | Qed | |

## Stage C: Boundaries.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| boundaries_wf | auto_elab | 48.5s | Qed | |

## Stage D: TypeCasing.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| type_casing_wf | auto_elab (as-is) | 257.4s | Qed | tactic 229.6s + Qed 27.8s; computational pathway not needed |
| source_multilanguage_wf | prove_by_lang_db | 3.8s | Qed | added in this stage |
| target_multilanguage_wf | prove_by_lang_db | 12.2s | Qed | added in this stage |

## Stage E: TrecTerms.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| trec_star_case_wf | solve_elab_term_or_sort | 20.9s | Qed | |
| trec_bool_case_wf | solve_elab_term_or_sort | 22.2s | Qed | |
| trec_func_case_sort_wf | solve_elab_term_or_sort | 24.0s | Qed | |
| trec_func_case_wf | solve_elab_term_or_sort | 108.1s | Qed | tactic 72.0s + Qed 36.1s |
| trec_boundaries_wf | solve_elab_term_or_sort | 134.2s | Qed | tactic 96.7s + Qed 37.5s |

## Stage F: SimpleMultilangCompiler.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| simple_multilang_compiler (inference) | `infer_compiler_simple_autoinj 4 target_multilanguage ...` + `Eval vm_compute` | 24.1s | FAIL | inference produces `{{e #""}}` for the `ttd` case and, for `dtt`, a term with ~10 `#"?#..."` holes in which the `typerec` node has been replaced by the *bool* case of the typerec. Unusable; the compiler is written by hand on top of `trec_boundaries` instead. |
| simple_multilang_compiler (by hand) | explicit `term_case` over `trec_boundaries` | -- | Qed | `dtt_case_wf` 27.3s, `ttd_case_wf` 26.5s, both `compute_term_wf`; confirms the hand-written cases are the elaboration of `simple_multilang_compiler_def` |
| simple_multilang_compiler (elaboration cross-check) | old `Derive` + `setup_elab_compiler` + `solve_elab_term_or_sort`, equations stubbed by an axiom | 325s | (probe only) | confirms the two `elab_term` goals still go through; only the equations are the problem |
| simple_multilang_compiler_preserving | `compute_preserving_compiler simple_interoperating_langs` | tactic 0.13s (deferred), `Qed` killed at 913s / RSS 1.31GB | TIMEOUT 913 | tactic returns instantly because `flagged_exact` uses `vm_cast_no_check`; all the work is in `Qed`. Killed once the per-equation runs below showed 8/13 equations cannot be discharged. |
| simple_multilang_compiler_preserving | assembled from per-equation lemmas | -- | ADMITTED | `(* ISSUE: see STATUS.md *)`; 5 of 13 equations proved, 8 not (below) |

### Per-equation results

Method for every row: standalone `eq_term target_multilanguage (compile_ctx CMP c)
(compile_sort CMP t) (compile CMP e1) (compile CMP e2)` with
`CMP = simple_multilang_compiler ++ interoperating_langs_compiler`, proved with
`by_reduction_checked` (= `Automation.by_reduction` with the e-graph computation
forced at tactic time rather than deferred to `Qed`, and with the three wf side
conditions discharged), under an Ltac `timeout`.

| Equation | Time | Result | Issue / localized culprit |
|---|---|---|---|
| "dtt star" | TIMEOUT 300s | ADMITTED | **Believed genuinely FALSE.** LHS compiles to `app (ret (lambda #"*" (ret #"hd"))) "e"` where `"e"` is a variable of sort `#"exp" #"ty_emp" "G" (#"*" #"ty_emp")`; RHS compiles to `"e"`. `STLC-beta` (SimpleVSTLC.v:39) only fires on `#"app" (#"ret" (#"lambda" ...)) (#"ret" "v")`, i.e. on a *value* argument, and there is no eta/administrative law for `app` applied to an arbitrary expression anywhere in `target_multilanguage`. So the LHS is a normal form distinct from the RHS and the two are not equal. Root cause: `boundaries`' `dtt`/`ttd` take `"e" : #"exp" "G" _` where the compiler needs `"v" : #"val" "G" _`. |
| "ttd star" | TIMEOUT 300s | ADMITTED | same as "dtt star", through the `.1` projection instead of `.2` |
| "dtt True" | 32.2s | Qed | |
| "dtt False" | 31.6s | Qed | |
| "ttd True" | 31.3s | Qed | |
| "ttd False" | 31.6s | Qed | |
| "dtt func" | TIMEOUT 300s; re-run TIMEOUT 900s | ADMITTED | needs the `"typerec func"` rule of `type_casing` (polymorphic `#"All"`/`#"@"` instantiation with the large `A_var` type). Peak RSS ~1.8GB, no OOM -- pure saturation blow-up. |
| "ttd func" | TIMEOUT 300s; re-run TIMEOUT 900s | ADMITTED | as "dtt func" |
| "dtt ulambda mismatch" | 31.3s | Qed | only mismatch equation at type `#"bool"`, i.e. the only one reachable via `"typerec bool"` |
| "dtt uT mismatch" | TIMEOUT 300s; re-run TIMEOUT 900s | ADMITTED | at type `#"->" "A" "B"`, so it needs `"typerec func"`; same wall as "dtt func" |
| "dtt uF mismatch" | TIMEOUT 300s | ADMITTED | same shape as "dtt uT mismatch" (the 900s re-run was interrupted before reaching it) |
| "exp_subst dtt" | TIMEOUT 300s | ADMITTED | substitution equation: requires pushing `#"exp_subst"` through the whole `trec_boundaries` term (`"exp_subst typerec"` plus every `exp_subst`/`val_subst` rule of the fragments). Not attempted at 900s. |
| "exp_subst ttd" | TIMEOUT 300s | ADMITTED | as "exp_subst dtt" |

**Summary of the localized issue.** The equations split exactly along which
`typerec` rule they need: everything that reduces via `"typerec star"` or
`"typerec bool"` proves in ~31s; everything that needs `"typerec func"` times out
at 900s; the two `exp_subst` equations time out at 300s; and the two `star`
equations are not merely slow but appear to be false, because the compiler turns
`#"dtt" #"*" "e"` into a beta-redex whose argument is an expression rather than a
value. Fixing the two `star` rows probably means changing `boundaries` so that
`dtt`/`ttd` take a `#"val"`, not an `#"exp"` (and then `"dtt star"`/`"ttd star"`
become `#"dtt" #"*" (#"ret" "v") = #"ret" "v"`, which does follow by `STLC-beta`).

## Stage G: PolyBoundaries.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| boundaries_parameterized_wf | | | PENDING | |
| polymorphic_interoperating_langs_wf | | | PENDING | (moves to Stage B) |
| boundaries_ty_subst_wf | | | PENDING | |
| poly_boundaries_wf | | | PENDING | |
| lump_cancellation_term_wf | | | PENDING | |
| lump_cancellation_holds | | | PENDING | |
| polymorphic_interoperating_langs_compiler_preserving | | | PENDING | |
| dtt_forall_partial_eval_term_wf | | | PENDING | |
| ttd_forall_partial_eval_term_wf | | | PENDING | |
| poly_multilang_compiler_preserving | | | PENDING | (was commented out in the source) |

## Stage H: TyperecPartialEval.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| func_partial_eval_term_wf | | | PENDING | |
| source_multilanguage_wf | | | PENDING | |
| ty_eq_sort_lemma | | | PENDING | |
| ty_inversion_lemma | | | PENDING | |
| compiled_types_are_simple | | | PENDING | |
| can_eliminate_typerec | | | PENDING | |
| target_multilanguage_wf | | | PENDING | |
| ty_env_eq_sort_lemma_tml | | | PENDING | |
| ty_inversion_lemma_tml | | | PENDING | statement known wrong in source (missing prod/All cases) |
| eq_sort_sml_implies_eq_sort_tml | | | PENDING | admitted in source |
| partial_eval_preserves_equality | | | PENDING | admitted in source |
| target_multilanguage_without_typerec_wf | | | PENDING | |
| partial_eval_wf_in_no_typerec_lang | | | PENDING | admitted in source |
