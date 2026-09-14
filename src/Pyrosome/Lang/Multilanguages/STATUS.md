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
| simple_multilang_compiler_preserving | | | PENDING | (13 boundary equations; per-equation rows added on failure) |

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
