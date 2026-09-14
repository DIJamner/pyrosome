# Multilanguages status / issue report

One row per definition. `Result` is one of: `Qed` (proved), `TIMEOUT <s>` (gave up
after that many seconds), `FAIL` (tactic/inference error), `ADMITTED` (left
admitted, see Issue column), `PENDING`. Times are wall-clock for the proof step
alone, on the 7GB build box with no other Coq process running.

## Stage A: ParamFragments.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| typed_bool_parameterized_wf | solve_parameterize_wrapper | | PENDING | |
| typed_bool_ty_subst | | | PENDING | |
| stlc_ty_subst | | | PENDING | |
| star_type_parameterized_wf | | | PENDING | |
| error_t_parameterized_wf | | | PENDING | |
| star_type_ty_subst | | | PENDING | |
| error_t_ty_subst | | | PENDING | |
| utlc_parameterized_wf | | | PENDING | |
| utlc_ty_subst | | | PENDING | |
| untyped_bool_parameterized_wf | | | PENDING | |
| untyped_bool_ty_subst | | | PENDING | |
| boolhuh_parameterized_wf | | | PENDING | |
| boolhuh_ty_subst | | | PENDING | |
| utlc_bool_parameterized_wf | | | PENDING | |
| mif_parameterized_wf | | | PENDING | |
| mif_ty_subst | | | PENDING | |
| prod_parameterized_wf | | | PENDING | |
| prod_ty_subst | | | PENDING | |

## Stage B: InteropLangs.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| simple_interoperating_langs_wf | | | PENDING | |
| polymorphic_interoperating_langs_wf | | | PENDING | |
| interoperating_langs_compiler_preserving | | | PENDING | |

## Stage C: Boundaries.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| boundaries_wf | | | PENDING | |

## Stage D: TypeCasing.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| type_casing_wf | | | PENDING | |
| target_multilanguage_wf | | | PENDING | |

## Stage E: TrecTerms.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| trec_star_case_wf | | | PENDING | |
| trec_bool_case_wf | | | PENDING | |
| trec_func_case_sort_wf | | | PENDING | |
| trec_func_case_wf | | | PENDING | |
| trec_boundaries_wf | | | PENDING | |

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
