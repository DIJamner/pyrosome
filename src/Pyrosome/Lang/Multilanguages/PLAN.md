# Multilanguages: incremental completion plan

Branch: `multilanguages-incremental` (off `faster-proofs`).

## Situation

`SimpleBoundaries.v`, `PolyBoundaries.v`, `TyperecPartialEval.v` last built in June
2026 and are not in the regular build. They use the old `Derive ... auto_elab` /
`auto_elab_compiler` / `solve_elab_term_or_sort` pathway, which is what makes the
e-graph tactics take too long, and `simple_multilang_compiler_preserving` is stubbed
with `apply TODO`. Everything downstream of `boundaries` (type casing, trec terms, the
boundary compiler, poly boundaries, the partial evaluator) is unverified.

## Strategy

1. **Checkpoint by splitting.** Cut `SimpleBoundaries.v` into one file per stage so
   each stage has its own `.vo` and later stages never re-run earlier proofs.
   `SimpleBoundaries.v` becomes a `Require Export` shim so `PolyBoundaries.v` and
   `TyperecPartialEval.v` keep working.
2. **Modernize each proof to the computational pathway** used elsewhere in `Lang/`:
   - languages: `infer_lang_ext_simple_incr 10 100 BASE def` + `compute_wf_lang`
   - compilers: `infer_compiler_simple_autoinj N tgt cmp_pre def src` +
     `compute_preserving_compiler cmp_pre_src`
   - terms: explicit term + `compute_term_wf` (or keep `Derive` if inference
     has no term entry point)
   Fall back to the old tactic only if the new one fails, and record why.
3. **Localize before proving.** When a whole-language/compiler check fails or times
   out, split it: `compute_wf_rule` per rule, and one standalone `eq_term` lemma per
   compiler equation (LHS/RHS compiled by hand) so the failing rule is named.
4. **Every step reports.** `STATUS.md` in this folder is the running issue report:
   one row per definition with method, wall time, result, and, if it fails, the
   named rule/equation plus the concrete evidence (error text or timeout).
5. **Hard resource rules.** One Coq build at a time (7GB box). Every probe runs under
   `timeout` and records `Time`. No `Admitted` left silently: a stage either ends in
   `Qed` or in a `STATUS.md` row explaining the localized failure, with the lemma
   `Admitted` and marked `(* ISSUE: see STATUS.md *)`.

## Stages (files, in dependency order)

| Stage | File | Contents | Method |
|---|---|---|---|
| A | `ParamFragments.v` | parameterized fragments (typed_bool, star_type, error_t, utlc, untyped_bool, boolhuh, utlc_bool, mif, prod) and their `*_ty_subst` langs | existing `solve_parameterize_wrapper`; ty_subst langs: try `eqn_rules` output + `compute_wf_lang` (no Derive), else `auto_elab` |
| B | `InteropLangs.v` | `simple_interoperating_langs`, `polymorphic_interoperating_langs`, wf lemmas, `interoperating_langs_compiler` | `prove_by_lang_db`; compiler via `infer_compiler_simple_autoinj` + `compute_preserving_compiler` |
| C | `Boundaries.v` | `boundaries` language (13 rules) | `infer_lang_ext_simple_incr` + `compute_wf_lang`; per-rule fallback |
| D | `TypeCasing.v` | `type_casing` language (6 rules), `target_multilanguage`, `source_multilanguage` | same as C |
| E | `TrecTerms.v` | `trec_star_case`, `trec_bool_case`, `trec_func_case_sort`, `trec_func_case`, `trec_boundaries` | `compute_term_wf`; fallback `Derive` + `solve_elab_term_or_sort` |
| F | `SimpleMultilangCompiler.v` | `simple_multilang_compiler` (2 rules, must preserve 13 boundary eqns) | `infer_compiler_simple_autoinj` + `compute_preserving_compiler`; per-equation `eq_term` lemmas with `by_reduction'` variants |
| G | `PolyBoundaries.v` | `boundaries_parameterized`, `boundaries_ty_subst`, `poly_boundaries`, lump cancellation, partial-eval terms, `poly_multilang_compiler` (currently commented out) | as A/C/E/F |
| H | `TyperecPartialEval.v` | partial evaluator metatheory; 4 admitted lemmas, one with a known-wrong statement | fix statements, prove or report; not e-graph bound |

Stage A is measured first with the untouched file (baseline build) to decide whether
it needs modernizing at all.

## Subagent protocol

Each stage is one Sonnet/Opus subagent, run serially. The prompt gives: the file(s),
the exact recipe, the fallback, the timeout budget, the build command
(`touch .Makefile.coq.d && make -f Makefile.coq <abs>.vo`), and the `STATUS.md` row
format. The agent must build in the foreground, never run two Coq processes, and
must end with a `Qed`-or-row outcome for every definition in its stage.

## Definition of done

- Every language in the three files has a `wf_lang_ext` theorem (Qed) or a named
  failing rule in `STATUS.md`.
- Every compiler has a `preserving_compiler_ext` theorem (Qed) or a named failing
  equation in `STATUS.md`.
- The three files (plus the split pieces) are in the build and compile end to end.
