# Multilanguages

A multi-language system: a typed language (STLC with booleans, products,
polymorphism) and an untyped language (UTLC with booleans) interoperating through
boundary terms, compiled to a single target that implements the boundaries by
type-directed case analysis (`typerec`), plus a partial evaluator that eliminates
`typerec` from compiled programs.

## Files (in dependency order)

| File | Contents |
|---|---|
| `ParamFragments.v` | Language fragments parameterized over a type environment (`typed_bool`, `star_type`, `error_t`, `utlc`, `untyped_bool`, `boolhuh`, `utlc_bool`, `mif`, `prod`, `let`) and their `*_ty_subst` languages. |
| `InteropLangs.v` | `simple_interoperating_langs`, `polymorphic_interoperating_langs`, and the identity-style `interoperating_langs_compiler` between them. |
| `Boundaries.v` | The `boundaries` language: `dtt`/`ttd` boundary terms and the 13 equations governing them (value-restricted `dtt func`, the mismatch-to-`Error` rules, substitution rules). |
| `TypeCasing.v` | The `type_casing` language (value-level `typerec` with `star`/`bool`/`func` cases and its substitution rules); `source_multilanguage` and `target_multilanguage_pre`. |
| `TrecTerms.v` | `boundary_cases` (the named case values `bstar`, `bbool`, `bfunc` with their substitution/definition rules), `target_multilanguage`, and the `trec_boundaries` term implementing the boundaries by `typerec`. |
| `SimpleMultilangCompiler.v` | `simple_multilang_compiler` (compiles `dtt`/`ttd` to `trec_boundaries`) and `simple_multilang_compiler_preserving`, assembled from one `eq_term` lemma per boundary equation. |
| `SimpleBoundaries.v` | `Require Export` shim over the six files above. |
| `PolyBoundaries.v` | The parameterized (polymorphic) boundaries, `poly_multilang_compiler`, and `poly_multilang_compiler_preserving`. |
| `TyperecPartialEval.v` | The partial evaluator `elim_typerec` and its metatheory: `can_eliminate_typerec`, `partial_eval_preserves_equality`, `partial_eval_wf_in_target`, `partial_eval_wf_in_no_typerec_lang`, `compiled_partial_eval_wf`. |

Every theorem in the folder is `Qed` and closed under the global context.

## Design notes

- **Boundaries are on expressions; the compiler let-binds.** `dtt G A e` compiles to
  `let e (app (.2 (exp_subst wkn TREC)) (ret hd))`, so STLC beta (which needs `ret v`)
  fires on the bound value. The target therefore includes `let` with a one-rule
  `let_eta` (`let e (ret hd) = e`).
- **`typerec` is value-level.** An expression-level `typerec` applied to a stuck
  `typerec A` at a type variable cannot be reduced by STLC beta, and the boundary
  equations are then provably unequal. The `func` case is a value open in two type
  variables and two term variables, instantiated by substitution.
- **Named case values.** The three cases are the constants `bstar`/`bbool`/`bfunc`
  of `boundary_cases`, with `bfunc` taking its type and recursive-result arguments
  explicitly. Substitution passes through a `typerec` in one rewrite step instead of
  being pushed through the case bodies.
- **Forward-only e-graph saturation.** The per-equation lemmas use
  `by_reduction'` with every rule oriented left-to-right; with all rules reversible
  the saturation is dominated by backward rewrites and the `func` equations do not
  terminate in reasonable time.
- **Two hops for the `func` equations.** The e-graph reducer restarts from the
  smallest extracted term whenever the weight drops, so a term-growing first step
  (`typerec func`) is discarded. Those lemmas go through an explicit intermediate
  term with `eq_term_trans`.
- **Conservativity for the partial evaluator.** `partial_eval_wf_in_no_typerec_lang`
  needs sort equalities of the full target to be derivable in the `typerec`-free
  sublanguage. `Theory/Conservativity.v` provides this for any extension whose new
  rules live above a closed stratum of sort names (here `{ty_env, env, ty, ty_sub}`),
  with the side condition decided by `vm_compute`.

## Building

Build single files with the absolute target, one Coq process at a time:

```
touch .Makefile.coq.d && make -f Makefile.coq /root/pyrosome-ai/src/Pyrosome/Lang/Multilanguages/<File>.vo
```

Approximate times: stages A-E about 20 minutes together; `SimpleMultilangCompiler.v`
and `PolyBoundaries.v` about an hour each; `TyperecPartialEval.v` about 5 minutes.
