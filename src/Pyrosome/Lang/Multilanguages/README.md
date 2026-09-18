# Multilanguages

A multi-language system: a typed language (STLC with booleans, products,
polymorphism) and an untyped language (UTLC with booleans) interoperating through
boundary terms, compiled to a single target that implements the boundaries by
type-directed case analysis (`typerec`), plus a partial evaluator that eliminates
`typerec` from compiled programs.

Two pipelines share the target:

```
simply typed source        poly source (typed side = System F fragment)
  | simple_multilang_compiler   | poly_multilang_compiler
  v                             v
target_multilanguage       poly_target_multilanguage  (typerec, no boundaries)
  |                             | mono  (monomorphization: type-level partial evaluation)
  | elim_typerec                | elim_typerec
  v                             v
target_multilanguage_without_typerec
```

For the simply typed source every compiled `typerec` is at a simple type
(`can_eliminate_typerec`), so elimination is unconditional.  For the
polymorphic source, elimination is preceded by monomorphization, and its
completeness is a decidable per-program side condition
(`all_typerecs_simple_b`): System F is not monomorphizable in general
(`Monomorphize.v`'s `ex2`, a program exporting a polymorphic function, is the
negative example).

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
| `PolySource.v` | `poly_boundaries`: the value-restricted quantifier boundary rules (`dtt forall`/`ttd forall` on `ret v`); `poly_source_multilanguage`, the source whose typed side is polymorphic. |
| `PolyTrecTerms.v` | `poly_target_multilanguage`: the target extended with the missing type-substitution laws for `Lam`/`@`, the quantifier case `bAll` of the boundary recursor and its boundary-specific rule `typerec All`, rigid restatements of a few type-substitution rules, the boundary-specialized recursor `btrec`, and the monomorphizer's rule set `mono_rule_names` with its reflective rigidity check. |
| `PolyMultilangCompiler.v` | `poly_multilang_compiler_preserving_full`: the same compiler preserves the full polymorphic source (13 lifted equations + `exp_ty_subst dtt/ttd` + `dtt/ttd forall`), and `poly_source_multilanguage_compiler_preserving` with the identity prefix folded in. |
| `Monomorphize.v` | `mono` (rewriting with `mono_rule_names`, then de-sugaring `btrec`), `mono_sound`/`mono_wf`, the decidable check `all_typerecs_simple_b`, transfer of well-formedness down to `target_multilanguage` (`wf_poly_to_tml`), `mono_elim_eq`/`mono_elim_wf`, and three worked examples. |
| `PolyPipeline.v` | `poly_pipeline`: the end-to-end theorem for the polymorphic source, instantiated on the examples. |

Supporting theory (generic, in `Theory/`): `RigidRewrite.v`, a rule-driven
rewriting engine whose soundness needs only a reflective per-rule check
(`rewrite_rule_ok`: the LHS is a rigid pattern in the sense of
`PatternRigidity.v`, its stated sort is the head rule's output sort
instantiated, and every context variable occurs in the LHS), and
`WfTransfer.v`, well-formedness transfer from a language to a sublanguage for
terms that avoid the extension's constructors.

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

### Polymorphic source

- **Quantifier boundary rules are value-restricted.**  `dtt (All A) e = ret (Lam (dtt A e))`
  on an arbitrary expression `e` delays the evaluation of `e` and is not
  preserved by a call-by-value compilation; the rules are stated on `ret v`
  (as `dtt func`/`ttd func` already were).
- **The quantifier case of the recursor is boundary-specific.**  A generic
  fourth case of `typerec` is not expressible: the recursive result at the body
  `A : ty (ty_ext D)` lives under the type binder while the case must produce a
  value at `D`; only a higher-kinded type variable could abstract over that.
  `bAll A c` (explicit arguments, as `bfunc`) and the rule `typerec All`, whose
  left-hand side is the boundary recursor itself, play that role.
- **Monomorphization is generic rewriting.**  `mono` rewrites with the target's
  own equations (`Lam-beta`, every type-substitution law, the type-level
  category laws), bottom-up with fuel; soundness and well-formedness come from
  `RigidRewrite.v` once the rule set passes `rewrite_rule_ok` by `vm_compute`.
  Three rules had to be restated with the sort in the syntactic form the check
  demands (`rigid_ty_subst`), and the rule pushing a type substitution through
  the boundary `typerec` is dead in a bottom-up pass (its explicit type
  argument is normalized before the root is tried), so the boundary recursor is
  folded into a constant `btrec` whose output sort is stated in normal form,
  rewritten, and de-sugared back before `elim_typerec`.
- **The `forall` compiler equations are proved by normalization, not by the
  e-graph.**  `typerec All` and `bAll def` grow the term and forward-only
  saturation restarts from the smallest representative; both sides are instead
  normalized with `RigidRewrite` (one e-graph step for `typerec All`, which is
  not a rigid rule) and compared by `vm_compute`.
- **Completeness is a side condition.**  The pipeline theorem is conditional on
  `all_typerecs_simple_b (mono c) = true` and on `mono c` mentioning neither
  `btrec` nor `bAll`; both are decided by `vm_compute` on a concrete program.

## Building

Build single files with the absolute target, one Coq process at a time:

```
touch .Makefile.coq.d && make -f Makefile.coq /root/pyrosome-ai/src/Pyrosome/Lang/Multilanguages/<File>.vo
```

Approximate times: stages A-E about 20 minutes together; `SimpleMultilangCompiler.v`
and `PolyBoundaries.v` about an hour each; `TyperecPartialEval.v` about 5 minutes;
`PolySource.v` 2 minutes, `PolyTrecTerms.v` 25 minutes (peak 5.4 GB),
`PolyMultilangCompiler.v` 36 minutes, `Monomorphize.v` 10 minutes.
