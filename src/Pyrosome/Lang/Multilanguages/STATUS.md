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
| let_eta_wf | infer_lang_ext_simple_incr + compute_wf_lang | 1.0s + Qed 0.1s | Qed | new: one-rule `("let eta") #"let" "e" (#"ret" #"hd") = "e"` over `let_lang ++ exp_subst ++ value_subst` |
| let_parameterized_wf | solve_parameterize_wrapper | 3.6s + Qed 0.7s | Qed | new: `parameterize_wrapper let_lang` (`Let.v`'s `let_lang`, unmodified) |
| let_ty_subst | auto_elab | 6.6s + Qed 1.2s | Qed | new |
| let_eta_parameterized_wf | parameterize_lang_preserving_ext + `cbv; reflexivity` | Qed 0.8s | Qed | new; no ty_subst lang needed (no new syntax, like `utlc_bool`) |

## Stage B: InteropLangs.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| simple_interoperating_langs_wf | prove_by_lang_db | 2.0s | Qed | |
| polymorphic_interoperating_langs_wf | prove_by_lang_db | 4.9s | Qed | |
| interoperating_langs_compiler_preserving | auto_elab_compiler | 129.0s | Qed | |

## Stage C: Boundaries.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| boundaries_wf | auto_elab | 48.5s | Qed | **SOURCE CHANGE (this session, user decision).** The `"dtt func"` rule's premise `"v" : #"val" "G" #"*"` was replaced by `"e" : #"exp" (#"ext" "G" #"*") #"*"` and `"v"` by `#"ulambda" "e"` on both sides.  Rationale: with an arbitrary `"v"` the rule overlaps `"dtt uT mismatch"` / `"dtt uF mismatch"`, so the source proves `#"Error" (#"->" "A" "B") = #"ret" (#"lambda" ...)`, which no compiler can preserve into a target whose `#"Error"` is inert.  Re-derives with `auto_elab` unchanged. |

## Stage D: TypeCasing.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| type_casing_wf | auto_elab (as-is) | 257.4s | Qed | tactic 229.6s + Qed 27.8s; computational pathway not needed |
| source_multilanguage_wf | prove_by_lang_db | 3.8s | Qed | added in this stage |
| target_multilanguage_wf | prove_by_lang_db | 1.6s + Qed 10.9s | Qed | added in this stage; now also contains `let_eta_parameterized ++ let_ty_subst ++ let_parameterized` |

## Stage E: TrecTerms.v

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| trec_star_case_wf | solve_elab_term_or_sort | 20.9s | Qed | |
| trec_bool_case_wf | solve_elab_term_or_sort | 22.2s | Qed | |
| trec_func_case_sort_wf | solve_elab_term_or_sort | 24.0s | Qed | |
| trec_func_case_wf | solve_elab_term_or_sort | see below | Qed | **TERM CHANGED (this session).** New shape, below. |
| trec_boundaries_wf | solve_elab_term_or_sort | see below | Qed | re-derived over the new `trec_func_case`; whole `TrecTerms.v` rebuild is now **7m15s** (was ~5m) |

### New `trec_func_case_unelab` (this session)

The two components of the `#"pair"` are now written so that they are *literally*
the compiled image of the two boundary rules' right-hand sides, i.e. let-shaped,
and the `#".2"` (the `dtt`) component eagerly checks that the untyped value
really is a function:

```
ret (Lam (ret (lambda P (ret (Lam (ret (lambda P (pair
  (* .1 : (t1 -> t2) -> *   -- mirrors ("ttd func") *)
  (ret (lambda (-> {ty_ovar 1} {ty_ovar 0})
     (ret (ulambda
        (let (app (ret {ovar 1}) (let (ret {ovar 0}) (app (.2 (ret {ovar 4})) (ret {ovar 0}))))
             (app (.1 (ret {ovar 3})) (ret {ovar 0})))))))
  (* .2 : * -> (t1 -> t2)   -- mirrors ("dtt func"), with the eager check *)
  (ret (lambda *
     (mif (bool? (ret {ovar 0}))
          (Error (-> {ty_ovar 1} {ty_ovar 0}))
          (ret (lambda {ty_ovar 1}
             (let (uapp (ret {ovar 1}) (let (ret {ovar 0}) (app (.1 (ret {ovar 4})) (ret {ovar 0}))))
                  (app (.2 (ret {ovar 3})) (ret {ovar 0}))))))))
))))))))
```

with `P = prod (-> {ty_ovar 0} *) (-> * {ty_ovar 0})`.  `trec_func_case_sort` is
**unchanged** (both components still have the same types).  Note the conditional
is `#"mif"`, not `#"if"`: `#"bool?"` returns an *untyped* boolean
(`#"exp" "G" #"*"`, rules `"bool?-true"`/`"bool?-false"` give `#"ret" #"uT"`,
`"bool?-func"` gives `#"ret" #"uF"`), and `#"mif"` is the eliminator with an
untyped scrutinee and a typed result (`"mif true"`/`"mif false"`/`"mif func"`/
`"mif Error"` in `BoolType.v`).  So
`#"dtt" (#"->" "A" "B") (#"ret" #"uT"/#"uF")` should now reduce to
`#"Error" (#"->" "A" "B")`, and `#"dtt" (#"->" "A" "B") (#"ret" (#"ulambda" "e"))`
to the `#"lambda"` wrapper.

## Stage F: SimpleMultilangCompiler.v

**UPDATE (let-binding change).**  The compiler no longer emits
`#"app" (#".2" TREC) "e"` with `"e"` an arbitrary expression.  It now
let-binds the argument:

```
#"dtt" "G" "A" "e"  |->  #"let" "e" (#"app" (#".2" (#"exp_subst" #"wkn" TREC)) (#"ret" #"hd"))
#"ttd" "G" "A" "e"  |->  #"let" "e" (#"app" (#".1" (#"exp_subst" #"wkn" TREC)) (#"ret" #"hd"))
```

The let-bound variable `#"hd"` *is* a value, so `STLC-beta` fires; the
residual `#"let" "e" (#"ret" #"hd")` is collapsed by a new one-rule language
`let_eta` (`("let eta") #"let" "e" (#"ret" #"hd") = "e"`).  `let_lang`
(`Lang/Let.v`) and `let_eta`, both parameterized, plus `let_ty_subst`, were
added to `target_multilanguage` (stage A rows above).  `boundaries` itself
was **not** changed.  Consequence: `"dtt star"` and `"ttd star"`, previously
believed FALSE, are now **Qed**; 7 of 13 equations now go through instead of
5.  The six `"typerec func"`/`exp_subst` equations still time out
(re-measured at 400 s each after the change).

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| simple_multilang_compiler (inference) | `infer_compiler_simple_autoinj 4 target_multilanguage ...` + `Eval vm_compute` | 24.1s | FAIL | inference produces `{{e #""}}` for the `ttd` case and, for `dtt`, a term with ~10 `#"?#..."` holes in which the `typerec` node has been replaced by the *bool* case of the typerec. Unusable; the compiler is written by hand on top of `trec_boundaries` instead. |
| simple_multilang_compiler (by hand) | explicit `term_case` over `trec_boundaries` | -- | Qed | (superseded) `dtt_case_wf` 27.3s, `ttd_case_wf` 26.5s |
| dtt_case_tgt / ttd_case_tgt (let-binding version) | `Derive` + `solve_elab_term_or_sort target_multilanguage` | 102.2s + Qed 43.2s / 135.1s + Qed 43.6s | Qed | the two compiler cases are now *elaborated* from the unelaborated `#"let" ...` body rather than written out; `dtt_case_wf`/`ttd_case_wf` re-check them with `compute_term_wf` (Qed 28.5s / 28.1s) |
| simple_multilang_compiler (elaboration cross-check) | old `Derive` + `setup_elab_compiler` + `solve_elab_term_or_sort`, equations stubbed by an axiom | 325s | (probe only) | confirms the two `elab_term` goals still go through; only the equations are the problem |
| simple_multilang_compiler_preserving | `compute_preserving_compiler simple_interoperating_langs` | tactic 0.13s (deferred), `Qed` killed at 913s / RSS 1.31GB | TIMEOUT 913 | tactic returns instantly because `flagged_exact` uses `vm_cast_no_check`; all the work is in `Qed`. Killed once the per-equation runs below showed 8/13 equations cannot be discharged. |
| simple_multilang_compiler_preserving | assembled from per-equation lemmas | -- | ADMITTED | `(* ISSUE: see STATUS.md *)`; **7 of 13** equations proved after the let-binding change (was 5), 6 not (below) |

### Per-equation results

Method for every row: standalone `eq_term target_multilanguage (compile_ctx CMP c)
(compile_sort CMP t) (compile CMP e1) (compile CMP e2)` with
`CMP = simple_multilang_compiler ++ interoperating_langs_compiler`, proved with
`by_reduction_checked` (= `Automation.by_reduction` with the e-graph computation
forced at tactic time rather than deferred to `Qed`, and with the three wf side
conditions discharged), under an Ltac `timeout`.

| Equation | Time | Result | Issue / localized culprit |
|---|---|---|---|
| "dtt star" | before: TIMEOUT 300s -- after: 34.9s + Qed 51.6s | **Qed** | Previously believed genuinely FALSE (`app (ret (lambda ...)) "e"` with `"e"` an expression is a normal form, and `STLC-beta` needs `#"ret" "v"`). The compiler now let-binds `"e"`, so the argument is the *variable* `#"hd"`, `STLC-beta` fires, and `"let eta"` collapses `#"let" "e" (#"ret" #"hd")` to `"e"`. `boundaries` unchanged. |
| "ttd star" | before: TIMEOUT 300s -- after: 35.2s + Qed 51.5s | **Qed** | as "dtt star", through the `.1` projection instead of `.2` |
| "dtt True" | before 32.2s -- after 34.8s + Qed 51.9s | Qed | |
| "dtt False" | before 31.6s -- after 35.0s + Qed 53.1s | Qed | |
| "ttd True" | before 31.3s -- after 35.6s + Qed 52.0s | Qed | |
| "ttd False" | before 31.6s -- after 36.2s + Qed 52.2s | Qed | |
| "dtt func" | TIMEOUT 300s; 900s; after the change TIMEOUT 400s | ADMITTED | unchanged: needs the `"typerec func"` rule of `type_casing` (polymorphic `#"All"`/`#"@"` instantiation with the large `A_var` type). Pure saturation blow-up, no OOM. |
| "ttd func" | TIMEOUT 300s; 900s | ADMITTED | as "dtt func" |
| "dtt ulambda mismatch" | before 31.3s -- after 35.7s + Qed 52.3s | Qed | only mismatch equation at type `#"bool"`, i.e. the only one reachable via `"typerec bool"` |
| "dtt uT mismatch" | TIMEOUT 300s; 900s | ADMITTED | at type `#"->" "A" "B"`, so it needs `"typerec func"`; same wall as "dtt func" |
| "dtt uF mismatch" | TIMEOUT 300s | ADMITTED | same shape as "dtt uT mismatch" |
| "exp_subst dtt" | TIMEOUT 300s; after the change TIMEOUT 400s | ADMITTED | substitution equation: requires pushing `#"exp_subst"` through the whole `trec_boundaries` term (`"exp_subst typerec"` plus every `exp_subst`/`val_subst` rule of the fragments), and now also through the `#"let"` node. |
| "exp_subst ttd" | TIMEOUT 300s | ADMITTED | as "exp_subst dtt" |
| "dtt star" (value-restricted variant) | 32.2s tactic + 46.6s Qed | Qed (probe) | Confirms the Stage F diagnosis. Same compiled LHS/RHS as "dtt star", with the expression variable `"e"` replaced by `#"ret" #"ty_emp" "G" (#"*" #"ty_emp") "v"` in ctx `[("v", #"val" #"ty_emp" "G" (#"*" #"ty_emp")); ("G", #"env" #"ty_emp")]`; proved by the same `by_reduction_checked`. So the only obstacle to "dtt star" is that `boundaries` gives `dtt`/`ttd` an `#"exp"` argument where `STLC-beta` needs a `#"ret" "v"`. |
| "ttd star" (value-restricted variant) | 32.2s tactic + 46.9s Qed | Qed (probe) | as above, through the `.1` projection. |

### UPDATE (this session: source change + new `trec_func_case`)

After the `Boundaries.v` `"dtt func"` restriction (stage C) and the new
`trec_func_case` (stage E), the whole chain still builds and **the 7 equations
that were `Qed` are still `Qed`** (`SimpleMultilangCompiler.v` full rebuild:
19m57s).  The remaining 6 are still open, but the diagnosis has changed:

| Equation | Before | Now | Evidence |
|---|---|---|---|
| "ttd func" | TIMEOUT 400s (saturation never finished) | **FAIL in 65s** | `by_reduction_checked` now *terminates*: the e-graph saturates and the final `vm_compute; exact I` check reports `The term "I" has type "True" while it is expected to have type "False"`, i.e. the two sides are not in the same e-class.  So the let-shaped `#".1"` wrapper removed the saturation blow-up, but something still does not join.  Not localized further: the diagnostic route (`compute_eq_compilation; reduce; hide_implicits; Show`) does not finish -- `Matches.reduce` alone was killed at 600s on this goal. |
| "dtt func", "dtt uT mismatch", "dtt uF mismatch" | TIMEOUT 300/400/900s | not re-measured | left `Admitted` with the ISSUE marker; the `#"mif"`/`#"bool?"` eager check is in place, so these are expected to behave like "ttd func" (terminate, then either close or report unequal). |
| "exp_subst dtt", "exp_subst ttd" | TIMEOUT 300/400s | **localized** | split into per-`typerec`-case leaves (the lemmas `star_case_subst` / `bool_case_subst` / `func_case_subst` now in the file), each of the form `#"exp_subst" "g" CASE[G] = CASE[G']` in ctx `[("g", #"sub" #"ty_emp" "G'" "G"); ("G'", #"env"); ("G", #"env")]`.  **`star_case_subst`: Qed, 2.9s tactic + 19.9s Qed.  `bool_case_subst`: Qed, 2.9s + 19.9s.  `func_case_subst`: TIMEOUT 900s** -- `Admitted. (* ISSUE *)`.  So the *only* obstruction to both `#"exp_subst"` equations is pushing `#"exp_subst"` through the (now larger) `#"->"` case of the typerec; the other two cases are cheap.  Next step: split `func_case_subst` itself with `eredex_steps_with` on `"exp_subst ret"` / `"val_subst Lam"` / `"val_subst lambda"` / `"exp_subst pair"` and then `term_cong` down to the two wrappers. |

The intended (unfinished) shape of the two `#"exp_subst"` equations, for the
record: `"exp_subst let"` (generated for `let_lang`) turns the LHS into
`#"let" (#"exp_subst" "g" "e") (#"exp_subst" (#"snoc" (#"cmp" #"wkn" "g") #"hd") BODY)`;
`term_cong` then leaves
`#"exp_subst" g^ (#"exp_subst" #"wkn" TREC[G]) = #"exp_subst" #"wkn" TREC[G']`,
which by `"exp_subst_cmp"` + `"wkn_snoc"` becomes
`#"exp_subst" #"wkn" (#"exp_subst" "g" TREC[G]) = #"exp_subst" #"wkn" TREC[G']`,
i.e. the helper `#"exp_subst" "g" TREC[G] = TREC[G']`, which `"exp_subst typerec"`
splits into the three case lemmas above.

**Summary of the localized issue (updated).** The equations still split exactly
along which `typerec` rule they need: everything that reduces via
`"typerec star"` or `"typerec bool"` proves in ~35 s (plus ~52 s at `Qed`);
everything that needs `"typerec func"` times out (300 s, 900 s, and 400 s after
the change); the two `exp_subst` equations still time out.  The two `star`
equations are **no longer a definitional problem**: let-binding the compiler's
argument (rather than weakening `boundaries` to take a `#"val"`) made both of
them provable, at the price of adding `let_lang` + a one-rule `let_eta` to the
target multilanguage.  The remaining 6 failures are pure e-graph saturation
cost, not soundness.

## Stage G: PolyBoundaries.v

PolyBoundaries.v now compiles end to end (14m31s originally; ~21m after the let-binding change, which adds two `solve_elab_term_or_sort` elaborations and two more `by_reduction_checked` equations).  The whole file builds as-is (with `Derive ... SuchThat ... As` modernized to
`Derive ... in ... as`, and `PolyCompilerLangs`/`PolyCompilersCPS` added to the
imports so `stlc_parameterized` and friends resolve).  No fallback was needed
for any of the original definitions.

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| boundaries_parameterized_wf | parameterize_lang_preserving_ext + `cbv; reflexivity` | tactic 27.7s + 0.2s, Qed 26.3s | Qed | parameterizer route, as in ParamFragments.v |
| polymorphic_interoperating_langs_wf | -- | -- | moved | now proved in Stage B (InteropLangs.v) |
| boundaries_ty_subst_wf | `Derive ... in ... as` + auto_elab | tactic 38.5s + Qed 19.3s | Qed | |
| poly_boundaries_wf | `Derive ... in ... as` + auto_elab | tactic 40.5s + Qed 19.0s | Qed | both "dtt forall" and "ttd forall" elaborate |
| lump_cancellation_term_wf | Derive + solve_elab_term_or_sort | tactic 2.0s + Qed 15.3s | Qed | |
| lump_cancellation_holds | prove_by_lang_db + by_reduction | tactic 1.2s + 3.2s, Qed 15.2s | Qed | `#"ttd" #"*" (#"dtt" #"*" "e") = "e"` really does hold |
| polymorphic_interoperating_langs_compiler_preserving | id_compiler_preserving | tactic 1.2s + Qed 12.8s | Qed | |
| dtt_forall_partial_eval_term_wf | Derive + solve_elab_term_or_sort | tactic 12.5s + Qed 15.3s | Qed | |
| ttd_forall_partial_eval_term_wf | Derive + solve_elab_term_or_sort | tactic 2.3s + Qed 15.3s | Qed | |
| trec_boundaries_poly_wf | Derive + solve_elab_term_or_sort | tactic 97.4s + Qed 32.7s | Qed | new in this stage: `trec_boundaries` re-elaborated at a *general* type environment `"D"` (the Stage-E one lives at `#"ty_emp"`), needed to build the poly compiler cases |
| poly_dtt_case_tgt / poly_ttd_case_tgt (let-binding version) | `Derive` + `solve_elab_term_or_sort target_multilanguage` | 126.9s + Qed 38.6s / 135.1s + Qed 37.7s | Qed | same let-binding change as stage F, at general `"D"`: `#"let" "e" (#"app" (#".2"/#".1" (#"exp_subst" #"wkn" trec)) (#"ret" #"hd"))`; `poly_dtt_case_wf`/`poly_ttd_case_wf` re-check with `compute_term_wf` (Qed 27.3s / 28.4s) |
| poly_multilang_compiler_preserving | `compute_preserving_compiler polymorphic_interoperating_langs` | tactic returns immediately (deferred); killed at `Qed` after 1500s, RSS ~1.0GB | TIMEOUT 1500 | tactic is `flagged_exact`/`vm_cast_no_check`, so all the work is at `Qed` |
| poly_multilang_compiler_preserving | assembled from per-equation lemmas | -- | ADMITTED | `(* ISSUE: see STATUS.md *)`; **7 of 13** equations proved after the let-binding change (was 5), 6 not (below) |

**Prefix compiler.**  The source language is `boundaries_parameterized`, whose
ambient prefix (from `boundaries_parameterized_wf`) is the parameterized
fragments `++ ty_env_lang`, i.e. a suffix of `polymorphic_interoperating_langs`.
So the prefix compiler is `polymorphic_interoperating_langs_compiler`
(`id_compiler polymorphic_interoperating_langs`), *not* the
`interoperating_langs_compiler` named in the commented-out source: that one's
source is `simple_interoperating_langs`, the unparameterized languages, which
are not part of this source language at all.  The target stays
`target_multilanguage`, which contains `polymorphic_interoperating_langs` as a
suffix, so the identity prefix compiler is target-valid.

### Per-equation results

Method for every row: standalone `eq_term target_multilanguage (compile_ctx PCMP c)
(compile_sort PCMP t) (compile PCMP e1) (compile PCMP e2)` with
`PCMP = poly_multilang_compiler ++ polymorphic_interoperating_langs_compiler`,
proved with the same `by_reduction_checked` as Stage F (e-graph computation
forced at tactic time), under an Ltac `timeout 240`.

| Equation | Time | Result | Issue / localized culprit |
|---|---|---|---|
| "dtt star" | before: TIMEOUT 240s -- after: 33.9s + Qed 51.0s | **Qed** | fixed by the let-binding change (see Stage F); `boundaries_parameterized` unchanged |
| "ttd star" | before: TIMEOUT 240s -- after: 34.8s + Qed 51.0s | **Qed** | as "dtt star", through the `#".1"` projection |
| "dtt True" | before 32s+48s -- after 34.1s + Qed 52.5s | Qed | |
| "dtt False" | before 32s+48s -- after 35.1s + Qed 51.6s | Qed | |
| "ttd True" | before 32s+48s -- after 34.2s + Qed 52.1s | Qed | |
| "ttd False" | before 32s+48s -- after 34.7s + Qed 51.5s | Qed | |
| "dtt func" | TIMEOUT 240s | ADMITTED | needs the `"typerec func"` rule of `type_casing`; same saturation wall as Stage F (which also failed at 900s) |
| "ttd func" | TIMEOUT 240s | ADMITTED | as "dtt func" |
| "dtt ulambda mismatch" | before 32s+48s -- after 34.5s + Qed 52.2s | Qed | the only mismatch equation at type `#"bool"`, i.e. reachable via `"typerec bool"` |
| "dtt uT mismatch" | TIMEOUT 240s | ADMITTED | at type `#"->" "A" "B"`, so it needs `"typerec func"` |
| "dtt uF mismatch" | TIMEOUT 240s | ADMITTED | as "dtt uT mismatch" |
| "exp_subst dtt" | TIMEOUT 240s | ADMITTED | pushing `#"exp_subst"` through the whole `trec_boundaries_poly` term |
| "exp_subst ttd" | TIMEOUT 240s | ADMITTED | as "exp_subst dtt" |

### UPDATE (this session)

`PolyBoundaries.v` was **not** edited; it was only rebuilt against the changed
`boundaries` (stage C) and `trec_func_case`/`trec_boundaries` (stage E), from
which `boundaries_parameterized`, `boundaries_ty_subst`, `poly_boundaries`,
`trec_boundaries_poly` and the two compiler cases all re-derive.  The 7 `Qed`
equations stayed `Qed`; the 6 `Admitted` ones were not re-attempted here (the
per-equation work was done in stage F, which is the cheaper file to iterate in).
The stage-F findings port verbatim: the `"typerec func"` equations should now
terminate rather than saturate, and the two `#"exp_subst"` equations are
localized to the `#"->"` case of the typerec.

**Summary (updated).**  The poly compiler splits *exactly* as the simple one
does: after the let-binding change the seven equations that reduce through
`"typerec star"`/`"typerec bool"` (including both `star` equations) prove in
~34 s plus ~52 s at `Qed`, and the six that need `"typerec func"` or
`exp_subst` still saturate.  Generalizing the type environment from `#"ty_emp"`
to `"D"` did not change which equations work; it only made the `typerec` term
~1.4x more expensive to elaborate.

## Stage H: TyperecPartialEval.v

The file now compiles against the current stage files.  Changes needed to get
there: `PolyCompilerLangs`/`PolyCompilersCPS` added to the imports (as in stage
G), `Compilers.SemanticsPreservingDef` and `Compilers.CompilerFacts` added,
(Total file build: 3m00s.)  And the local copies of `source_multilanguage_wf` / `target_multilanguage_wf`
(plus their `wf_lang_db` entries) deleted, since stage D now proves them in
`TypeCasing.v`.  The `Derive ... in ... as` syntax was already modern.

| Definition | Method | Time | Result | Issue / localized culprit |
|---|---|---|---|---|
| func_partial_eval_term_wf | Derive + solve_elab_term_or_sort | tactic 28.6s + Qed 18.2s | Qed | |
| no_sort_eqns_in_sml | `apply I` | 0s | Qed | |
| ty_eq_sort_lemma | manual enumeration | 2.3s + Qed 2.4s | Qed | unchanged |
| ty_inversion_lemma' | cut-free induction + **cheap lang inversion** | 0.002s + Qed 0.05s | Qed | **re-proved this session**; was 19.7s + 8.4s |
| ty_inversion_lemma | -- | <1s | Qed | unchanged |
| compiled_types_are_simple | cut-free induction + **cheap lang inversion** | 0.01s + Qed 0.06s | Qed | **re-proved this session**; was 18.6s + 7.9s |
| can_eliminate_typerec | cut-free induction + **cheap lang inversion** + `ats_subst` | 0.05s + Qed 0.1s | **Qed** | **CLOSED this session** (was ADMITTED/OOM). No enumeration at all; peak RSS for the *whole file* is now 941MB. Axiom-free (`Print Assumptions`: closed under the global context). |
| target_multilanguage_wf | -- | -- | moved | now proved in stage D (`TypeCasing.v`) |
| source_multilanguage_wf | -- | -- | moved | now proved in stage D (`TypeCasing.v`) |
| no_sort_eqns_in_tml | `apply I` | 0s | Qed | `no_sort_eqns target_multilanguage` really does compute to `true` |
| ty_env_eq_sort_lemma_tml | manual enumeration | | Qed | unchanged |
| ty_inversion_lemma_tml | cut-free induction + **cheap lang inversion**, generalized to `sort_name t = "ty"` | 0.006s + Qed 0.02s | **Qed** | **CLOSED this session** (was ADMITTED). Statement as corrected in the previous session, unchanged. Axiom-free. |
| interop_preserving_tml | `preserving_compiler_embed` + `compute_incl` | <1s | Qed | new |
| source_multilanguage_compiler_preserving | `CompilerFacts.compiler_append` | <1s | Qed | new; modulo `simple_multilang_compiler_preserving` (stage F) |
| sml_semantics_preserving | `Compilers.inductive_implies_semantic` | <1s | Qed | new; modulo `simple_multilang_compiler_preserving` |
| eq_sort_sml_implies_eq_sort_tml | `proj1 sml_semantics_preserving` | <1s | Qed | modulo `simple_multilang_compiler_preserving` |
| partial_eval_preserves_equality | -- | -- | ADMITTED | unchanged statement; proof retained in a comment. It was already incomplete (`1-2: admit`, the `dtt`/`ttd` cases), and it opens with the *same* `unshelve`/`destruct` enumeration over `source_multilanguage` as `can_eliminate_typerec`, preceded by `vm_compute in H`, so it cannot be run on this box either. |
| target_multilanguage_without_typerec_wf | prove_by_lang_db | | Qed | updated to include `let_eta_parameterized ++ let_ty_subst ++ let_parameterized`, since the compiled `dtt`/`ttd` now contain a `#"let"` node |
| partial_eval_wf_in_no_typerec_lang | -- | -- | ADMITTED (statement fixed) | `all_typerecs_simple e` added as a hypothesis (the old statement is false); proof not attempted -- it now depends on `partial_eval_preserves_equality`, see below |
| compiled_partial_eval_wf | corollary | <1s | Qed | new; the intended use of the previous row, with `all_typerecs_simple` discharged by `can_eliminate_typerec` |

### `eq_sort_sml_implies_eq_sort_tml` (goal 2, done)

It is a corollary of `Compilers.inductive_implies_semantic`, exactly as
`CombinedThm.full_compiler_semantic` uses it.  Two new lemmas were needed to get
the compiler into the `preserving_compiler_ext _ [] cmp src` shape the theorem
wants:

* `interop_preserving_tml` re-targets `interoperating_langs_compiler_preserving`
  (whose target is `polymorphic_interoperating_langs`) at `target_multilanguage`
  with `CompilerFacts.preserving_compiler_embed` + `compute_incl`;
* `source_multilanguage_compiler_preserving` glues it to
  `simple_multilang_compiler_preserving` with `CompilerFacts.compiler_append`
  (side conditions: `incl_refl` twice, `compute_all_fresh`,
  `source_multilanguage_wf`).

`prove_by_cmp_db` does *not* work here (`cmp_wf_in_db` returns a failure rather
than `Is_Success`); the explicit `compiler_append` route does.

Everything in this chain is `Qed` **modulo `simple_multilang_compiler_preserving`,
which is `Admitted` in stage F.**

### `ty_inversion_lemma_tml` (goal 3) -- statement (previous session); **now Qed**

By computation, the term rules of `target_multilanguage` whose result sort is
`#"ty" _` are exactly

```
["prod"; "*"; "bool"; "->"; "All"; "ty_hd"; "ty_subst"]
```

with rules

```
D:ty_env, A:ty D, B:ty D |- prod A B : ty D
D:ty_env |- * : ty D
D:ty_env |- bool : ty D
D:ty_env, t:ty D, t':ty D |- -> t t' : ty D
D:ty_env, A:ty (ty_ext D) |- All A : ty D
D:ty_env |- ty_hd : ty (ty_ext D)
D:ty_env, D':ty_env, g:ty_sub D D', A:ty D' |- ty_subst g A : ty D
```

so the old statement was missing `prod`, `All`, `ty_hd` and `ty_subst` (the last
two are the "type-substitution/variable form"), and its `a`/`b` conjuncts
wrongly mentioned `source_multilanguage`.  The corrected statement in the file
existentially quantifies every type-environment argument: `target_multilanguage`
has no sort equations (`no_sort_eqns_in_tml`), so a conversion step only tells us
the two sorts have the same *name* (`Parameterizer.sort_names_equal`), never that
their arguments agree, and there is no sort-injectivity principle available.
`#"ty_hd"` is kept in the list: it is impossible only at `D = #"ty_emp"`, and the
lemma is stated at an arbitrary `ty_env`.  The wf-ness conjuncts on `a`/`b` were
dropped (a weakening) because they are not needed by any caller --- the lemma has
no callers in this file.

SUPERSEDED: the proof is now **Qed** (see "The cheap language inversion"
below); the recommended shape suggested here -- generalising the induction to
`sort_name t = "ty"` -- is exactly what was done (`ty_inversion_lemma_tml'`).
The original note, for the record: the proof was *not* attempted, for the same
resource reason as `can_eliminate_typerec`: it needs the cut-free `In`-enumeration over
`target_multilanguage`, which is strictly larger than `source_multilanguage`
(whose enumeration already costs 193s / 6.5GB).  There is no soundness obstacle:
`no_sort_eqns target_multilanguage` computes to `true`, so the sort-equality side
case of `wf_term_cut_ind` is closable by `sort_names_equal` exactly as in
`ty_eq_sort_lemma` / `ty_env_eq_sort_lemma_tml`; the recommended shape is to
generalise the induction to `sort_name t = "ty"` rather than `t = {{s #"ty" D}}`,
so that the conversion case is a one-liner.

### The cheap language inversion (this session) -- the Stage H blocker is gone

The dominant cost in this file used to be the cut-free `In`-membership
enumeration (`unshelve (repeat (destruct H; [> first [...] | ..]); destruct H)`)
over a whole language: 193s and ~6.5GB for `source_multilanguage`, which OOMed
the 7GB box.  It has been replaced throughout by a *reflective* inversion, built
from three ingredients (all in `TyperecPartialEval.v`, in the block after
`Ltac invert_wf_args`):

1. `in_lang_lookup : all_fresh l -> In (n,r) l -> named_list_lookup_err l n = Some r`
   (a one-line corollary of `Utils.NamedList.all_fresh_named_list_lookup_err_in`),
   plus `sml_all_fresh` / `tml_all_fresh` by `compute_all_fresh`.  Once `n` is a
   *concrete* name, `vm_compute` on the lookup recovers the rule's context,
   argument list and sort in milliseconds.
2. A boolean `forallb` check over the language, discharged once by
   `vm_compute; reflexivity`, that bounds which names can occur:
   `sml_ty_names` (result sort `#"ty"` implies the name is `"*"`, `"bool"` or
   `"->"`) and `tml_ty_names` (result sort name `"ty"` implies one of the seven
   names listed above).
3. `subst_sort_name_nil` (`t[/s/] = scon n [] -> t = scon n []`), so that the
   substituted result sort of the cut-free rule case can be read back.

So each induction case does a *name* case split over 3 (resp. 7, resp. 2)
candidates instead of a membership enumeration over hundreds of rules.

Measured effect (whole-file build, `make TIMING=1`, nothing else running):

| | before | after |
|---|---|---|
| `TyperecPartialEval.vo` | 3m00s, OOM on `can_eliminate_typerec` at 7GB | **2m21s, peak RSS 941MB** |
| `ty_inversion_lemma'` | 19.7s + Qed 8.4s | 0.002s + Qed |
| `compiled_types_are_simple` | 18.6s + Qed 7.9s | 0.01s + Qed |
| `can_eliminate_typerec` | 193s then Killed (>7GB) | 0.05s + Qed |
| `ty_inversion_lemma_tml` | not attempted | 0.006s + Qed |

Almost all of the remaining 2m21s is the two unchanged manual enumerations
`ty_eq_sort_lemma` (2.3s+2.6s) and `ty_env_eq_sort_lemma_tml` (17.0s+19.9s) --
which are over *sort* rules and were never the blocker -- plus
`func_partial_eval_term_wf` (32.1s + Qed 19.9s) and the `prove_by_lang_db` Qeds.

### `all_typerecs_simple` restated (this session)

`all_typerecs_simple` selected its `#"typerec"` case with a nested *pattern
match* on the head name, so `all_typerecs_simple (con n s)` was irreducible when
`n` was a variable -- exactly the situation the cheap inversion leaves you in.
It is now

```
Definition typerec_mu_ok (n : string) (s : list term) : Prop :=
  if eqb n "typerec"
  then match s with [_;_;_;_;mu;_;_] => is_simple_type mu | _ => True end
  else True.

Fixpoint all_typerecs_simple (program : term) : Prop :=
  match program with
  | var _ => True
  | con n s => typerec_mu_ok n s /\ all all_typerecs_simple s
  end.
```

which is *stronger* than the old one (it recurses into every argument of a
`#"typerec"` node, not just `e1`,`e2`,`e3`) and, crucially, reduces under a
`eqb n "typerec" = false` hypothesis.  `is_simple_type` is unchanged.

### How `can_eliminate_typerec` is proved now

Two supporting reflective notions, `typerecs_are_var e` (every `#"typerec"`
node's type argument is a *variable*) and `typerec_mu_vars e` (the list of those
variables), and one substitution lemma

```
Lemma ats_subst (b : term) (s : subst)
  : Is_true (typerecs_are_var b) ->
    all (fun p => all_typerecs_simple (snd p)) s ->
    all (fun m => is_simple_type (term_subst_lookup s m)) (typerec_mu_vars b) ->
    all_typerecs_simple b[/s/].
```

Then one `vm_compute`d fact about the *compiler*,

```
Lemma cmp_cases_ok : forallb cmp_case_ok
  (simple_multilang_compiler ++ interoperating_langs_compiler) = true.
```

where `cmp_case_ok (n, term_case _ b)` says `typerecs_are_var b` and, unless
`n` is `"dtt"` or `"ttd"`, `typerec_mu_vars b = []`.  In the induction, the
generic case therefore instantiates `ats_subst` with an empty
`typerec_mu_vars`, and the two boundary cases instantiate it with `["A"]`,
whose image is `compile CMP A` with `A` the source type argument -- simple by
`compiled_types_are_simple`.  Nothing needs to look at the shape of the other
compiler bodies, and no language is ever enumerated.

### `partial_eval_preserves_equality` (goal 4) -- still ADMITTED, but no longer for memory reasons

The memory wall is gone: the proof skeleton can now be *run*.  What blocks it is
no longer resources but missing infrastructure, and the shape of the generic
(non-`dtt`/`ttd`) case has changed as a result of the cheap inversion: because
the rule name stays a *variable*, the old per-rule tactic
`setup_eq_goal ...; solve_eq_goal` (which `vm_compute`s the compiler case for a
concrete name) no longer applies.  The generic case has to be done uniformly
instead, which needs three lemmas that do not exist yet:

1. `elim_typerec (b[/s/]) = b[/named_map elim_typerec s/]` whenever `b` contains
   no `#"typerec"` (provable by `term_ind_all`, as `ats_subst` is);
2. `named_map elim_typerec (combine_r_padded args l) =
    combine_r_padded args (map elim_typerec l)` (needs
    `elim_typerec default = default`);
3. a substitution congruence `wf_term l c' b t -> eq_subst l [] c' s1 s2 ->
   eq_term l [] t[/s2/] b[/s1/] b[/s2/]` applied to the compiler case body `b`,
   whose well-typedness comes from `source_multilanguage_compiler_preserving`
   (itself modulo the Stage F `simple_multilang_compiler_preserving` admit).

The two boundary cases are unchanged from the previous session's plan: by
`ty_inversion_lemma` the scrutinee type is `#"*"`, `#"bool"` or an arrow, and
the arrow case is `eredex_steps_with type_casing "typerec func"` followed by the
identity `func_partial_eval_term[...]` plus the inner induction on the simple
type.  Guided steps only -- whole-goal `by_reduction` saturates (Stage F).

Left `Admitted. (* ISSUE: see STATUS.md *)`, proof skeleton retained in a
comment.

### `partial_eval_wf_in_no_typerec_lang` (goal 5) -- statement fixed, still ADMITTED

The statement now carries the missing hypothesis:

```
forall t e, Core.wf_term target_multilanguage [] e t ->
            all_typerecs_simple e ->
            Core.wf_term target_multilanguage_without_typerec [] (elim_typerec e) t.
```

(the old statement is false: `meta_typerec` falls through to `| _ => mu` at a
non-simple type, so `elim_typerec` leaves such a `#"typerec"` in place).  The
corollary `compiled_partial_eval_wf`, which is the form the theorem is meant to
be used in, is **Qed**: it discharges `all_typerecs_simple` with
`can_eliminate_typerec`.

The theorem itself was not attempted, for a *structural* reason rather than a
resource one.  Running the cut-free induction on
`Core.wf_term target_multilanguage [] e t`, the non-`typerec` constructor case
must re-apply the same rule in the smaller language at the sort
`t[/with_names_from c' (map elim_typerec s)/]`, whereas the goal's sort is
`t[/with_names_from c' s/]`.  Those two sorts are only *equal up to
`eq_sort`*, and the bridge between them is precisely
`partial_eval_preserves_equality` (goal 4) applied to each argument.  So goal 5
is downstream of goal 4 and should be attempted after it; the transfer of rules
from `target_multilanguage` to `target_multilanguage_without_typerec` is the
easy part (a `vm_compute`d `incl` check of the same reflective kind used above,
i.e. `forallb (fun p => inb p target_multilanguage_without_typerec) ...`).
The residual risk flagged in the previous session -- that `eq_sort` in the
bigger language cannot be transferred to the sublanguage -- is still open; the
fallback is to weaken the conclusion to well-typedness in `target_multilanguage`
itself.
