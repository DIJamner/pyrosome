# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Pyrosome is a Coq/Rocq formalization of programming-language metatheory: term/rule/language syntax, judgmental equality, compilers between languages, an elaboration judgment, and an e-graph (egglog-style) automation engine. Tested with Rocq 9.0; later versions may work.

## Build

This is a Coq project driven by `coq_makefile`. There is no separate test suite — proofs are the tests.

**During development, only build the file you are working on.** A full build takes an hour or more, so do not run `make` or `make -jN` to check your work. Build the single `.vo` for the file you edited (and let `make` resolve its `.v` dependencies):

```bash
make -f Makefile.coq src/Pyrosome/Theory/Core.vo   # build just this file (and its deps)
```

The full-build / setup commands below exist for completeness but should not be invoked during routine edits:

```bash
make clone_all        # one-time: fetch git submodules (coqutil, canonical-binary-tries)
make -jN              # full build; N >= 4 strongly recommended (hour+ on first build) — avoid during dev
make clean            # remove .vo, generated Makefile.coq, _CoqProject
make clean_all        # also clean submodules
```

`make` regenerates `_CoqProject` and `Makefile.coq` on each invocation from `SRC_VS` (every `.v` under `src/`). If `Makefile.coq` is missing, run `make Makefile.coq` once to produce it, then use the single-file form above. Submodules `coqutil/` and `canonical-binary-tries/` build via their own makefiles before the main project.

`shell.nix` provides a default Coq shell. With `--arg native-enabled true` it switches to opam (some files use `native_compute`, which is unreliable on the nix-packaged Coq).

## Source layout

`_CoqProject` defines four logical names:

- `Utils` → `src/Utils/` — generic library (lists, maps, monads, decidability, union-find, e-graph).
- `Pyrosome` → `src/Pyrosome/` — project-specific code.
- `coqutil` → submodule.
- `Tries` → submodule (canonical binary tries).

`WIP/` is **not** in `_CoqProject` and is not built. Treat it as a scratch area; do not rely on its files compiling.

## Architecture

The metatheory is layered, and most layers are parameterized so the same definitions can be reused at different levels of the stack.

### Theory (`src/Pyrosome/Theory/`)

- `Substable.v` — `Substable0`/`Substable` typeclasses abstracting "thing you can substitute into."
- `Model.v` — `PreModel` (just substitution structure) and `Model` (adds `eq_sort`/`eq_term`/`wf_sort`/`wf_term` as fields). Compilers and many lemmas are stated against an arbitrary `Model` rather than syntax.
- `Term.v`, `Rule.v` — concrete syntax of terms, sorts, rules (`sort_rule`/`term_rule`/`sort_eq_rule`/`term_eq_rule`), and languages (`lang := named_list rule`).
- `Core.v` — the central mutually-recursive judgments `eq_sort`, `eq_term`, `wf_sort`, `wf_term`, defined inductively and packaged via `core_model l : Model`. This file is large (~2k lines); it also sets up `basic_core_crush` / `basic_core_firstorder_crush`, the standard automation tactics for the project.
- `Renaming.v`, `ConvElim.v`, `CutElim.v`, `CutFreeInd.v`, `WfCutElim.v`, `ClosedTerm.v`, `ClosedCore.v`, `ModelImpls.v` — admissibility / structural / cut-elimination results.

When working at this layer: most files are inside `Section WithVar. Context (V : Type) ...` so the variable type is abstract. Concrete instantiations (e.g. `string`, `int`/`int63`) live in the consumers.

### Compilers (`src/Pyrosome/Compilers/`)

- `CompilerDefs.v` — `compiler_case = term_case args e | sort_case args t`; compilers target an arbitrary `PreModel`, not necessarily syntax.
- `Compilers.v` — the central inductive-implies-semantic theorem.
- `SemanticsPreservingDef.v`, `OperationalBridge.v`, `CompilerFacts.v`, `CompilerTransitivity.v`, `Parameterizer.v`, `PartialEval.v` — supporting and derived results.

### Elaboration (`src/Pyrosome/Elab/`)

`Elab.v` and `ElabCompilers.v` define elaboration judgments that fill in implicit arguments for terms/rules/compilers; `PreTerm.v`/`PreRule.v` are the surface syntax with implicits.

### Lang (`src/Pyrosome/Lang/`)

Concrete language definitions and the case-study compiler stack: `SimpleVSubst`, `SimpleVSTLC`, `SimpleVCPS`, `SimpleEvalCtx[CPS]`, `SimpleVCC`, `SimpleVFix[CC|CPS]`, `NatHeap`/`SimpleV*Heap`, plus polymorphic versions. The two top-level theorems are:

- `CombinedThm.v` — combined correctness for the simply-typed compiler.
- `PolyCompilers.v` — the polymorphic extension and final theorem.

`PolySubst.v` and `Subst.v` generate substitution calculi; `SubstEqnGen.v` generates equation rules.

### Proof (`src/Pyrosome/Proof/`)

`TreeProofs.v` and `DAGProofs.v` give proof-term representations used by automation and the e-graph machinery.

### Tools (`src/Pyrosome/Tools/`)

User-facing tactics and automation:

- `Matches.v` — most of the Pyrosome tactics for working with the judgments. Specialized to `int63` keys.
- `ComputeWf.v`, `Linter.v`, `Resolution.v`, `Latex.v`, `AllConstructors.v`, `ConstructorsOf.v`, `CompilerTools.v`.
- `Int63Renaming.v` / `PosRenaming.v` — rename languages from `string`-keyed to `int63`/positive-keyed for fast computation.
- `EGraph/` — Pyrosome-side e-graph integration: `Defs.v`, `Theorems.v`, `Automation.v` (egraph-driven tactics), `TypeInference.v`, `ComputeWf.v` (egraph-based wf checker), `Test.v`.

### Utils/EGraph (`src/Utils/EGraph/`)

The actual e-graph implementation, independent of Pyrosome:

- `Defs.v` — datatypes: `db_entry`, `db_map` (per-symbol n-ary table of epoch-stamped entries), `atom`, union-find, analysis typeclass.
- `Semantics.v` — model-theoretic interpretation of the e-graph (~5800 lines). Key predicates: `atom_in_egraph`, `atom_in_egraph_up_to_equiv`, `atom_sound_for_model`, `state_sound_for_model`. The `state_triple` Hoare-style abstraction is used for sequencing soundness lemmas about stateful operations (`db_set_entry`, `repair_*`, `rebuild`, etc.).
- `QueryOpt.v` — query planning / optimization.

This is where the active proof work tracked in recent commits (`repair_sound`, `rebuild_sound`, `state_sound_for_model`) lives.

## Conventions worth knowing

- `Section WithVar. Context (V : Type) {V_Eqb : Eqb V} ...` is the dominant idiom; concrete `V` is chosen by callers (`string` for source-level languages, `int63`/`positive` for fast variants).
- Custom tactics layered by module:
  - `basic_utils_crush` (Utils) → `basic_term_crush` (Theory/Term) → `basic_core_crush` (Theory/Core), each adding hint databases (`utils`, `term`, `lang_core`, `model`, `inversion`, `bool`, `rw_prop`).
  - `basic_goal_prep` is the standard "intros + simpl-ish" preamble.
- Inversion lemmas (`invert_eq_X_Y`) are generated for every constructor pair and added to the `term` rewrite db; use them via `autorewrite` or the `*_crush` tactics rather than manual `inversion`.
- The project uses `Set Implicit Arguments` pervasively. When stating a lemma referencing `term`, `sort`, `rule`, etc., follow the pattern `Notation term := (@term V).` from neighbouring code.
