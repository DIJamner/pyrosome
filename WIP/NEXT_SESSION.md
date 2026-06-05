# Next-session kickoff — OTT two-sided PER migration

Paste this as the opening prompt (or just read it) to resume the OTT/Norm/Pi
migration to a two-sided PER-of-conversion logical relation (Divide and Check).

---

**Resume the OTT/Norm/Pi migration to the two-sided PER-of-conversion logical
relation.** Goal: decidable conversion for OTT. Branch `gluing-nbe`. Read
`WIP/ConvRelPlan.md` (design + live STATUS) and the `[[ott-convrel-pivot]]`
memory first.

## State (all committed + pushed on `gluing-nbe`, all axiom-free)

- **Ph1 DONE** — `src/Pyrosome/Lang/OTT/Norm/Pi/LogRel2.v`: the two-sided PER core
  (`LRPack.redTmEq`, two-sided `PolyRedPack`/`PiRedTmEq`/`PolyRedPackAdequate`,
  two-sided `LR` graph + finite tower + `RedTyEq`/`RedTmEq`/`RedSubEq`). Kernel
  accepts `LR` (positivity holds). `NeConv` neutral base is PROVISIONAL (strict
  diagonal) — becomes the genuine `∼ne` in Ph3.
- **UNIVERSE REFACTOR DONE** — `LogRel2.v` now uses the universe-poly **3-level
  UNFOLDED tower** (lower relations as separate params `rec0`/`rec1`, `LRU` split
  into `LRU0`/`LRU1`, no value-level `match`; ladder `i0<i,i1<i,i<j,j0<=i,j1<=i`,
  NO `i0=i1`). Whole `LogRel2*` chain is `Set Universe Polymorphism` +
  `Unset Strict Universe Declaration`. Validated first in `WIP/UnivProto.v`.
- **Ph2 IRRELEVANCE DONE** — `LogRel2Irr.v` (axiom-free): `LR_irrelevant_gen`
  (bidirectional `IrrCar` over `LR_mut`, 7 cases incl. Pi + `LRU0`/`LRU1`),
  `LR2_irrelevant` + `RedTmEq_irr` (Def 7). REMAINING Ph2: transport + renaming
  stability.
- **Ph4 PER SYMMETRY DONE & axiom-free** — `src/.../LogRel2Sym.v` (NO LONGER
  blocked). `LR_sym_gen` builds the swapped `PolyRedPack` (`sym_pack`/`sym_adeq`
  — the `LRPack`-field storage the old encoding forbade) and discharges the Pi
  `bwd` via `LR_irrelevant_gen` + `Apply_val_det`; tower `LRbot/LR0/LR1_sym`
  (`RecSym1`); top-level `RedTyEq_sym` + `RedTmEq_sym`.
- **Ph0 NEUTRAL ANNOTATIONS DONE & green** — `(F,B)` on `nApp`/`nAppI`, whole
  domain layer + `LogRel2*` re-greened (commits `a24ad6d`, `3c68002`). Single-
  sided `LogRel*` chain retired to `WIP/OTT_LogRel_single_sided/` (commit
  `220ce2a`; out of the build, kept as reference for renaming/subst algebra).
- **TRANSITIVITY BLOCKED (finding)** — needs general Apply totality (≈
  normalization); see `ConvRelPlan.md` STATUS. Defer to post-fundamental (Ph5).

## State update (2026-06-05): RENAMING STABILITY COMPLETE

`LogRel2Ren.v` is fully built, axiom-free, green.  The renaming-stability
presheaf for the two-sided LR is DONE: top-level `RedTyEq_ren` / `RedTmEq_ren`
(`LR2 Ge A B P` ↦ `LR2 Ge' A[rho] B[rho]` + forward value map), via
`LR_ren_gen` (by `LR_mut`), the renamed Pi pack `ren_pack`/`ren_adeq`/
`ren_pack_fwd` (reuse `PA0` at the composite `comp_sub sg2 rho`), the
composite-sub algebra, and the REVERSE composition `Apply_ren_uncomp_sc`.
See `ConvRelPlan.md` STATUS for the full structure and the two key findings
(forward-only carrier; reverse-comp needs no Apply-totality, distinguishing
renaming from transitivity).

## State update (2026-06-05): Ph3 FOUNDATION DONE

`LogRel2Conv.v` is built, axiom-free, green: the genuine structural
neutral/normal-form conversion `conv_nf`/`conv_ne` (paper Def 13 `∼annot`)
replacing the provisional strict-diagonal `NeConv`.  Annotations related
recursively (not required equal); untyped+structural is complete here because
`Reflect` bakes eta into normal forms; independent of `LR` (positivity-safe).
Proven `conv_refl`/`conv_sym`/`conv_trans` + diagonal embeddings
`conv_ne_of_eq`/`conv_nf_of_eq` + scheme `conv_mutind`.

## State update (2026-06-05): Ph3 SWAP COMPLETE

The genuine `conv_ne` is now wired into `LR` across all 7 `LogRel2*` files,
axiom-free and green; the provisional strict-diagonal `NeConv` is GONE.  The
base neutral relation is now **TWO-TYPED** (`NeConv Ge T S n m` /
`RedNeutralEq Ge T S`) — forced by a typing-conversion wall (`has_svalty` has no
conversion rule, so `RedTmEq_wf`'s `LRne` case couldn't type the right member at
`dEl(vNe m)` from a left-typed relation).  Added `conv_ren` (renaming stability
of conv).  See `ConvRelPlan.md` STATUS "Ph3 SWAP — DONE" for the per-file
landing notes and the verified axiom-free list.

## Next move — Ph3 PROPER: mutual reify / reflect (Theorem 11)

Connect `conv_ne` (LogRel2Conv.v) to REDUCIBLE conversion `RedTmEq` (LogRel2.v):
- **Reflect:** `conv_ne n m` at a reducible type ⟹ `RedTmEq Ge T S (vNe n) (vNe m)`.
- **Reify:** `RedTmEq Ge A B a b` ⟹ `conv_nf a b` (+ deep-normalize).
Mutual because reifying a function applies it to a reflected variable.  Reuse
the existing `Reflect`/`Reify` infrastructure + the deep-normalization
machinery; induct over `LR` via `LR_mut`.  This is the old `reflect_red` blocker,
now approachable because the relation is two-sided + the neutral conversion is
genuine.  Transport (Lemma 12) + transitivity stay deferred to post-fundamental
(Ph5).  Then the fundamental lemma (Ph5) → connect to gluing `Model.v`/`ModelOk.v`
⇒ `eq_term` decidability.

## Build (per CLAUDE.md — never run full `make` during dev)
```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome \
     src/Pyrosome/Lang/OTT/Norm/Pi/<File>.v
```
(The Rocq MCP works on project files via `rocq_start(file=...)`; it does NOT pick
up loadpaths for a brand-new unbuilt file, so compile new files with `coqc`
first.) Always `git push` after each green commit.
