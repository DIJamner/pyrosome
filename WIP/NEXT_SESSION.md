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

## Next move: RENAMING STABILITY presheaf (the tractable remaining PER item)

Transitivity + transport are deferred (blocked on general Apply totality ≈
normalization — see `ConvRelPlan.md` STATUS). The tractable remaining Ph2/Ph4
work is **stability under renaming** (the LR2 presheaf over renamings), which
lives over RENAMINGS, where `ren_Apply_total` supplies the very Apply witness
transitivity lacked.

**Algebra foundation: DONE & green** — `src/Pyrosome/Lang/OTT/Norm/Pi/RenSubst.v`
(commits `64959f1`, `899a57b`, `8b8bd94`), ported from the retired single-sided
`LogRelRen.v` with the `(F,B)` neutral annotations threaded through every
`nApp`/`nAppI`/`Vapp` case (recipe in `WIP/OTT_LogRel_single_sided/README.md`):
- `is_ren` helpers (`_nil/_tl/_cons/_id/_wkn/_up`, `ren_nth_var`);
- `ren_Apply_total` — Apply_* is TOTAL + neutrality-preserving under a renaming
  (the totality witness general subs lack);
- `ne_below_shift` / `ne_below_mono` / `sub_below`(`_up`/`_beta`) /
  `Apply_ne_below` (Apply-preserves-scope, with the F,B-scoped Vapp motive);
- `Apply_ren_comp` + `Apply_ren_comp_sc` (scoped) — renaming-then-arbitrary
  composition (apply `s1` then `s2` = apply composite `s3`).

**Remaining = the presheaf proof itself.** Write `LR_ren_gen` (new file, e.g.
`Norm/Pi/LogRel2Ren.v`, `Set Universe Polymorphism`) mirroring `LR_sym_gen`'s
shape: a `RenCar` carrier + `RecRen1` tower hypothesis, by `LR_mut`. A renaming
`sg` (`is_ren`, `wf_ssub Ge' sg Ge`) sends `LR Ge A B P` to
`LR Ge' A[sg] B[sg] Q` with `P` transported pointwise (use `ren_Apply_total`
for the renamed `A[sg]`/`B[sg]` witnesses). The Pi case is the boss: build the
renamed `PolyRedPack Ge' FA' BA' FB' BB'`; its `shpRed`/`posRed` at `(Delta,
sg2)` reduce to the original pack at `(Delta, sg2∘sg)` via `Apply_ren_comp(_sc)`
+ `Apply_val_det`. ON-DEMAND ports still in WIP if the proof needs them:
`Apply_ren_decomp` (converse of comp), `ren_is_Apply`, `Apply_ren_eq`
(renamed-image uniqueness vs the syntactic `ren_*`) — port with the same `(F,B)`
recipe. Then top-level `RedTyEq_ren` / `RedTmEq_ren`.

Keep the whole `LogRel2*` chain `Set Universe Polymorphism` so the poly tower
instances align (as `LogRel2Sym.v` needs).

After renaming stability: Ph3 genuine `∼ne` (the Ph0 annotation prerequisite is
now satisfied), then Ph5 fundamental lemma (whence transitivity/transport come
for free / become provable).

## Build (per CLAUDE.md — never run full `make` during dev)
```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome \
     src/Pyrosome/Lang/OTT/Norm/Pi/<File>.v
```
(The Rocq MCP works on project files via `rocq_start(file=...)`; it does NOT pick
up loadpaths for a brand-new unbuilt file, so compile new files with `coqc`
first.) Always `git push` after each green commit.
