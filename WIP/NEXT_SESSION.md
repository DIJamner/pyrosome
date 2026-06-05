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
  (`RecSym1`); top-level `RedTyEq_sym` + `RedTmEq_sym`. REMAINING Ph4:
  transitivity.
- **Ph0 DE-RISKED** — prototype `WIP/Phase0Proto.v`. Mechanical refactor.

## Pick one of two next moves

### A. Execute the mechanical Ph0 ripple (critical path → Ph3)
Annotate `nApp`/`nAppI` in `Domain.v` with `(F B : sval)` and thread the Pi type
`(F,B)` as indices through `Vapp`/`VappI`/`Apply_ne`. Design is validated by
`WIP/Phase0Proto.v` (annotated `nApp f F B a`; `Vapp m F B vf a v`;
`vapp_ne : Vapp m F B (vNe n) a (vNe (nApp n F B a))`; `ap_app` substitutes F at
`s`, B at `up s`, feeds substituted `(F',B')` to `Vapp`). Key facts:
- The one hard proof is ALREADY DONE: `Apply_reflect_cod` in `ApplySubst.v`
  (the `refl_Pi` codomain reconciliation). REUSE it.
- `Apply_deterministic` + `Reflect_det` keep their proof shape (prototype proves
  this); only `Vapp`/`VappI` pattern underscore-arity changes.
- Edit order (dependency-respecting, build each `.vo` green before the next):
  `Domain.v` (ctor + `shift_ne`, B at `S c`) → `Apply.v` (ap_app/ap_appI,
  Vapp/VappI indices, `Apply_mutind` P3/P4 motives, `Apply_deterministic`
  underscores) → `Reflect.v` (annotated `refl_Pi` stamps `shift_val 0 1 F` /
  `shift_val 1 1 B`; `Reflect_det`) → `Typing.v` (`ne_below_ne`; `n_app`/`n_appI`
  promote existential F,B to stored — nearly free) → `Preservation.v` (shift
  commutation + Vapp/VappI shift-preservation — BULK) → `ApplyLemmas.v` (2 cases)
  → `ApplySubst.v` (4 cases — BULK) → `EvalRel.v` (`ev_app`/`ev_appI` thread the
  in-scope `vF vB`).
- INSULATED, recompile only (no source edit): `SortInj.v`, `Model.v`,
  `ModelOk.v`, `Reify.v`.
- DECISION: the single-sided `LogRel*` chain (`LogRel`, `LogRelInd`,
  `LogRelLemmas`, `LogRelRed`, `LogRelSubst`, `LogRelRen`, `LogRelFund`, `Smoke`)
  is superseded by LogRel2 → delete it rather than repair (else it breaks under
  the `Domain.v` change). Confirm with the user before deleting.
- NOTE: this breaks LogRel2 + the whole domain layer until the ripple is
  complete — no intermediate green build. Don't commit until the chain is green.

### B. Finish the remaining green Ph2/Ph4 PER laws (no `Domain.v` change)
Irrelevance + symmetry are DONE. Remaining: **transitivity** (`RedTyEq`/`RedTmEq`
trans, Pi case — mirror `LogRel2Sym.v`'s `LR_sym_gen`/`RecSym1` tower pattern but
with a `RecTrans`-style hypothesis, discharge the Pi codomain via irrelevance) +
**transport** (Lemma 12, from `RedTmEq_irr`) + **renaming stability** (presheaf
over renamings, reuse the session 1–6 `Apply_ren_commute`/`ren_*` algebra). Keep
the whole `LogRel2*` chain `Set Universe Polymorphism` so the poly tower instances
align (as `LogRel2Sym.v` needs).

## Build (per CLAUDE.md — never run full `make` during dev)
```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome \
     src/Pyrosome/Lang/OTT/Norm/Pi/<File>.v
```
(The Rocq MCP works on project files via `rocq_start(file=...)`; it does NOT pick
up loadpaths for a brand-new unbuilt file, so compile new files with `coqc`
first.) Always `git push` after each green commit.
