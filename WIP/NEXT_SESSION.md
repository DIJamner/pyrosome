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
- **Ph2 PARTIAL** — `LogRel2Ind.v` (`LR_mut`) + `LogRel2Lemmas.v` (escape +
  base-PER typing/sym/trans) + **`LogRel2Irr.v` IRRELEVANCE DONE** (axiom-free):
  `LR_irrelevant_gen` (same-type-pair derivations carry equivalent relations,
  all 6 cases incl. Pi), top-level `LR2_irrelevant` + `RedTmEq_irr` (Def 7),
  `TLlt_pirr`. REMAINING Ph2: transport + renaming stability.
- **Ph0 DE-RISKED** — prototype `WIP/Phase0Proto.v`. Mechanical refactor.
- **Ph4 PER SYMMETRY: UNIVERSE-BLOCKED** (do NOT retry the unified carrier).
  `WIP/LogRel2Sym.v` GAP 2': the symmetry carrier `{ Q & LR B A Q * maps }`
  needs `Q <= LRPack.u0` (Pi-domain pack storage) AND `Q >= RedRel.u2` (LRU
  witness), but `LRPack.u0 < RedRel.u2` is intrinsic to the `LR` inductive's
  sizing. Fix = level-indexed universes, OR reformulate symmetry to USE
  `RedTmEq_irr` instead of carrying a swapped `LR` derivation.

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

### B. Finish the green Ph2 PER laws first (no `Domain.v` change)
Top-level `RedTyEq`/`RedTmEq` symmetry + transitivity + irrelevance + transport,
over the **Pi** case. Standard logrel plumbing: build a swapped/related
`PolyRedPack` inside an `LR_mut` induction (motive `M Ge A B P H := LR ... Ge B A
(flip P)` for symmetry). ~150 lines. Stays green; validates `LR_mut`.

## Build (per CLAUDE.md — never run full `make` during dev)
```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome \
     src/Pyrosome/Lang/OTT/Norm/Pi/<File>.v
```
(The Rocq MCP works on project files via `rocq_start(file=...)`; it does NOT pick
up loadpaths for a brand-new unbuilt file, so compile new files with `coqc`
first.) Always `git push` after each green commit.
