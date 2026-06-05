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
- `ren_Apply_total` — Apply_* is TOTAL + neutrality-preserving under a renaming;
- `ne_below_shift` / `ne_below_mono` / `sub_below`(`_up`/`_beta`) /
  `Apply_ne_below` (Apply-preserves-scope);
- `Apply_ren_comp` + `Apply_ren_comp_sc` (scoped) — renaming-then-arbitrary comp.

**Functional renaming layer + `Reflect_ren`: DONE & green (Phase 2c, this
commit)** — appended to `RenSubst.v`, axiom-free. Ported the syntactic
renaming `renm`/`up_renl`/`ren_sub`/`ren_val`/`ren_ne`/`ren_ty` + `ren_is_Apply`
/ `Apply_ren_eq` (bridge to the relational world), the `RenShSc` conjugation
(`ren_ok`/`_up`/`_le`, `RenShSc_up`/`_beta`/`_wkn`), **`Apply_ren_commute`**
(Apply commutes with renaming — the engine that existentially produces a beta
step's substituted codomain), the shift/rename commutes `ren_shift_comm0_val/ne`
+ **NEW `ren_shift_comm1_val`** (cutoff-1: `ren_sub (up_renl rho)` is itself an
`up`, so the cutoff-1 `ShiftSub` chains from `ShiftSub_0_up` via `ShiftSub_up`
— no `ins_renl` needed), and **`Reflect_scoped` / `Reflect_ren`** (the refl_Pi
spine now carries `(F,B)`, discharged by comm0/comm1).

**Universe-typed renaming preservation: DONE & green (Phase 2d, this commit)** —
`src/Pyrosome/Lang/OTT/Norm/Pi/RenTyping.v`, axiom-free: `ren_ctx` (renaming as
a context map), `ren_ctx_up_dEl`, `ren_typing_dU` (has_svalty/wf_neutral
preservation RESTRICTED to `T = dU r l`), `wf_svalty_ren`. Covers the type-side
LR side-conditions: `LRpi`/`LRpiI` (`wf_svalty (dEl (vPi ..))`), `LRU`
(`has_svalty c (dU r l)`), `LRne` (`NeConv (dU r l) ..`).

**BLOCKER CLEARED + ren_typing DONE & GREEN (2026-06-05, commits `9fc1bdd`,
`26299f5`, `08f3028`; all axiom-free, whole `LogRel2*` chain re-greened).**
- Added `has_svalty Ge F (dU rF lF)` to `t_lam`, `t_lam_eta`, AND `t_lamI`
  (`t_lamI` too: `LRpiI` carries `has_svalty` at `dEl (vPiI ..)`, so the presheaf
  renames `vLamI` terms). Ripple was exactly as predicted (Preservation builders
  + ApplySubst/RenTyping induction binders).
- `RenTyping.typing_ne_below` (full `well_typed ⇒ ne_below`, all types): VALUES
  get only `ne_below_val` (type-side never consumed → `t_lam_eta` trivial, NO
  `Reflect_scoped`/B/ARG needed); NEUTRALS get both sides (`n_app`/`n_appI`
  recover the (F,B) annotation scopedness from the function type `dEl (vPi F B)`,
  result `dEl B'` via `Apply_val_ne_below`). New `ne_below_ctx` precondition +
  extender `ne_below_ctx_up_dEl`. Projections `has_svalty_ne_below` /
  `wf_neutral_ne_below`.
- `RenTyping.ren_typing` (full renaming preservation, all types; generalizes
  `ren_typing_dU`). Signature: `has_svalty/wf_neutral Ge v T → ne_below_ty
  (length Ge) T → ne_below_ctx Ge → ren_ctx rho Ge Ge' → ren_ok rho
  (S (length Ge)) (length Ge') → has_svalty/wf_neutral Ge' (ren_val/ren_ne rho v)
  (ren_ty rho T)`. The `ren_ok` is at `S (length Ge)` (one above source) to feed
  `Reflect_ren`/`Apply_val_ren_commute`. `t_lam_eta` renames Reflect via
  `Reflect_ren` + codomain via `Apply_val_ren_commute`/`ren_shift_comm1_val`;
  `n_app`/`n_appI` rename codomain via `Apply_val_ren_commute` + `RenShSc_beta`.
  GOTCHA that cost time: `ren_ok_le`'s SOURCE bound `N` is an existential that
  `apply` leaves unresolved — pin it with `apply ren_ok_le with (N := ...)`.

## Next move: BASE-PER RENAMING then the LR_ren_gen presheaf

1. **Base-PER renaming lemmas** (new, in `LogRel2Ren.v` or `LogRel2Lemmas.v`):
   `NeConv_ren` (almost immediate: `NeConv Ge T n m = wf_neutral n * wf_neutral m
   * (n=m)`; rename both `wf_neutral` via `ren_typing` snd, and `ren_ne` respects
   `=`), `RedNatEq_ren` (induct on `RedNatEq`; `rne_ne` uses `NeConv_ren` at
   `dEl vNat`), `RedNeutralEq_ren` (`rneT` uses `NeConv_ren`). These consume the
   `ne_below_ty`/`ne_below_ctx`/`ren_ctx`/`ren_ok` package now available.
2. **The presheaf `LR_ren_gen`** (new file `Norm/Pi/LogRel2Ren.v`, `Set Universe
   Polymorphism`) mirroring `LR_sym_gen`'s shape: a `RenCar` carrier + `RecRen1`
   tower hypothesis, by `LR_mut`. A renaming (bundle `ren_ctx rho Ge Ge'` +
   `ren_ok rho (S (length Ge)) (length Ge')` + the source well-scopedness it
   needs) sends `LR Ge A B P` to `LR Ge' A[rho] B[rho] Q`. Key insight (CLEANER
   than symmetry): the Pi pack does NOT need the domain/codomain IHs — its
   `shpRed`/`posRed` at `(Delta, sg2)` REUSE the ORIGINAL pack at
   `(Delta, sg2∘sg)` via a constructed composite `sg3` (`Apply_val_ren_comp_sc`
   + `Apply_val_det`); adequacy comes from the original `ad`. Base cases use
   `ren_typing_dU`/`wf_svalty_ren` (types) + the base-PER renaming lemmas (1).
   Then top-level `RedTyEq_ren` / `RedTmEq_ren`. DESIGN NOTE: the presheaf must
   supply each renamed component's scopedness preconditions from the LR pack's
   stored `wf_svalty`/typing (via `typing_ne_below`/the dU `typing_scoped`).

After renaming stability: Ph3 genuine `∼ne`, then Ph5 fundamental lemma (whence
transitivity/transport become provable).

## Build (per CLAUDE.md — never run full `make` during dev)
```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome \
     src/Pyrosome/Lang/OTT/Norm/Pi/<File>.v
```
(The Rocq MCP works on project files via `rocq_start(file=...)`; it does NOT pick
up loadpaths for a brand-new unbuilt file, so compile new files with `coqc`
first.) Always `git push` after each green commit.
