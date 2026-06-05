# OTT/Norm/Pi → two-sided PER-of-conversion LR (Divide and Check)

Goal: **decidable conversion** for OTT. Pivot the logical relation from the
single-sided membership predicate (`redTm : sval -> Type`) to a two-sided PER of
reducible conversion, following Poiret–Maillard–Tabareau, *Divide and Check*
(2026, hal-05495420). OTT's "conversion" is the gluing/NbE model
(`Norm/Model.v`); the two-sided relation is what makes COMPLETENESS (hence
decidability) provable — a single-sided predicate gives only normalization.

## Reuse vs rebuild

- **Reuse (domain layer, formulation-independent):** `Norm/Pi/Domain`,
  `Apply`/`ApplyLemmas`/`ApplySubst`, `Determinism`, `Preservation`, `Reflect`,
  `EvalRel`; `Norm/SortInj.v` (no-confusion); `Norm/Model.v`+`ModelOk.v` (gluing
  target). Most session 1–6 renaming algebra survives (`Apply_ren_commute`,
  `Reflect_ren`, `ren_*`, `ne_below`, scoping, `Determinism`).
- **Rebuild:** `Norm/Pi/LogRel*.v` — the relation + `reflect_red` become a
  two-sided PER + a mutual `reify`/`reflect`.

## New core definitions (Pi fragment), adapting paper Def 9/10

```coq
(* type-conversion pack: the PER of reducible TERM-conversion at A ≡ B *)
Record LRPack (Ge : senv) (A B : svalty) : Type :=
  { redTmEq : sval -> sval -> Type }.
(* "reducible membership" of v = reflexive point redTmEq v v *)

(* Π case: A = vPi FA BA, B = vPi FB BB.  Kripke-quantified over renamings
   carrying wf_senv Delta (fixes session-6 obstruction (c)). *)
Record PolyRedPack (Ge : senv) (FA BA FB BB : sval) : Type :=
  { shpRed : forall Delta sg FA' FB',
      wf_senv Delta -> wf_ssub Delta sg Ge -> is_ren sg ->
      Apply_val (length Delta) sg FA FA' ->
      Apply_val (length Delta) sg FB FB' ->
      LRPack Delta (dEl FA') (dEl FB')                         (* domain conv pack *)
  ; posRed : forall Delta sg a b FA' FB'
      (wfD : wf_senv Delta) (ws : wf_ssub Delta sg Ge) (rn : is_ren sg)
      (afA : Apply_val (length Delta) sg FA FA')
      (afB : Apply_val (length Delta) sg FB FB'),
      redTmEq (shpRed wfD ws rn afA afB) a b ->                (* a ≡ b at domain *)
      { BresA & { BresB &
        ( Apply_val (length Delta) (a :: sg) BA BresA
        * Apply_val (length Delta) (b :: sg) BB BresB
        * LRPack Delta (dEl BresA) (dEl BresB) )%type } } }.   (* codomain pack at (a,b) *)

(* term-conversion at Π: f ≡ g.  No neutral case (η is baked in for negative
   types — dissolves the bare-neutral-vs-eta mismatch). *)
Definition PiRedTmEq Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
  : sval -> sval -> Type :=
  fun f g =>
    ( has_svalty Ge f (dEl (vPi FA BA)) * has_svalty Ge g (dEl (vPi FB BB))
    * (forall Delta sg a b FA' FB' fsg gsg
         (wfD : wf_senv Delta) (ws : wf_ssub Delta sg Ge) (rn : is_ren sg)
         (afA : Apply_val (length Delta) sg FA FA')
         (afB : Apply_val (length Delta) sg FB FB')
         (afsf : Apply_val (length Delta) sg f fsg)
         (afsg : Apply_val (length Delta) sg g gsg),
         redTmEq (shpRed PA wfD ws rn afA afB) a b ->
         { v & { w &
           ( Vapp (length Delta) fsg a v * Vapp (length Delta) gsg b w
           * redTmEq (posPack PA .. a b ..) v w )%type } } ) )%type.
```

`LR lvl rec` becomes a two-sided graph indexed by `(A B : svalty)` and a relation
`sval -> sval -> Type`; keep the finite tower (tl0<tl1<tl2) for IR-avoidance, or
move to small IR. Top-level `RedTyEq Ge A B` / `RedTmEq Ge A B a b`.

## Irrelevance + Transport (PER axioms — Def 7, finally first-class)

- **Irrelevance:** `redTmEq` independent of the chosen `RedTyEq` witness.
- **Right transport (Lemma 12):** `RedTyEq Ge A B` and `RedTyEq Ge A C` ⇒
  `redTmEq` at A≡B equiv `redTmEq` at A≡C. The general tool that all the
  session-6 bespoke transports collapse into.
- **`∼annot` (Def 13) + Change-of-annotations (Lemma 14):** relate terms differing
  only by convertible annotations — handles the reify-vs-a discrepancy.
- Stability under renaming (presheaf over renamings).

## Mutual reify / reflect (Theorem 11) — the old blocker, now early

`RedTyEq Ge A B` implies: Reify-type (A,B deeply-normalize, equal whnf shape);
Reify (related terms are conv + deep-normalize); Reflect (∼ne-related neutrals are
reducibly conv). Mutual because reifying a function applies it to a reflected var.
Needs the deep-normalization predicate + a neutral-conversion relation `∼ne` on
domain neutrals (annotations make argument types inferable).

## Prerequisite: annotate domain neutrals (greenlit)

`nApp (f:neutral)(a:sval)` → `nApp (f:neutral)(F B:sval)(a:sval)` (domain F,
codomain B); same for `nAppI`. Ripple: Apply/shift/ren/Determinism/Preservation/
Reflect/Typing/EvalRel. Mechanical.

## STATUS (updated 2026-06-05)

- **Ph1 DONE & VALIDATED.** `Norm/Pi/LogRel2.v` — the two-sided PER core
  (LRPack `redTmEq`, two-sided `PolyRedPack`/`PiRedTmEq`/`PolyRedPackAdequate`,
  two-sided `LR` graph + finite tower + `RedTyEq`/`RedTmEq`/`RedSubEq`). Kernel
  ACCEPTS the `LR` inductive — **positivity holds** (the riskiest design point),
  same discipline as `LogRel.v` (LR only positive via adequacy + `rec`; the
  `is_ren` gate stays on `PiRedTmEq`'s app clause). `LR2` is axiom-free.
  `NeConv` neutral base is PROVISIONAL (strict diagonal) pending Ph0 + Ph3.
- **Ph2 PARTIAL & green.** `Norm/Pi/LogRel2Ind.v` — `LR_mut`, the custom nested
  induction principle (IHs for shpAd/posAd). `Norm/Pi/LogRel2Lemmas.v` — base-PER
  typing (`RedNatEq_wf`/`RedNeutralEq_wf`), ESCAPE (`RedTyEq_wf`, `RedTmEq_wf`),
  base-case PER laws (`NeConv`/`RedNatEq`/`RedNeutralEq` sym+trans).
  **IRRELEVANCE DONE** — `Norm/Pi/LogRel2Irr.v` (axiom-free, green):
  `LR_irrelevant_gen` (two `LR` derivations of the SAME type pair carry
  EQUIVALENT relations; bidirectional `IrrCar` motive over `LR_mut`, all 6
  cases incl. Pi); top-level corollaries `LR2_irrelevant` and `RedTmEq_irr`
  (paper Def 7: membership independent of the `RedTyEq` witness — the form
  symmetry's `bwd`/transport consume).  Also `TLlt_pirr` (axiom-free proof
  irrelevance for the level order, convoy pattern, for the `LRU` case).  Pi
  case: bidirectional domain/codomain IHs + `Apply_val_det` to align codomain
  types; the type transport is done in the GOAL of the aligned derivation
  (rewriting a hypothesis is blocked by `posPack`'s dependency on `posTyA`).
  REMAINING Ph2: transport + renaming stability.
- **UNIVERSE REFACTOR DONE (2026-06-05).** `LogRel2.v` ported to the universe-poly
  **3-level UNFOLDED tower** (`UNIVERSE_FIX_PLAN.md` Step 1B, validated first in
  `WIP/UnivProto.v`): lower relations as separate params `rec0`/`rec1` (no
  dispatching `rec` function / no value-level `match`), `LRU` split into
  `LRU0`/`LRU1`; `Set Universe Polymorphism` + `Unset Strict Universe Declaration`
  across the whole `LogRel2*` chain.  Recorded ladder `i0<i, i1<i, i<j, j0<=i,
  j1<=i`, **no `i0=i1` collapse**.  Chain re-greened, all axiom-free.
- **Ph4 PER SYMMETRY: DONE & axiom-free — universe block CLEARED.**
  `Norm/Pi/LogRel2Sym.v`.  The former block (swapped carrier `Q` needing both
  `<= LRPack.u0` and `>= RedRel.u2`) is gone: `Q` now lives at the motive's
  relation universe `i`, big enough for the `LRU0`/`LRU1` witnesses and small
  enough to store into an `LRPack` field (the `sym_pack` storage that was
  impossible).  `LR_sym_gen` (generic) builds the swapped `PolyRedPack`
  (`sym_pack`/`sym_adeq`) and discharges the Pi `bwd` via IRRELEVANCE
  (`LR_irrelevant_gen` + `Apply_val_det`); tower `LRbot_sym`/`LR0_sym`/`LR1_sym`
  (`RecSym1`); top-level `RedTyEq_sym` + `RedTmEq_sym`.  (Supersedes the earlier
  "fundamentally universe-blocked" finding; full swapped-derivation symmetry now
  goes through, so the deferred reformulation-via-`RedTmEq_irr` plan is moot.)
- **Ph0 NEUTRAL ANNOTATIONS: DONE & green (2026-06-05).** `nApp`/`nAppI` carry
  `(F B : sval)`; the whole domain layer + `LogRel2*` chain is re-greened against
  it (commits `a24ad6d`, `3c68002`).  Domain-layer leaves repaired (`Smoke`,
  `Determinism`, `ApplySubst`, `Glue`).  `ApplySubst.typing_scoped` was re-scoped
  to UNIVERSE types `dU r l` only — see its header comment (general `dEl`
  scopedness now needs context validity, which `t_lam` doesn't record; every
  consumer only scopes type-codes, which inhabit `dU`).  The superseded
  single-sided `LogRel*` chain was retired to `WIP/OTT_LogRel_single_sided/`
  (out of the build; kept as a reference for the renaming/subst algebra).
- **TRANSITIVITY: BLOCKED on general Apply totality (finding 2026-06-05).**
  Attempted `LR_trans_gen` mirroring `LR_sym_gen`.  Base cases are ready
  (`RedNatEq_trans`/`RedNeutralEq_trans`/`NeConv_trans` already in
  `LogRel2Lemmas.v`; `LRU0`/`LRU1` via a `RecTrans1` hyp like `RecSym1`).  The
  Pi case is the blocker: composing `PA : PolyRedPack Ge FA BA FB BB` with
  `PA' : PolyRedPack Ge FB BB FC BC` into `PolyRedPack Ge FA BA FC BC`, the
  composed `shpRed''` is invoked with `Apply_val sg FA FA'` and
  `Apply_val sg FC FC'` over a GENERAL `wf_ssub sg`, but to call `shpRed PA`/
  `shpRed PA'` it must synthesize the MIDDLE `Apply_val sg FB FB'`.  Applying a
  general well-typed substitution to the middle Pi domain is normalization-
  strength (a `vNe (nApp ...)` head can beta-reduce under `sg`), and NO general
  Apply-totality lemma exists (only `ren_Apply_total`, renamings, in WIP).  So
  type-level transitivity via pointwise pack composition is circular with
  normalization and should NOT be an early Ph4 law — defer it to AFTER the
  fundamental/normalization results (Ph5), or rederive it from them.  Symmetry
  avoids this because `sym_pack`'s `shpRed` receives BOTH apply witnesses from
  its caller (it only swaps them).
- **RENAMING STABILITY — algebra + typing prereqs DONE & green (2026-06-05).**
  `RenSubst.v` now also carries the functional renaming layer
  (`renm`/`up_renl`/`ren_sub`/`ren_val`/`ren_ne`/`ren_ty`, `ren_is_Apply`,
  `Apply_ren_eq`), `RenShSc` + `Apply_ren_commute` (Apply commutes with a
  renaming), the shift/rename commutes (`ren_shift_comm0_val/ne` + NEW
  `ren_shift_comm1_val`), and **`Reflect_scoped`/`Reflect_ren`** (Phase 2c).
  `RenTyping.v` adds `ren_ctx` + **`ren_typing_dU`/`wf_svalty_ren`** — typing
  preservation under a renaming for the UNIVERSE-typed fragment (`T = dU r l`),
  covering `LRpi`/`LRpiI`/`LRU`/`LRne`'s type-side side-conditions (Phase 2d).
  All axiom-free.
- **TYPING-RULE GAP — FIXED & GREEN (2026-06-05, commits `9fc1bdd`, `26299f5`).**
  Added `has_svalty Ge F (dU rF lF)` to `t_lam`, `t_lam_eta`, AND `t_lamI`
  (`t_lamI` too: `LRpiI` carries `has_svalty` at `dEl (vPiI ..)`, so the presheaf
  renames `vLamI` terms).  Full `well_typed ⇒ ne_below` = `RenTyping.typing_ne_below`
  (axiom-free).  Motive asymmetry: VALUES get only `ne_below_val` (their type-side
  is never consumed by an IH; dropping it makes `t_lam_eta` trivial — NO
  `Reflect_scoped`/B/ARG needed, cleaner than planned); NEUTRALS get both sides
  (`n_app`/`n_appI` recover the (F,B) annotation scopedness from the function type
  `dEl (vPi F B)`, result `dEl B'` via `Apply_val_ne_below`).  New `ne_below_ctx`
  precondition + extender `ne_below_ctx_up_dEl` (uses the F premise).  Projections
  `has_svalty_ne_below`/`wf_neutral_ne_below`.  Whole `LogRel2*` chain re-greened
  (insulated; no `t_lam` construction outside Preservation).
- **FULL `ren_typing` DONE & GREEN (2026-06-05, commit `08f3028`, axiom-free).**
  `RenTyping.ren_typing` generalizes `ren_typing_dU` to ALL types.  Mutual
  `has_svalty`/`wf_neutral` preservation under `ren_ctx` + `ren_ok rho
  (S (length Ge)) (length Ge')`, with `ne_below_ty T` + `ne_below_ctx Ge`
  preconditions; `t_lam_eta` via `Reflect_ren`+`Apply_val_ren_commute`
  (`ren_shift_comm1_val`), `n_app`/`n_appI` via `Apply_val_ren_commute`+
  `RenShSc_beta`.  (Gotcha: pin `ren_ok_le`'s source bound with `with (N:=..)`.)
- **REMAINING Ph2/Ph4:** base-PER renaming (`NeConv_ren` ⇒ `RedNatEq_ren`/
  `RedNeutralEq_ren`, now trivially built on `ren_typing`) + the `LR_ren_gen`
  presheaf itself (the Pi pack REUSES the original pack at the composite
  `sg2∘sg` — no domain/codomain IHs needed, cleaner than symmetry) + transport
  (Lemma 12, deferred) + transitivity (deferred).  Then Ph3 genuine ∼ne.

- **Ph0 RE-SCOPED then DE-RISKED.** Annotating `nApp`/`nAppI` is NOT a mechanical
  local change: `vapp_ne` constructs `nApp` with no type to draw annotations from,
  so `(F,B)` must be threaded as INDICES through `Vapp`/`VappI`/`Apply_ne` (e.g.
  `Vapp m F B vf a v`, `vapp_ne : Vapp m F B (vNe n) a (vNe (nApp n F B a))`,
  `ap_app` substitutes F at `s` and B at `up s` and feeds the substituted (F',B')
  to `Vapp`). It breaks the ENTIRE proven domain layer (Apply/Determinism/
  Preservation/Reflect/Typing/EvalRel) AND transitively LogRel2 — no intermediate
  green build until all are repaired. Critical-path for Ph3 (genuine `∼ne`).
  **DE-RISKING DONE:**
  1. The one feared GENUINE proof obligation — the `refl_Pi` codomain
     reconciliation (`Apply (ARG :: wkn_list m) B = Apply (ARG :: id_list (S m))
     (shift_val 1 1 B)`) — **is ALREADY PROVEN** in `ApplySubst.v` as
     `Apply_reflect_cod` (the c=1 instance of the existing `Apply_cancel`
     insert/weakening lemma, via `InsAt_1_wkn_id`). Nothing new to prove there.
  2. The remaining design risk — does threading `(F,B)` through `Vapp` break
     `Apply` determinism or the annotated `Reflect_det`? — was validated in a
     self-contained throwaway prototype `WIP/Phase0Proto.v`: both
     `Apply_deterministic` and `Reflect_det` go through UNCHANGED in shape (the
     `(F,B)` indices are output-determined, never obstructing inversion/IH
     plumbing). Both axiom-free.
  CONCLUSION: Ph0 is now a purely MECHANICAL arity-ripple refactor (8 domain
  files; `ApplySubst.v` + `Preservation.v` shift-commutation are the bulk) that
  REUSES `Apply_reflect_cod`, plus the delete-vs-keep decision on the superseded
  single-sided `LogRel*` chain. Insulated (recompile only, no source edit):
  `SortInj.v`, `Model.v`, `ModelOk.v`, `Reify.v`. Typing's `n_app` already binds
  `(F,B)`; `EvalRel.ev_app` already has `vF vB` in scope.

## Order

1. **Ph1** new two-sided PER core (new additive file; verify POSITIVITY first — riskiest).  [DONE]
2. **Ph0** annotate neutrals.
3. **Ph2** irrelevance [DONE] + transport + renaming stability.
4. **Ph3** mutual reify/reflect.
5. **Ph4** PER laws — SYMMETRY [DONE, `LogRel2Sym.v`], trans pending; + rule-by-rule model + contextualization (= validity/RedCtx).
6. **Ph5** fundamental lemma → deep-norm (Prop6) / no-confusion (Prop4, via SortInj) /
   neutral-conv (Prop5); connect to gluing `Model.v`/`ModelOk.v` ⇒ eq_term decidability.
7. **Ph6** extend Pi fragment → full OTT (Cast/Id/ProofIrr/Sigma) as extra reduction
   rules + relation cases. (vPiI/vLamI = paper's negative/irrelevant types.)
