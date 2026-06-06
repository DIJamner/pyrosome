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

## STATUS

- **GATE LANDED (2026-06-06d): `is_lam` member gate added to `PiRedTmEq`; whole
  `LogRel2*` chain + `Glue` re-greened, axiom-free.**  Per Dustin's call (option
  (B), paper-faithful NbE), `PiRedTmEq` now requires both members to be lambdas
  (`is_lam v := { b & v = vLam b }`, the paper's `PiRedTm.isfun`).  This REMOVES
  the falsity below: bare neutrals at a Pi are no longer direct members (they
  enter via `refl_Pi`, which outputs `vLam`).  Edits: `LogRel2.v` (def + new
  `is_lam`); `LogRel2Lemmas`/`LogRel2Reflect` `RedTmEq_wf{,_gen}` LRpi destruct
  `[[[..] _] _]`; `LogRel2Sym` fwd/bwd swap typings AND gates; `LogRel2Ren`
  `ren_pack_fwd` rebuilds the gate (`ren_val rho (vLam b) = vLam (ren_val (up_renl
  rho) b)`); `LogRel2Reflect` `RR_pi_case` REFLECT supplies the two gates
  (`eexists; reflexivity`).  `LogRel2Irr` unchanged (members preserved).
  Verified `Closed under the global context`: `RR_gen`, `LR_sym_gen`,
  `LR_ren_gen` (+ build clean for the rest).
  CONSEQUENCE for the residuals: (R2) is now a TRUE, provable statement (no longer
  a dead end), BUT still NOT a one-liner -- with both members `vLam ba`/`vLam bb`,
  `conv_nf` reduces via `cnf_lam` to `conv_nf ba bb`, and the lambda body is NOT
  recovered by `Vapp` at the fresh var (the beta sub `a::id_list` contracts the
  binder -- `entry (i+1) = vNe(nVar i)`, a non-invertible renaming -- so the app
  clause gives `conv_nf (ba⟨contract⟩) (bb⟨contract⟩)`, not `conv_nf ba bb`).
  So (R1)+(R2)+(R3) all still need the genuine VR/reify-adequacy layer; the gate's
  contribution is making them ACHIEVABLE rather than (R2) being false. NEXT =
  build the VR layer (reducible substitutions + reify adequacy) and discharge the
  three residuals; then prove (R2) inside `RR_pi_case` and drop the `Hreify_tm`
  Context.

- **BLOCKER FOUND & MACHINE-VERIFIED (2026-06-06d) [RESOLVED by the gate above]:
  residual (R2) was FALSE as stated -- structural reify-tm at Pi is INCOMPATIBLE
  with the UNGATED `PiRedTmEq`.**  (R2) is `RRCar`'s reify-tm clause specialised
  to the relevant
  Pi: `forall a b, PiRedTmEq PA a b -> conv_nf a b`.  It cannot hold, and neither
  can the eventual user-facing completeness theorem
  `reify_tm : LR2 Ge A A P -> P a b -> conv_nf a b`.

  REASON.  `PiRedTmEq` (LogRel2.v) gates members only by `has_svalty _ (dEl(vPi
  ..))` + the application clause; it has NO "member is a function / reduces to a
  `vLam`" gate (the paper's `PiRedTm.{nf,red,isfun}` field).  So a BARE NEUTRAL
  at a Pi type (e.g. a variable `vNe (nVar 0)` typed at `dEl(vPi vNat vNat)` by
  `t_ne`/`n_var`) is a member, ALONGSIDE its eta-expansion `vLam (vNe (nApp
  (nVar 1) vNat vNat (vNe (nVar 0))))` (typed by `t_lam`/`t_lam_eta`).  These two
  are eta-equal -- the whole POINT of `PiRedTmEq` is to relate them ("eta baked
  in at negative types") -- yet `conv_nf (vLam _) (vNe _)` has NO constructor.

  COQ-VERIFIED (all in dev against `LogRel2Reflect.v`'s context, axiom-free):
  1. `forall x y, conv_nf (vLam x) (vNe y) -> False`  (by `inversion`).
  2. `forall Ge, nth_error Ge 0 = Some (dEl(vPi vNat vNat)) ->
      has_svalty Ge (vNe (nVar 0)) (dEl(vPi vNat vNat))`  (`t_ne`+`n_var`).
  3. eta-relatedness CORE: at `m=1`, BOTH
       `Vapp 1 vNat vNat (vNe (nVar 0)) vZero v`  and
       `Vapp 1 vNat vNat (vLam (vNe (nApp (nVar 1) vNat vNat (vNe (nVar 0))))) vZero v`
     hold with the SAME `v = vNe (nApp (nVar 0) vNat vNat vZero)` (`vapp_ne` /
     `vapp_lam`+`ap_app`+`ap_var`).  i.e. the lambda and the bare neutral apply to
     the same argument to the same result -- they ARE reducibly related.

  CONSEQUENCE.  `RR_pi_case`'s `- (* REIFY-tm *) exact Hreify_tm` line cannot be
  honoured, so `RR_pi_res` (which assumes `Hreify_tm` = R2) is unprovable, so the
  `RR_pi_at_from_res` reduction is a dead end on the reify-tm component.  (R1)
  `conv_nf BA BB` and (R3) `RR_app2` are reflect-side and unaffected by THIS
  argument, but reify-tm must be fixed first since it is part of the same motive.

  FIX OPTIONS (architectural -- DECISION FOR DUSTIN):
  - **(B) gate `PiRedTmEq` members to functions** (paper-faithful NbE; RECOMMENDED).
    Add an `isFun`/`{ bf & f = vLam bf }` (or "reduces to `vLam`") field to
    `PiRedTmEq`.  Then members are `vLam`, reify-tm is structural via `cnf_lam` +
    the codomain reify IH (`posIH`).  Bare neutrals at Pi enter the LR ONLY via
    REFLECTION (`refl_Pi` already outputs `vLam`), so the eta-short form is never a
    direct member -- it is represented by its eta-long reflection, exactly NbE.
    Cost: thread the new field through `LogRel2{Irr,Sym,Ren,Lemmas,Red,Ind}` and
    escape; `refl_Pi` supplies it for free.  Positivity unaffected (positive Σ).
  - **(A) add eta to `conv_nf`** (declarative-style; the paper's *spec* conv has
    eta).  Reverses the stated design goal ("conv stays structural, eta baked into
    NFs") and complicates `conv_trans`/decidability.  NOT recommended.

- **RR_pi_at REDUCED to 3 reify/reflect residuals, axiom-free + green
  (2026-06-06c).**  `LogRel2Reflect.v` now proves the relevant-Pi crux
  `RR_pi_at` MODULO three explicit residuals (two-sided port of the single-sided
  `reflect_pi_step_from_reify` methodology).  The eta-expansion construction,
  both `t_lam_eta` typings, the domain reify-ty, and the Pi-code reify-ty are all
  DISCHARGED; only the genuine VR-layer core remains abstract.  New (all
  axiom-free, verified `Closed under the global context`):
  1. `RedTmEq_wf_gen` -- level-generic escape: a `P`-member at ANY
     `@LR lvl rec0 rec1` node is well-typed at both indices (needed because the
     abstract-level packs in `RR_pi_at` are NOT `LR2`, so `RedTmEq_wf` fails).
  2. `conv_ctx` + `conv_ctx_refl`/`_length`/`_map_shift`/`_nth` +
     `typing_ctx_conv` -- CONTEXT CONVERSION: `has_svalty`/`wf_neutral` are
     stable under replacing context entries by `conv_nf`-related ones (var case
     via `n_conv`; binder cases extend with the identical shifted domain).  This
     bridges the two-sided gap: the RIGHT eta-body `body_m` is reflected in the
     LEFT-domain context `dEl (shift FA) :: ..` but `t_lam_eta` for the RIGHT Pi
     types it in `dEl (shift FB) :: ..` (differ only at the convertible front
     domain `conv_nf FA FB`).
  3. `eta_bodies` -- the two-sided eta-expansion.  From `NeConv` at the LEFT Pi:
     `pi_bound_var_reflects` gives `ARGn`/`ARGm` + the domain member `rab`;
     `posIH`'s REFLECT on the two eta-body neutrals (LEFT typed by `n_app`, RIGHT
     typed at `posTyB` then `n_conv`'d to `posTyA` via the codomain reify-ty)
     yields `body_n`/`body_m`; `refl_Pi` assembles both `vLam`s; `t_lam_eta`
     (RIGHT via `typing_ctx_conv`) types them.  Outputs the two `Reflect`s, two
     typings, the codomain member, and the eta-body `Reflect`s.
  4. `dom_reify_ty` -- `conv_nf FA FB` from `domIH` at the identity substitution.
  5. `RR_pi_case` + `RR_pi_res` + `RR_pi_at_from_res` -- `RR_pi_at lvl rec0 rec1`
     follows from `RR_pi_res lvl rec0 rec1`, i.e. supplying at every Pi node:
       (R1) `conv_nf BA BB`  (codomain reify-ty for RAW codes -- shared by REFLECT
            + REIFY-ty; the eta substitution is NOT a renaming for higher-order
            domains, so this is genuine adequacy, not transport);
       (R2) `forall a b, PiRedTmEq PA a b -> conv_nf a b`  (function reify-tm);
       (R3) `RR_app2`  (the eta-expansion application clause; two-sided analog of
            single-sided `reflect_pi_app_step` -- the beta-reduct / RedSub-closure
            adequacy never closed even single-sided).
  RESIDUAL (the live NEXT): discharge (R1)+(R2)+(R3) = the VR/validity layer
  (reducible substitutions + reducibility-eta-irrelevance), mutually entangled
  with `reflect_red` for higher-order domains (see `WIP/ReifyDev.v`).  Closing
  them fully discharges `RR_pi_at` and unblocks the `RR1`/`RR2` tower (the
  monomorphic-`Hpi` universe wall lifts once `RR_pi_at` is a poly LEMMA).

- **TYPING-CONVERSION WALL DISSOLVED -- paper-faithful single-typed migration
  DONE, axiom-free, green (2026-06-06).**  Per Dustin's call ("be faithful to the
  paper"), adopted the paper's SINGLE-TYPED neutral architecture + typed
  conversion (`WfTmConv`), not the two-typed `n_conv`-only patch.  Landed:
  1. **`n_conv` on `wf_neutral`** (`Typing.v`): `wf_neutral Ge n (dEl A) ->
     conv_nf A B -> wf_neutral Ge n (dEl B)` -- the value-world `WfTmConv`/paper
     `ConvNeChChk`.  Sound (in the gluing model `dEl A ≡ dEl B` denote the same
     type).  `Typing.v` now imports `LogRel2Conv` for `conv_nf`.
  2. **Domain-layer re-greened** (4 files): the `has_neutral_mutind` `n_conv`
     case is `discriminate` for the `dU`-only lemmas (`typing_scoped`,
     `ren_typing_dU`), and uses three new conv-stability helpers otherwise --
     `conv_shift` (LogRel2Conv), `conv_ne_below` (Typing), `conv_ren`
     (RenTyping; the LogRel2Ren duplicate removed).
  3. **`NeConv`/`RedNeutralEq` now SINGLE-typed** (`LogRel2.v`): `NeConv Ge T n m`
     (both at one type `T`); `RedNeutralEq Ge T` carries the LEFT type only;
     `LRne`'s relation is `RedNeutralEq Ge (dEl (vNe n))` (paper's `RelAtNe Γ A`).
  4. **Escape + symmetry re-greened** (`LogRel2Lemmas`/`Sym`/`Ren`/`Red`/`Ind`):
     `RedTmEq_wf`'s `LRne` right member is re-typed at the node's RIGHT type via
     `n_conv` + the `LRne` premise `conv_ne n m` (the `WfTmConv`-bridge);
     `LR_sym_gen`'s `LRne` likewise re-types both members across the swapped
     codes.  (`LogRel2Irr` needed no change.)
  5. **`RRCar` REFLECT is now SINGLE-typed at the LEFT type** (`LogRel2Reflect.v`):
     premise `NeConv Ge A n m` (was the two-typed `NeConv Ge A B n m`); all 5
     non-Pi cases discharged axiom-free unchanged in spirit.
  6. **CRUX SET-UP, wall demonstrated GONE: `pi_bound_var_reflects`**
     (`LogRel2Reflect.v`, axiom-free).  The exact step the two-typed encoding
     could NOT perform -- reflecting the eta bound variable `nVar 0` into the
     domain pack -- now goes through: the premise is `NeConv Delta (dEl FA')
     (nVar 0) (nVar 0)` (LEFT typing only, by `n_var`), yet the domain IH returns
     BOTH eta reflections (`ARGn` at `dEl FA'`, `ARGm` at `dEl FB'`) + the domain
     MEMBER -- exactly what feeds `posRed`/`posAd` in the eta-expansion.
  RESIDUAL (unchanged, the genuine Theorem-11 core, STILL `RR_pi_at` abstract):
  assemble `vLam ARGn`/`vLam ARGm` (`refl_Pi`/`t_lam_eta`) and discharge
  `PiRedTmEq`'s application clause = the reflect/reify adequacy core the
  single-sided dev reduced to and never closed (Ph5).  The WALL that blocked even
  reaching it is gone.  Whole `LogRel2*` chain + `Glue` re-greened; verified
  axiom-free: `RR_gen`, `pi_bound_var_reflects`, `RedTmEq_wf`, `LR_sym_gen`,
  `LR_ren_gen`, `conv_ne_below`, `reflect_U`.

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
- **RENAMING STABILITY — COMPLETE, axiom-free, green (2026-06-05).**
  `LogRel2Ren.v` now holds the full presheaf + top-level `RedTyEq_ren` /
  `RedTmEq_ren` (`{P & LR2 Ge A B P}` ↦ `{Q & LR2 Ge' A[rho] B[rho] Q}` with a
  forward value map).  Structure:
  - base-PER renaming `NeConv_ren`/`RedNatEq_ren`/`RedNeutralEq_ren` (trivially
    on `ren_typing`);
  - **`Apply_ren_uncomp_sc`** — the REVERSE renaming composition (composite-side
    `Apply` ⇒ renamed-side), by `Apply_mutind` on the EXISTING composite
    derivation.  **This was the gap in the plan's "(comp_sc + det)" note:**
    `shpRed'` needs the forward `Apply_val_ren_comp_sc` but the codomain
    `posRed'` needs this reverse direction.  Crucially it needs NO Apply
    totality (the derivation is given, only replayed) — exactly what
    distinguishes renaming from transitivity (which must MANUFACTURE a middle
    witness ≈ normalization);
  - `comp_sub`/`comp_sub_RenSubSc`/`comp_sub_cons_RenSubSc`/`wf_ssub_comp`/
    `is_ren_comp_sub` — the `sg2`-after-`rho` composite-substitution algebra;
  - `ren_pack`/`ren_adeq`/`ren_pack_fwd` — the renamed Pi pack: REUSE `PA0` at
    the composite (no IHs).  **Cleaner than symmetry: the carrier `RenCar` is
    FORWARD-ONLY** (no backward map) and the forward map needs NO irrelevance/
    `Apply_val_det` — `shpRed'`/`posRed'` are STANDALONE named constants sharing
    the `rp_*` witnesses, so `rab` and the codomain relation match
    DEFINITIONALLY.  (Gotcha: a record self-projection `shpRed ?PA` under
    `refine {| |}` stays an unsolved evar that won't reduce — hence the
    standalone constants + explicit `Build_*`.)
  - `LR_ren_gen` by `LR_mut` (LRU0/LRU1 via `RecRen1` on the lower tower), tower
    `LRbot_ren`/`LR0_ren`/`LR1_ren`.
- **REMAINING Ph2/Ph4:** transport (Lemma 12, deferred) + transitivity
  (deferred — both need normalization).  Then **Ph3 genuine ∼ne** (the next
  live item, gated on Ph0 neutral annotations, which are DONE).

- **Ph3 FOUNDATION DONE & green (2026-06-05).** `LogRel2Conv.v` — the genuine
  structural neutral/normal-form conversion, replacing the provisional
  strict-diagonal `NeConv` (`n=m`).  Mutual `conv_nf : sval->sval->Type` /
  `conv_ne : neutral->neutral->Type` (paper Def 13 `∼annot`): UNTYPED, purely
  STRUCTURAL, with type ANNOTATIONS (`F`,`B` on `nApp`/`nAppI`; motive `A` on
  `nEmptyrec`) related RECURSIVELY rather than required equal.  Sound+complete
  here because `Reflect` bakes eta into normal forms (relevant functions are
  always `vLam`, neutrals only at base types), so structural comparison loses
  nothing; INDEPENDENT of `LR` (positivity-safe to reference from the base
  cases).  Proven: `conv_refl` (+ diagonal embeddings `conv_ne_of_eq` /
  `conv_nf_of_eq`), `conv_sym`, `conv_trans` — all axiom-free.  Mutual scheme
  `conv_mutind`.

- **Ph3 SWAP — DONE, axiom-free, green (2026-06-05).**  The genuine `conv_ne`
  is now wired into `LR` across all 7 files (`LogRel2{,Ind,Lemmas,Red,Irr,Sym,
  Ren}.v`); the provisional strict-diagonal `NeConv` is GONE.  Key finding that
  shaped it (a typing-conversion wall): `has_svalty` has NO conversion rule, so
  once `n ∼ne m` with `n≠m`, a member typed at `dEl(vNe n)` is NOT typed at
  `dEl(vNe m)`, and `RedTmEq_wf`'s `LRne` case (right member at the right type)
  would be UNPROVABLE from a single-left-typed `RedNeutralEq`.  Resolution —
  the neutral base relation became **TWO-TYPED**:
  ```coq
  (* in LogRel2.v; import LogRel2Conv *)
  Definition NeConv (Ge : senv) (T S : svalty) (n m : neutral) : Type :=
    (wf_neutral Ge n T * wf_neutral Ge m S * conv_ne n m)%type.
  Inductive RedNeutralEq (Ge : senv) (T S : svalty) : sval -> sval -> Type :=
  | rneT : forall n m, NeConv Ge T S n m -> RedNeutralEq Ge T S (vNe n) (vNe m).
  (* rne_ne : NeConv Ge (dEl vNat)(dEl vNat) n m ;  LRempty uses (dEl vEmpty)(dEl vEmpty);
     LRne   : NeConv Ge (dU r l)(dU r l) n m -> ... RedNeutralEq Ge (dEl(vNe n))(dEl(vNe m)) *)
  ```
  How each file landed:
  1. `LogRel2.v` — imports `LogRel2Conv`; two-typed `NeConv`/`RedNeutralEq`;
     `rne_ne`/`LRempty`/`LRne` carry both types.  (LRne's codes typed diagonally
     at `dU r l`; only the RELATION's outer pair is `(vNe n,vNe m)`.)
  2. `LogRel2Lemmas.v` — `RedTmEq_wf` LRne goes through with NO `subst` (the
     wall is gone: `RedNeutralEq_wf` gives `a:dEl(vNe n) * b:dEl(vNe m)`).
     `NeConv_sym : NeConv Ge T S n m -> NeConv Ge S T m n`, `NeConv_trans`
     `..T S.. -> ..S R.. -> ..T R..` via `conv_ne_sym`/`_trans`;
     `RedNeutralEq_sym`/`_trans` swap/chain the indices likewise.
  3. `LogRel2Sym.v` LRne — drops `destruct..enm; subst`; builds the swapped
     `LRne`/`RedNeutralEq` via `conv_ne_sym` + `RedNeutralEq_sym`.
  4. `LogRel2Ren.v` — new `conv_ren` (conv_ne/conv_nf stable under `ren_ne`/
     `ren_val`, by `conv_mutind`; app/pi recurse cod annotation under
     `up_renl rho`); two-typed `NeConv_ren`/`RedNeutralEq_ren` (param named `T2`
     to avoid shadowing `Nat.S` in `ren_ok rho (S (length Ge)) ..`); LRne/LRempty
     presheaf cases carry both types.
  5. `LogRel2Irr.v` — LRne `IrrCar` unchanged (identity maps via inversion; Irr
     never destructures `NeConv`).
  6. `LogRel2Red.v` (`redTyEq_neEl`/`redTmEq_empty`/`redTmEq_neEl`/
     `RedTmEq_empty_inv`) + `LogRel2Ind.v` (`mne` motive) — bumped type args.
  Verified axiom-free: `conv_trans`, `RedTmEq_wf`, `LR_sym_gen`, `conv_ren`,
  `LR_ren_gen` (`Print Assumptions` = Closed under the global context).

- **Ph3 PROPER — BASE + UNIVERSE CASES DONE & green (2026-06-05).**
  `LogRel2Reflect.v` (axiom-free) lands the self-contained LEAVES of mutual
  reify/reflect (Theorem 11) — the cases that do NOT recurse through Pi members:
  - REIFY: `reify_nat` / `reify_neutral` (`RedNatEq`/`RedNeutralEq` member ⟹
    `conv_nf`).
  - REFLECT (base El): `reflect_nat`/`reflect_empty`/`reflect_neEl` — a `conv_ne`
    pair well-typed at a base element type is reducibly convertible there
    (reflection = identity, `Reflect`'s `refl_Nat`/etc.).
  - REFLECT (universe): `reflect_U` — `conv_ne` neutral CODES are reducibly
    convertible AT the universe; the substantive case (manufactures the NEW
    reducible type `dEl(vNe·)` from a neutral via `LRne`, landing in `LR0`/`LR1`
    selected by `lvl_of_cases l` — never `tl2`).  Companion `reflect_neEl_ty`:
    `RedTyEq Ge (dEl(vNe n))(dEl(vNe m))` (type-FORMATION from neutral codes,
    for the fundamental lemma's `dEl`-formation).

- **ETA DESIGN — RESOLVED (2026-06-06, paper-faithful).**  Question raised: at a
  relevant Pi, REIFY-tm (`PiRedTmEq` member ⟹ `conv_nf`) cannot relate a bare
  `vNe` member to an eta-long `vLam` member (structural `conv_nf` has no
  `vNe`∼`vLam` rule).  ANSWER (paper "Divide and Check" + this repo's `conv_nf`
  header): the paper does NOT add eta to conversion; `conv_nf`/`conv_ne` stay
  UNTYPED+structural (Def 13 `∼annot`).  Eta is BAKED INTO NORMAL FORMS by
  `Reflect`: a neutral at a relevant Pi reflects to its eta-expansion `vLam`, so
  every relevant-function value is a `vLam`, never a bare `vNe`.  IMPLEMENTATION:
  `RRCar`'s REFLECT is now TYPE-DIRECTED — it produces the `Reflect`-value
  (`{vn vm & Reflect A n vn * Reflect B m vm * P vn vm}`); identity at
  base/code/universe (`refl_Nat`/`refl_U`/…), eta-long at relevant Pi
  (`refl_Pi`).  REIFY-tm at `vPi` thus only ever hits `cnf_lam` (vLam-vLam); the
  mismatch never arises.  (Earlier bare-neutral REFLECT motive was a base-only
  simplification, now corrected.)
- **Ph3 PROPER — MUTUAL-INDUCTION ENGINE DONE & green (2026-06-06).**
  `LogRel2Reflect.v` now carries the full `LR_mut`-driven combined reify/reflect
  induction `RR_gen` (axiom-free): motive `RRCar` bundles REFLECT (type-directed:
  `NeConv` ⟹ `Reflect`-values `P`-related), REIFY-tm (`P` ⟹ `conv_nf`), REIFY-ty
  (codes ⟹ `conv_nf_ty`).
  All 5 NON-Pi cases (nat/empty/ne/U0/U1) discharged axiom-free; the two Pi
  cases are the abstract premises `RR_pi_at`/`RR_piI_at` (universal
  `RR_pi_step`/`RR_piI_step`).  Tower kit `RRbot`/`NeElBuild_LR`/`NeElBuild_vac`;
  `RR0 : RecRR1 LR0` closes the level-0 instance.  Design notes recorded in-file:
  (i) reflect-at-`vPi` MUST eta-expand (bare-neutral Pi members would force
  REIFY-tm to compare `vNe` vs eta-long `vLam`, unprovable in structural
  `conv_nf`) — so the single-sided eta construction genuinely ports, it is NOT a
  trivial bare-neutral membership; (ii) reify-at-`vPiI` deferred (Ph6).
- **UNIVERSE FINDING (2026-06-06) — tower needs the crux as a POLY LEMMA, not an
  abstract premise.**  `RR1`/`RR2` (and hence user `reflect_red`/`reify_tm`/
  `reify_ty`) canNOT be closed from the ABSTRACT `Hpi : RR_pi_step`: the tower is
  universe-polymorphic, so `RR_gen` at `rec0 := LR0` needs the SAME poly instance
  in `HR0` (a poly constant, flexible) and in `Hpi _ _ _` — but a BOUND hypothesis
  is monomorphic, so `Hpi _ _ _` is pinned to `Hpi`'s binding universes ⇒ rigid
  universe clash.  `RR0` dodges it only via `rec0 = LRbot` (trivial universes).
  CONSEQUENCE: discharging `RR_pi_at` (the eta mutual knot) as an axiom-free poly
  LEMMA is BOTH the math crux AND the universe-unblocker for the whole tower; no
  separate refactor.  `RR_gen`+`RR0` are the engine the proven crux plugs into.

- **REMAINING (Ph3 proper): the relevant-Pi MUTUAL KNOT.**  Reflect-at-`vPi` and
  reify-at-`vPi` are ONE mutual induction over the `LR` derivation (well-founded:
  domain via `shpAd`, codomain via `posAd` — see `LogRel2Ind.LR_mut`).  Mining the
  retired single-sided roadmap (`WIP/OTT_LogRel_single_sided/LogRelFund.v`,
  steps (1)–(4) + the session-6 CORRECTION), now re-framed two-sided:
  - **Reflect-at-Pi** (`conv_ne n m` at `vPi FA BA`/`vPi FB BB` ⟹ `PiRedTmEq`
    members = the eta-expansions `vLam`): the single-sided construction (reflect
    bound var via `shpAd` IH; `Apply_reflect_cod`; reflect eta-body via `posAd` IH;
    assemble `vLam body` typed by `t_lam_eta`) PORTS directly.  Its conv-side
    additionally needs reify of the domain TYPES + the domain MEMBER (to fill
    `cne_app`'s `conv_nf F F'`/`conv_nf B B'`/`conv_nf a a'`) + `conv_ren` on
    `n`,`m` — i.e. it CALLS reify.  This is why the two directions are one mutual
    proof, not two.
  - **The genuine open core** (single-sided `reflect_pi_reify_step`, the session-6
    CORRECTION): the application clause's beta-reduct `body[a::sg]` must be
    reducible at the codomain instance `posPack PA ra`.  Single-sided this was
    blocked because the bridge to the `posAd`-reflection is UP-TO-LR / eta
    (a bare neutral does not reflect at a relevant Pi; `Reflect_det` fails for
    higher-order codomains).  The TWO-SIDED PER is the intended fix: relate the
    two sides' reflections DIRECTLY via `posAd`'s reflect IH + genuine `conv_ne`,
    instead of proving a single canonical value.  `Reflect_ren` (naturality of
    reflection under renamings, `RenSubst.v`) + `conv_ren` are the transport kit.
    Still substantial; THE crux of the development.
  - **DESIGN FINDING — reify at the IRRELEVANT Pi (`vPiI`) is NOT expressible
    against the current structural `conv_nf`.**  `LRpiI`'s relation relates ANY
    two typed terms (proof irrelevance), but `LogRel2Conv.conv_nf` is purely
    STRUCTURAL (`cnf_lamI` needs `conv_nf` of the bodies — no irrelevance rule).
    So `RedTmEq` member ⟹ `conv_nf` is FALSE at `vPiI` for structurally-distinct
    irrelevant terms.  Reify-at-`vPiI` sits on the critical path (a relevant-Pi
    codomain can BE a `vPiI`).  Resolution options (decision for next session /
    Dustin): (a) add a proof-irrelevance rule to `conv_nf` for the irrelevant
    fragment (reify irrelevant terms to a canonical/erased form); (b) state reify
    over a reflexive sub-relation; (c) defer the irrelevant fragment with the rest
    of full OTT (Ph6) and prove Theorem 11 for the RELEVANT fragment only.  Note
    the order doc already groups `vPiI`/`vLamI` (= paper's negative/irrelevant
    types) into Ph6.  Reflect-at-`vPiI` is FINE (`reflect`'s `mpiI`: members are
    just typings, reflection = `refl_PiI` identity) — only reify is gapped.

  Transport (Lemma 12) + transitivity stay deferred to post-fundamental (Ph5).

- **CRUX BLOCKER FOUND & VERIFIED (2026-06-06) — two-sided reflect/reify-at-Pi
  hits the `has_svalty` TYPING-CONVERSION WALL on the eta bound variable.**
  Discharging `RR_pi_at` (the relevant-Pi case of `RR_gen`) requires reflecting
  the eta bound variable `nVar 0` into the DOMAIN pack `redTmEq (shpRed PA ws afA
  afB)` at `dEl FA' ≡ dEl FB'`.  The only entry point is the domain IH's REFLECT,
  whose premise is `NeConv Delta (dEl FA') (dEl FB') (nVar 0) (nVar 0)` =
  `wf_neutral Delta (nVar 0) (dEl FA') * wf_neutral Delta (nVar 0) (dEl FB') *
  conv_ne ..`.  But `wf_neutral _ (nVar 0) T` is provable ONLY via `n_var`, which
  RIGIDLY pins `nth_error Delta 0 = Some T` (verified: `n_var` is the unique
  `nVar`-headed constructor; `has_svalty`/`wf_neutral` have NO conversion rule).
  So `nVar 0` can be typed at `dEl FA'` OR `dEl FB'` but NEVER BOTH unless
  `FA' = FB'` SYNTACTICALLY.  Off-diagonal (`FA' ≢ FB'`, only `conv_nf`-related —
  e.g. `dEl (vNe p) ≡ dEl (vNe q)`, `p ≠ q`) is the ESSENCE of the two-sided PER,
  so the wall bites pervasively.  This is the SAME wall that forced the two-typed
  neutral base ([[ott-logrel2-two-typed-neutral]]), now resurfacing structurally.
  The SINGLE-SIDED dev avoided it (one domain `F`, one-sided typing — its
  `reflect_pi_step_from_app` compiled).  PROVABLE PIECE landed in-analysis: the
  domain-codes reify `conv_nf FA FB` comes cleanly from `domIH` at the IDENTITY
  sub (`wf_ssub_id` + `Apply_val_id`, `snd` of the carrier).  CONSEQUENCE: the
  codomain reify `conv_nf BA BB` and BOTH REFLECT directions are blocked on the
  wall (can't manufacture the related fresh-var domain member).  This is a DESIGN
  FORK (see NEXT_SESSION.md): (a) add a typed-conversion rule
  `t_conv`/`n_conv` to `has_svalty`/`wf_neutral` (standard OTT; big domain-layer
  ripple; soundness vs `ModelOk` must be checked); (b) weaken `RRCar`'s REFLECT
  premise to one-sided typing + `conv_ne`, recovering the other side's typing
  elsewhere (but escape `RedTmEq_wf`'s `LRne` case needs BOTH — the original
  reason for two-typing); (c) reduce off-diagonal reflect-at-Pi to the diagonal
  via symmetry/transport (both deferred/normalization-strength).  `RR_gen`+`RR0`
  (the engine) stay green with `RR_pi_at`/`RR_piI_at` abstract.
  PAPER RESOLUTION — read the FSCD2026 paper's CODE (Poiret/Maillard/Tabareau
  `metamltt`, branch `fscd2026`: `Neutrals.v`/`LogicalRelation.v`/`Declarative.v`/
  `FundamentalLemma.v`).  Typed conversion IS needed (their `Declarative.v` has
  `WfTmConv : Γ⊢t⦂A → Γ⊢A≡B → Γ⊢t⦂B` + `ConvTmConv`) BUT the shape is NOT
  "two-typed NeConv + n_conv with structural conv_nf".  Instead:
  (1) **neutrals are SINGLE-TYPED.**  `ConvNe` is `Γ ⊢ n ~ne n' ⦂ R` (ONE result
      type) with `≡`-conversion premises per rule — `ConvNeRel` (variable):
      `in_ctx Γ n A` + `decl(Γ⊢R≡A)`; `ConvNeAppCong`: annotations only
      `≡`-convertible + `decl(Γ⊢R≡Cod[a])` + `decl(Γ⊢R≡Cod'[a'])`.  The neutral
      TERM relation `RelAtNe Γ A t u` is single-typed too (both at the left whnf
      A).  Two-sidedness is reserved for STRUCTURED types (`RelAtPi`: Dom/Dom',
      Cod/Cod').  ⇒ our two-typed `NeConv Ge T S n m` is the ROOT DIVERGENCE.
  (2) **conversion = full DECLARATIVE `≡`** (`ConvTy`/`ConvTm`), NOT structural
      `conv_nf` (soundness automatic).
  (3) **the variable uses a VALID/reducible CONTEXT** `⊨ Γ` (a `TelRed` telescope
      of per-variable reducibility): `varRed : Γ ⊨ tRel n ≡ tRel n ⦂ A` at the
      var's SINGLE context type, via `irrelevance`.  Never typed at two types.
  PAPER-FAITHFUL FIX (bigger than n_conv): (i) single-typed neutral conversion
  with `≡`-premises + typing-conversion; (ii) valid-context telescope for vars.
  Dissolves BOTH the variable wall AND the escape wall that motivated two-typing.
  Supersedes the "add n_conv / structural conv_nf" recommendation above.

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
