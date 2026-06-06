# Next-session kickoff — OTT two-sided PER migration

## UPDATE 2026-06-06e — OPTION A (NbE read-back) CHOSEN; adequacy layer BUILT

Dustin chose option (A): a type-directed reify (read-back) FUNCTION/relation that
eta-expands at Pi, with reify-tm restated on read-backs.  Reason: R2 (`P a b ->
conv_nf a b` on raw members) is FALSE even with the `is_lam` gate — member bodies
can be eta-short bare neutrals at NESTED function codomains (machine-verified
counterexample; see [[ott-r2-hereditary-eta]]).

**DONE this session (3 new files, all green + axiom-free, committed+pushed):**
- `Reify.v` — `ReifyTy`/`Reify`/`ReifyNe` mutual read-back relations (dual of
  `Reflect`; eta-expands at relevant Pi via `rfy_Pi`, structural elsewhere) +
  `Reify_det` (determinism).
- `ApplyConv.v` — `Apply_conv`: `Apply` is a CONGRUENCE for conv under
  pointwise-conv substitutions (`conv_sub`, with length).  Proved by induction on
  the Apply DERIVATION (not the type) — dodges the dependent-codomain
  non-termination.  Keystone for read-back congruence.  Also `conv_sub_refl/
  cons/up/nth`, `conv_tyc`.
- `ReifyConv.v` — `Reflect_conv` + `Reify_conv` (ReifyTy/Reify/ReifyNe): Reflect
  and Reify map conv-related inputs (at conv-related types `conv_svty`, Empty_set
  on dU/dEl mismatch) to conv-related normal forms.  Eta cases use `Apply_conv` +
  `Reflect_conv`.  Projections `ReifyTy_conv`/`Reify_conv_val`/`ReifyNe_conv`,
  `Apply_conv_val`/`Apply_conv_Vapp`.

**RRCar REWIRE DONE (2026-06-06e, committed+pushed, green+axiom-free):**
`LogRel2Reflect.v` RRCar reify-tm is now the read-back form
`(forall a b na nb, P a b -> Reify A a na -> Reify B b nb -> conv_nf na nb)`;
`RR_gen` re-greened all cases (base via `Reify_conv_val`, universe via
`ReifyTy_conv`, line-762 consumer via `Reflect_conv`).  R2 residual (`Hreify_tm`/
`RR_pi_res` middle) rethreaded to the read-back form — now TRUE/provable.

**NEXT = discharge the 3 residuals `RR_pi_res` (now all provable), in
`LogRel2Reflect.v`'s `RRPiDev` section (all IHs `domIH`/`posIH` in scope):**
- (R2) read-back reify-tm at Pi — VALIDATED INTERACTIVELY, recipe (mirrors
  eta_bodies, REIFY direction):
  ```
  intros a b na nb Hab Hra Hrb.
  destruct Hab as [[[Hta Htb] [[ba Ea] [bb Eb]]] Happm]. subst a b.
  inversion Hra as [...rfy_Pi: ARGa B'a faa bodya HARa HAPa HVAa HBDa]; subst.
  inversion Hrb as [...rfy_Pi: ARGb B'b fbb bodyb HARb HAPb HVAb HBDb]; subst.
  apply cnf_lam.   (* goal: conv_nf bodya bodyb *)
  destruct (pi_bound_var_reflects PA ws0 afA0 afB0 HwfD (domIH ...))
    as [ARGn [ARGm [[Hargn Hargm] rab]]]. rewrite HL in Hargn,Hargm.
  pose proof (Reflect_det Hargn HARa); subst ARGn.   (* ARGn = ARGa *)
  pose proof (Reflect_det Hargm HARb); subst ARGm.   (* ARGm = ARGb *)
  (* rab : redTmEq (shpRed PA ws0 afA0 afB0) ARGa ARGb -- DONE up to here *)
  ```
  **CRUCIAL: do NOT use Apply_conv on the bodies** — the members `vLam ba`/
  `vLam bb` are NOT conv-related (eta-short vs eta-long), so `conv_nf faa fbb`
  via Apply_conv is FALSE.  Instead get `faa`/`fbb` REDUCIBLY related via the app
  clause `Happm` instantiated at `Delta=Dlt`, `sg=wkn`, args `ARGa`/`ARGb`, witnesses
  `FA':=shift FA` (afA0), `BA':=shift_1 BA`, `fsg:=shift(vLam ba)` (Apply_val_wkn,
  scopedness via `has_svalty_ne_below` Hta + `ne_below_ctx` from Hwf), `rab`; then
  `Vapp_det` aligns its `v`/`w` with `faa`/`fbb` (HVAa/HVAb); then `posIH ... rab Hwf`'s
  read-back reify-tm with HBDa/HBDb (after aligning `B'a = posTyA PA rab` via
  `Apply_val_det` on HAPa vs `posAppA`) gives `conv_nf bodya bodyb`.
  Then drop the `Hreify_tm` Context (prove R2 as a Lemma in RRPiDev after Hcod).
- (R1) `conv_nf BA BB`: already proved as `dom_reify_ty`/`Hcod` analog — actually
  R1 is the codomain `conv_nf BA BB`; revisit whether `posIH` reify-ty at the
  bound var gives it (was the entangled one).
- (R3) `RR_app2` (eta application clause / beta-reduct closure): the reflect-side;
  hardest (never closed even single-sided) — but now `Reify`/`Apply_conv`/
  `Reflect_conv` are available.
Then prove R2 INSIDE `RR_pi_case` and drop the `Hreify_tm` Context; close
`RR_pi_res`/`RR_pi_step`; instantiate the tower (`RR0`/`RR1`/`RR2`) + user
`reflect_red`/`reify_tm`/`reify_ty`.

OLD plan (superseded, kept for reference) — the integration into `LogRel2Reflect.v`:
1. Change `RRCar`'s reify-tm clause from `(forall a b, P a b -> conv_nf a b)` to
   the read-back form.  RECOMMENDED: UNIVERSAL form (no totality needed):
   `(forall a b na nb, P a b -> Reify (length Ge) A a na -> Reify (length Ge) B b nb -> conv_nf na nb)`.
   (Totality of Reify on reducible members can be a SEPARATE lemma for the final
   completeness theorem; the universal form keeps RR_gen totality-free.)
2. Re-green `RR_gen` all cases:
   - base/neutral cases: invert the two `Reify` (→ `vNe (ReifyNe ·)`), close via
     `ReifyNe_conv` from the members' `conv_ne` (RedNeutralEq).
   - universe code cases: via `ReifyTy_conv` / `Reify_conv_val`.
   - Pi case: invert both `Reify` (→ `rfy_Pi`, bodies = reify of the members
     applied to the reflected bound vars); the bodies are conv by the codomain
     reify IH (`posIH`) applied to the app-clause results (the eta_bodies
     machinery, now TRUE because reify eta-expands).  R1/R3 fold in here.
3. Internal consumer `eta_bodies` line ~762 (`conv_nf ARGn ARGm` for `cne_app`):
   now DIRECT via `Reflect_conv` (Reflect of nVar0 at conv-related domains) — no
   longer needs the reify-tm component.
4. Fix `RecRR1`/`RR0`/`RRbot`/tower + `RR_pi_res`/`RR_pi_at_from_res` to the new
   clause; drop the `Hreify_tm` Context; discharge R1/R2/R3; unblock RR1/RR2 tower
   + user `reflect_red`/`reify_tm`/`reify_ty`.
Dependency: `LogRel2Reflect.v` should import `Reify ReifyConv` (no cycle: ReifyConv
depends only on Apply/Reflect/Reify/ApplyConv/LogRel2Conv).
Then Ph5 fundamental lemma → gluing `Model.v`/`ModelOk.v` ⇒ `eq_term` decidability.

---


Paste this as the opening prompt (or just read it) to resume the OTT/Norm/Pi
migration to a two-sided PER-of-conversion logical relation (Divide and Check).

---

**Resume the OTT/Norm/Pi migration to the two-sided PER-of-conversion logical
relation.** Goal: decidable conversion for OTT. Branch `gluing-nbe`. Read
`WIP/ConvRelPlan.md` (design + live STATUS) and the `[[ott-convrel-pivot]]`
memory first.

## UPDATE 2026-06-06d — `is_lam` GATE LANDED (read [[ott-pi-reify-gate-blocker]])

Machine-verified that residual (R2) (Pi reify-tm) was FALSE under the UNgated
`PiRedTmEq` (it admitted eta-short bare-neutral members; `conv_nf (vLam _)(vNe _)`
has no rule).  Per Dustin's call, added the paper-faithful `is_lam` member gate
(`PiRedTmEq` members must be lambdas).  Whole `LogRel2*` chain + `Glue` re-greened,
axiom-free.  R1/R2/R3 are now TRUE/achievable but STILL need the VR/reify-adequacy
layer (the gate removed the falsity, not the work).  **NEXT = build the VR layer
(reducible substitutions + reify adequacy), discharge R1/R2/R3, then prove R2
inside `RR_pi_case` and drop the `Hreify_tm` Context.**  Details in ConvRelPlan
STATUS "GATE LANDED".

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

## State update (2026-06-05): Ph3 PROPER — BASE + UNIVERSE CASES DONE

`LogRel2Reflect.v` is built, axiom-free, green: the self-contained LEAVES of
mutual reify/reflect (Theorem 11), i.e. every case that does NOT recurse through
Pi members.
- REIFY: `reify_nat` / `reify_neutral` (base PER member ⟹ `conv_nf`).
- REFLECT (base El): `reflect_nat` / `reflect_empty` / `reflect_neEl`.
- REFLECT (universe): `reflect_U` (neutral CODES reducibly convertible at U; the
  substantive case — builds the NEW reducible type `dEl(vNe·)` via `LRne`,
  `lvl_of_cases` picks `LR0`/`LR1`) + companion `reflect_neEl_ty` (type-FORMATION
  `RedTyEq Ge (dEl(vNe n))(dEl(vNe m))`).

## DONE THIS SESSION (2026-06-06) — engine + eta design

`LogRel2Reflect.v` now carries the FULL `LR_mut`-driven combined reify/reflect
induction `RR_gen` (axiom-free, green), with motive `RRCar` =
  - REFLECT (TYPE-DIRECTED): `NeConv Ge A B n m ⟹ { vn vm & Reflect (length Ge) A
    n vn * Reflect (length Ge) B m vm * P vn vm }` — identity at base/code/U
    (`refl_Nat`/`refl_Empty`/`refl_neEl`/`refl_U`), eta-long at relevant Pi
    (`refl_Pi`);
  - REIFY-tm: `P a b ⟹ conv_nf a b`;
  - REIFY-ty: `conv_nf_ty A B` (the codes; `unit` at U).
All 5 NON-Pi cases discharged; both Pi cases abstracted as `RR_pi_at` /
`RR_piI_at` (universals `RR_pi_step`/`RR_piI_step`).  Tower kit `RRbot`/
`NeElBuild_LR`/`NeElBuild_vac` + `RR0 : RecRR1 LR0` (level-0 instance) green.

**ETA QUESTION RESOLVED (paper-faithful).**  The paper does NOT add eta to
conversion; `conv_nf`/`conv_ne` stay UNTYPED+structural (Def 13 `∼annot`).  Eta is
BAKED INTO NORMAL FORMS by `Reflect` (relevant-function values are always `vLam`,
never bare `vNe`) — hence the type-directed REFLECT motive above, and REIFY-tm at
`vPi` only ever hits `cnf_lam`.

**UNIVERSE FINDING.**  `RR1`/`RR2` + user `reflect_red`/`reify_tm`/`reify_ty`
CANNOT close from the ABSTRACT `Hpi` premise (a bound hypothesis is monomorphic
⇒ can't supply the poly tower's per-level `LR0`/`LR1` instances ⇒ rigid universe
clash; `RR0` dodges via `rec0 = LRbot`).  So discharging `RR_pi_at` as a genuine
axiom-free POLY LEMMA is BOTH the math crux AND the universe-unblocker for the
whole tower — no separate refactor.

## DONE THIS SESSION (2026-06-06b) — plumbing + CRUX BLOCKER verified

1. **PLUMBING DONE & green (committed+pushed).** `RRCar` now threads `wf_senv Ge`
   (the leading `wf_senv Ge ->`, mirroring single-sided `reflect_motive`); only
   the relevant-Pi case consumes it.  `RR_gen` re-greened (`intros Hwf` per case;
   the universe REIFY-tm feeds `Hwf` to the lower-tower delegate `HR0`/`HR1`).
   `RR_pi_at`/`RR_piI_at` stay abstract; file green + axiom-free.
2. **CRUX BLOCKER FOUND & VERIFIED — the `has_svalty` typing-conversion wall.**
   `RR_pi_at`'s REFLECT/REIFY both need to reflect the eta bound variable `nVar 0`
   into the DOMAIN pack at `dEl FA' ≡ dEl FB'` via `domIH`'s REFLECT, whose
   premise `NeConv Delta (dEl FA')(dEl FB')(nVar 0)(nVar 0)` requires `nVar 0`
   typed at BOTH `dEl FA'` AND `dEl FB'`.  `wf_neutral _ (nVar 0) T` is ONLY
   provable by `n_var`, which pins `nth_error Delta 0 = Some T` — so impossible
   unless `FA' = FB'` SYNTACTICALLY, while off-diagonal (`conv_nf`-related but
   unequal) is the whole point of two-sided.  No conversion rule on
   `has_svalty`/`wf_neutral` (verified via `Print`).  Single-sided dodged it (one
   domain).  PROVABLE leaf confirmed in dev: `conv_nf FA FB` (domain-codes reify)
   from `domIH` at the identity sub.  Full detail + the airtight argument in
   `ConvRelPlan.md` STATUS ("CRUX BLOCKER FOUND & VERIFIED").

## HOW THE PAPER ACTUALLY RESOLVES IT (read the FSCD2026 code)

Source: Poiret/Maillard/Tabareau `metamltt`, branch `fscd2026`
(`Neutrals.v`/`LogicalRelation.v`/`Declarative.v`/`FundamentalLemma.v`; PDF
hal-05495420).  Typed conversion IS required (their `Declarative.v` has
`WfTmConv : Γ⊢t⦂A → Γ⊢A≡B → Γ⊢t⦂B` + `ConvTmConv`), confirming the diagnosis —
but the SHAPE is NOT our two-typed-NeConv-plus-n_conv-with-conv_nf:
1. **Neutrals are SINGLE-TYPED.**  `ConvNe` = `Γ ⊢ n ~ne n' ⦂ R` (ONE result
   type) with declarative `≡`-premises baked in per rule.  Variable rule
   `ConvNeRel`: `in_ctx Γ n A` + `decl(Γ⊢R≡A)` (var ~ itself at ANY R convertible
   to its context type).  App rule `ConvNeAppCong`: annotations only
   `decl(Γ⊢Dom≡Dom')`/`decl(Γ,,Dom⊢Cod≡Cod')` + `decl(Γ⊢R≡Cod[a])` +
   `decl(Γ⊢R≡Cod'[a'])`.  The neutral TERM relation `RelAtNe Γ A t u` is
   single-typed too (both members reduce to neutrals at the SAME A = left whnf;
   `Rel_tot_Ne` uses the left rep `Ane`).  Two-sidedness is reserved for
   STRUCTURED types (`RelAtPi Γ Dom Cod Dom' Cod'`).  ⇒ our two-typed
   `NeConv Ge T S n m` (the `[[ott-logrel2-two-typed-neutral]]` workaround) is the
   ROOT DIVERGENCE that created the wall.
2. **Conversion = full DECLARATIVE `≡`** (`ConvTy`/`ConvTm`), not structural
   `conv_nf`.  Soundness automatic (it's the spec).
3. **The variable uses a VALID/reducible CONTEXT** `⊨ Γ` (a `TelRed` telescope of
   per-variable reducibility witnesses).  `varRed : Γ ⊨ tRel n ≡ tRel n ⦂ A`
   proves the var reducible at its SINGLE context type A, pulled from the context
   + `irrelevance`.  The var is NEVER typed/reflected at two types; under a binder
   the fresh var enters the domain relation as a related PAIR from the EXTENDED
   valid context — not by manufacturing a `(FA',FB')` NeConv on the spot.

PAPER-FAITHFUL FIX (an architectural pivot, bigger than `n_conv`): (i) move the
neutral conversion to SINGLE-typed (`~ne ⦂ R`) with `≡`-premises + a typing-
conversion rule (`WfTmConv`/`ConvTmConv` analogues on `has_svalty`); (ii) adopt a
valid-context telescope (`⊨ Γ`) so variables are reducible at their single type.
This dissolves BOTH the variable wall AND the escape wall that originally forced
two-typing (escape then lands typing at the single carried type, conversion
bridges).  Modules to mirror: their `LogicalRelation/ReifyReflect`, `Irrelevance`,
`Transport`, `Symmetry`, `Transitivity`, `Telescope` are SEPARATE — our monolithic
plan should likely split similarly.

## DONE (2026-06-06) — PAPER-FAITHFUL SINGLE-TYPED MIGRATION; WALL DISSOLVED

Dustin chose the paper's single-typed-neutral + typed-conversion architecture
(not the cheap patch).  Landed, axiom-free, whole `LogRel2*` chain + domain layer
+ `Glue` green:
- `n_conv` added to `wf_neutral` (Typing.v) = value-world `WfTmConv`; domain layer
  re-greened with conv-stability helpers `conv_shift`/`conv_ne_below`/`conv_ren`.
- `NeConv`/`RedNeutralEq` made SINGLE-typed (LEFT type; paper `RelAtNe`); `LRne`
  relation single-typed; escape (`RedTmEq_wf`) + symmetry (`LR_sym_gen`) bridge to
  the right type via `n_conv` + `conv_ne`.
- `RRCar` REFLECT premise single-typed at LEFT type.
- **`pi_bound_var_reflects`** (axiom-free) demonstrates the wall is GONE: the eta
  bound variable reflects from a SINGLE left typing, the domain IH returns both
  reflections + the domain member.

## DONE (2026-06-06c) — RR_pi_at REDUCED to 3 reify/reflect residuals (axiom-free)

`LogRel2Reflect.v` now PROVES the relevant-Pi crux `RR_pi_at` MODULO three
explicitly-isolated residuals (the two-sided port of single-sided
`reflect_pi_step_from_reify`).  All NEW content axiom-free + green:
- `RedTmEq_wf_gen` — level-generic escape (`@LR lvl rec0 rec1`, not just `LR2`).
- `conv_ctx` + `typing_ctx_conv` — CONTEXT CONVERSION metatheorem (typing stable
  under pointwise-`conv_nf` context entries).  Bridges the two-sided gap: the
  RIGHT eta-body is reflected in the LEFT-domain context but `t_lam_eta` for the
  RIGHT Pi needs the RIGHT-domain context (differ only at the convertible front
  domain).
- `eta_bodies` — the two-sided eta-expansion: from a `NeConv` pair at the LEFT Pi
  builds `vLam body_n`/`vLam body_m`, both `refl_Pi` reflects, both `t_lam_eta`
  typings, and the codomain member (via `pi_bound_var_reflects`,
  `Apply_reflect_cod`, `n_app`/`n_conv`, `typing_ctx_conv`).
- `dom_reify_ty` — domain reify-ty leaf (`conv_nf FA FB` from `domIH` at id sub).
- `RR_pi_case` + `RR_pi_res` + **`RR_pi_at_from_res`** — `RR_pi_at` follows from
  `RR_pi_res`, i.e. the three residuals:
    (R1) `conv_nf BA BB`  (codomain reify-ty for RAW codes),
    (R2) `forall a b, PiRedTmEq PA a b -> conv_nf a b`  (function reify-tm),
    (R3) `RR_app2`  (the eta-expansion application clause; two-sided analog of
         single-sided `reflect_pi_app_step`).

**NEXT = discharge the three `RR_pi_res` residuals (the genuine VR-layer core).**
(R1)+(R3) are entangled reify/reflect adequacy for the eta substitution (NOT a
renaming for higher-order domains; see `WIP/ReifyDev.v`), needing a
validity/reducible-substitution (VR) layer + reducibility-eta-irrelevance.  (R2)
needs casing on the members + the codomain reify IH.  Closing all three fully
discharges `RR_pi_at` and unblocks the `RR1`/`RR2` tower +
`reflect_red`/`reify_tm`/`reify_ty`.  Full detail in `WIP/ConvRelPlan.md` STATUS.

## Superseded fork — RE-PLAN around the single-typed-neutral pivot (RESOLVED above)

The earlier 3-option fork is SUPERSEDED: the paper neither keeps two-typed
neutrals nor uses structural conv_nf.  Decision for Dustin: adopt the paper's
single-typed-neutral + valid-context architecture (a real migration of `NeConv`/
the base relation + a new `⊨ Γ` telescope), vs a cheaper local patch.  Old
options retained below for reference (the paper points away from all three):
- **(a)** add `t_conv`/`n_conv` (typed conversion) to `has_svalty`/`wf_neutral`
  — standard OTT; lets `nVar 0 : dEl FA'` transport to `dEl FB'` via
  `conv_nf FA' FB'`; BIG domain-layer ripple (Apply/Determinism/Preservation/
  Reflect/RenTyping + `LogRel2*`) and soundness vs `Norm/Model.v`+`ModelOk.v`
  MUST be re-checked (is structural `conv_nf`-conversion of types model-valid?).
- **(b)** weaken `RRCar`'s REFLECT premise to one-sided typing + `conv_ne`,
  recovering the other side's typing from the relation — but escape
  `RedTmEq_wf`'s `LRne` case needs BOTH sides (the reason the neutral base went
  two-typed); would need a different escape route.
- **(c)** prove `RR_pi_at` only for the DIAGONAL (`FA=FB`,`BA=BB`) and reach
  off-diagonal via symmetry/transport — but transport+trans are deferred
  (normalization-strength) and `RR_gen`'s `LRpi` case is GENERAL, so a diagonal
  `RR_pi_at` does not plug into `RR_gen` as-is.

Once resolved: the eta construction itself ports from single-sided
`reflect_pi_step_from_app` (`wf_ssub_wkn`/`Apply_val_wkn`/`Apply_reflect_cod`/
`refl_Pi`/`t_lam_eta`), TWO-SIDED (build `vLam body_n`/`vLam body_m` via the
dom/cod IHs; `conv_ren`+`Reflect_ren` for transport; app-clause beta-reduct
closed by relating the two `posIH` reflections via the PER + `conv_ne`).  The
codomain reify `conv_nf BA BB` also waits on the resolution (it needs the
reflected-var domain member to instantiate `posIH`).  Helper signatures are all
confirmed in-scope from `ApplyLemmas`/`ApplySubst`/`RenSubst`/`RenTyping`/
`LogRel2Ren` (note: `wf_ssub_id` has `Ge` IMPLICIT — use `@wf_ssub_id Ge Hwf`).
Then the tower (`RR1`/`RR2`) + user `reflect_red`/`reify_tm`/`reify_ty` close.

Then the fundamental lemma (Ph5) → connect to gluing `Model.v`/`ModelOk.v` ⇒
`eq_term` decidability.  Transport (Lemma 12) + transitivity stay deferred (Ph5).
`vPiI`/`vLamI` reify deferred to Ph6.

## Build (per CLAUDE.md — never run full `make` during dev)
```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome \
     src/Pyrosome/Lang/OTT/Norm/Pi/<File>.v
```
(The Rocq MCP works on project files via `rocq_start(file=...)`; it does NOT pick
up loadpaths for a brand-new unbuilt file, so compile new files with `coqc`
first.) Always `git push` after each green commit.
