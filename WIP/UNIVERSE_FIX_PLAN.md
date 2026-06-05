# Fixing the LogRel2 universe block (PER symmetry) — plan for future sessions

Branch `gluing-nbe`. This documents WHY two-sided PER **symmetry** (and any lemma
that *constructs* a swapped/derived `PolyRedPack`) does not typecheck in the
current `LogRel2.v` encoding, and the best plan to fix it. Read together with
`WIP/LogRel2Sym.v` (the parked attempt + GAP 2' header) and the
`[[logrel2-irrelevance-and-symmetry-universe-block]]` memory.

Irrelevance (`LogRel2Irr.v`) is DONE and is universe-clean (its motive returns
equivalence *maps*, never builds a derivation). Everything below is only about
proofs that must **build a new `LR` derivation** (symmetry, transport-by-
construction, the fundamental lemma's pack constructions).

---

## 1. The exact contradiction

Universe facts in the current monomorphic `LogRel2.v`
(`Print Universes Subgraph (LRPack.u0 RedRel.u1 RedRel.u2 LR.u0)`):

```
LRPack.u0 <= RedRel.u1      (PolyRedPackAdequate: a pack field is fed to LR's relation slot)
LRPack.u0 <  RedRel.u2      (LR : Type@{RedRel.u2} takes a PolyRedPack arg : Type@{LRPack.u0+1})
RedRel.u2 <= RedRel.u1      (the LRU witness {P & rec h .. P} fits LR's relation slot)
LR.u0     <  RedRel.u1
```

- `LRPack.redTmEq : sval -> sval -> Type@{LRPack.u0}`   (pack field universe)
- `RedRel` relation arg : `Type@{RedRel.u1}`, output `Type@{RedRel.u2}`
- `LR : ... -> Type@{RedRel.u2}` (the inductive)
- LRU witness `fun c d => has*has*{P : Type@{LR.u0} & rec h Ge (dEl c)(dEl d) P}`
  lives at `max(RedRel.u2, LR.u0+1) = RedRel.u2` (because `rec .. P : Type@{RedRel.u2}`).

Any construction of a swapped pack carries the swapped relation `Q` through a
single value/motive, and `Q` must be **both**:

- `<= LRPack.u0` — because building a `PolyRedPack` means storing `Q` as an
  `LRPack.redTmEq` field (e.g. `sym_pack`'s `shpRed := {| redTmEq := projT1 (Xshp ..) |}`);
- `>= RedRel.u2` — because in the `LRU` sub-case the only `LR Ge (dU r l)(dU r l) Q`
  is the witness above, at `RedRel.u2`.

But `LRPack.u0 < RedRel.u2`. **Impossible.** No annotation fixes it; naive
`Set Universe Polymorphism` does not either (the constraint is intrinsic to a
*single* `LR` instance). This is also exactly why a Π whose **domain is a
universe** is not representable, and why `projT1` of a `RedTyEq` (rigidly at
`RedRel.u1`) cannot be stored into a pack field.

**Root cause:** `rec : forall l', TLlt l' lvl -> RedRel` returns the SAME
monomorphic `RedRel` whose output is `RedRel.u2` — so the lower-level
reducibility predicate lives at the SAME universe as the current level, instead
of strictly below it.

---

## 2. The fix principle (logrel-coq discipline)

In CoqHott/logrel-coq the universes are laid out so the contradiction cannot
arise. Two changes, both required:

1. **Unify the pack-field universe with the relation universe.** Make
   `LRPack.redTmEq` and `RedRel`'s relation arg both live at one universe `i`.
   Then a "generic" relation (at `i`) can be stored into a pack field (at `i`).
   The inductive `LR` lives at a SEPARATE, larger universe `k` with `i < k`
   (it still takes a `PolyRedPack` arg) — that's fine, `k` is not the relation
   universe.

2. **Make each lower level's relations live at a STRICTLY SMALLER universe.**
   The level-`l` universe case quantifies a witness `{P : Type@{i'} & rec..P :
   Type@{j'}}` over a lower relation with `i' < i` and `j' <= i`, so the witness
   lands `<= i` and fits the current relation slot. The monomorphic single-
   `RedRel` `rec` cannot do this (one universe for all levels). **NB:** with more
   than two levels this CANNOT be delivered by a single dispatching `rec : forall
   l', _ -> RedRel` function — a value-level `match` on `l'` collapses the lower
   relation universes (Section 3, empirically confirmed). For >2 levels the lower
   relations must be UNFOLDED into separate inductive parameters with `LRU` split
   per level (Step 1B). For exactly two levels a constant `rec1 := LR0` suffices
   (Step 1A).

Target ladder per level `l`:  `i_l < k_l`,  and  `k_{l-1} <= i_l`  (lower
inductive's output fits the current relation slot), giving the strictly
increasing chain  `i_0 < k_0 <= i_1 < k_1 <= i_2 < k_2 ...`.

With (1)+(2), the symmetry carrier works: inducting on the top `LR`, the
Pi-domain stores `Q` at the top relation universe `i_top` (✓, pack field = `i_top`),
and the `LRU` sub-case's witness sits at `< i_top` (✓). No clash.

---

## 3. The real complication: the finite-tower `match` collapses lower levels

Current tower (`LogRel2.v`):

```coq
Definition rec1 (l' )(h) : RedRel := LR0.                                  (* single branch *)
Definition LR1 : RedRel := @LR tl1 rec1.
Definition rec2 (l' )(h) : RedRel :=
  match l' with tl0 => LR0 | tl1 => LR1 | tl2 => LR0 end.                  (* TWO lower branches *)
Definition LR2 : RedRel := @LR tl2 rec2.
Definition RedTyEq Ge A B := { P & LR2 Ge A B P }.                        (* uses LR2 *)
```

`rec2`'s `match` returns a single `RedRel@{i j}`. **EMPIRICALLY CONFIRMED** (with
the faithful function-typed relation arg) that such a match forces the two
branches' **relation-arg (contravariant) universes EQUAL**, not bracketed:

```coq
Definition RR@{i j} := (nat -> nat -> Type@{i}) -> Type@{j}.
Definition pick@{i j a b c d} (n:nat) : RR@{i j} :=
  match n with O => A0@{a b} | _ => A1@{c d} end.
(* recorded constraints:  b <= j   d <= j   a = i   c = i  *)
```

`a = i = c`: the branch relation universes collapse to `i`; only the output
universes bracket (`b,d <= j`). Writing `i_l` = level-l relation/pack universe,
`j_l` = its inductive/output universe, the ladder needs `i_0 < j_0` (`LRpi`'s
`PolyRedPack` arg at `i_0+1` inside `LR0 : Type@{j_0}`) and `j_0 <= i_1` (`LR1`'s
universe case stores the `LR0`-witness, at `j_0`, into `LR1`'s relation slot
`i_1`). The match collapse `i_0 = i_1` then gives `i_0 < j_0 <= i_1 = i_0` —
contradiction. So **the poly TOWER ITSELF would not typecheck** (not just
symmetry); the multi-branch `match` in `rec2` is incompatible with the ladder.
The 2-level tower escapes only because `rec1 := LR0` is a CONSTANT (no dispatch);
logrel-coq escapes for the same reason (exactly two levels, `zero << one`).

**3 levels IS still achievable** — just not by "one more match branch". You must
avoid the dispatching `match` entirely: **UNFOLD** the `rec` dispatch into the
inductive. The clean way (Step 1B) keeps ONE uniform `LR`: replace the single
`rec : forall l', _ -> RedRel` parameter with the fixed, finite list of lower
relations as SEPARATE parameters at distinct universes
(`LR (lvl) (rec0 : RedRel@{i0 j0}) (rec1 : RedRel@{i1 j1}) : RedRel@{i2 j2}`),
and SPLIT `LRU` into per-source-level constructors (`LRU0` needs `tl0 < lvl`,
uses `rec0`; `LRU1` needs `tl1 < lvl`, uses `rec1`). Each U-constructor names a
CONCRETE parameter at its own universe — no value-level `match`, so no collapse,
and the ladder `i_0 < j_0 <= i_1 < j_1 <= i_2 < j_2` becomes ordinary universe
constraints on `LR`'s parameters. Because it is still ONE inductive, you keep
ONE `LR_mut`, ONE set of relation defs, ONE escape/irrelevance — NO ~3x
duplication (that cost applies only to the cruder "N separate inductives"
variant). This is why Step 0 (does the fragment need TWO reducible object
universes?) still sizes the job, but the 3-level path is now concrete and
moderate, not prohibitive: 2 levels is least churn; 3 levels pays for splitting
`LRU` + threading the extra `recK` params.

logrel-coq avoids this by having only **two** `TypeLevel`s (`zero`, `one`) and a
`rec` for `one` that returns the `zero` relation as a *single* thing (no
multi-branch match), with the WORKING relation being the top object level
`LR one` (not a third "ambient" level). Our `tl0/tl1/tl2` with `tl2` ambient and
`RedTyEq := {P & LR2 ..}` is the source of the collapse.

---

## 4. Recommended plan

### STATUS (2026-06-05): Step 0 + Step 2 DONE; chose 1B; ready for Step 3 port
- **Step 0 answered:** the Pi fragment uses only `L0` as a reducible type (`Pi.v`:
  all codomains/Pi types at `#"U" … "L0"`; `L1` / `u0 : U L1` appear only in
  `Cast.v` = Ph6).  2 levels would suffice for Pi alone, but the **user chose
  Step 1B (3 levels)** to future-proof Ph6/Cast (where `U1` is genuinely reduced).
- **Step 2 prototype DONE & GREEN:** `WIP/UnivProto.v` (coqc exit 0) validates the
  unfolded encoding + tower under `Set Universe Polymorphism`.  All three decisive
  tests pass: (T1) tower typechecks, per-level ladder `i0<j0<=i2`, `i1<j1<=i2`,
  `i2<j2`, **no `i0=i1` collapse**; (T2) kernel accepts `LR` (`LR_ind` constraints
  `i0<i,i1<i,i<j,j0<=i,j1<=i`, no `i0=i1`); (T3) the symmetry-shaped storage (an
  `LRU0` witness at `j0` into a *domain* `LRPack` field at `i2`) typechecks.
- **NEXT: Step 1B + Step 3 port** to `src/.../LogRel2.v` (then re-green
  `LogRel2Ind/Lemmas/Red/Irr` with the split `LRU0`/`LRU1` cases).

### Step 0 — answer the gating question (cheap, do first)  [DONE → 1B]
**Does the Π-fragment actually need TWO reducible object universes (`U0 : U1`),
or is `tl1` only ever an ambient top?** `lvl_of` maps level term `"L1" -> tl1`,
else `tl0`; `LR2`'s `LRU` makes `dU r l` reducible at `lvl_of l ∈ {tl0,tl1}`.
- If only `tl0`-universes (`U0`) ever appear as *reducible types* in the Pi
  fragment (i.e. `U1` is only the ambient sort of `U0`, never itself reduced),
  then collapse the tower to **two levels** and the fix is clean (Step 1A).
- If genuine `U0 : U1 : U2` reducibility is needed, you need Step 1B (harder).
Check by grepping the OTT Pi language defs / `Typing.v` / `Model.v` for whether
`dU _ "L1"` is ever a *type-being-reduced* vs only a classifier. Ask the user.

### Step 1A — two-level, well-founded tower + poly (preferred, matches logrel-coq)
- Drop `tl2`. `TypeLevel := tl0 | tl1`. `TLlt`: only `tl0 < tl1`.
- `rec1 := fun _ _ => LR0` (single branch — no collapse). Working relation =
  `LR1`. `RedTyEq := { P & LR1 Ge A B P }` (and `RedTmEq`, `RedSubEq` likewise).
- `Set Universe Polymorphism` on `LogRel2.v`. Make `RedRel@{i j}`, `LRPack@{i}`
  (field at `i`), `PolyRedPack`/`PiRedTmEq`/`PolyRedPackAdequate`/`LR@{i j k}`
  poly, **with the pack field universe = the relation-arg universe `i`** (do NOT
  let them split — add an explicit `@{i}` to both, or a `Constraint`).
- Tower with explicit constraints:
  `LR0@{i0 j0 k0}` , `LR1@{i1 j1 k1 | k0 <= i1, i0 < k0, i1 < k1, ...}` so the
  `LRU`-witness of `LR1` (which references `LR0`) fits. Pin via `@{...}`
  annotations on `LR0`/`LR1`/`rec1`.
- Re-green the chain (`LogRel2Ind`, `LogRel2Lemmas`, `LogRel2Red`, `LogRel2Irr`):
  proofs should be unchanged; only universes float. `LR_mut` etc. need their
  `tl2`/`LR2` references retargeted to `tl1`/`LR1`.
- Then re-attempt symmetry (`WIP/LogRel2Sym.v`): the carrier should now
  typecheck. Better still, reformulate it to USE `RedTmEq_irr` (already proven)
  for the `bwd` direction instead of the bidirectional-`SymCar` admit.

### Step 1B — keep three levels by UNFOLDING the `rec` dispatch (if Step 0 says you must)

The blocker is solely the value-level `match` in `rec2` (it equates the branch
relation universes). Eliminate it by moving the lower-level relations from a
dispatching function into the inductive's PARAMETERS, and splitting `LRU` so each
universe constructor names a concrete parameter. The finite tower has a fixed
depth (3), so the parameter count is fixed.

**B1. Re-shape the inductive (one `LR`, no `rec` function).** Under
`Set Universe Polymorphism`, with the pack field universe unified to the
relation-arg universe (`LRPack@{i}` field at `i`, `RedRel@{i j}` relation at `i`):

```coq
(* lower relations passed as SEPARATE params at DISTINCT universes -- no match,
   no collapse.  recK = reducibility at source level tlK. *)
Inductive LR@{i0 j0 i1 j1 i j}
    (lvl  : TypeLevel)
    (rec0 : RedRel@{i0 j0})
    (rec1 : RedRel@{i1 j1}) : RedRel@{i j} :=
  | LRnat  : ...
  | LRempty: ...
  | LRne   : ...
  | LRpiI  : ...
  | LRpi   : forall Ge FA BA FB BB (PA : PolyRedPack@{i} Ge FA BA FB BB), ...
             PolyRedPackAdequate (LR lvl rec0 rec1) PA -> LR ... (PiRedTmEq PA)
  | LRU0   : forall Ge r l, TLlt tl0 lvl -> lvl_of l = tl0 ->     (* U at source lvl 0 *)
             LR lvl rec0 rec1 Ge (dU r l) (dU r l)
               (fun c d => has*has* { P : Type@{i0} & rec0 Ge (dEl c)(dEl d) P })
  | LRU1   : forall Ge r l, TLlt tl1 lvl -> lvl_of l = tl1 ->     (* U at source lvl 1 *)
             LR lvl rec0 rec1 Ge (dU r l) (dU r l)
               (fun c d => has*has* { P : Type@{i1} & rec1 Ge (dEl c)(dEl d) P }).
```

Universe constraints recorded by the kernel: `i0 < j0`, `i1 < j1` (LRpi/inductive
sizing per the lower relations once instantiated), `j0 <= i`, `j1 <= i` (the
`LRU0/LRU1` witnesses, at `j0`/`j1`, fit the current relation slot `i`), `i < j`.
No constraint forces `i0 = i1`, because nothing dispatches on the level value.

**B2. Build the tower with concrete instantiations (no `match`).**
```coq
Definition LRbot : RedRel := fun _ _ _ _ => False.   (* dummy for unused recK slots *)
Definition LR0@{...} : RedRel@{...} := LR tl0 LRbot  LRbot.   (* LRU0/LRU1 gated off *)
Definition LR1@{...} : RedRel@{...} := LR tl1 LR0    LRbot.   (* LRU0 -> LR0; LRU1 off *)
Definition LR2@{...} : RedRel@{...} := LR tl2 LR0    LR1.     (* LRU0 -> LR0; LRU1 -> LR1 *)
Definition RedTyEq Ge A B := { P & LR2 Ge A B P }.
```
Pin `LR0/LR1/LR2` with explicit `@{...}` so the ladder
`i_0 < j_0 <= i_1 < j_1 <= i_2 < j_2` is satisfied (each instantiation chooses the
`recK` slots' universes). `LRbot`'s universe is free (its constructorless witness
is never built — the `TLlt tlK lvl` guard is false at the bottom).

**B3. Cost / ripple (moderate, NOT 3x).** Still ONE inductive ⇒ ONE `LR_mut`
(now with two U motive cases `LRU0`/`LRU1` instead of one), ONE set of relation
defs, ONE escape, ONE irrelevance. The diffs vs today: (a) `LRU` splits into
`LRU0`/`LRU1` (extra case in every `match`/induction over `LR` — `LogRel2Ind`,
`LogRel2Lemmas`, `LogRel2Red`, `LogRel2Irr`); (b) `rec` becomes `rec0 rec1`
params; (c) the tower defs get explicit universe annotations. The PROOFS are
otherwise unchanged.

**Alternative (only if levels become unbounded / variadic):** `Acc`/well-founded
recursion over `TLlt` à la logrel-coq, giving each level its own universe via the
accessibility proof. Not worth it for a fixed 3-level tower — B1/B2 is simpler.

### Step 2 — PROTOTYPE FIRST (do not touch the green chain yet)
Before editing `LogRel2.v`, build a **minimal standalone scratch file**
(`WIP/UnivProto.v`) replicating only: `RedRel`, `LRPack`, a toy `PolyRedPack`
(domain pack + one codomain pack), and `LR` with just `LRnat`, `LRpi`, and the
universe case(s) — for Step 1B use the UNFOLDED encoding (params `rec0 rec1` +
split `LRU0`/`LRU1`, B1) and the `LR0/LR1/LR2` tower (B2); for Step 1A use the
2-level `LR0/LR1` tower with `rec1 := LR0`. Then verify, in this order:
1. it compiles with the chosen poly scheme;
2. **positivity still holds** (kernel accepts `LR`) — universes don't affect
   positivity, but confirm, especially after splitting `LRU`;
3. the decisive test — a TOY symmetry obligation typechecks: build a swapped pack
   whose DOMAIN is a universe, i.e. store an `LRU` witness into a domain
   `LRPack` field (the exact thing that fails today). For Step 1B also confirm
   the kernel did NOT force `i0 = i1` (`Print Universes Subgraph`);
4. `Print Universes Subgraph` shows the pack-field universe is now `>=` the
   witness universe at the top level (gap closed).
Only after (3) passes, port the annotations to the real `LogRel2.v`. The toy
`fun n => match n with O => A0@{a b} | _ => A1@{c d} end` snippet (Section 3) is
the fast canary for whether any residual `match`-on-level still collapses.

### Step 3 — port + re-green + re-attempt symmetry
Apply the validated annotations to `LogRel2.v`; rebuild `LogRel2Ind/Lemmas/Red/Irr`
(single-file `coqc`, green each before the next); then finish symmetry and the
remaining Ph2 (transport, renaming stability) and proceed to Ph4 PER laws.

---

## 5. Fallback (if the refactor is deferred)
`RedTmEq_irr` / `LR2_irrelevant` (proven, axiom-free) already give *membership*
transport between `RedTyEq` witnesses WITHOUT constructing packs. Several
downstream results (relating two reducibility proofs of the same type, transport
of term-conversion across irrelevant witnesses) can be built on irrelevance
alone and do NOT hit the universe wall. Push those first; defer anything that
must *construct a swapped pack* (true PER symmetry of the type relation, the
fundamental lemma) until the universe refactor lands.

## 6. Cross-checks / pitfalls
- The split `LRPack.u0 < RedRel.u1` is the tell-tale; after the fix
  `Print Universes Subgraph` should show pack-field = relation universe.
- `Strict Universe Declaration` is ON: every `@{...}` binder must list ALL
  universes used in that definition (this bit us already — see git history of
  `LogRel2PER.v`).
- `inversion` on `LR` at concrete indices is axiom-free here (verified in
  `LogRel2Irr.v`); the poly change should not affect that.
- Keep `TLlt_pirr` (axiom-free, in `LogRel2Irr.v`) — still needed for `LRU`.
