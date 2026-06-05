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

2. **Make the lower-level `rec` return relations at a STRICTLY SMALLER
   universe.** `rec` at level `l` returns `RedRel@{i' j'}` with `i' < i` and
   `j' <= i` (so the witness `{P : Type@{i'} & rec..P : Type@{j'}}` lands at
   `<= i`, fitting the current relation slot). This is what the monomorphic
   single-`RedRel` `rec` cannot do.

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

`rec2`'s `match` returns a single `RedRel@{i j}`, so **`LR0` and `LR1` are forced
to the SAME universe**. But the ladder needs `LR1` to reference `LR0` at a
strictly lower universe (`k_0 <= i_1`, `i_0 < k_0`). Same-universe `LR0=LR1`
plus `LR1` referencing `LR0` gives `k_0 <= i_1 = i_0 < k_0` — contradiction.
So **you cannot universe-polymorphize the tower as-is**; the multi-branch `match`
in `rec2` is incompatible with the strict ladder.

logrel-coq avoids this by having only **two** `TypeLevel`s (`zero`, `one`) and a
`rec` for `one` that returns the `zero` relation as a *single* thing (no
multi-branch match), with the WORKING relation being the top object level
`LR one` (not a third "ambient" level). Our `tl0/tl1/tl2` with `tl2` ambient and
`RedTyEq := {P & LR2 ..}` is the source of the collapse.

---

## 4. Recommended plan

### Step 0 — answer the gating question (cheap, do first)
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

### Step 1B — keep three levels (only if Step 0 says you must)
The multi-branch `rec2` cannot be poly'd directly. Options, increasing effort:
- Replace the finite tower with **`Acc`/well-founded recursion** over `TLlt`
  (logrel-coq's actual technique): define `LR` by recursion on a `TLlt`-accessibility
  proof so each level genuinely gets its own universe and the witness references
  exactly the next level down. This dissolves the `match` collapse.
- Or split `LR` into per-level **named inductives** `LR0_ind`, `LR1_ind`,
  `LR2_ind` at explicitly ordered universes, with each `LRU` case referencing the
  concrete lower inductive (no universe-shared `match`). Verbose but mechanical.

### Step 2 — PROTOTYPE FIRST (do not touch the green chain yet)
Before editing `LogRel2.v`, build a **minimal standalone scratch file**
(`WIP/UnivProto.v`) replicating only: `RedRel`, `LRPack`, a toy `PolyRedPack`
(domain pack + one codomain pack), `LR` with just `LRnat`, `LRpi`, `LRU`, and the
tower. Then verify, in this order:
1. it compiles with the poly scheme of Step 1A/1B;
2. **positivity still holds** (kernel accepts `LR`) — universes don't affect
   positivity, but confirm;
3. a TOY symmetry obligation typechecks: build a swapped pack whose domain is a
   universe (`LRU` witness stored into a domain `LRPack` field) — this is the
   exact thing that fails today; if it goes through, the scheme is correct;
4. `Print Universes Subgraph` shows `i_top` is now `>=` the witness universe.
Only after (3) passes, port the annotations to the real `LogRel2.v`.

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
