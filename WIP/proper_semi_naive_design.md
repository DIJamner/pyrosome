# Proper semi-naive evaluation for `process_erule` — design / prep doc

Branch: `proper-semi-naive` (off `egraph-dedup-writes`, which carries Phase 1
runtime dedup + Phase 2 soundness, commit `cab9088`). This is the **deeper
change** that replaces the post-hoc dedup hack with a principled delta
decomposition so each new match is generated exactly once.

Status: **NOT STARTED — this is a prep doc for the next session.** Everything
below is design; no code/proof has been written on this branch yet.

---

## 0. Background: where we are

Phase 1 (`80c8afd`) found that on the positive engine the **writes**
(`exec_write`), not the join, dominate a saturation iteration (~92%), and that
the semi-naive frontier loop double-counts matches (n=6 monoid: 1089 total
matches, only 299 distinct → ~73% redundant). Phase 1 dedups assignments across
frontiers before `exec_write` (idempotent on repeats), cutting sat_eq ~0.130s →
~0.030s. Phase 2 (`cab9088`) updated the soundness proofs; `egraph_sound` stays
axiom-free.

Phase 1 is a **collapse-after-the-fact** fix: it still runs the join for every
frontier choice and then throws away duplicate keys. Proper semi-naive instead
**never generates the duplicates**, by giving each clause one of three roles per
frontier position.

---

## 1. The mechanism today (full / frontier dichotomy)

Per-clause trie data (`Defs.v`):

- `db := symbol_map (idx_trie db_entry)`; `db_entry := { entry_epoch; entry_value; out_args }`.
  Each `(symbol f, args)` has **one** entry with **one** `entry_epoch`.
- `build_tries_for_symbol current_epoch q_clauses tbl : idx_map (idx_trie unit * idx_trie unit)`
  produces, per clause id `n`, a pair `(full, frontier)`:
  - `full`  = every assignment matching the clause (key = projected assignment, val = tt).
  - `frontier` = assignments matched via an entry with `entry_epoch == current_epoch`
    (the **NEW**/delta set). Built by `if eqb epoch current_epoch then put frontier ... else frontier`.
  So `frontier ⊆ full`, and (since each args has one entry/epoch) `full` partitions
  into `frontier` (epoch = current) and "the rest" (epoch ≠ current = **OLD**).
- `trie_of_clause query_vars db_tries frontier_n (Build_erule_query_ptr f n clause_vars)`
  selects, for this clause, `frontier` **iff** `eqb n frontier_n`, else `full`.
- `process_erule` (post-Phase-1) iterates `frontier_n` over `seq 0 nclauses`
  (mapped through `idx_of_nat`), unions all frontiers' intersection keys into one
  deduping `idx_trie`, and `exec_write`s each unique key once.

Double-count cause: a match where clauses `j1, j2` are both NEW is produced at
`frontier_n = j1` (frontier∩full∩…) **and** at `frontier_n = j2`.

### ⚠ Critical wrinkle: `n` is NOT a position

`compile_query_clause` (`QueryOpt.v:998`) sets the ptr's id via
`hash_clause compiled_clause`, i.e. a **per-symbol hash-cons id**
(`map_inverse_get`, ids 0,1,2… *per symbol* `f`). So:

- The clause id `n` is **not** the clause's index in `query_clause_ptrs`.
- `eqb n frontier_n` can select the frontier trie for the *wrong* clause, for
  *several* clauses (same per-symbol id across symbols), or for *none*.
- This is **sound regardless** (frontier ⊆ full ⇒ any selection still yields real
  matches), which is exactly why the current scheme gets away with it. There is a
  `TODO: frontier_n a hack` at `Defs.v:815`.

Proper semi-naive needs a genuine **total order on the query clauses** and each
clause's **position** in it. The ne-list order of `query_clause_ptrs` is the
obvious choice. **This is the central restructuring**, not the OLD trie.

---

## 2. Target: OLD / NEW / TOTAL trichotomy, min-index assignment

Query `Q = C_0 ∧ … ∧ C_{k-1}` (positions = ne-list order). Per clause define
three key-sets:

- `NEW_j`   = assignments matching `C_j` via an entry with `epoch == current`.
- `OLD_j`   = assignments matching `C_j` via an entry with `epoch ≠ current` (= `< current`).
- `TOTAL_j` = `OLD_j ∪ NEW_j` (= today's `full`).

Frontier `i` (for `i = 0..k-1`) intersects:

```
OLD_0 ∧ … ∧ OLD_{i-1} ∧ NEW_i ∧ TOTAL_{i+1} ∧ … ∧ TOTAL_{k-1}
```

**Exactly-once:** for any match, let `S = { j : C_j matched by a NEW entry }`.
A "new match" has `S ≠ ∅`. The decomposition counts it at `i = min S` and only
there: `C_i` is NEW ✓; for `j < i`, `j ∉ S` so `C_j` is OLD ✓; for `j > i`,
TOTAL covers either ✓. Every other `i'` fails (`i' < min S` ⇒ some `j ≤ i'` in
the OLD-prefix is actually NEW; `i' > min S` and `i' ∈ S` ⇒ fine but `min S`'s
OLD-prefix already excludes it — only `min S` has the full OLD prefix matching).
⇒ **no dedup trie needed**; `process_erule` reverts to one `exec_write` pass per
frontier (like the pre-dedup shape) but with non-overlapping key sets.

Note epochs only increase and entries are stamped at creation, so every entry
has `epoch ≤ current`; thus `OLD = (epoch ≠ current) = (epoch < current)` — no
`<` on `idx` is required, plain disequality suffices.

---

## 3. Runtime changes (`src/Utils/EGraph/Defs.v`)

1. **`build_tries_for_symbol`**: also accumulate `OLD`. Cleanest is a **triple**
   `(full, new, old)` (rename `frontier`→`new`). `upd_trie_pair`:
   ```
   full'        := put full assignment tt;
   if eqb epoch current_epoch then (full', put new assignment tt, old)
                              else (full', new,                    put old assignment tt)
   ```
   Result type `idx_map (idx_trie unit * idx_trie unit * idx_trie unit)`.
   (Alternative: keep `(full, new)` and compute `old` as a trie key-difference in
   `trie_of_clause`; rejected — O(n) per lookup and an extra map op to verify.)

2. **Position-indexed iteration.** Replace the id-based `frontier_n` with a
   POSITION. Options:
   - (a) Pre-zip: build `indexed_ptrs : ne_list (nat * erule_query_ptr)` once
     (`ne_combine (seq 0 k) query_clause_ptrs`), and have the new
     `trie_of_clause_sn frontier_pos (pos, ptr)` compare `pos ?= frontier_pos`
     (`<` / `=` / `>`) to pick `old`/`new`/`full`. This keeps the per-clause
     selection a pure function of position, which the soundness proof wants.
   - (b) Thread an index through `ne_map` (need an indexed `ne_map`).
   Prefer (a). Add `ne_combine` / indexed map helpers to `Utils` if absent.

3. **New `trie_of_clause_sn`** (semi-naive): like `trie_of_clause` but takes the
   clause's position and selects `old` (pos < fn) / `new` (pos = fn) / `full`
   (pos > fn). Keep the old `trie_of_clause` (used by `process_erule'` and its
   still-compiling proof) and `trie_of_clause'` (diagnostic `run_query`) intact.

4. **`process_erule`**: drop the dedup trie; for each frontier position
   `i ∈ seq 0 k`, intersect the position-indexed tries and `exec_write` each key.
   I.e. essentially the **pre-dedup** `list_Miter (process_erule'_sn …) (seq 0 k)`
   with `process_erule'_sn` using `trie_of_clause_sn`. `erule_frontier_keys` can
   be retired or kept for benches.

Keep changes **additive** where cheap so the existing (now-passing) lemmas about
`trie_of_clause` / `process_erule'` don't need editing.

---

## 4. Proof changes — *soundness only*, and it's small

**KEY INSIGHT: `egraph_sound` needs soundness (no spurious writes), NOT
completeness/exactly-once.** Exactly-once is a *performance* property. So the
trichotomy needs only: *every key produced still corresponds to a real match*.

The whole soundness pipeline already reduces a trie hit to a db atom via
`build_tries_sound`, with `frontier`/`full` both routed through it
(`clause_ptr_atom_in_db`, `Semantics.v:915`):

- `full` hit → `build_tries_sound` (direct).
- `frontier` hit → `build_tries_frontier_subset` (frontier ⊆ full) → `build_tries_sound`.

`OLD ⊆ full` identically, so:

1. Add `build_tries_for_symbol_old_subset` + `build_tries_old_subset`
   (copy `*_frontier_subset`, `Semantics.v:807`/`888`, swap the `new` branch for
   the `old` branch). With the `(full,new,old)` triple, `old ⊆ full` is the same
   fold invariant.
2. Generalize `clause_ptr_atom_in_db` to the 3-way selection: a hit in
   `old`/`new`/`full` all reduce to `build_tries_sound` on `full` via the subset
   lemmas. (If `build_tries`'s result type changes to the triple, update the few
   destructs `[ [full new old] | ]`.)
3. **`process_erule_sound`**: the soundness core
   **`exec_write_loop_sound` (already on this branch, `SemanticsProcessErule.v`)
   is exactly the right tool** — it's frontier-parametric and consumes, per key,
   an existential "this key's per-clause projections hit *some* selection of
   tries that are each sound". Re-wire its per-frontier premise to the new
   `trie_of_clause_sn` selection. Because each clause trie (old/new/full) hit ⇒
   real db atom (step 2), `query_atoms_sound` goes through unchanged (its
   conclusion is selection-independent). Expect `process_erule_sound`'s proof to
   look like the pre-dedup per-frontier induction calling `exec_write_loop_sound`
   (or `process_erule'_sound`-shaped), NOT the dedup membership argument.
4. `fold_put_keys_inner/src` become **dead** (no dedup trie) — delete with the
   `Maps` import if nothing else needs it.

What does **not** need touching: `exec_write_sound`, `query_atoms_sound`,
`a_q_wf_query_vars`, `query_clause_ptr_sound`, the saturate chain signature
(`process_erule_sound` keeps its statement), `egraph_sound` wiring.

**Risk note:** if the runtime switches `query_clause_ptrs` iteration to a
position-indexed structure, the *coverage* hypotheses fed into
`process_erule_sound` from `build_rule_set` (the `Hwf`/`Hcov`/`Hsli` family in
`SemanticsSaturate`/`QueryOptSound`) must still be derivable for the new
per-position tries. Check `QueryOptSound.v` discharges of the `Hlen_sig`/`Hsli`
premises — they currently quantify over an arbitrary `frontier_n : idx`; the new
ones quantify over a position `i : nat`. This is the most likely place real
proof work hides. Scope it first.

---

## 5. Suggested next-session order

1. **Resolve the position question** (Section 3.2): add `ne_combine`/indexed map
   helper; settle `trie_of_clause_sn`'s signature. Smallest commit, unblocks all.
2. Runtime: `(full,new,old)` triple in `build_tries_for_symbol` + `build_tries`;
   `trie_of_clause_sn`; rewrite `process_erule`. Build `Defs.vo` only.
3. **Benchmark first** (WIP/PerfBench.v, positive, monoid n=6): confirm
   correctness (`s_check`/`sat_eq`/`easy_check`) and measure. NB Phase 1 already
   captured the *write* win; proper semi-naive's marginal runtime gain is mainly
   a smaller join (OLD-prefixes) + no dedup-trie build — **could be modest**.
   Decide if it's worth the proof cost before doing the proofs. (Honest framing
   for the user; see [[project_egraph_perf]].)
4. Proofs: `*_old_subset`, generalize `clause_ptr_atom_in_db`, re-wire
   `process_erule_sound` via `exec_write_loop_sound`; chase `QueryOptSound`
   `Hsli`/`Hlen_sig` discharges. Build the chain to `Automation.vo`.
5. `Print Assumptions egraph_sound` = "Closed under the global context"
   (scratch coqc with the four `-R` flags; the MCP coqc doesn't read `_CoqProject`,
   and MCP `rocq_start`/`rocq_assumptions` choke on this file's sections — use
   `make -f Makefile.coq <ABSOLUTE path>.vo`).

---

## 6. File/line index (as of `cab9088`)

- `Defs.v:50` `db_entry`; `:511` `build_tries_for_symbol`; `:533` `build_tries`;
  `:558` `trie_of_clause` (semi-naive); `:574` `process_erule'`; `:585`
  `erule_frontier_keys`; `:606` `process_erule`; `:792` `trie_of_clause'`
  (diagnostic); `:811` `run_query`.
- `QueryOpt.v:998` `compile_query_clause` (the `hash_clause`/`n` source).
- `Semantics.v:659` `build_tries_for_symbol_sound`; `:766` `build_tries_sound`;
  `:807` `*_frontier_subset`; `:888` `build_tries_frontier_subset`; `:915`
  `clause_ptr_atom_in_db`.
- `SemanticsProcessErule.v`: `exec_write_loop_sound` (soundness core, reusable),
  `fold_put_keys_inner/src` (dedup-only, will be dead), `process_erule_sound`.
- `SemanticsSaturate.v:157` consumes `process_erule`; `:167` `process_erule_sound`.
- Related memory: [[project_egraph_perf]], [[project_egraph_sound]].
