# egraph_sound — accurate status & remaining plan (rewritten 2026-06-02)

> This file used to be a multi-session palimpsest (sessions 45–48b) framed
> around "(II) conclusion-construction" being the WALL: `term/sort_rule_concl_obligation`
> Admitted, `Hcover` an unproven ~250–450 LoC coverage induction, `assum_db_frame ~400 LoC`.
> **That wall has been scaled.** The old narrative is preserved compressed at the bottom
> ("HISTORY"); read the top for the real current frontier.

## VERIFIED CURRENT STATE (via `Print Assumptions`, .vo's up to date)

`egraph_sound` (Automation.v:402, Qed) rests on **EXACTLY ONE axiom**:
`egraph_reducing_equal'_to_pos` — and that lemma is `Admitted` *solely* because of a
**single internal `admit`** at Automation.v:364, the `schedule_sound l' sched` conjunct.

Everything else on the path is proven, 0-axiom ("Closed under the global context"):
- `egraph_reducing_cong_sound` (ReducingCong.v) — PROVEN (memory's "two axioms" is stale; it's one).
- `optimize_sequent_forward_atoms` (QueryOptSound.v:~7461) — PROVEN. The forward direction
  source-rule ⇒ optimized-rule soundness; the form schedule_sound actually consumes.
- `term_rule_concl_obligation` + `sort_rule_concl_obligation` (AdapterGlue.v:1129/1622) — PROVEN.
  The wf-rule ⇒ `model_satisfies_rule_closed (lang_model l) (rule_to_log_rule … rule)` adapter.
- `compiled_rules_run1iter_rule_hyps` (QueryOptSound.v:6449) — PROVEN. The schedule_sound
  assembly hub; takes per-rule optimized soundness (line 6457) and yields `run1iter_rule_hyps`.
- `pt_spaced_intersect_correct` (PosListMapIntersectSpec.v:3352) — PROVEN.

## TWO STRUCTURAL FACTS THAT RESHAPE THE PLAN

1. **AdapterGlue.v is fully proven (0 admits) but ORPHANED** — nothing in `src/` imports it
   (only its own `.glob`/`.aux`). The proven obligations are not yet wired into the
   egraph_sound cone. This is the real gap: *wiring*, not math.

2. **`optimize_sequent_forward` / `_reverse` / `_equiv` (6 admits, QueryOptSound.v:~7706+) are
   OFF-PATH.** Confirmed absent from `Print Assumptions egraph_sound`; consumed by nothing
   outside their own mutual island. They are a separate general-equivalence deliverable.
   A quarantine banner now sits above them in QueryOptSound.v; the file header was corrected
   (it used to advertise `optimize_sequent_equiv` as the "Main theorem"). **Do not work these
   for egraph_sound.**

## REMAINING WORK (verified against the current S62 frontier)

> NOTE: R5 ("open→closed contract") is **already DONE** — the ⊆-confinement premise is baked
> directly into `model_satisfies_rule` (QueryOptSound.v:166, second `has_key → In forall_vars`
> clause, added S57). The adapter and `optimize_sequent_forward_atoms` both speak this confined
> predicate and compose directly. Earlier drafts of this doc listed R5 as remaining; ignore that.

The single `schedule_sound` admit (Automation.v:364) = for the two built rule_sets,
`schedule_sound_real` = `forall (n,rs) ∈ sched, rs_saturation_hyps lang_model rs`. The
`fresh sort_of l'` conjunct is closed (S62, `rename_lang_fresh_xH`). The rest decomposes into:

**(R1) eq-rule adapters — NOT done.** Only `model_satisfies_rule_adapter_term`/`_sort`
(AdapterGlue.v:1200/1693) exist. `posR`/`posRR` contain `term_eq_rule`/`sort_eq_rule` (and `posRR`'s
are *reversed* eq-rules, valid by symmetry not membership), whose `rule_to_log_rule` conclusion is
`union x1 x2`. A fresh multi-lemma effort mirroring the term/sort adapters: assumption side recovers
`sg` from ctx + e1's representation; conclusion needs `e1[/sg/] = e2[/sg/]` (domain_eq) from the
rule's `eq_term`/`eq_sort` wf. **This gates the central bridge (R3) for eq rules.**

**(R2) const-rule keystone — partially done.** `compile_rule` takes the `inr (const_rule)` branch
for empty-assumption (ground-ctx) rules. `const_rule_sound` + `process_const_rules_sound` exist
(SemanticsExecConst.v:383/391), but the connecting keystone `compile_rule_inr_const_sound`
(`model_satisfies_rule … ⇒ const_rule_sound a_src`) does NOT exist yet. Discharges
`rs_saturation_hyps`' first (const) conjunct.

**(R3) central bridge — gates DONE, assembly remains.** Per-rule
`model_satisfies_rule (optimize_sequent (rule_to_log_rule … rule))` = adapter (R1 for eq; term/sort
done) ∘ `optimize_sequent_forward_atoms` (proven, parametric fuel). Its gates `Hassum`
(definitional) + `Huniq` (`db_to_atoms_NoDup_fn_args`, QueryOptSound.v:4502) are DONE (S62).
Remaining: discharge the adapter's per-rule `Hsucc` rebuild-success side condition (a fact about
the actual run), and lift to all rules of `posX` via `incl` + ctx membership (reversed `posRR` rules
via the symmetry route).

**(R4) trie conjuncts 9,10.** The two `Hsli` trie-hit hyps of `compiled_rules_run1iter_rule_hyps`:
`fpt_spaced_intersect_inputs_hit` (FullPosTrieConv.v, proven) + `pt_spaced_intersect_correct`
(proven) + establishing their depth/`combined_bools`/`wf_tries` preconds from build_tries output.
Trie-lawfulness adjacent (see Secondary, below).

**(R5-assemble) wire Automation.v:364.** `rs_saturation_hyps (build_rule_set …)` =
const conjunct (R2) + `compiled_rules_run1iter_rule_hyps ∘ in_compiled_rules` (R3 + R4) over the
2-entry schedule + `fresh sort_of` (done). Then discharge the admit for both rule_sets.

ORDER: R1 (eq-adapters, gates R3) → R2 (const) → R3 (central, needs R1+Hsucc) → R4 (trie) →
assemble. After assembly, `Print Assumptions egraph_sound` should be "Closed under the global
context". The live, blow-by-blow frontier is tracked in the project memory `project-egraph-sound`
(maintained per session); this doc is a snapshot.

## SECONDARY / SEPARABLE — the trie endgame
`pt_spaced_intersect_correct` is already proven; the `fpt_to_pt_get` / unify-tries /
depth-invariant cluster exists to make the *fattened DB trie* `fpt_spaced_intersect` inherit it.
This subtree is currently short-circuited behind the one `schedule_sound` admit, so it does NOT
appear in `egraph_sound`'s assumptions today. **OPEN QUESTION worth checking before more trie
work:** can the positive egraph instantiation point at the already-proven `pt` path instead of
`fpt`? If yes, that whole endgame (and several thrashing memos) shrinks. If `fpt` is genuinely
forced by DB-table `map.ok`, keep it — but treat it as a separate subproject, not part of W1/W2.

---

## HISTORY (compressed — the scaled wall)
Sessions 45–48b drove the conclusion-construction obligations from Admitted to proven:
- S45: `all_clause_sound_setoid`/`list_Mmap_get_setoid` (deq-transfer linchpin); the open-`a`
  contract is genuinely false ⇒ the `model_satisfies_rule_closed` (set_eq) realignment (R5).
- S46: `atom_tree_deq`/`atom_tree_sort_deq`/`term_concl_construct` (R3/R4 core, putmany plumbing).
- S47: `assumption_ids_agree` (agreement engine, Hcover decoupled from confinement);
  `add_ctx_readback_eF` (A1).
- S48: inner coverage engine `atom_node` + `atom_node_covered`.
- S48b: clause-restricted reframe — collapsed the coverage obligation to the proven
  `Hcover_concl_term` (no full add_ctx exhaustiveness induction needed).
Net: `Hcover_concl_term`, `term_rule_concl_obligation`, `sort_rule_concl_obligation` and their
mirrors are now proven 0-axiom Lemmas in AdapterGlue.v. The "FRAME / assum_db_frame ~400 LoC
exhaustiveness induction" the older drafts planned was avoided.
