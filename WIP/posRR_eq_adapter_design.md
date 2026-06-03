# posRR reversed-eq adapter — refactor design (S69)

Goal: produce `central_obligation_term_eq_rev` and `central_obligation_sort_eq_rev`
in AdapterGlue.v `Section Adapter`, giving
`model_satisfies_rule (lang_model l) (optimize_sequent (rule_to_log_seq name (term_eq_rule c e2 e1 t)) rf)`
from the ORIGINAL `In (name, term_eq_rule c e1 e2 t) l` (the reversed rule ∉ l).
These feed the posRR analog of `central_msr_seqs` (next step, not in this task).

## Key fact (already established)
The whole eq adapter chain depends on `Hin` for ONLY two things:
  - symmetric wf facts: `wf_ctx l c`, `wf_term l c e1 t`, `wf_term l c e2 t` (all available from the
    original Hin regardless of side);
  - the equation, used at EXACTLY ONE spot: `conclusion_egraph_sound_eq` line ~1993
    (`ConclSemantic.term_eq_concl`).
`eq_assumption_inversion` (AddCtxInversion.v:1197) is ALREADY Hin-free (takes Hwfc/Hwfe1).
`concl_clauses_sound_eq` does NOT use Hin or Hsg at all.

`term_eq_concl     n c e1 e2 t : In … -> forall sg, wf_subst l [] sg c -> eq_term l [] t[/sg/] e1[/sg/] e2[/sg/]`
`term_eq_concl_rev n c e1 e2 t : In … -> forall sg, wf_subst l [] sg c -> eq_term l [] t[/sg/] e2[/sg/] e1[/sg/]`
(ConclSemantic.v:77/115). Sort mirrors at :93/125 (eq_sort, no `t`).

## The refactor (TERM_EQ chain). Replace `(Hin)` with the hyps listed; bodies barely change.

New hypotheses (same NAMES as the existing local asserts so bodies keep working):
  Hwfc  : wf_ctx l c
  Hwfe1 : wf_term l c e1 t
  Hwfe2 : wf_term l c e2 t
  Heqf  : forall sg0, wf_subst l [] sg0 c -> eq_term l [] t[/sg0/] e1[/sg0/] e2[/sg0/]

1. `conclusion_egraph_sound_eq name c e1 e2 t (sg) …`  (line ~1915)
   - sig: drop `Hin`, add `Hwfc Hwfe1 Hwfe2 Heqf` (keep `Hsg` last as before).
   - body: DELETE the `pose proof (rule_in_wf … Hin) … invert_wf_term_eq_rule … destruct Hr as (Hwfc & Hwfe1 & Hwfe2 & _)` block (~1942-1944) — those names are now params.
   - body: at ~1993 replace `pose proof (@ConclSemantic.term_eq_concl V V_Eqb l Hwf name c e1 e2 t Hin sg Hsg) as Heq_e1e2.` with `pose proof (Heqf sg Hsg) as Heq_e1e2.`

2. `conclusion_i2_sound_assum_eq` (~2049)
   - sig: drop `Hin`, add `Hwfc Hwfe1 Hwfe2 Heqf`.
   - body ~2068: pass them to `conclusion_egraph_sound_eq name c e1 e2 t sg Hwfc Hwfe1 Hwfe2 Heqf Hsg`.

3. `concl_clauses_sound_eq` (~2080)
   - sig: DROP both `Hin` and `Hsg` (unused). Body unchanged.

4. `eq_assum_ids_covered` (~2153)
   - sig: drop `Hin`, add `Hwfc Hwfe1`.
   - body: DELETE the two rule_in_wf derivation blocks (~2174-2179).

5. `Hcover_concl_eq` (~2312)
   - sig: drop `Hin`, add `Hwfc Hwfe1`.
   - body ~2345: `eq_assum_ids_covered name c e1 e2 t Hwfc Hwfe1 Hsucc k`.

6. `term_eq_rule_concl_obligation` (~2386)
   - sig: drop `Hin`, add `Hwfc Hwfe1 Hwfe2 Heqf`.
   - body: DELETE the Hwfc/Hwfe1 derivation asserts (~2418-2423).
   - update calls: conclusion_i2_sound_assum_eq → `… sg Hwfc Hwfe1 Hwfe2 Heqf Hsg`;
     concl_clauses_sound_eq → `concl_clauses_sound_eq name c e1 e2 t i2 Hsnd_concl_i2` (dropped Hin/Hsg);
     Hcover_concl_eq → `… a i2 sg Hwfc Hwfe1 Hsg Hsnd_a Hconf Hsucc …` (match new arg order).

7. `model_satisfies_rule_adapter_term_eq` (~2469)
   - sig: drop `Hin`, add `Hwfc Hwfe1 Hwfe2 Heqf`.
   - body: DELETE the Hwfc/Hwfe1 derivation asserts (~2494-2499).
   - call term_eq_rule_concl_obligation (~2546): replace `Hin` with `Hwfc Hwfe1 Hwfe2 Heqf` in its arg slot.

8. `central_obligation_term_eq` (~2551): RENAME to `central_obligation_term_eq_core`.
   - sig: drop `Hin`, add `Hwfc Hwfe1 Hwfe2 Heqf` (keep `Hsucc`).
   - body: final bullet `exact (model_satisfies_rule_adapter_term_eq name c e1 e2 t Hwfc Hwfe1 Hwfe2 Heqf Hsucc).`
     (the `apply optimize_sequent_forward_atoms …` preamble + first two bullets are unchanged — they do not use Hin.)

9. NEW `central_obligation_term_eq` (forward wrapper, SAME public sig as the old one: `name c e1 e2 t (Hin) (Hsucc)`):
   ```
   Proof.
     assert (Hwfc  : wf_ctx l c)        by (pose proof (rule_in_wf _ _ Hwf Hin) as Hr; rewrite app_nil_r in Hr; rewrite invert_wf_term_eq_rule in Hr; destruct Hr as (h&_&_&_); exact h).
     assert (Hwfe1 : wf_term l c e1 t)  by (pose proof (rule_in_wf _ _ Hwf Hin) as Hr; rewrite app_nil_r in Hr; rewrite invert_wf_term_eq_rule in Hr; destruct Hr as (_&h&_&_); exact h).
     assert (Hwfe2 : wf_term l c e2 t)  by (pose proof (rule_in_wf _ _ Hwf Hin) as Hr; rewrite app_nil_r in Hr; rewrite invert_wf_term_eq_rule in Hr; destruct Hr as (_&_&h&_); exact h).
     exact (central_obligation_term_eq_core name c e1 e2 t Hwfc Hwfe1 Hwfe2
              (@ConclSemantic.term_eq_concl V V_Eqb l Hwf name c e1 e2 t Hin) Hsucc).
   Qed.
   ```
   (`term_eq_concl … Hin : forall sg, wf_subst … -> eq_term … e1 e2` = Heqf exactly.)

10. NEW `central_obligation_term_eq_rev name c e1 e2 t (Hin : In (name, term_eq_rule c e1 e2 t) l)`
    with `Hsucc` about the egraph that opens **e2** first:
    ```
    (Hsucc : fst (rebuild rf (snd (add_open_term succ sort_of l false false
              (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
              e2
              (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))) = Result.Success tt)
    : model_satisfies_rule V V V_map (lang_model l)
        (QueryOpt.optimize_sequent V V_Eqb succ V_default V V_map V_map V_trie
           (rule_to_log_seq name (term_eq_rule c e2 e1 t)) rf).
    Proof.
      assert (Hwfc  : wf_ctx l c)        by (… destruct Hr as (h&_&_&_); exact h).
      assert (Hwfe1 : wf_term l c e1 t)  by (… destruct Hr as (_&h&_&_); exact h).
      assert (Hwfe2 : wf_term l c e2 t)  by (… destruct Hr as (_&_&h&_); exact h).
      exact (central_obligation_term_eq_core name c e2 e1 t Hwfc Hwfe2 Hwfe1
               (@ConclSemantic.term_eq_concl_rev V V_Eqb l Hwf name c e1 e2 t Hin) Hsucc).
    Qed.
    ```
    Note the SWAP: core is called at `(e2, e1)`; its `Hwfe1` slot = wf of its first term (e2) = Hwfe2,
    its `Hwfe2` slot = Hwfe1; `term_eq_concl_rev … Hin : forall sg, … -> eq_term l [] t[/sg/] e2[/sg/] e1[/sg/]`
    = the core's Heqf at `(e2,e1)`. Conclusion is the reversed rule's optimize_sequent — exactly what posRR needs.

## SORT_EQ chain — identical mirror.
Lemmas: conclusion_egraph_sound_sort_eq (~2676), conclusion_i2_sound_assum_sort_eq (~2799),
concl_clauses_sound_sort_eq (~2830, drop Hin/Hsg), eq_sort_assum_ids_covered (~2898),
Hcover_concl_sort_eq (~3049), sort_eq_rule_concl_obligation (~3123),
model_satisfies_rule_adapter_sort_eq (~3206), central_obligation_sort_eq (~3283 → _core + wrappers).
Hyps: Hwfc : wf_ctx l c; Hwft1 : wf_sort l c t1; Hwft2 : wf_sort l c t2;
      Heqf : forall sg0, wf_subst l [] sg0 c -> eq_sort l [] t1[/sg0/] t2[/sg0/].
Use `invert_wf_sort_eq_rule` (3-way destruct: (Hc & Ht1 & Ht2)), `ConclSemantic.sort_eq_concl` /
`sort_eq_concl_rev` (NO `t` arg: `@ConclSemantic.sort_eq_concl V V_Eqb l Hwf name c t1 t2 Hin`).
The eq spot is `conclusion_egraph_sound_sort_eq` ~2747.
central_obligation_sort_eq_rev: core at `(t2,t1)`, Hsucc about add_open_sort of t2, conclusion uses
`sort_eq_rule c t2 t1`; eq from `sort_eq_concl_rev`.

## Verification
- After EACH lemma edit, re-check it (rocq-MCP rocq_verify / step) — the bodies are nearly unchanged so
  failures localize to arg-order mismatches in the updated calls.
- Final: `rocq_compile_file` (or make) AdapterGlue.vo must build with 0 admits.
- `rocq_assumptions` on `central_obligation_term_eq_rev` and `central_obligation_sort_eq_rev` — must be
  Closed / axiom-free (only the section's standard context).
- Do NOT commit (Opus will review + commit). Report any signature/arg-order surprises.
