# (II) conclusion-construction design — term_rule_concl_obligation / sort_rule_concl_obligation

> ## STATUS AFTER SESSION 47 (read this first)
> All assembly pieces for `term_rule_concl_obligation` are 0-axiom DONE except TWO:
>  1. **Hcover (coverage)** — the only remaining MATH. `assumption_ids_agree` (DONE) reduces
>     Hagree to: every id in dom(a)∩dom(i2) carries an atom_tree/atom_tree_sort. Proving this
>     needs (i) R5 confinement so dom(a) ⊆ forall_vars(e_assum atoms), and (ii) a coverage fact
>     "every id in e_assum's atoms is a readback root". DECISION PENDING — option A (full add_ctx
>     coverage induction, ~300 LoC, mirror add_ctx_readback Theorems.v:5557) vs option B (weaken
>     all_clause_sound_setoid + term_concl_construct to clause-var-restricted compat ⇒ only need
>     coverage for conclusion-clause-vars = x' leaves [trivial at_var] + shared sort rets [need
>     atom_tree_sort + hash-cons identification]; avoids the big induction but needs add_open_term
>     output characterization). **Resolve A-vs-B before delegating.**
>  2. **R5 (contract)** — repoint the proven bridge `optimize_sequent_forward_atoms`
>     (QueryOptSound.v:5306) hypothesis from open `model_satisfies_rule` (QueryOptSound.v:160,
>     has_key) to a new `model_satisfies_rule_closed` (set_eq), add confinement premise to the
>     two `*_rule_concl_obligation`s + adapters. a_src in the bridge is already confined (pullback).
>     Risky (touches proven 0-axiom file) — do LAST.
> DONE 0-axiom in AdapterGlue.v: assumption_ids_agree, egraph_atoms_sound, conclusion_i2_sound_assum
> (+strengthened conclusion_egraph_sound), leaf_agree, term_concl_construct, concl_clauses_sound_term,
> conclusion_egraph_sound, assumption_egraph_sound, atom_tree_deq/atom_tree_sort_deq/args_deq,
> all_clause_sound_setoid. Then SORT mirror of everything. The two obligations remain `Admitted`.


Target file: `src/Pyrosome/Tools/EGraph/AdapterGlue.v` (two `Admitted` obligations).
Goal of each obligation: given `sg : wf_subst l [] sg c`, `Hmapfst`, `Hfaith` (the
faithfulness output of `add_ctx_inversion` relating the query assignment `a` to the
assumption-egraph readback ids), and `Hin`, produce
`exists a', map.extends a' a /\ all (clause_sound_for_model (lang_model l) a') (seq_conclusions (rule_to_log_rule ... (term_rule c args t)))`.

## PROVEN TEMPLATE = `optimize_sequent_forward_atoms` (QueryOptSound.v:5306-5505)
This is the structural blueprint. It proves `model_satisfies_rule m s -> model_satisfies_rule m (optimize_sequent s)`.
Read 5461-5504 for the endgame. Key moves we must mirror:

1. Final witness `a' := map.putmany i_concl a` (given `a` WINS).
   - `Hext_final : map.extends (putmany i_concl a) a` is FREE via `Properties.map.get_putmany_right`.
2. The real obligation: `Hagree : map.extends (putmany i_concl a) i_concl`, i.e. on every id in
   `dom(i_concl)`, `a` AGREES with `i_concl`. Discharged via a DOMAIN-PROVENANCE lemma
   (`Hdom_c`/`Hdom_e1`): every `i_concl`-domain key is threaded from `a`. Then on overlap
   `a(k) = i_concl(k)` by construction (template: pullback + renaming `congruence`).
3. Conclusion soundness: `all_clause_sound_extend m i_concl a' Hagree` applied to
   `all_app`:  `uf_eqs_sound i_concl e_c2` (the eq clauses, filtered ⊆) ++
   `db_to_atoms_sound i_concl e_c2` (the atoms, `incl_remove_atoms` for dedup).
   Both need `egraph_sound_for_interpretation lang_model i_concl conclusion_inst`.

## FORWARD SOUNDNESS CHAIN (feasible — all pieces exist)
Build `i_concl` sound on `conclusion_inst` by sequencing soundness through the
`rule_to_log_rule` pipeline: `add_ctx false false c ;; rebuild ;; add_open_term true false sub (con n (id_args c)) ;; rebuild ;; force_equiv`.
Note `denote e := fun i => egraph_sound_for_interpretation m i e` (Semantics.v:1565), so:
- `empty_sound_for_interpretation` : base, `egraph_sound_for_interpretation lang_model map.empty empty`.
- `add_ctx_sound` (Theorems.v:1897) with `s:=sg` → `ctx_post sg c i` ⇒ exists i1, `extending_sound empty e_ctx i1`, `args_in_instance l (map snd sg) i1 (map snd sub)`, `map fst sub = map fst c`.
- `rebuild_sound (fun _=>True) rf` (Semantics.v:10958): postcond `forall i, egraph_sound_for_interpretation m i e <-> ... (snd res)` — preserves soundness of i1 across rebuild. (Used at 5397 & 5455.)
- `add_open_term_sound` (Theorems.v:1871) with `e := con n (id_args c)`, `t := rule sort`, `r := sub`, `s := sg` → `open_term_post` ⇒ exists i2 extending i1, sound, `option_relation domain_eq (get i2 (fst res)) (Some (inl (con n (id_args c))[/with_names_from c (map snd sub)/]))`.
  - precond `wf_term l c (con n (id_args c)) t`: the `Hconcl` assertion inside `ConclSemantic.term_concl_wf` proof (id_args_wf + wf_term_by). precond `wf_args l [] sg c`: from `wf_subst` (sg wf). precond `args_in_instance` carried from ctx_post (monotone under extends, Theorems.v:1160).
- `rebuild_sound` again: preserve i2.
- `force_equiv_preserves_sound` (QueryOptSound.v, used at 5459) : preserve i2 across force_equiv (db & PER preserved).
⇒ `i_concl := i2`, `egraph_sound_for_interpretation lang_model i2 conclusion_inst`.
Dedup (`db_remove` loop) preserves soundness (removes atoms only; equiv unchanged — `db_remove_sound` Semantics.v:1901). `incl_remove_atoms` (QueryOpt.v) handles the atom-subset for `db_to_atoms_sound`.

## THE CRUX / OPEN DESIGN POINT  ⚠
`Hagree` needs `a` to agree with `i_concl` on `dom(i_concl)`.  `dom(i_concl)` =
 (A) assumption readback ids (c's vars) — `Hfaith` gives `a(id)=inl(sg x)`; `i_concl(id)=i1(id) =deq inl(sg x)` (from `args_in_instance`, only up to `domain_eq`!).
 (B) FRESH ids allocated by `add_open_term` (the con-node ret, sort nodes) — NOT threaded from `a`.

Two gaps vs the template:
 1. (A) is only `domain_eq`-agreement, not exact (`add_*_sound` postconds use `option_relation domain_eq` / `args_in_instance` = `all2 domain_eq`). The template gets EXACT agreement because it builds `i_concl` from `a`'s pulled-back values (`congruence`). Two sub-options:
    (a) **setoid Hagree**: generalize `all_clause_sound_extend` to a `domain_eq`-tolerant transfer using `interprets_to_preserved` (model_ok). Then deq-agreement on (A) suffices.
    (b) **build i_concl from a** (thread a's exact values through add_ctx/add_open) — needs `add_ctx`/`add_open_term` "preserves_ok"-style lemmas analogous to `clauses_to_instance_preserves_ok`. This is the session-30 "dual of add_open_sound" / ~1500 LoC.
 2. (B) the fresh ids: if arbitrary `a` BINDS a fresh conclusion id k to junk, then `a'=putmany i_concl a` (a wins) gives `a'(k)=junk ≠ i_concl(k)` ⇒ `Hagree` FALSE ⇒ conclusion atom (con-node ret) unsound ⇒ obligation FALSE for that `a`.
    The template has NO un-threaded fresh ids (clauses_to_instance renames ALL ids), so it never hits this. `rule_to_log_rule` allocates fresh ⇒ genuinely exposed.
    RESOLUTION REQUIRED: either (i) the fresh ids are provably ∉ dom(a) (a freshness invariant — but `a` is `forall`-quantified with only `has_key` on `forall_vars` = assumption vars; need to show conclusion-fresh ids can't be in `a`'s domain — NOT obvious), or (ii) make i_concl WIN on fresh ids while still `extends a` (requires fresh ∉ dom(a)), or (iii) the obligation needs an extra hypothesis the plumbing must thread.
    Since `optimize_sequent_forward_atoms` CONSUMES raw `model_satisfies_rule (rule_to_log_rule …)` as a hypothesis (its `Hsat`), the codebase BELIEVES the raw form is provable for arbitrary `a` ⇒ a freshness mechanism must exist. FIND IT before committing to the transfer proof.

## ⭐ CRUX RESOLVED (session 45 audit) — CONTRACT REALIGNMENT
The raw obligation (has_key premise, arbitrary `a`) is GENUINELY FALSE: concrete counterexample
`term_rule [] [] t`, `a := {k ↦ inl junk}` where `k` = the fresh con-node id (an `exists_var`).
Premises hold (forall_vars=[], assumptions=[]) but no `a'⊇a` is sound. `None <$> P = False` (Utils.v:34)
and `all_clause_sound_extend` needs EXACT extends ⇒ no escape.

BUT the audit shows the raw form is only ever CONSUMED confined:
- `optimize_sequent_forward_atoms` (QueryOptSound.v:5306) applies its hypothesis `Hsat : model_satisfies_rule m s`
  ONLY to `a_src := pullback_assignment a_opt sub2` (line 5384, 5422-5423). `pullback_assignment`
  (QueryOptSound.v:4856) has domain ⊆ keys of `sub2` = EXACTLY `forall_vars s`. So a_src is confined
  (set_eq keys = forall_vars s). The has_key weakening (comment QueryOptSound.v:156) is for the
  OPTIMIZED conclusion (renamed keys), NOT the raw hypothesis.
- Downstream (erule_sound / run1iter_rule_hyps / schedule_sound) consume the OPTIMIZED (compiled) rule
  soundness, i.e. `model_satisfies_rule m (optimize_sequent …)` — the strong/open form, unaffected.

### REALIGNMENT (proposed)
Introduce a CONFINED predicate (set_eq premise) for the RAW side; keep the open (has_key) form for the
optimized side + downstream. Touch ONLY the bridge's hypothesis + the adapter.
- `model_satisfies_rule_closed (r) := forall a, set_eq (map.keys a) (forall_vars r) -> all clause_sound a seq_assumptions -> exists a', extends a' a /\ all clause_sound a' seq_conclusions`
  (set_eq, i.e. domain(a) = forall_vars r exactly; equivalently `incl (keys a) (forall_vars r)` + has_key).
- Change `optimize_sequent_forward[_atoms]` hypothesis `model_satisfies_rule m s` → `model_satisfies_rule_closed m s`
  (conclusion unchanged = open form). Proof: a_src already confined; add the `incl (keys a_src) (forall_vars s)`
  obligation (true from pullback domain). Risk: touches the PROVEN 0-axiom rate-limiter — small, localized.
- Adapter proves `model_satisfies_rule_closed (lang_model l) (rule_to_log_rule … r)`.

### WHY THE ADAPTER IS NOW TRACTABLE (confined a)
With a confined to forall_vars = assumption readback vars, a binds NO fresh conclusion id ⇒ on dom(i_concl):
 - fresh ids: a undefined ⇒ a' (=putmany i_concl a) = i_concl ✓ EXACT.
 - assumption ids: a(id)=inl(sg x) (Hfaith), i_concl(id) =deq inl(sg x) (args_in_instance, only domain_eq).
   ⇒ need a SETOID transfer (deq-tolerant) instead of exact `all_clause_sound_extend`, OR build i_concl's
   assumption part to equal a exactly. SETOID is smaller:
   prove `all_clause_sound_setoid : model_ok -> (forall k d, get i k=Some d -> exists d', get a' k=Some d' /\ domain_eq d d') -> all clause_sound i cs -> all clause_sound a' cs`
   via `interprets_to_preserved` + `interprets_to_functional` + PER. Then canonical forward-chain i_concl
   (from sg) + deq-agreement (Hfaith on assumption ids, identity on fresh) closes it. NO dual-induction needed.

## ⭐ SESSION 46 (2026-06-01): R3 CORE LANDED (atom_tree_deq, 0 axioms, commit 890500b) + R4 design refined.
**KEY ASSET FOUND**: Theorems.v already has the model-free `atom_tree` (inductive: at_var x → lookup sub x;
at_con n s sids xe → Forall2 atom_tree s sids ∧ atom_in_egraph(n sids xe)) + `atom_tree_sort` (one scon layer) +
`atom_tree_to_represents`/`atom_tree_sort_to_represents_sort` (need EXACT leaves — only `a` has them, NOT i2) +
`add_open_faithful_rep[_sort]`. model_ok has BOTH `interprets_to_functional` AND `interprets_to_preserved`;
`domain_wf x := domain_eq x x` (refl = needs deq d d, from wf).
**R3a DONE — `atom_tree_deq` (AdapterGlue.v, 0 axioms)**: the genuine non-mechanical lemma, but PURELY RELATIONAL
(no term denotation, no eq_term congruence). Statement: two interps j1,j2 both sound on eF's atoms (Hsnd1/Hsnd2),
agreeing up to domain_eq on readback leaves (Hleaf), Hdom: map fst cc = map fst sub ⇒ ∀ e t, wf_term l cc e t →
∀ xe, atom_tree eF sub e xe → ∃d1 d2, get j1 xe=Some d1 ∧ get j2 xe=Some d2 ∧ domain_eq d1 d2. Proof MIRRORS
atom_tree_to_represents (term_ind; var→Hleaf via wf_term_implies_ws+Hdom; con→invert_wf_term_con, helper
`atom_tree_args_deq` builds list_Mmap+all2 deq from per-arg IH, then atom soundness on (n sids xe) for BOTH +
`interprets_to_functional`). interprets_to_functional sig = `@interprets_to_functional V (lang_model l) Hmok n
d1s d2s out1 out2 H1 H2 Hds` (ALL explicit, @-form; lang_model_ok also needs @). Both lemmas Closed under global.
**R4 SOUNDNESS HYPS ALL AVAILABLE** (no new work): Hsnd1 = the `a`-sound-on-eF hyp (Hsound/assumption_atoms_sound);
Hsnd2 = i2 sound on eF's atoms FROM i1 sound on e_assum=eF (assumption_egraph_sound) + i2 extends i1 +
atom_sound monotone-under-extends (atom_sound only reads the atom's own ids, which i1 maps). Leaves: a via Hfaith,
i2 via i1's args_in_instance + extends.
**STRUCTURAL INSIGHT (collapses coverage?)**: SORT ids are ONLY ever atom RETS, never ARGS (sort heads/sort_of
take TERM args). So conclusion atoms reference, as ARGS, only term ids = x' leaves (at_var, trivial) or fresh.
RETS of NEW conclusion atoms = fresh (con-node xe_out fresh; sort_of[xe_out]→s_out) EXCEPT a sort ret s_out can
hash-cons to an EXISTING var-sort id (shared) when the rule's output sort t equals a ctx var's sort. For such a
shared sort ret tx' (= ret of sort_of[x']→tx', arg x' a leaf): deq(a tx')(i2 tx') follows from
interprets_to_functional on sort_of with args [a x'][i2 x'] (deq via leaf) — i.e. atom_tree_sort_deq applies. So
the ONLY coverage needed = shared sort rets referenced by conclusions have atom_tree_sort (from ctx_readback_eF).
**LANDED session 46** (all 0-axiom, pushed long_horizon): atom_tree_args_deq + atom_tree_deq (commit 890500b),
atom_tree_sort_deq (86d9e21), **term_concl_construct (a72dc6d)** — R4 assembly CORE (pure putmany plumbing):
given (Hwf_i2: i2 values are domain_wf) + (Hclauses: i2 sound on seq_conclusions, = concl_clauses_sound_term) +
(Hagree: ∀k d da, get i2 k=Some d → get a k=Some da → deq d da), build a':=putmany i2 a, extends a
(get_putmany_right), sound on conclusions (all_clause_sound_setoid: fresh→i2 refl via Hwf_i2/get_putmany_left,
shared→a via Hagree). get_putmany_{right,left} sig: `@Properties.map.get_putmany_{right,left} V (domain V
(lang_model l)) (V_map _)(V_map_ok _) _ (@eqb_boolspec V V_Eqb V_Eqb_ok) i2 a k …`. lang_model_ok sig =
`@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf` (NO V_map args). domain_wf m x := domain_eq m x x.
So `term_rule_concl_obligation = conclusion_egraph_sound (i2,Hi2_concl,Hai2) + concl_clauses_sound_term (Hclauses)
+ idx_interpretation_wf of Hi2_concl (Hwf_i2) + assumption_ids_agree (Hagree) + term_concl_construct`. ALL pieces
proven EXCEPT assumption_ids_agree.
**THE ONLY REMAINING HARD PIECE = `assumption_ids_agree` (produces Hagree).** Decomposes into:
 (a) i2 sound on eF's LITERAL atoms (Hsnd1 for atom_tree_deq): from i1 sound on e_assum=eF (assumption_egraph_sound)
     + i2 extends i1 (add_open_term_sound Hext12) + atom_sound monotone-under-extends. ⚠ conclusion_egraph_sound
     does NOT currently expose i1/extends/i2-sound-on-eF — must STRENGTHEN it or re-derive (re-run
     assumption_egraph_sound + add_open_term_sound). RISK: re-proving touches a proven Qed.
 (b) leaf agreement i2/a (Hleaf): a(lookup sub x)=inl(sg x) [Hfaith]; i2(lookup sub x) =deq inl(sg x) [extract
     per-x from Hai2 = args_in_instance l (map snd sg) i2 (map snd sub), aligning lookup sub x = snd-of-x-entry].
     Combine via PER symmetry. Fiddly list extraction (~40 LoC).
 (c) ⚠⚠ COVERAGE (the genuine remaining math, ~250-450 LoC, MULTI-SESSION): ∀ k ∈ keys(a)=forall_vars(eF),
     ∃ atom_tree eF sub e k (wf_term) ∨ atom_tree_sort eF sub ts k (wf_sort). Sub-agent (a20b693d) CONFIRMED: NO
     existing completeness lemma (all readback infra runs SOUNDNESS dir: readback→atom; the converse atom→readback
     is new). Needs either a fresh add_ctx induction threading "every atom is a readback node" through
     alloc/hash/union/rebuild (mirrors db_ctx_inv-preservation proofs Theorems.v:4231-4700, ~200 LoC each), OR a
     completeness lemma "db_to_atoms eF ⊆ readback-tree atoms" from ctx_readback_eF (which is currently NOT exposed
     by add_ctx_inversion — would need re-deriving via ctx_readback_to_eF). This is the subproject's remaining core.
     NB SORT ids only ever atom RETS (never args) ⇒ conclusion atoms reference x' leaves (at_var, trivial) + fresh
     as ARGS; shared ids referenced = x' leaves + shared sort RETS (hash-consed to a var sort). The interface path
     (weaken all_clause_sound_setoid to Hcompat-on-clause_vars + characterize add_open_term output) is the agent's
     recommended alternative (~120-200 LoC) but hides the hash-consing identification (conclusion sort ret = which
     readback xs?). Either way coverage/completeness is the wall.
 (i_old) `atom_tree_sort_deq` — DONE (86d9e21).
 (ii) COVERAGE — ⚠ THE remaining risk: for each conclusion-referenced shared id k ∈ keys(a), an atom_tree(_sort)
     witness. x' leaves trivial (at_var + wf_term var). Shared sort rets: need atom_tree_sort eF sub t k from
     ctx_readback_eF. OPEN: is it cleaner to (A) prove UNIVERSAL coverage [every db_to_atoms eF id has
     atom_tree/sort, from ctx_readback_eF completeness] + keep all_clause_sound_setoid's universal Hcompat, or
     (B) weaken all_clause_sound_setoid to Hcompat-on-clause_vars + cover only the interface ids. Investigating.
 (iii) R3b/R4 assembly: a':=putmany i2 a; extends via get_putmany_right; Hcompat: leaf→Hfaith+args_in_instance,
     fresh→putmany_left+domain_wf refl, shared-sort-ret→atom_tree_sort_deq; close via all_clause_sound_setoid +
     concl_clauses_sound_term. Then sort rule mirror. Then R5 contract (model_satisfies_rule_closed set_eq premise).
 NOTE: i2 sound on eF atoms needs eF atoms = literal atoms i1 maps; transfer i1→i2 by extends (atom_sound monotone).

## ⭐ SESSION 47 (2026-06-01): `assumption_ids_agree` LANDED (0 axioms) — agreement engine.
The Hagree producer is now a 0-axiom lemma (AdapterGlue.v, after atom_tree_sort_deq).
Statement: given a,i2 both sound on eF atoms (Hsnd_a/Hsnd_i2), leaf-agreement (Hleaf),
Hdom, and **OVERLAP-coverage** Hcover (∀ k da d, get a k=Some da → get i2 k=Some d →
∃atom_tree/atom_tree_sort rooted at k under wf_term/wf_sort), conclude
∀ k d da, get i2 k=Some d → get a k=Some da → deq d da. Proof = pick the tree witness,
apply atom_tree_deq (j1:=a,j2:=i2) or atom_tree_sort_deq, congruence the gets, PER_Symmetric.
KEY DESIGN CHOICE: Hcover is stated on the OVERLAP dom(a)∩dom(i2), NOT on all forall_vars.
⇒ the R5 confinement premise (dom a ⊆ forall_vars) stays OUT of assumption_ids_agree's
statement; it is needed only to DISCHARGE Hcover (an unconfined a binding a FRESH conclusion
id k — not an atom_in_egraph eF — would have no atom_tree ⇒ Hcover false for that k). This
cleanly decouples the agreement engine (DONE) from confinement (R5, deferred to Hcover's proof).
Verified: rocq_assumptions = "Closed under the global context"; make builds AdapterGlue.vo.

### REMAINING to close term_rule_concl_obligation (term; sort mirrors):
 term_rule_concl_obligation = conclusion_egraph_sound (i2 + Hai2=args_in_instance) [DONE]
   + concl_clauses_sound_term (Hclauses) [DONE] + idx_interpretation_wf of i2 (Hwf_i2) [easy,
   from egraph_sound_for_interpretation's wf component] + assumption_ids_agree (Hagree) [DONE
   modulo its 3 premises] + term_concl_construct (assembly) [DONE].
 The 3 OPEN premises of assumption_ids_agree, with eF := e_assum, sub, cc := c:
  • Hsnd_a  : a sound on e_assum atoms — ALREADY HAVE as `Hsnd_atoms` in the adapter
              (assumption_atoms_sound (lang_model l) a _ Hassum). ✓ free.
  • Hsnd_i2 : ✅ DONE (commit b3b997e). conclusion_egraph_sound STRENGTHENED to also return
              (i1, Hsnd_i1: sound on e_assum, Hext12: extends i2 i1). New `egraph_atoms_sound`
              (egraph_sound_for_interpretation → per-atom soundness) + `conclusion_i2_sound_assum`
              (packages i2 sound on e_concl + args_in_instance + i2 sound on e_assum atoms via
              atom_sound_extend on i1). 0 axioms.
  • Hleaf   : ✅ DONE (commit 99c3f76). `leaf_agree` (abstract over a,i2,sg,cc,sub): Hfaith for the
              a-side, Theorems.args_in_instance_in on Hai2 for the i2-side (gives lang_model_eq =
              domain_eq), PER symmetry. 0 axioms. Feeds assumption_ids_agree's Hleaf directly.
  • Hcover  : ⚠⚠ THE WALL (coverage) — THE ONLY REMAINING MATH. Stated on overlap; PROOF needs R5 confinement
              (dom a ⊆ forall_vars = ids in db_to_atoms e_assum) + the new COVERAGE induction:
              every id in e_assum's atoms carries atom_tree/atom_tree_sort. Explore verdict
              (S47): FEASIBLE but NEW induction mirroring add_ctx_readback (Theorems.v:5557-5870,
              ~300 LoC), reusing add_open_sort_node_atoms / atom_tree_survives / db_ctx_inv /
              ctx_readback. NO existing completeness lemma. Biggest risk = canonicalization
              (sort_of atom ret tx' vs sort-tree root xs are only uf_rel-equiv pre-rebuild; post-
              rebuild they coincide — needs the rebuild-canonical fact). MULTI-SESSION.
 PLUS R5 (contract): the obligation is stated for arbitrary `a` (open model_satisfies_rule,
   QueryOptSound.v:160, has_key premise). To get confinement for Hcover, introduce
   model_satisfies_rule_closed (set_eq premise), repoint optimize_sequent_forward[_atoms]'s
   HYPOTHESIS open→closed (a_src already confined via pullback; +1 incl obligation), and add a
   confinement premise to term/sort_rule_concl_obligation + the adapters. LAST (touches proven
   0-axiom bridge). NB the active model_satisfies_rule is QueryOptSound.v:160 (has_key); the
   Semantics.v:295 set_eq version is COMMENTED OUT.

## PROGRESS LOG (session 45)
- ✅ `all_clause_sound_setoid` + `list_Mmap_get_setoid` (AdapterGlue.v, generic, 0 axioms) — commit 1d8a47c. The deq-transfer linchpin.
- ✅ `assumption_egraph_sound` (AdapterGlue.v Section Adapter, 0 axioms) — commit a5745be. i1 sound on e_assum + args_in_instance + map fst eq.
- ⏳ `conclusion_egraph_sound` (in progress, background Sonnet) — i2 sound on e_concl + args_in_instance l (map snd sg) i2 (map snd sub).

## REMAINING ASSEMBLY (after conclusion_egraph_sound lands) — all in AdapterGlue.v, then bridge
- R1: dedup preservation — `db_remove` loop (conclusion_inst → conclusion_inst_dedup) preserves `egraph_sound_for_interpretation i2`. From `db_remove_sound` (Semantics.v:1901; atoms subset, equiv preserved). Small.
- R2: i2 sound on ALL seq_conclusions clauses: `db_to_atoms_sound i2 e_concl` (atoms, via `incl_remove_atoms` QueryOpt.v:567 for the dedup subset) ++ `uf_eqs_sound i2 e_concl` (eqs, filtered by live_eqn ⊆). Mirror template QueryOptSound.v:5491-5504. Needs i2 sound on conclusion_inst (=e_concl) — have it. NOTE: db_to_atoms_sound/uf_eqs_sound act on conclusion_inst's db/equiv; dedup preserves equiv so eqs fine; atoms use the dedup'd db via incl_remove_atoms.
- ⚠ R3 REFINED (session 45 audit): `add_ctx false false c` is NOT atom-free. It calls `add_open_sort sub t`
  (the variable's OWN sort — with_sorts only gates TERM-sort annotations) + `alloc_opaque` (no atom) +
  `hash_entry sort_of [x']` + `union`. So `e_assum` has `sort_of [x'] tx'` atoms + sort-structure atoms ⇒
  `forall_vars` (= ids in db_to_atoms e_assum, via clause_vars = atom_ret::atom_args) INCLUDES non-readback ids
  (sort ids tx', sort-tree ids). `Hfaith` (add_ctx_inversion, AddCtxInversion.v:154) only covers READBACK var ids
  (`map fst (fst(add_ctx…))`). So Hcompat's `deq i2(k) a(k)` is NOT immediate on non-readback k.
  RESOLUTION (the real R3 lemma — a genuine induction): "two sound interps agreeing on readback leaves agree
  everywhere up to deq". Each non-readback id k is the RET of an atom `f(args)->k` (DAG, bottom-up from add_ctx).
  a & i2 both sound on that atom (Hsnd_atoms for a; i2-soundness atom_interpretation) ⇒ `interprets_to f (a args) (a k)`
  & `interprets_to f (i2 args) (i2 k)`; with `all2 deq (a args) (i2 args)` (IH) ⇒ `deq (a k) (i2 k)` by
  `interprets_to_functional` (model_ok). Base = readback var ids via Hfaith (+ args_in_instance gives i2=deq there).
  Does NOT need a to respect unions (rel_interpretation) — each k derived from its own defining atom. Induct over
  the add_ctx atom DAG / `atom_tree`/`ctx_readback` scaffolding (Theorems.v:5506 ctx_readback, :2543 atom_tree).
  Needs confinement premise to bound keys a ⊆ assumption-atom ids (so every k∈keys a has a defining atom, base or
  step). EST ~150-300 LoC; the one genuinely non-mechanical remaining lemma. DESIGN before delegating.
- R3b: build Hcompat for `all_clause_sound_setoid` with a' := putmany i2 a (uses R3-refined deq-agreement):
    forall k d, get i2 k = Some d -> exists d', get (putmany i2 a) k = Some d' /\ domain_eq d d'.
    Two id classes (CONFINED a ⇒ a binds only forall_vars = assumption readback ids):
     • k ∈ assumption readback ids: a(k)=inl(sg x) (Hfaith), i2(k) =deq inl(sg x) (args_in_instance i2 + sub↔readback). putmany: a wins ⇒ get=a(k); deq i2(k) a(k) ✓.  Need: a's domain ∩ dom(i2) ⊆ readback ids (confinement) and the Hfaith↔args_in_instance value match.
     • k ∉ a's domain (fresh conclusion ids): putmany_left ⇒ get = i2(k) = d, deq d d ✓ (domain_wf, from idx_interpretation_wf of i2-soundness).
    KEY new sub-fact: confinement ⇒ a binds no fresh conclusion id. From `model_satisfies_rule_closed` premise `set_eq (keys a) (forall_vars (rule_to_log_rule…))` and `forall_vars = vars of assumption atoms = readback ids`; fresh ids ∉ readback ids (allocator freshness / not in db_to_atoms assumption). Prove fresh ∉ keys a.
- R4: assemble term_rule_concl_obligation: a' := putmany i2 a; extends a' a via `Properties.map.get_putmany_right`; all clause_sound a' seq_conclusions via `all_clause_sound_setoid (lang_model l) lang_model_ok i2 a' seq_conclusions Hcompat (R2)`. Same for sort (use add_open_sort_sound + sort_concl_wf).
- R5 (CONTRACT): define `model_satisfies_rule_closed` (set_eq premise) in QueryOptSound.v; restate the two obligations + adapters against it; patch `optimize_sequent_forward[_atoms]` hypothesis open→closed (a_src confined; +1 incl obligation). LAST (touches proven bridge). Big rebuild.
- NOTE on a vs i2 on assumption ids being EXACT vs deq: we use the SETOID transfer (R2/R4 via all_clause_sound_setoid), so deq suffices — no need to build i2 to match a exactly. This is why the setoid lemma was the linchpin.

## OLDER NEXT ACTIONS (superseded by PROGRESS/REMAINING above)
- N1a: Build & validate the FORWARD chain as a standalone WIP lemma
  `concl_term_sound : exists i_concl, egraph_sound_for_interpretation lang_model i_concl conclusion_inst /\ <i_concl extends the assumption interp> /\ <output-id denotes (con n (id_args c))[/sg/]>`.
  This is reusable under EITHER crux resolution. Delegate mechanical proof to Sonnet once skeleton pinned.
- N1b: Resolve the CRUX (the fresh-id freshness vs arbitrary `a`). Check: is there a freshness
  invariant on `rule_to_log_rule` conclusion ids? How does the template guarantee conclusion ids ⊆ threaded? Inspect `clauses_to_instance_preserves_ok`'s `Hdom`/`Hren` for the analogous add_open story.
- N1c: Pick transfer flavor (setoid 1(a) vs build-from-a 1(b)) once crux resolved.
