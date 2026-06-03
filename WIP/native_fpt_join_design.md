# Native conversion-free `fpt_spaced_intersect` — implementation design

Goal: the running e-graph join must operate directly on the lawful `fpt'` carrier
with **no fold-rebuild conversion**. Proofs may still use the conversion reference
`fpt_spaced_intersect_via_conv`. Public name `fpt_spaced_intersect` and the two
consumed lemma *statements* stay stable.

Status: **M0 done** (commit c6e8d28): `fpt_spaced_intersect_via_conv` = old conversion
body; `fpt_spaced_intersect` is currently a definitional alias of it. M1+ below.

All new code lives in `src/Utils/FullPosTrieConv.v`. Reference algorithm:
`pt_spaced_intersect'` / `pt_spaced_intersect` (`PosListMap.v:852-898`).

## Carrier facts
- `fpt' = fpt_leaf a | fpt_node (m:tree' fpt') | fpt_both a (m:tree' fpt')` (FullPosTrie.v:31).
- `pos_trie' = pos_trie_leaf a | pos_trie_node (m:tree' pos_trie')` (PosListMap.v:279).
- Join inputs satisfy `fpt_depth'` (FullPosTrieConv.v:107) which has NO `fpt_both`
  constructor ⇒ `fpt_both` is dead in inputs; handle it as a node (drop value).
- `list_intersect` (TrieMap.v:472 `Section MapIntersectList`, `Context {B C}
  (elts_intersect : bool -> B -> list B -> option C)`) is element-type polymorphic;
  post-section signature: `list_intersect elts_intersect (hd:tree' B) (args:list (tree' B))
  : option (tree' C)`. The native join reuses THE SAME `list_intersect`, instantiated at
  `B:=fpt'`, `C:=fpt'`.

## M1 — native definitions (proof-free; just need to typecheck)

Put inside a `Section` with `Context {B:Type} (Hdef: WithDefault B) (merge:B->B->B)`
(mirror PosListMap's `Section __. Context WithDefault A. Context (merge:A->A->A).`).

### proj (O(1), runtime)
```
Definition fpt_proj_node_unchecked (p:fpt') : PTree.tree' fpt' :=
  match p with
  | fpt_leaf a => PTree.Node010 (fpt_leaf default)
  | fpt_node m => m
  | fpt_both _ m => m
  end.
```

### leaf_intersect (runtime, structural on list)
```
Fixpoint fpt_leaf_intersect (a:B) (ptl:list fpt') : B :=
  match ptl with
  | [] => a
  | (fpt_leaf a')::ptl' => fpt_leaf_intersect (merge a a') ptl'
  | (fpt_node _ | fpt_both _ _)::ptl' => fpt_leaf_intersect a ptl'  (* dead *)
  end.
```

### partition (mirror `partition_result` + `partition_tries`, carrier fpt')
Clone `Variant partition_result` (PosListMap.v:468) and `Fixpoint partition_tries`
(476-502) verbatim with `pos_trie'`→`fpt'`. Name them `fpt_partition_result` /
`fpt_partition_tries`.

### the fixpoint (mirror pt_spaced_intersect' 852-889, carrier fpt')
```
Fixpoint fpt_spaced_intersect'' fuel cil ptl (ci0:list bool) cil' pt0 ptl'
  : option fpt' :=
  match fuel, ci0, pt0 with
  | S _, [], fpt_node _   | S _, [], fpt_both _ _  (* both treated as node: dead *)
  | O, _, _ => None
  | S fuel, [], fpt_leaf a =>
      Some (fpt_leaf (fpt_leaf_intersect (fpt_leaf_intersect a ptl) ptl'))
  | S fuel, ci0_hd::ci0_tl, _ =>
      let initial_part := if ci0_hd then have_true_part [] [] ci0_tl pt0 [] []
                          else just_false_part ci0_tl pt0 [] [] in
      let part := fpt_partition_tries cil' ptl' (fpt_partition_tries cil ptl initial_part) in
      match part with
      | just_false_part ci0 pt0 oc ot => fpt_spaced_intersect'' fuel oc ot ci0 [] pt0 []
      | have_true_part oc ot t_ci0 t_pt0 t_cil t_ptl =>
          let true_cil_rev := rev t_cil in
          let pt_intersect :=
            list_intersect
              (fun is_forward => fpt_spaced_intersect'' fuel oc ot t_ci0
                                   (if is_forward then t_cil else true_cil_rev))
              (fpt_proj_node_unchecked t_pt0)
              (map fpt_proj_node_unchecked t_ptl)
          in option_map fpt_node pt_intersect
      end
  end.
```
NOTE the matched `pt0` in the `S _,[],fpt_node`/`fpt_both` "should-never-happen" arms
returns None — mirror pt_spaced_intersect' which returns None for `S _,[],pos_trie_node`.

### wrapper (mirror pt_spaced_intersect 891)
```
Definition fpt_spaced_intersect_native (tries : ne_list (fpt * list bool)) : fpt :=
  let '(ptl, cil) := split (snd tries) in
  let '(pt0, ci0) := fst tries in
  let fuel := S (length ci0) in
  @!let pt0' <- pt0 in
    let ptl' <- list_Mmap id ptl in
    (fpt_spaced_intersect'' fuel cil ptl' ci0 [] pt0' []).
```
End Section. Then the top-level `fpt_spaced_intersect` (the public name) is set to this
native wrapper with merge arg threaded — matching the via_conv signature
`(merge) (tries : (fpt*list bool) * list (fpt*list bool))`. Note via_conv takes the
PAIR-form `(fst, list)`, while the wrapper takes `ne_list = (fst, list)` — same shape.

Guard checker: the fixpoint is structural on `fuel` (like the original) — no nested-fix
problem. `list_intersect` is already defined. Only thing to watch: the `option_map
fpt_node` and that `list_intersect`'s `C := fpt'` is inferred.

## M1b — structural injection (PROOF ONLY, efficiency irrelevant)
```
Definition pt'_of_fpt' : fpt' B -> pos_trie' B   (* leaf→leaf, node→node-map, both→node-map drop val *)
```
Define via the nested-fix / `trie_fold'`-inlined pattern (like `fpt_elements'`,
FullPosTrie.v:612) OR via `fpt'_strong_ind` if defined as a Fixpoint fails the guard
checker. Need a `tree'_map' : (X->Y)->tree' X->tree' Y` (structural on tree', plain
Fixpoint, fine) — define locally if not present (Canonical only has `map_filter'`).
Then `pt'_of_fpt' (fpt_node m) = pos_trie_node (tree'_map' pt'_of_fpt' m)` — guard
needs the nested-fix inline; clone the `fpt'_strong_ind` body shape.

Get lemma (a): `fpt_depth' t n -> length k = n -> fpt_get' t k = pt_get' (pt'_of_fpt' t) k`.
Proof by `fpt'_strong_ind` (both case vacuous under fpt_depth').

## M2 — simulation lemma (THE CRUX)
```
Lemma sim : forall fuel cil ptl ci0 cil' pt0 ptl',
  option_map pt'_of_fpt' (fpt_spaced_intersect'' fuel cil ptl ci0 cil' pt0 ptl')
  = pt_spaced_intersect'  fuel cil (map pt'_of_fpt' ptl) ci0 cil'
                          (pt'_of_fpt' pt0) (map pt'_of_fpt' ptl').
```
By induction on fuel. The leaf base case: `pt'_of_fpt' (fpt_leaf x) = pos_trie_leaf x`
and `fpt_leaf_intersect` vs `leaf_intersect` agree under `map pt'_of_fpt'` (leaf images
are leaves; node/both images are nodes → both skip). The have_true_part case: the
`list_intersect` step — use the existing cross-type congruence lemma
**`list_intersect_Perm_combined` (PosListMap.v:2354)** (or a thinner naturality sibling)
to relate `list_intersect (fpt elts) (fpt_proj t_pt0) (map fpt_proj t_ptl)` mapped
through `tree'_map' pt'_of_fpt'` to `list_intersect (pt elts) (pt_proj …) …`. Key
sub-facts: `tree'_map' pt'_of_fpt' (fpt_proj_node_unchecked t) = proj_node_map_unchecked
(pt'_of_fpt' t)` (holds for all 3 ctors, incl both), and the elts closures correspond by
the fuel-IH. `partition_tries` commutes with `map pt'_of_fpt'` (structural, carries
values opaquely) — prove a small `partition_tries` map-commute helper.

Fallback if `list_intersect_Perm_combined` doesn't fit: prove a dedicated
`list_intersect` naturality lemma via `list_intersect_correct` + `tree'` get-extensionality.

Also need: depth of native result. `fpt_depth (option-of native result) N` where
N = #true flags — mirror `pt_spaced_intersect_depth`; OR derive from sim +
`pt_spaced_intersect_depth` + a `pt'_of_fpt'`-reflects-depth lemma.

## M3 — bridge lemma + keys corollary
```
Lemma fpt_spaced_intersect_native_eq_via_conv :
  (call-site hyps: each input fpt_depth-uniform, wf_tries, combined_bools=repeat true N)
  -> length k = N
  -> fpt_get (fpt_spaced_intersect_native (tries,rest)) k
   = fpt_get (fpt_spaced_intersect_via_conv merge (tries,rest)) k.
```
RHS: `fpt_get (pt_to_fpt (compat_intersect …)) k = pt_get (compat_intersect …) k`
(pt_to_fpt_get + Hdepth) = merge-fold of `fpt_get (fst pᵢ) (proj k)` via
`pt_spaced_intersect_correct` spec + `fpt_to_pt_get`.
LHS: `fpt_get' native k = pt_get' (pt'_of_fpt' native) k` (get-lemma (a) + native-depth)
= `pt_get (pt_spaced_intersect on pt'_of_fpt'-mapped inputs) k` (sim) = same merge-fold
via `pt_spaced_intersect_correct` + get-lemma (a). Both sides equal ⇒ done.

Keys corollary: `In sigma (map.keys native) <-> In sigma (map.keys via_conv)` from
get-eq at length-N keys + `full_pos_trie_map_ok` extensionality (`fpt_map_ext`,
FullPosTrie.v:991); all keys length N under hyps.

## M4 — swap + re-route
- Replace the M0 alias body of `fpt_spaced_intersect` with `fpt_spaced_intersect_native`
  (threaded merge). 
- `fpt_spaced_intersect_inputs_hit` (FullPosTrieConv.v:534): the opening
  `assert (Heq: … = pt_to_fpt R) … reflexivity` (now ~595) no longer holds
  definitionally → replace with the keys corollary (rewrite `In sigma (map.keys native)`
  to `In sigma (map.keys via_conv)`); rest unchanged.
- QcAlignment `trie_join_H9` (~760) / `trie_join_H10` (~854): same `Hsimp …
  reflexivity` → keys corollary.

## M5 — verify
Build FullPosTrieConv.vo → QcAlignment.vo → Automation.vo (absolute-path targets:
`make -f Makefile.coq /root/pyrosome-ai/src/Utils/FullPosTrieConv.vo`).
`Print Assumptions egraph_sound` must stay "Closed under the global context".
rocq_assumptions on the new bridge lemmas: no new axioms. Perf: `Time` a saturating
EGraph/Test goal before/after.

## Build note
Makefile.coq targets are ABSOLUTE paths. Build e.g.
`make -f Makefile.coq /root/pyrosome-ai/src/Utils/FullPosTrieConv.vo`.
