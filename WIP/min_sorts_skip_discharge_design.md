# min-sorts skip-soundness discharge — design

Goal: close the single remaining admit `skip_var_decl_sort_core`
(`src/Pyrosome/Tools/EGraph/CtxReadback.v:849`), which is the last gap in the
min-sorts-query branch's e-graph skip soundness.

## Context

Commit b8dc3be added, gated on `syntactic_sort_eq l` (Core.v):
- `covering_var_leaf_syn` (Qed): for `e` source-typed in `c'` and image-typed
  in `c`, every `x ∈ fv e` with `In (x,t') c'` gets
  `wf_term l c (subst_lookup s x) (t'[/s/])`. Needs `Hsyn`, source wf, **image
  wf `wf_term l c (e[/s/]) (t[/s/])`**, `map fst s = map fst c'`.
- `covering_var_leaf_syn_args_aux` (Qed): same over an args list, taking a
  per-arg term IH.
- `wf_subst_from_args_image` (Qed): builds full `wf_subst` — but takes the
  image wf_args as a hypothesis (the deferred extraction).

The gate `syntactic_sort_eq_langb l = true` ⟹ `syntactic_sort_eq l` via
`SyntacticSorts.syntactic_sort_eq_sound` (+ `wf_lang l`).

## The missing piece: wf_subst-free whole-LHS image wf

`covering_var_leaf_syn` needs `wf_term l [] ((con n0 s0)[/sg/]) (t1[/sg/])`.
`add_open_faithful_rep` would give it but requires `wf_subst l [] sg c` — the
thing we are building. So we need a **wf_subst-free** extraction, gated on
`syntactic_sort_eq`.

Where `add_open_faithful_rep` used wf_subst:
1. var base case (typing `sg x` at its sort) — only reached for var ROOTS;
2. the final rule-sort→declared `eq_sort_subst` transport.
Under `syntactic_sort_eq`, (2) collapses to syntactic equality (no eq_subst).
(1) is avoided by handling var ARGS off the model `wf_args` (like
`add_open_use_sort_args`) instead of as a term base case. var ROOTS are never
in the skip set, so `match e with con => ... | var => True`.

### New deliverable lemmas (Theorems.v, Section AddOpenSound)

```
Lemma faithful_rep_syn (Hsyn : syntactic_sort_eq l)
  (a eF sg) (Hsound : forall al, atom_in_egraph al eF -> atom_sound_for_model ... a al)
  : forall e c t, wf_ctx l c -> wf_term l c e t ->
      forall xe, represents a eF sg e xe ->
      match e with
      | con _ _ => exists e', map.get a xe = Some (inl e') /\ eq_term l [] (t[/sg/]) e' (e[/sg/])
      | var _ => True
      end.
```
Proved by `term_ind`; con case delegates the args to:
```
Lemma faithful_args_syn (Hsyn) (a eF sg) (Hsound)
  : forall (s : list term) (c c' : ctx),
      wf_ctx l c -> wf_ctx l c' -> wf_args l c s c' ->
      (IHs : all (fun e => match e with
              | con _ _ => forall c t, wf_ctx l c -> wf_term l c e t -> forall xe,
                  represents a eF sg e xe ->
                  exists e', map.get a xe = Some (inl e') /\ eq_term l [] (t[/sg/]) e' (e[/sg/])
              | var _ => True end) s) ->
      forall sids, Forall2 (represents a eF sg) s sids ->
      forall args_terms, Forall2 (fun i e => map.get a i = Some (inl e)) sids args_terms ->
        wf_args l [] args_terms c' ->
        eq_args l [] c' args_terms (s[/sg/]).
```
Induction on `wf_args` (mirrors `faithful_args_eq` + `add_open_use_sort_args`).
cons head `(nm,tnm)::c'0`, goal head eq_term at sort `(tnm[/wnf c'0 rest/])[/sg/]`
= `tnm[/wnf c'0 (rest[/sg/])/]` (`faithful_sort_align`):
- **con arg** `e0 = con m ss`: use `IHs` head (term IH) — gives eq_term at exactly
  `(tnm[/wnf c'0 rest/])[/sg/]`. Same as original `faithful_args_eq`. No Hsyn.
- **var arg** `e0 = var x`: `args_terms_head = sg x = e0[/sg/]` (rep_var), so the
  goal is `eq_term_refl` needing `wf_term l [] (sg x) (tnm[/wnf c'0 (rest[/sg/])/])`.
  Model `wf_args` head gives `wf_term l [] (sg x) (tnm[/wnf c'0 args_terms_tail/])`.
  Convert by `eq_sort` from the **tail `eq_args`** (the IH result on rest:
  `eq_args l [] c'0 args_terms_tail (rest[/sg/])`) via
  `eq_args_implies_eq_subst` + `eq_sort_subst` on `eq_sort_refl tnm`
  (`wf_sort l c'0 tnm` from `invert_wf_ctx_cons` on `Hwfc'`).
  ⟹ compute the **tail eq_args FIRST**, then build the head.

`eq_term`/`eq_sort`/`wf` of the recursive structure: `faithful_sort_align`,
`eq_args_wf_r`, `term_sorts_eq`, `eq_sort_subst`, `eq_args_implies_eq_subst`,
`sort_con_congruence`, `wf_term_conv`, `wf_term_con_args`,
`WfCutElim.invert_wf_term_con`, `list_Mmap_get_nth_inl`, `in_all_fresh_same`.

## Rewiring (mechanical)

`skip_var_decl_sort_core` is **deleted**. `skip_var_decl_sort_wf` /
`skip_var_decl_sort_wf_scon` get `(Hsyn : syntactic_sort_eq l)` and
`(Hdomsgcf : map fst sg = map fst Cfull)` and become:

term: from `Hrep` + `faithful_rep_syn` get `e'`, `Heqt : eq_term l [] (t1[/sg/])
e' ((con n0 s0)[/sg/])`; `Himg := eq_term_wf_r Heqt : wf_term l [] ((con n0
s0)[/sg/]) (t1[/sg/])`. Then `covering_var_leaf_syn` with `c:=[]`, `c':=Cfull`,
`s:=sg`, `e:=con n0 s0`, `t:=t1`, `t':=t`, using `Hwfe1f`, `Himg`, `Hxfv`,
`In (x,t) Cfull` (from `Hcfull`), `Hdomsgcf`. Reconcile `subst_lookup sg x`
with `named_list_lookup default sg x` via `nll_default_indep` (x ∈ dom sg).
Goal sort `t[/sg/]`; convert to `t[/sg'/]` via `decl_sort_subst_prefix_eq`
(as now).

sort: invert `wf_sort` to `wf_args l Cfull s0 c'` (source); from `Hrep`
(`represents_sort`) + `faithful_args_syn` get `eq_args l [] c' args_terms
(s0[/sg/])`, `Himg_args := eq_args_wf_r : wf_args l [] (s0[/sg/]) c'`. Then
`covering_var_leaf_syn_args_aux` with IHterm := `covering_var_leaf_syn`,
`args:=s0`, source/image wf_args, `Hxfv : In x (fv_args s0)`, `In (x,t) Cfull`.

Thread `(Hsyn_skip : forall x, no_sort x = true -> syntactic_sort_eq l)` through
`skip_decl_wf_from_image{,_sort}` (head clause: `Hsyn := Hsyn_skip x Hns`;
`Hdomsgcf` from existing `Hdomsgc : map fst sg = map fst c` at line 908/1049),
`eq_ctx_inversion_gen` (AddCtxInversion.v:1815) / `eq_sort_ctx_inversion_gen`
(AddCtxInversion.v:3679), discharge in AdapterGlue.

## Sort side needs a THIRD Theorems lemma (agent adds; short)
The cleanest interface keeps ALL the wf_sort inversion in Theorems and returns
the image wf_args directly (so CtxReadback's scon case stays clean):
```
Lemma faithful_rep_sort_args_syn (Hsyn) (a eF sg) (Hsound)
  : forall n0 s0 c, wf_ctx l c -> wf_sort l c (scon n0 s0) ->
      forall xs, represents_sort a eF sg (scon n0 s0) xs ->
      exists c', wf_ctx l c' /\ wf_args l c s0 c' /\ wf_args l [] (s0[/sg/]) c'.
```
Proof: copy `add_open_faithful_rep_sort` (line 3009) skeleton up to the eq_args:
build the per-arg con IH `all (con-match) s0` from `faithful_rep_syn` (closed);
get `eq_args l [] c' args_terms (s0[/sg/])` via `faithful_args_syn` (NOT
faithful_args_eq — no wf_subst). Then: source `wf_args l c s0 c'` = the inverted
`Hws`; image `wf_args l [] (s0[/sg/]) c'` = `eq_args_wf_r` of the eq_args; `c'` is
the sort rule ctx (`rule_in_ctx_wf` ⟹ `wf_ctx l c'`). No sort_con_congruence /
eq_sort_trans needed for THIS lemma (we only want the two wf_args + ctx).

`skip_var_decl_sort_wf_scon` then: destruct `faithful_rep_sort_args_syn` into
`cR, HwfcR, HwfaSrc, HwfaImg`; `covering_var_leaf_syn_args_aux l Hwf [] Cfull sg
Hsyn Hwfcf Hdomsgcf s0 (fun e _ => covering_var_leaf_syn l Hwf [] Cfull sg Hsyn
Hwfcf Hdomsgcf e) cR HwfcR HwfaSrc HwfaImg x t Hxfv <In (x,t) Cfull>`.
(ALREADY WRITTEN in CtxReadback.v:994-1037.)

## Confirmed shapes
- `eq_term_wf_r (l) c e1 e2 t : wf_lang l -> wf_ctx l c -> eq_term l c t e1 e2
  -> wf_term l c e2 t`. (sort is the 1st explicit term-arg `t`; e2 is 2nd term.)
  So `eq_term_wf_r Hwf ltac:(constructor) Heqt : wf_term l [] ((con n0 s0)[/sg/])
  (t1[/sg/])` where `Heqt : eq_term l [] (t1[/sg/]) e' ((con n0 s0)[/sg/])`.
- Theorems.AddOpenSound invocation prefix (from existing CtxReadback uses):
  `@Theorems.faithful_rep_syn V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of
   X l Hwf Hsof Hsyn a eF sg Hsound (con n0 s0) Cfull t1 Hwfcf Hwfe1f x1 Hrep`.
- `subst_lookup sg x = named_list_lookup default sg x` for x∈dom sg via
  `nll_default_indep` (already in CtxReadback). x∈dom sg from `Hdomsgcf` +
  `In x (map fst Cfull)` (Cfull = pre++(x,t)::c').

## AdapterGlue discharge (call sites 2618, 3402)
`no_sort = term_eq_skip e1` (resp `sort_eq_skip t1`) `= andb
(syntactic_sort_eq_langb l) (inb x ...)`. Insert:
```
assert (Hsyn_skip : forall x, term_eq_skip e1 x = true -> syntactic_sort_eq l).
{ intros x Hx. unfold term_eq_skip in Hx.
  destruct e1; [rewrite Bool.andb_false_r in Hx; discriminate Hx|].
  rewrite Bool.andb_true_iff in Hx.
  exact (SyntacticSorts.syntactic_sort_eq_sound l (proj1 Hx) Hwf). }  (* shape TBD at build *)
```
and pass `Hsyn_skip` to the `_gen` inversion. (`syntactic_sort_eq_sound :
syntactic_sort_eq_langb l = true -> wf_lang l -> forall c t1 t2, eq_sort l c
t1 t2 -> t1 = t2` — i.e. literally `syntactic_sort_eq l`.)
