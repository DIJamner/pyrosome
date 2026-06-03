# posRR Hrev recovery lemma — design (S69)

Goal: provide the `Hrev` hypothesis that `central_msr_seqs_rev` (AdapterGlue.v) needs for the REAL posRR:
  Hrev : forall n r', In (n,r') posRR -> exists r0, In (n,r0) Lp /\ r' = rev_rule r0
where (Automation.v:311-318)
  Lp    = fst (rename_lang (ctx_to_rules c ++ l) init)
  posRR = fst (rename_lang (ctx_to_rules c ++ named_map rev_rule (filter (fun p=>reversible p&&lf p) l)) r4)
with `rename_grows` from Lp's renaming state down to posRR's.

This sits at the RENAMING layer (V→positive), top-level (NOT inside Section Adapter).

## Placement
Put both lemmas in `src/Pyrosome/Tools/EGraph/AdapterGlue.v`, at TOP LEVEL inside the
outer `Section WithVar` (the one with V/Eqb etc.), BEFORE `Section Adapter`.
Add import: `From Pyrosome.Tools Require Import PosRenamingProperties.`
(ACYCLIC: PosRenamingProperties imports only Core/PosRenaming/Renaming; AdapterGlue is a leaf
imported by nothing. EGraph.Defs (already imported, gives rev_rule = PositiveInstantiation.rev_rule)
and PosRenamingProperties are mutually independent.) Verify by building AdapterGlue.vo.

Reuse from PosRenamingProperties (model: `rename_lang_filter_incl`, line 1665): `pos_of_v`,
`pos_of_v_matches`, `f_matches`, `f_matches_grows`, `rename_grows_trans`, `rename_lang_correct`,
`rename_lang_via_f`. `Renaming.rename_lang`/`Renaming.rename_rule` from Theory.Renaming
(rename_lang = map (fun p => (f (fst p), rename_rule f (snd p))); rename_rule case-matches the 4
rule ctors, renaming uniformly).

## Helper 1: rev_rule commutes with renaming (trivial)
```
Lemma rename_rule_rev_commute (g : V -> positive) (r : rule) :
  Renaming.rename_rule g (rev_rule r) = rev_rule (Renaming.rename_rule g r).
Proof. destruct r; reflexivity. Qed.
```
(`rev_rule` swaps the two eq-sides; rename_rule renames uniformly ⇒ they commute. Non-eq rules:
both sides identity. `rev_rule` here = `PositiveInstantiation.rev_rule` (qualify as central_msr_seqs_rev does).
Note types: input `rule` = rule V, output rule positive; rev_rule is generic {V} so both typecheck.)

## Helper 2: named_map inverse membership (prove inline if not in NamedList)
```
Lemma in_named_map_inv {A B} (g:A->B) X n y :
  In (n,y) (named_map g X) -> exists x, y = g x /\ In (n,x) X.
Proof. induction X as [|[n0 a0] X IH]; cbn; [contradiction|]. intros [H|H]; [inversion H; subst; eauto | destruct (IH H) as (x&?&?); eauto]. Qed.
```
(Check NamedList.v first — there is `in_named_map` forward (line 272); if no inverse, add this locally.)

## Main lemma
```
Lemma rename_lang_rev_filter_recovers
    (cc l : lang) (pf : V * rule -> bool)
    (Hcc : forall n0 r0, In (n0, r0) cc -> rev_rule r0 = r0)
    (r ra rb rc : renaming) (Lp posRR : list (positive * prule)) :
  renaming_ok r ->
  rename_lang (cc ++ l) r = (Lp, ra) ->
  rename_grows ra rb ->
  renaming_ok rb ->
  rename_lang (cc ++ named_map rev_rule (filter pf l)) rb = (posRR, rc) ->
  forall n r', In (n, r') posRR -> exists r0, In (n, r0) Lp /\ r' = rev_rule r0.
```
Match `rename_lang_filter_incl`'s exact binder types: `Lp posRR : list (positive * prule)`,
`prule := Rule.rule positive`, `lang := named_list rule`, etc.

### Proof skeleton (mirror rename_lang_filter_incl's via-f preamble verbatim, then case-split)
```
intros Hcc Hr HrL Hgrow Hrb HrPRR.
pose proof (rename_lang_correct _ Hr HrL) as (Hraok & _ & _ & _).
pose proof (rename_lang_correct _ Hrb HrPRR) as (Hrcok & Hg_bc & _ & _).
set (f := pos_of_v rc).
assert (Hfm_c : f_matches f rc) by exact (pos_of_v_matches Hrcok).
assert (Hg_ac : rename_grows ra rc) by exact (rename_grows_trans Hgrow Hg_bc).
assert (Hfm_a : f_matches f ra) by exact (f_matches_grows (f:=f) Hraok Hrcok Hg_ac Hfm_c).
rewrite (rename_lang_via_f (f:=f) _ Hr HrL Hfm_a).        (* Lp    -> Renaming.rename_lang f (cc++l) *)
rewrite (rename_lang_via_f (f:=f) _ Hrb HrPRR Hfm_c).      (* posRR -> Renaming.rename_lang f (cc++named_map rev_rule (filter pf l)) *)
unfold Renaming.rename_lang.
intros n r' Hin.
rewrite map_app, in_app_iff in Hin.
destruct Hin as [Hin_cc | Hin_rev].
- (* cc part: r' = rename_rule f r0, (n0,r0) in cc, rev_rule r0 = r0 *)
  apply in_map_iff in Hin_cc as ([n0 r0] & Heq & Hmem0).
  inversion Heq; subst n r'. clear Heq.
  exists (Renaming.rename_rule f r0). split.
  + rewrite map_app, in_app_iff; left; apply in_map_iff; exists (n0, r0); split; [reflexivity| exact Hmem0].
  + rewrite <- rename_rule_rev_commute, (Hcc n0 r0 Hmem0); reflexivity.
- (* rev-filter part: r' = rename_rule f (rev_rule r1), (n0,r1) in filter pf l *)
  apply in_map_iff in Hin_rev as ([n0 r0rev] & Heq & Hmem_rev).
  inversion Heq; subst n r'. clear Heq.
  apply in_named_map_inv in Hmem_rev as (r1 & Hr0rev & Hmem1).   (* r0rev = rev_rule r1 *)
  subst r0rev.
  apply filter_In in Hmem1 as (Hmem1l & _).
  exists (Renaming.rename_rule f r1). split.
  + rewrite map_app, in_app_iff; right; apply in_map_iff; exists (n0, r1); split; [reflexivity| exact Hmem1l].
  + rewrite rename_rule_rev_commute; reflexivity.
```
GOTCHAS:
- `inversion Heq` on the pair equation `(f (fst p), rename_rule f (snd p)) = (n, r')` may need `cbn [fst snd] in Heq` first, or use `Pairs`/`pair_equal_spec`. Adjust.
- the goal element `g (n0,r0)` where g = `fun p => (f (fst p), Renaming.rename_rule f (snd p))` — `in_map_iff` witness `(n0,r0)` with `split;[reflexivity|…]` needs the function applied to (n0,r0) to be `(f n0, rename_rule f r0)`; `cbn` if needed.
- `rev_rule` must be written exactly as `PositiveInstantiation.rev_rule` if that's how it resolves (the `named_map rev_rule` in posRR uses the SAME one — confirm by matching Automation.v:317's `rev_rule`).

## Callsite discharge (for the FUTURE assembly, not this task)
Hcc for cc = ctx_to_rules c: `ctx_to_rules = named_map (fun t => term_rule [] [] (sort_var_to_con t))`
(Defs.v:76) ⇒ every rule is a term_rule ⇒ rev_rule = identity. Prove
`forall n0 r0, In (n0,r0) (ctx_to_rules c) -> rev_rule r0 = r0` via in_named_map_inv (r0 = term_rule…) then `reflexivity`.

## Verify
- AdapterGlue.vo builds clean (confirms acyclic import + lemma). ABSOLUTE-path make target.
- rocq_assumptions on `rename_lang_rev_filter_recovers` = axiom-free.
- Do NOT commit (Opus reviews + commits).
