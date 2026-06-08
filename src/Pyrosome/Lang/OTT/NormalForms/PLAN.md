# OTT Normalization via In-Language Normal-Form Extension

## Context

The current OTT normalization effort (branch `gluing-nbe`) builds a `Type`-valued logical-relations / NbE tower over an external value domain, and has repeatedly stalled: a `Prop→Type` elimination wall (`wf_term` is `Prop`, the reducibility relation is `Type`), eta-falsity at Pi, and a universe tower needing `RR_pi_at` as an abstract premise. (See MEMORY: `ott-logrel2-*`, `ott-pivot-reduction-on-syntax`, `next-session-kickoff`.)

This plan abandons that direction and reframes normalization **entirely inside Pyrosome's own machinery**: normal and neutral forms become *object-level sorts* in a language extension of OTT; the embeddings are *object-level term rules with equations*; "normal forms are derivable" is a *verified Pyrosome compiler*; decidability is *syntactic equality*; and "every term has a normal form" is a *gluing model* à la `Gluing/CutTModel.v`. The intended payoff is decidability of OTT conversion, reached without any `Type`-valued metatheoretic relation threaded through the development — the user-facing content lives entirely against `Model` (whose `eq_*`/`wf_*` are `Prop`), which is why this sidesteps the prior wall.

**Setup:** create a new branch off `gluing-nbe`, e.g. `git checkout -b ott-nf-extension`.

**Resolved design decisions (from the user):**
- **nf/ne sorts indexed by BASE `G`/`i`/`A`** (the same indices `exp`/`ty` use). Indexing by *normal* contexts/types was considered and rejected: it forces a hereditary-substitution calculus into the definitions (the `ne_app` result type `B[a]` and the `vz`/`vs` types would need normal-form weakening/instantiation), which defeats the clean equation-free decidability story. Keeping base indices keeps the nf/ne fragment equation-free among its own sorts and the collapse compiler trivial.
- **Eta-long (gated) normal forms.** `nf_ne` admitted only at neutral/base type codes, never at `El(Pi_rel …)`. Gives unique eta-long normal forms ⇒ syntactic equality of nfs = judgmental equality (a *complete* decision procedure). Cost: the model must eta-expand neutrals at Pi.
- **Minimal fragment first:** `subst_ott + ott_base (U/El) + Pi_rel + Nat`. Defer `Pi_irr`, `Sigma`, `Id`, `Cast`, and higher levels.
- **Object-level `nf_sub`/`nf_ctx` sorts** (list-shaped), in addition to their use as model carriers. The no-sub-in-neutrals constraint is preserved: neutrals embed de Bruijn `var`s, never substitutions; `nf_sub` is an independent snoc-list of `nf_exp`.

## Confirmed ground truth (do not re-derive)

From `src/Pyrosome/Lang/Subst.v` + tyinfo-parameterization in `src/Pyrosome/Lang/OTT/Base.v:158-183`:
- `#"env" srt`; `#"ty" "G" "i" srt` (`i : #"tyinfo"`); `#"exp" "G" "i" "A" srt` (`A : #"ty" "G" "i"`); `#"sub" "G" "G'" srt`.
- `#"hd" : #"exp" (#"ext" "G" "A") "i" (#"ty_subst" #"wkn" "A")`; `#"wkn" : #"sub" (#"ext" "G" "A") "G"`; `#"snoc" "g" "v" : #"sub" "G" (#"ext" "G'" "A")`; `#"exp_subst" "g" "v" : #"exp" "G" "i" (#"ty_subst" "g" "A")`.
- Pi (`OTT/Pi.v`), code style (`exp` of `U`, decoded by `El`): `#"Pi_rel" "rF" "lF" "lG" "F" "B" : #"exp" "G" (#"info" #"rel" (#"next" "lG")) (#"U" #"rel" "lG")`; `#"lam_rel" … "t" : #"exp" "G" (#"info" #"rel" (#"iota" "lG")) (#"El" (#"Pi_rel" …))`; `#"app_rel" … "f" "a" : #"exp" "G" … (#"ty_subst" (#"snoc" #"id" "a") (#"El" "B"))`.
- `CutTModel` (`Gluing/CutTModel.v:55`): `ceq_sort : sort->sort->Type`, `ceq_term : sort->term->term->Type`, **fixed ambient context, NO substitution case**. `CutTModel_ok` operations = cterm_var/cong/by/trans/sym/conv + csort_cong/by/trans/sym.
- Decidable syntactic equality already exists: `term_eqb`/`term_eqb_ok` (`Theory/Term.v:159-240`).
- Compiler obligations: `preserving_compiler_ext` (`Compilers/CompilerDefs.v:173`) — sort rule ↦ `Model.wf_sort` of compiled sort; term rule ↦ `Model.wf_term`; sort_eq/term_eq ↦ `Model.eq_sort`/`Model.eq_term`. Lifted by `inductive_implies_semantic` (`Compilers/Compilers.v:1122`). Elaborated-compiler idiom: `Derive … in (elab_preserving_compiler …) … Proof. auto_elab_compiler. Qed.` (`Lang/SimpleVCC.v:117-151`).

## File layout (new, under `src/Pyrosome/Lang/OTT/NormalForms/`)

```
NormalForms/
  Defs.v       — the extension ott_nf: new sorts (var, ne/nf exp & ty, nf_sub, nf_ctx),
                 constructors, eta-gated nf_ne, and embedding equations into base.
  Compiler.v   — nf_to_ott collapse compiler + preservation theorem.
  DecEq.v      — eq_term over the no-equation nf/ne sorts = syntactic eq; decidability.
  Model.v      — (HARD; its own follow-up plan) gluing model: base sorts ↦ nf carriers;
                 the "every term has a normal form" theorem.
```
Base fragment: `Definition ott := ott_nat ++ ott_pi ++ ott_base ++ subst_ott ++ ott_info.` (confirm `ott_pi`/`ott_nat` are the right names when implementing.)

## Phase 1 — `Defs.v`: the extension language `ott_nf`

Build with `Derive ott_nf in (wf_lang_ext ott ott_nf) … Proof. auto_elab. Qed.`, falling back to `setup_lang_interactive`/`push_rule`/`compute_wf_rule` on dependently-indexed rules (the documented `OTT/Pi.v` workaround). All new sorts/constructors carry injectivity entries (mirror `subst_ott_injectivity`).

**1a. De Bruijn variables** (intrinsically typed; NO `sub` sub-term — index uses only `ty_subst wkn`, forced by `hd`'s type):
- `#"var" "G" "i" "A" srt`.
- `#"vz" : #"var" (#"ext" "G" "A") "i" (#"ty_subst" #"wkn" "A")`.
- `#"vs" "B" "x" : #"var" (#"ext" "G" "B") "i" (#"ty_subst" #"wkn" "A")` for `x : #"var" "G" "i" "A"`, `B : #"ty" "G" "j"`.

**1b. Neutral / normal sorts** (indexed by *base* `G,i,A` — same indices as `exp`/`ty`):
- `#"ne_exp" "G" "i" "A" srt`, `#"nf_exp" "G" "i" "A" srt`, `#"ne_ty" "G" "i" srt`, `#"nf_ty" "G" "i" srt`.

**1c. Neutral constructors** (never carry a `sub`):
- `#"ne_var" "x" : #"ne_exp" "G" "i" "A"` for `x : #"var" "G" "i" "A"`.
- `#"ne_app" "rF" "lF" "lG" "F" "B" "f" "a"`: head `f : #"ne_exp" "G" … (#"El" (#"Pi_rel" …))`, arg `a : #"nf_exp" "G" … (#"El" "F")`, result `#"ne_exp" "G" … (#"ty_subst" (#"snoc" #"id" (#"nf2exp" "a")) (#"El" "B"))`. (The index uses `nf2exp "a"` so it lives in base syntax — see 1f.)
- Nat eliminator neutral `#"ne_natrec" …` with scrutinee `n : #"ne_exp" … (#"El" Nat-code)`; motive/branches normal.

**1d. Normal constructors** (eta-long):
- `#"nf_lam" "rF" "lF" "lG" "F" "B" "t" : #"nf_exp" "G" … (#"El" (#"Pi_rel" …))` with body `t : #"nf_exp" (#"ext" "G" (#"El" "F")) … (#"El" "B")`. **The only normal at a Pi code.**
- `#"nf_zero"`, `#"nf_suc" "n"` (`n : #"nf_exp" … Nat`).
- Type-level normals: `#"nf_U" "r" "l" : #"nf_ty" "G" (#"info" #"rel" (#"next" "l"))`; `#"nf_El" "e" : #"nf_ty" "G" (#"info" "r" (#"iota" "l"))` for a *normal/neutral* code `e`; `#"nf_Nat"`; and the neutral type `#"ne_El" "m"` for `m : #"ne_exp" … U`.

**1e. The eta-positivity gate** — admit neutral-as-normal *only at neutral/base type codes*, never at `El(Pi_rel …)`:
- `#"nf_ne_at" "n" "m" : #"nf_exp" "G" "i" (#"nf2ty" "n")` where `n : #"ne_ty" "G" "i"` (a neutral type code, e.g. `ne_El` of a neutral, or `Nat`) and `m : #"ne_exp" "G" "i" (#"nf2ty" "n")`. Because the gate is the *sort of the type index* (`nf2ty` of a neutral code), there is statically no way to form `nf_ne_at` at `El(Pi_rel …)`. Smoke test: assert no introduction of `nf_exp G i (El (Pi_rel …))` other than `nf_lam`.

**1f. `nf_sub` / `nf_ctx`** (object sorts, list-shaped; carry normal exps/types, NOT base subs):
- `#"nf_ctx" srt`; `#"nf_emp_ctx" : #"nf_ctx"`; `#"nf_ext_ctx" "Gn" "An" : #"nf_ctx"` (`An : #"nf_ty" …`).
- `#"nf_sub" "G" "G'" srt`; `#"nf_forget" : #"nf_sub" "G" #"emp"`; `#"nf_snoc" "gn" "vn" : #"nf_sub" "G" (#"ext" "G'" "A")` (`vn : #"nf_exp" …`). No `nf_wkn`/`nf_cmp`/`nf_id` — those normalize into snoc-lists.

**1g. Embedding term rules + equations** (every equation concludes at a *base* sort):
- Maps: `#"var2exp" "x" : #"exp"`, `#"ne2exp" "m" : #"exp"`, `#"nf2exp" "t" : #"exp"`, `#"nf2ty" "n" : #"ty"`, `#"nfsub2sub" "gn" : #"sub"`, `#"nfctx2env" "Gn" : #"env"`.
- Equations (`term_eq_rule`/`sort_eq_rule`): `var2exp vz = hd`; `var2exp (vs B x) = exp_subst wkn (var2exp x)`; `ne2exp (ne_var x) = var2exp x`; `ne2exp (ne_app … f a) = app_rel … (ne2exp f) (nf2exp a)`; `nf2exp (nf_lam … t) = lam_rel … (nf2exp t)`; `nf2exp (nf_ne_at n m) = ne2exp m`; `nf2exp nf_zero = zero`; `nf2exp (nf_suc n) = suc (nf2exp n)`; `nf2ty (nf_U r l) = U r l`; `nf2ty (nf_El e) = El (nf2exp e)`; `nfsub2sub nf_forget = forget`; `nfsub2sub (nf_snoc gn vn) = snoc (nfsub2sub gn) (nf2exp vn)`; etc.

## Phase 2 — `Compiler.v`: collapse compiler `nf_to_ott : ott_nf → ott`

`compiler_case` list (`match # from ott_nf with …` style). Sorts collapse onto their base denotation; constructors map to the denotation; embeddings collapse to the identity (a bound variable), so each embedding equation's two sides compile to *syntactically identical* base terms ⇒ obligation closed by reflexivity.

```
| {{s #"var" "G" "i" "A"}}    => {{s #"exp" "G" "i" "A"}}
| {{s #"ne_exp" "G" "i" "A"}} => {{s #"exp" "G" "i" "A"}}
| {{s #"nf_exp" "G" "i" "A"}} => {{s #"exp" "G" "i" "A"}}
| {{s #"ne_ty" "G" "i"}}      => {{s #"ty" "G" "i"}}
| {{s #"nf_ty" "G" "i"}}      => {{s #"ty" "G" "i"}}
| {{s #"nf_sub" "G" "G'"}}    => {{s #"sub" "G" "G'"}}
| {{s #"nf_ctx"}}             => {{s #"env"}}
| {{e #"vz" …}}               => {{e #"hd"}}
| {{e #"vs" … "x"}}           => {{e #"exp_subst" #"wkn" "x"}}
| {{e #"ne_app" … "f" "a"}}   => {{e #"app_rel" … "f" "a"}}
| {{e #"nf_lam" … "t"}}       => {{e #"lam_rel" … "t"}}
| {{e #"nf_ne_at" "n" "m"}}   => {{e "m"}}
| {{e #"nf_zero" …}}          => {{e #"zero"}}
| {{e #"nf_suc" … "n"}}       => {{e #"suc" "n"}}
| {{e #"nf_snoc" … "gn" "vn"}}=> {{e #"snoc" "gn" "vn"}}
| {{e #"nf_forget" …}}        => {{e #"forget"}}
| {{e #"var2exp" … "x"}}      => {{e "x"}}      (* identity *)
| {{e #"ne2exp"  … "m"}}      => {{e "m"}}
| {{e #"nf2exp"  … "t"}}      => {{e "t"}}
| {{e #"nf2ty"   … "n"}}      => {{e "n"}}
| {{e #"nfsub2sub" … "gn"}}   => {{e "gn"}}
| {{e #"nfctx2env" … "Gn"}}   => {{e "Gn"}}
(* + ne_var, nf_U, nf_El, nf_Nat, ne_El, nf_ext_ctx, nf_emp_ctx, ne_natrec *)
```

Goal + discharge:
```
Derive nf_to_ott in (elab_preserving_compiler [] ott nf_to_ott_def nf_to_ott ott_nf)
  as nf_to_ott_preserving.
Proof. auto_elab_compiler. Qed.
```
Then `elab_compiler_implies_preserving` + `inductive_implies_semantic` give: every `ott_nf`-judgment maps under `compile` to an `ott`-judgment — i.e. **`ott_nf` is a conservative/derivable extension of `ott`**. This milestone validates that the whole design is coherent and must be reached before any model work.

## Phase 3 — `DecEq.v`: syntactic = judgmental equality at nf sorts

Statement (honest about index conversion):
```
Theorem nf_eq_term_iff_syntactic c G i A e1 e2 :
  wf_term (ott_nf ++ ott) c e1 (scon "nf_exp" [A;i;G]) ->
  (eq_term (ott_nf ++ ott) c (scon "nf_exp" [A;i;G]) e1 e2 <-> e1 = e2).
```
(and `ne_exp`, `nf_ty`, `ne_ty`, `var`). Proof: run on the **cut-free** derivation (`Theory/CutElim.v`) so only `refl`/`cong`/`by`/`sym`/`trans`/`conv` appear. `by` is impossible — no `term_eq_rule` concludes at an nf/ne/var sort (Phase-1 invariant: every embedding equation concludes at a *base* sort). `cong` collapses argument-wise by IH. The one subtlety is `conv`: there is no `sort_eq_rule` between two `nf_exp` sorts other than equality of their index annotations `(A,i,G)`, so the *carried nf syntax* is syntactically unique while the *type annotation* may vary by conversion. Document the precise theorem as "nf term unique modulo index conversion"; for closed/ground normal indices this reduces to `term_eqb` again. Decidability corollary is immediate from `term_eqb_ok`.

## Phase 4 — `Model.v`: every term has a normal form (SKETCH — own follow-up plan)

Research-risky; defer detailed design to a second plan. Shape: a `CutTModel`-style gluing model whose carriers are normal forms — base `exp G i A ↦ nf_exp`, `ty G i ↦ nf_ty`, `sub ↦ nf_sub`/list, `env ↦ nf_ctx`/list — with model equality = **syntactic** equality of the nf carrier (this is what makes "unique nf" fall out). The `CutTModel_ok` operations must *compute* nfs: `app_rel` ↦ hereditary substitution / NbE eval on nf syntax; `hd`/`wkn`/`snoc`/`cmp` ↦ the de Bruijn `var` + a **Kripke/presheaf renaming** structure (nf carriers functorial in weakenings, `wkn` = the `vs` shift); the `…_by` ops (beta/eta/subst equations) ↦ proven to preserve the nf carrier. Eta-long output (forced by the Phase-1 gate) means **reflect must eta-expand at Pi**, which `OTT/Norm/Reify.v` does not yet do.

Target theorem:
```
Theorem every_term_has_nf c G i A e :
  wf_term ott c e (scon "exp" [A;i;G]) ->
  exists t, wf_term (ott_nf ++ ott) c t (scon "nf_exp" [A;i;G]) /\
            eq_term ott c (scon "exp" [A;i;G]) e (compile nf_to_ott t).
```
Combined with Phase 3 (nf syntactic-eq decides nf judgmental-eq) and Phase 2 (embedding sound), this yields **decidability of OTT conversion** on the fragment.

Reusable: `Gluing/{CutTModel,SyntacticModel,Eval}.v` (the model framework + the `eval` fold that turns a `CutTModel_ok` into a `Prop` `eq_term` conclusion — note `SyntacticModel.v` already does this with no universe trouble); `OTT/Norm/{Domain,EvalRel,Reify,Determinism,ApplyLemmas,Preservation,Typing}.v` (eval/readback/hereditary-substitution logic, incl. `OTT/Norm/Pi/{Apply,Domain}.v`'s `Apply`/`Vapp`/cutoff-shift, to be adapted to nf-syntax carriers). Genuinely new and central: the named-explicit-sub ↔ de-Bruijn-neutral Kripke bridge and eta-long reflect. Recommendation: land the framework on the binder-free part (U/El/Nat) first, then tackle Pi.

## Milestones & risk

1. **Defs.v** — mostly mechanical; risk medium-low (`auto_elab` may stall on dependent indices → `push_rule` fallback). Validates the gate encoding.
2. **Compiler.v** — mechanical *if* `auto_elab_compiler`'s e-graph inference cooperates on `ne_app`/`nf_lam`; risk medium. Proves conservativity. **Reach this before Phase 4.**
3. **DecEq.v** — moderate; the cut-free induction is routine, the conversion/index caveat is the only subtlety.
4. **Model.v** — high risk, own follow-up plan; do U/El/Nat before Pi.

Risks: (a) **gate** too strict/loose — guard with the no-`nf_ne_at`-at-Pi smoke test; (b) **Prop/Type wall** — avoided: all of Phases 1–3 are stated against `Prop`-valued `Model`; the only `Type` layer is the local `CutTModel` in Phase 4, which `Eval.v` consumes into a `Prop` conclusion (a flat record, no `LR` universe tower); (c) **de Bruijn `A[wkn]` transport towers** from iterated `vs` — keep indices explicit; (d) **Kripke/eta-long reflect** in Phase 4 — the real research content.

## Verification

- Per-file single builds only (full build is an hour+): `make -f Makefile.coq src/Pyrosome/Lang/OTT/NormalForms/Defs.vo`, then `…/Compiler.vo`, `…/DecEq.vo`.
- Use the rocq-mcp tools (`rocq_check`, `rocq_assumptions`) to confirm each milestone lemma is `Qed` and **axiom-clean** (only the pre-existing `egraph_sound`), per the project's axiom-hygiene norm.
- Phase 1 acceptance: `ott_nf` is `wf_lang_ext ott`. Phase 2: `nf_to_ott_preserving` Qed'd. Phase 3: `nf_eq_term_iff_syntactic` Qed'd + a decidability corollary. Phase 4: `every_term_has_nf` Qed'd (follow-up plan).
