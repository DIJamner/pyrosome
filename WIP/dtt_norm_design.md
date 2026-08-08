# Normalization for the OTT dependent type theory — design (η revision)

Status: **plan**. Supersedes the pre-η version of this file. Two things changed:

1. **η is in.** `Lang/OTT/Pi.v` now proves `"Pi_rel eta"` with `push_rule` (the e-graph
   wf-check closes it in ~90 s); `ott_pi` is axiom-free, `push_rule_todo` is used nowhere in
   `src/`, and `WIP/DttPiNoEta.v` (the module boundary that existed only to dodge the `todo`
   hint) is obsolete. The target language is the **whole** of `ott_pi`, 69 rules.
2. **The plan had a hole**, at the point where the previous attempt died, and it is closed
   here by §4 (*code rigidity*). See §3.

Everything else — the layer decomposition, the `CutTModel` route, "state everything up to
`eq_term`", the empty meta-context — survives.

---

## 1. The target language

```
ott_dtt := ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info      (69 rules)
```

Census (computed, `named_map summ ott_dtt`): **32** `term_rule`, **28** `term_eq_rule`,
**9** `sort_rule`, **0** `sort_eq_rule`.

Sorts: `env`, `sub G G'`, `ty G i`, `exp G i A`, `tyinfo`, `relevance`, `lvl`, `tlvl`,
`ltl a b`. Types are terms of the sort `ty`; `exp` is indexed by such a term. There are no
sort equations anywhere, so `csort_by` is vacuous.

`ott_nat` is mandatory, not decoration: the closed codes are `Nat`, `Empty` and
`Pi_rel`/`Pi_irr` built from codes, so Π alone has no base case and without `ott_nat` every
universe is empty and the theorem vacuous. This is exactly the `unit_lang` situation of the
STLC proof.

Excluded for Phase 1: `Sigma`, `Id`, `Cast`, `ProofIrr`, `Computations`. `Cast` in
particular is *not* benign — its `u0` gives a code for a universe, which breaks §2's
key structural fact.

Argument-order gotchas, read off the compiled language (the surface notation disagrees):

```
snoc     -> con "snoc"      [v; g; A; i; G'; G]   (* v BEFORE g, unlike STLC *)
exp_subst-> con "exp_subst" [v; A; i; g; G'; G]
ty_subst -> con "ty_subst"  [A; i; g; G'; G]
ext      -> con "ext"       [A; i; G]
hd / wkn -> con "hd"/"wkn"  [A; i; G]
U        -> con "U"         [l; r; G]
El       -> con "El"        [e; l; r; G]
Pi_rel   -> con "Pi_rel"    [B; F; lG; lF; rF; G]
lam_rel  -> con "lam_rel"   [t; B; F; lG; lF; rF; G]
app_rel  -> con "app_rel"   [a; f; B; F; lG; lF; rF; G]
sorts:   scon "exp" [A;i;G]   scon "ty" [i;G]   scon "sub" [G';G]
```

---

## 2. The structural fact this proof is built on

> **In `ott_dtt`, the only neutral codes are variables. Equivalently: the code fragment is a
> free σ-algebra over universe-typed variables, with no βη content at all.**

Why. A *code* is a term of sort `exp G (info rel (next l)) (U G r l)`. Check every term
former that could produce one:

| former | result sort | a code? |
|---|---|---|
| `Nat`, `Empty`, `Pi_rel`, `Pi_irr` | `U …` | yes — the canonical codes |
| `zero`, `suc` | `El _ _ _ (Nat _)` | no |
| `lam_rel`, `lam_irr` | `El _ _ _ (Pi_… )` | no |
| `app_rel`, `app_irr` | `ty_subst ⟨id,a⟩ (El _ B)` | **no** — always an `El` |
| `Emptyrec` | `El G rA lA A` | **no** — always an `El` |
| `hd`, `exp_subst … x` | `ty_subst … A` for the declared `A` | yes iff `A` is a `U` |

There is **no eliminator whose result type is a universe** (no large elimination, no `natrec`
at all, no `u0` — that is `Cast`, excluded). So a neutral code is a variable, and the code
grammar is exactly

```
c ::= x | Nat G | Empty G | Pi_rel G rF lF lG c c | Pi_irr G rF lF c c
```

closed under substitution *structurally*: substituting into a code only ever replaces
universe-typed variables, and a reducible substitution supplies **normal codes** at those
slots. Three consequences, each of which the pre-η plan either got wrong or left open:

* **R2 dissolves.** "Normal codes are closed under reducible substitution" — which the old
  plan flagged as *the single lemma most likely to force a restructuring*, requiring the
  code-level fundamental theorem to be merged into Layer 2 — is now a **plain structural
  induction on the code**, provable in Layer 1 with no reducibility at all.
* **Type equality is a σ-calculus question.** Two normal types can be provably equal only
  through the substitution calculus; β and η live at `El`-sorts and can never rewrite a code.
* **Level stratification is a non-issue.** `RTy` (§5) is an inductive with no measure, so the
  unconstrained domain level `lF` of `Pi_rel` (old risk R1) costs nothing: a domain at `L1`
  is just a type whose only inhabitants are neutral, because there are no closed `L1` codes.
  **Both universe levels are in scope from the start**; the old plan's "Phase 1 restricts to
  `L0`" is dropped, and with it the old P9.

---

## 3. The hole in the old plan, and how §4 closes it

The old plan defined reducibility of a term as

```coq
RTmN G i A e := forall A0, TyOk G i A0 -> eq_term _ _ (sTy G i) A A0 -> RTm G i A0 e
```

— universally quantified over the *normal representatives* of the type — and asserted that
this is what makes `Ceq_sort` cheap ("two provably-equal sorts have literally the same set of
normal representatives"). That part is right. What it never states is the obligation this
creates **inside** a congruence case. Take `app_rel`. To produce `RTmN` for the conclusion one
is handed an arbitrary normal `A0` with `A0 ≡ (El B)[⟨id,a⟩]` and an arbitrary candidate `P`
for it, and must show `P` holds of the application. What the premises give is `Pc`, the
codomain candidate of *the* Π-derivation one built oneself, at *one's own* named normal
representative `C0 ≡ A0`. Closing the gap needs

```coq
RTy_fun_eq : RTy G i A P -> RTy G i B Q -> eq_term _ _ (sTy G i) A B -> forall e, P e <-> Q e
```

i.e. **non-confusion and injectivity for normal types up to provable equality**. Every
alternative formulation trades the problem around rather than removing it:

| `Ceq_term` at `exp` sorts | building it | using it |
|---|---|---|
| ∀ normal representative | needs `RTy_fun_eq` | free |
| ∃ normal representative | free | needs `RTy_fun_eq` |
| ∀ candidate given a *semantic* type equality | free | needs the Π clause to quantify over candidates, i.e. a **negative** occurrence of `RTy` — rejected by strict positivity |

This is the same wall the abandoned attempt hit, one level down (its `LogRel2Reflect.v` needed
`whnf` determinism and confluence, refused them, and the Π member relation stopped being
determined by its indices). In Abel–Öhman–Vezzosi the wall is not there because the logical
relation is stated over **weak-head reduction**, so non-confusion is syntactic. Pyrosome has
no reduction relation, only the equational theory, so it has to be earned.

§2 is what makes earning it cheap: the needed statement is about the **code fragment only**,
and that fragment has no β and no η.

---

## 4. Layer 0.5 — code rigidity (NEW; the load-bearing addition)

Goal, and the *only* thing this layer exports:

```coq
Theorem NfCode_inj G r l c1 c2 :
  NfCode G r l c1 -> NfCode G r l c2 ->
  eq_term ott_dtt [] (sCode G r l) c1 c2 -> c1 = c2.

Theorem TyOk_inj G i A1 A2 :
  TyOk G i A1 -> TyOk G i A2 -> eq_term ott_dtt [] (sTy G i) A1 A2 -> A1 = A2.

Theorem EnvOk_inj G1 G2 :
  EnvOk G1 -> EnvOk G2 -> eq_term ott_dtt [] sEnv G1 G2 -> G1 = G2.
```

*Syntactic* equality, not just same-head: it subsumes non-confusion **and** Π-injectivity, and
it makes `RTy_fun_eq` a corollary of the syntactic `RTy_fun` (which is an ordinary induction,
the six clauses being pairwise disjoint by head symbol).

**Method: a second, much smaller `CutTModel`** — the *rigid model* `DttRM` — that interprets
only the σ-fragment and is trivial everywhere else. Its `ceq_term` is, by sort:

| sort | `rceq_term` |
|---|---|
| `relevance`, `lvl` | syntactic equality of the (rigid) constructors |
| `tlvl`, `tyinfo` | equality of the index normal forms `ntlvl`/`ninfo` |
| `ltl a b` | `True` (proof-irrelevant, no content) |
| `env` | `RigEnv` — same normal environment |
| `sub G G'` | `RigSub` — same normal substitution (a `forget`-spined `snoc` chain) |
| `ty G i` | `RigTy` — same normal type |
| `exp G i A`, `A` universe-like | `RigCode` — same normal code |
| `exp G i A`, otherwise | `True` |

"Universe-like" is decided by the `TySkel : term -> bool -> Prop` invariant the old plan
already identified as available: the four equations at sort `ty` (`ty_subst_id`,
`ty_subst_cmp`, `U subst`, `El subst`) all preserve the `U`/`El` head, so `TySkel` is a
legitimate model invariant, and `U`-ness of a type is stable under provable equality.

The obligations that carry content are exactly the σ-calculus ones — `exp_subst_id`,
`exp_subst_cmp`, `snoc_hd`, `wkn_snoc`, `cmp_snoc`, `snoc_wkn_hd`, `id_left`, `id_right`,
`cmp_assoc`, `cmp_forget`, `id_emp_forget`, `ty_subst_id`, `ty_subst_cmp`, and the five
`X subst` commutations for `U`, `El`, `Nat`, `Empty`, `Pi_rel`, `Pi_irr`. Everything at an
`El`-sort, including **both β rules and η**, is discharged by `exact I`. That is the whole
point: *β and η never reach a code*, so the hard rules of the theory are invisible to this
model.

This is the analogue of what the old plan called "an auxiliary `CutTModel`, of the kind §3
shows *is* available", and which it then wrongly concluded was unavailable for codes. It was
unavailable for the *old* code grammar the author had in mind — one in which an eliminator
could land in `U`. In `ott_dtt` none can.

Effort estimate: a first-order normalization proof for explicit substitutions over a free
term algebra. Comparable to `Gluing/Stlc/RSub.v` + half of `NormalForms.v`, i.e. ~600–1200
lines, with no logical relation.

**Kill-switch.** If `NfCode_inj` is not proved by the end of Layer 0.5, stop and re-plan —
every later layer consumes it, and there is no second route to it.

---

## 5. Layers, revised

| layer | file | content |
|---|---|---|
| 0 | `Dtt/Syntax.v` | `ott_dtt`, `wf_lang ott_dtt` (axiom-free), sort/term abbreviations, index normalizers `ntlvl`/`ninfo` |
| 0.25 | `Dtt/Eqns.v` | the toolkit: `wf_*` and `*_cong` for all 32 formers, all 28 equations as `eq_term` lemmas in *dependent* form (the type rewritten alongside the term) |
| 1 | `Dtt/NormalForms.v` | the mutual block `EnvOk`/`TyOk`/`NfCode`/`VarT`/`NeET`/`NfET`; `Wk`; typing, weakening, and **code substitution** lemmas |
| 0.5 | `Dtt/Rigid.v` | the rigid model and `NfCode_inj`/`TyOk_inj`/`EnvOk_inj` (§4). Depends on Layer 1 only for the *statements* |
| 2 | `Dtt/LogRel.v` | `RTy` (candidate relation), `RTm`, escape/reflect, `RTy_fun`, `RTy_fun_eq`, weakening, the Π interface |
| 3 | `Dtt/RSub.v` | `RSub`; elimination, `RSub_id`, `RSub_wk`, `RSub_lift`, `RSub_proj` |
| 4a | `Dtt/Ceq.v` | `Ceq_term` (9 sort clauses), `Ceq_sort`, `DttCM : CutTModel` |
| 4b | `Dtt/Model*.v` | the 75 `CutTModel_ok` obligations |
| 4c | `Dtt/Normalization.v` | `DttCM_ok`, the three theorems, the smoke test |

`Gluing/CutTModel.v`, `Gluing/Eval.v`, `Gluing/CutModelSound.v` are reused unchanged.

---

## 6. Layer 1 with η: normal forms are η-long

The mutual block is six-way (`EnvOk`, `TyOk`, `NfCode`, `VarT`, `NeET`, `NfET`) with
`Combined Scheme`. Three things are specific to η, and one to dependency.

**(a) `NfET` has no neutral clause at a `Pi_rel` type.** The clauses are indexed by the
*normal type*, and dispatch on its head:

```
A = U G r l                       -> NfCode G r l e                (normal codes)
A = El G rel L0 (Nat G)           -> zero | suc n | neutral
A = El G irr L0 (Empty G)         -> neutral
A = El G r l c,  c neutral        -> neutral
A = El G rel lG (Pi_rel …)        -> lam_rel … t   ONLY            <-- η
A = El G irr L0 (Pi_irr …)        -> lam_irr … t | neutral         <-- no η for Pi_irr
```

`"Pi_irr eta"` is not a rule of `ott_pi` (upstream it is subsumed by proof irrelevance, and
`ProofIrr` is out of scope), so the irrelevant Π keeps the STLC-style shape. The asymmetry is
harmless — it just means one clause has a neutral case and the other does not.

**(b) The STLC `neet_lamapp` clause disappears.** It existed because `SimpleVSTLC` is
call-by-value and β fires only when both sides are `ret`s. `"Pi_rel beta"` fires for an
arbitrary argument, and there is no value/expression split in `ott_dtt` at all. A normal
function applied to anything is a redex, never stuck.

**(c) Neutrals carry a *named* normal type.** `app_rel`'s result type is `(El B)[⟨id,a⟩]`,
which is not a normal type. So the neutral clause is

```coq
| neet_app_rel : forall G rF lF lG F B f a C,
    NeET G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) f ->
    NfET G (iEl rF lF) (oEl G rF lF F) a ->
    TyOk G (iEl oRel lG) C ->
    eq_term ott_dtt [] (sTy G (iEl oRel lG))
      (oTySubst G (oExtC G rF lF F) (oInst G rF lF F a) (iEl oRel lG)
                (oEl (oExtC G rF lF F) oRel lG B)) C ->
    NeET G (iEl oRel lG) C (oAppRel G rF lF lG F B f a)
```

— the representative `C` is supplied at construction. By §2 it always exists and is
computable: `C = El G rel lG (B[⟨id,a⟩])` with the substitution pushed structurally through
the code `B`. That is Layer 1's `NfCode_subst`, and it is where the old R2 used to be.

**(d) `Wk`'s lift clause weakens the domain type**, so `Wk_wf` genuinely needs
`wf_term_conv` (`A[w][wkn]` vs `A[wkn ∘ w]`, agreeing only by `ty_subst_cmp`). Essentially
every Layer-1 typing lemma acquires such a conversion. Routine, high volume.

---

## 7. Layer 2 with η: escape and reflect become one induction

`RTy G i A P` relates a **syntactically normal** type to a candidate, as a strictly-positive
`Prop` inductive; the well-foundedness is strict positivity, not a measure (`Pd`/`Pc` are
constructor *parameters*, so the negative occurrence that forces induction–recursion in
Abel–Öhman–Vezzosi becomes a negative occurrence of a bound variable, which Coq accepts). The
universe clause's candidate is *"provably equal to a syntactic normal code"* — it does **not**
mention `RTy`, which is what kills the would-be negative occurrence there. Everything is in
`Prop`; the single `Prop`→`Type` bridge is `CutModelSound.v`'s `inhabited`, unchanged.

η changes the interface in the direction of *simplification*:

* **The Π candidate needs no `HasNf` conjunct.** Without η one has to carry "…and it has a
  normal form" separately, because a neutral at a Π type is already normal. With η the normal
  form of an inhabitant of a Π type *is* its η-expansion, so it is derivable.
* **Escape and reflect are one mutual induction on the `RTy` derivation.** At Π:
  * *reflect*: given a neutral `n`, show `P n`, i.e. that `n[w] a` is in the codomain
    candidate for every reducible `a`. By IH-escape at the domain, `a` has a normal form; so
    `n[w] a` is neutral (clause (c) above); by IH-reflect at the codomain, done.
  * *escape*: given `P e`, work in `D = ext G (iEl rF lF) (El G rF lF F)`. By IH-reflect at
    the domain, `hd` is reducible; so `Pc` holds of `(e[wkn]) hd`; by IH-escape at the
    codomain it has a normal form `t`; then `lam_rel … t` is a normal form of `e` **by η**.

  Without η the second bullet has no proof — the term is not equal to any λ — which is
  exactly why the old plan had to keep reification untyped and defer η to a later phase.
* `RTy_fun` (same syntactic type ⇒ same candidate) is an ordinary induction on the two
  derivations, the six clauses being disjoint by head symbol; `RTy_fun_eq` (§3) then follows
  from `TyOk_inj` (§4) with no further work.

---

## 8. Layer 4: what the model looks like

`Ceq_term` is an inductive family over the 9 sorts (so off-diagonal sorts are uninhabited for
free). At the two interesting sorts:

```coq
| ceq_ty  : forall G i A1 A2,
    eq_term ott_dtt [] (sTy G i) A1 A2 ->
    (forall D g, EnvOk D -> RSub D G g ->
       exists A0 P, TyOk D (ninfo i) A0
                 /\ eq_term _ _ (sTy D (ninfo i)) (oTySubst D G g i A1) A0
                 /\ RTy D (ninfo i) A0 P) ->
    Ceq_term (sTy G i) A1 A2
| ceq_exp : forall G i A e1 e2,
    eq_term ott_dtt [] (sExp G i A) e1 e2 ->
    (forall D g, EnvOk D -> RSub D G g ->
       RTmN D (ninfo i) (oTySubst D G g i A) (oExpSubst D G g i A e1)) ->
    Ceq_term (sExp G i A) e1 e2
```

with `RTmN` the ∀-over-normal-representatives form of §3 — now legitimate, because
`RTy_fun_eq` is available. `Ceq_sort` stays as in the old plan:

```coq
Definition Ceq_sort (t1 t2 : sort) : Prop :=
  eq_sort ott_dtt [] t1 t2
  /\ (forall e1 e2, Ceq_term t1 e1 e2 -> Ceq_term t2 e1 e2)
  /\ (forall e1 e2, Ceq_term t2 e1 e2 -> Ceq_term t1 e1 e2).
```

Sort equality *is* the bidirectional transfer, so `cterm_conv`, `csort_trans`, `csort_sym` are
one line each, `csort_by` is vacuous (no `sort_eq_rule`s), and all the work is in `csort_cong`
— 9 cases, 5 nullary, `ltl` proof-irrelevant, leaving `sub`, `ty`, `exp` substantive. The
semantic conjunct constrains only `e1`; the fact for `e2` is recovered from the equation, as
in `Gluing/Stlc/ModelCong.v`.

Obligation count: `cterm_cong` 32, `cterm_by` 28, `csort_cong` 9, `csort_by` 0, structural 6
— **75** (STLC was 45).

---

## 9. Phases

| phase | content | main risk |
|---|---|---|
| **P0** ✅ | η proved in `Lang/OTT/Pi.v`; `ott_pi` axiom-free; the abandoned `OTT/Norm` deleted | — |
| **P1** | Layer 0 + the equation toolkit | volume; e-graph blowup (run under `ulimit -v 4500000`, never let `by_reduction` see a whole obligation) |
| **P2** | Layer 1, incl. `NfCode_subst` (the old R2) | (c) above |
| **P3** | **Layer 0.5, code rigidity** | **the kill-switch** |
| **P4** | Layer 2 | escape/reflect at Π |
| **P5** | Layer 3 | — |
| **P6** | Layer 4a + the structural, index and σ obligations (≈ 40) | volume |
| **P7** | Layer 4b for the 13 new formers + β + η | — |
| **P8** | Layer 4c, theorems, smoke test | — |
| **P9** | extensions: `ProofIrr`, `Sigma`, `Id`, `Computations` | — |
| **—** | `Cast` | **breaks §2**: `u0` is a code for a universe, so eliminators can land in `U`, code rigidity fails, and the whole architecture reverts to the induction–recursion problem. Do not add `Cast` without redesigning Layers 0.5 and 2 |

## 9b. The index-spelling mismatch, and why it is not an authoring bug

`tlvl` has `next0` (`next L0 = iota L1`) and `next1` (`next L1 = inf`), and the compiled rules of
`ott_dtt` do not agree on which representative to use — not merely between neighbouring rules, but
between a term rule and its own substitution equation: `"Nat"` concludes at `rel (next L0)` and
`"Nat subst"` at `rel (iota L1)`; `"Empty"` at `rel (iota L1)` and `"Empty subst"` at
`rel (next L0)`; the codomain code `B` sits at `rel (iota L1)` in `"Pi_irr"`/`"Pi_irr subst"`/
`"Pi_irr beta"` but at `rel (next L0)` in `"lam_irr"`/`"app_irr"`.

**Writing the ideal representation in the prerule does not fix it.** `Lang/OTT/Nat.v` already
writes `rel (next L0)` uniformly in all four Nat/Empty rules. `Elab.PreRule`'s `infer_rule` does
not take the written conclusion sort as authoritative: it loads the sort into an e-graph,
saturates, and re-**extracts** a representative with `TypeInference.mk_weight`, which charges 1
per non-hole atom. `info rel (next L0)` and `info rel (iota L1)` both cost 4, so the winner is an
arbitrary tie-break, and it depends on the *ambient language* rather than on the rule. Both halves
checked directly:

* `infer_rule (ott_base ++ subst_ott ++ ott_info) inj` applied to the `"Empty"` rule returns
  `next L0` whether the prerule is written with `next L0` or with `iota L1` — the two prerules
  elaborate to the **identical** rule;
* inside `Nat.v`'s `Derive`, where the base has grown by `Nat`/`zero`/`suc` and their substitution
  equations, the same rule comes out `iota L1`.

Fixing it at the source would mean either hand-elaborating the affected rules and adding them with
`push_rule` (as `Pi.v` now does for η), or changing the extraction weight in
`Tools/EGraph/TypeInference.v` — which re-elaborates every language in the project.

**The cheap fix is to let the e-graph bridge it.** `WIP/DttIdx.v`'s `egraph_eq` discharges the
index equations in 0.005 s of tactic time and 0.7 s at `Qed`, axiom-free; the conversion lemmas
built on them (`eq_sort_ty_cong`, `eq_sort_exp_cong`, `eq_sort_exp_ty`, `wft_U0irr_next`,
`wft_U0irr_iota`) live in `WIP/DttNfWf.v`. Every conversion the development needs falls into
exactly two families: this `next0` spelling mismatch, and the *named normal type* of a variable or
neutral (bridged by the clause's own `eq_term` premise).

## 10. What the previous attempt got wrong (unchanged, still worth heeding)

17 581 lines, three mutually incompatible architectures, zero `Admitted`, no fundamental
lemma. (1) It rebuilt the substitution metatheory *outside* the theory, on an external value
domain — ~3 900 lines whose only job was to re-derive what the Pyrosome equational theory
already has, and the relational `Apply` was *partial*, which its own `RenSubst.v:82` calls
fatal. (2) The `Prop`/`Type` mismatch was relocated, never resolved: the hard direction was
never even stated. (3) Layers B and C shared nothing and neither imported the other; three
files never compiled. (4) The universe tower needed universe polymorphism and two recursors,
which made "assume the hard case, check the rest is green" *structurally unavailable* — the
one failure mode I would call unfixable in place. (5) η was designed around, repeatedly.

All five are avoided by: staying inside the theory (everything up to `eq_term`), staying in
`Prop`, one architecture with one file per layer, no universe tower (§7), and η first (§6).
