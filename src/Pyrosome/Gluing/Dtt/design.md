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
ott_dtt := ott_proofirr_el ++ ott_subst_commute ++ ott_pi ++ ott_nat ++ ott_base
             ++ subst_ott ++ ott_info                                  (74 rules)
```

Census (computed, `named_map summ ott_dtt`): **32** `term_rule`, **33** `term_eq_rule`,
**9** `sort_rule`, **0** `sort_eq_rule`. `ott_subst_commute` is §9a's fix.

Sorts: `env`, `sub G G'`, `ty G i`, `exp G i A`, `tyinfo`, `relevance`, `lvl`, `tlvl`,
`ltl a b`. Types are terms of the sort `ty`; `exp` is indexed by such a term. There are no
sort equations anywhere, so `csort_by` is vacuous.

`ott_nat` is mandatory, not decoration: the closed codes are `Nat`, `Empty` and
`Pi_rel`/`Pi_irr` built from codes, so Π alone has no base case and without `ott_nat` every
universe is empty and the theorem vacuous. This is exactly the `unit_lang` situation of the
STLC proof.

Excluded for Phase 1: `Sigma`, `Id`, `Cast`, `Computations`. `Cast` in
particular is *not* benign — its `u0` gives a code for a universe, which breaks §2's
key structural fact.

`ProofIrr` **is** included, but in the `El`-sorted presentation `ott_proofirr_el` rather
than the bare-type-metavariable `ott_proofirr`: for a code `c : U G irr l`, any two
`t u : El G irr l c` are equal. The restatement is forced by the rigid model — `rceq_term`
at an `exp` sort dispatches on `USkel` of the type and ignores the info index, and it has no
well-typedness hypotheses, so a premise `A : ty G (info irr l)` lets the rigid obligation be
instantiated at `A := U emp irr L0`, `t := Nat`, `u := Empty`, which is refutable by `I_fun`.
`USkel (El …) = false` makes the case `exact I`. See §11.

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

* **R2 dissolves — for weakening.** "Normal codes are closed under substitution", which the old
  plan flagged as *the single lemma most likely to force a restructuring*, requiring the
  code-level fundamental theorem to be merged into Layer 2, is a **plain structural induction on
  the code**. `NfCode_wk` is proved that way, with no reducibility at all.

  The *general* statement is weaker than first claimed, and two corrections are on the record:
  (i) the class of normal substitutions must constrain only the **universe-typed** entries — the
  naive "every entry is an `NfET`" class is not closed under lifting, because going under a
  binder snocs `hd`, and `hd` at a `Pi_rel` type is not η-long normal; (ii) the variable case
  needs **`TyOk_inj`, i.e. Layer 0.5** — reading a code variable off a `snoc` gives a normal term
  at the entry's normal type, and turning that into an `NfCode D r l` requires knowing the type
  is *syntactically* `oU D r l`. The head and the level come for free (a `TyOk` at info `iCode l`
  can only be `oU _ _ l`, since `oIota l0 ≠ oNext l`), but the **relevance** does not.
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

Nor is it touched by proof irrelevance, which is why adding that rule (§1) left Layer 0.5
alone: *every* code sits at info `rel (next l)`, including the irrelevant ones
(`Pi_irr : exp G (info rel (next L0)) (U G irr L0)`), and the irrelevance rule applies only
at `info irr`. So it can never equate two codes, and `NfCode_inj`/`TyOk_inj` survive intact.

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

### 4a. How Layer 0.5 is put together

**Status: closed.** All three exports are proved and axiom-free.

Three files:

* **`Dtt/Rigid.v`** — the rigid model. A first-order de Bruijn domain (`rcode`/`rty`/`renv`,
  §0) plus rigid substitutions `rsub := nat -> rcode`; four mutually inductive
  *interpretation* relations `IEnv`/`ITy`/`ICode`/`ISub` over **arbitrary** syntax of the
  four σ-sorts; and **all ten** `CutTModel_ok` obligations.
* **`Dtt/RigidOk.v`** — `RigCM_ok` and `rigid_sound`, with the four readings
  `rigid_env`/`rigid_ty`/`rigid_sub`/`rigid_code`.
* **`Dtt/Inj.v`** — the three exports.

§2's claim survived contact with every one of the 28 equation obligations: everything at an
`El`-sort, **including both β rules and η**, is discharged by `exact I`.

**The composition is trivial, and that is the point.** The readings hand back a *common*
interpretation of the two sides, at a common index:

```coq
Definition Req_code G e1 e2 := exists E n, IEnv G E /\ ICode E e1 n /\ ICode E e2 n.
```

So injectivity is stated over `I*` — *two normal objects with the same interpretation at the
same `renv` are syntactically equal* — and each export is then two lines: destruct the
reading, apply the `I*` statement. There is nothing to construct. No totality lemma, no
functionality lemma, no alignment of indices between two systems: the model has already chosen
the `renv`, and both sides are already interpreted at it.

(An earlier version of this layer carried a *second*, purely syntactic erasure of the same
objects — `Dtt/Erase.v`'s `ErEnv`/`ErTy`/`ErCode`/`ErVar` — proved injectivity over that, and
then needed a mutual induction, `Nf_ErI`, whose only job was to manufacture `Er*` derivations
at the `renv` the model had already picked. Deleting the second system deletes that problem
rather than moving it. What survives of `Erase.v` is the domain and the two index erasures
`ErRel`/`ErLvl`, now `Rigid.v` §0.)

### 4b. The variable case, and the universe observation

The one place the argument is not routine is variables. **Normal environments do not determine
each slot's type syntactically.** `VarT` *names* the normal representative of a weakened type
and pins it only by an `eq_term` premise, and the index-`k+1` variable term *contains* the
named representative of the index-`k` one. So injectivity on variables is exactly uniqueness of
that naming — and stated in general it is a fact about `eq_term`, not a syntactic one.

The design once proposed to break the resulting circularity with a strong induction on
environment length, proving the environment, type, code and variable statements simultaneously.
**That does not work, and is not needed.** It does not work because the code statement's Π case
recurses into a *longer* environment, and the variable statement there needs the type statement
back at the original length: the dependency is `T(m) → C(m) → V(m+1) → T(m)`, which no measure on
environment length repairs. It is not needed because of

> **THE UNIVERSE OBSERVATION.** The named type a *code* variable carries is always a
> **universe** — a code variable's type is `oU G r l` and nothing else. And at a universe,
> uniqueness of the naming is **unconditional**.

```coq
Lemma WknU_shape G j B i A r l :
  TyOk G i A ->
  eqt (sTy (oExt G j B) i) (oTySubst (oExt G j B) G (oWkn G j B) i A) (oU (oExt G j B) r l) ->
  A = oU G r l.
```

— proved with no recursion at all: `rigid_ty`, then invert the interpretation
(`ITy_subst_inv`/`ISub_wkn_inv`), then `tsub rshift T0 = rt_U br bl ⇒ T0 = rt_U br bl`, with `r`
and `l` pinned by `ErRel_inj`/`ErLvl_inj`. So `Inj.v` is **linear**: two ordinary inductions
(on the de Bruijn index, `VarTU_I_inj`; on the `rcode`, `NfCode_I_inj`) and two case analyses
(`TyOk_I_inj`, `EnvOk_I_inj`).

The only friction the `I*` formulation costs is that `ICode`'s `icode_subst` clause produces
`csub s n`, which is not a constructor pattern, so the shape of a variable's interpretation
takes a small induction (`VarT_ICode_var`) rather than an inversion. That, plus seven
one-line `I*` inversions, is the whole of it.

*(Historical note: the hypothesis this section used to be organised around, `WknInj` — weakening
is injective on normal types up to the naming, with `A1`/`A2` in the shorter environment — was
proved and then found to be used nowhere. It is deleted.)*

**The alternative, considered and declined.** All of this disappears if Layer 1's `VarT`/`NeET`
(and `RTy`'s Π clause) named the *computed* normal representative rather than an arbitrary
provably-equal one — §2 says the substitution action on normal forms is a total function, so it
is available. That would also make `RTy_fun` (§7) an ordinary induction instead of one
parameterised by `NfCode_inj`/`TyOk_inj`. It is declined because the existential form *does*
compose, and switching would invalidate several thousand verified lines. Worth revisiting only
if a later layer hits the same wall a third time.

**Kill-switch: passed.** `NfCode_inj` is proved. Every later layer may consume it.

---

## 5. Layers, revised

| layer | file | content |
|---|---|---|
| 0 | `Dtt/Syntax.v` | `ott_dtt`, `wf_lang ott_dtt` (axiom-free), sort/term abbreviations, index normalizers `ntlvl`/`ninfo` |
| 0.25 | `Dtt/Eqns.v` | the toolkit: `wf_*` and `*_cong` for all 32 formers, all 28 equations as `eq_term` lemmas in *dependent* form (the type rewritten alongside the term) |
| 1 | `Dtt/NormalForms.v` | the mutual block `EnvOk`/`TyOk`/`NfCode`/`VarT`/`NeET`/`NfET`; `Wk`; typing, weakening, and **code substitution** lemmas |
| 0.5 | `Dtt/Rigid.v`, `Dtt/RigidOk.v`, `Dtt/Inj.v` | the rigid model and `NfCode_inj`/`TyOk_inj`/`EnvOk_inj` (§4). Depends on Layer 1 only for the *statements* |
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

**(a) `NfET` has no neutral clause at EITHER Π type.** The clauses are indexed by the
*normal type*, and dispatch on its head:

```
A = U G r l                       -> NfCode G r l e                (normal codes)
A = El G rel L0 (Nat G)           -> zero | suc n | neutral
A = El G irr L0 (Empty G)         -> neutral
A = El G r l c,  c neutral        -> neutral
A = El G rel lG (Pi_rel …)        -> lam_rel … t   ONLY            <-- η
A = El G irr L0 (Pi_irr …)        -> lam_irr … t   ONLY            <-- proof irrelevance
```

The two rows hold for different reasons, and the difference shows up in the proof. At
`Pi_rel` the normal form of a neutral must be **the** η-expansion, and only `"Pi_rel eta"`
proves that equality. At `Pi_irr` there is no η rule, but `"proof irrelevance"` equates a
neutral with **every** well-typed `lam_irr` at that type at once, so *any* normal inhabitant
of the codomain will do; escape supplies one by escaping the body at the fresh variable and
wrapping it in `lam_irr`. Either way a neutral is not a normal form there, and the candidate
at `Pi_irr` is the plain Kripke one — identical to `Pi_rel`'s up to relevance and level.

`Empty` is untouched by this: proof irrelevance equates the inhabitants of
`El G irr L0 (Empty G)` but supplies none, so the neutral clause there is still what makes a
normal form EXIST.

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

* **Neither Π candidate needs a `HasNf` conjunct.** Without η one has to carry "…and it has a
  normal form" separately, because a neutral at a Π type is already normal. With η the normal
  form of an inhabitant of a `Pi_rel` type *is* its η-expansion, so it is derivable. The same
  holds at `Pi_irr`, via `"proof irrelevance"` instead of η (§6(a)), so the two clauses are
  symmetric. `rty_pi_irr` did carry the extra conjunct while `nfet_ne_pi_irr` existed; both
  are now gone.
* **Escape and reflect are one mutual induction on the `RTy` derivation** (`RTy_escape_reflect`,
  proved). At Π:
  * *reflect*: given a neutral `n`, show `P n`, i.e. that `n[w] a` is in the codomain
    candidate for every reducible `a`. By IH-escape at the domain, `a` has a normal form; so
    `n[w] a` is neutral (clause (c) above); by IH-reflect at the codomain, done.
  * *escape*: given `P e`, work in `D = ext G (iEl rF lF) (El G rF lF F)`. By IH-reflect at
    the domain, `hd` is reducible; so `Pc` holds of `(e[wkn]) hd`; by IH-escape at the
    codomain it has a normal form `t`; then `lam_rel … t` is a normal form of `e` **by η**.
    At `Pi_irr` the same construction runs, with `"proof irrelevance"` in place of η for the
    last step: it equates `e` with `lam_irr … t` outright, so the body `t` need not be the
    η-expansion — it just has to be *some* normal inhabitant of the codomain, and the escape
    at the codomain supplies one.

  Without η the second bullet has no proof — the term is not equal to any λ — which is
  exactly why the old plan had to keep reification untyped and defer η to a later phase.
* `RTy_fun` is **not** an ordinary induction on the two derivations, as a first pass assumed.
  Clause disjointness is real (verified: `inversion` discriminates every pair except `rty_var`
  against a canonical code, which `VarT_head` closes) but it is not enough. The Π clauses name
  their domain and codomain candidates at a **chosen** representative — `F'` for `F[w]`, `C` for
  the codomain instance — and record only that it is *provably* equal to the raw instance. Two
  derivations at the same syntactic type may choose different representatives, so the induction
  hypothesis, which compares candidates at the *same* type, does not apply until §4's
  `NfCode_inj`/`TyOk_inj` identify them. `WIP/DttLRBasics.v` therefore exports
  `RTy_fun_of_inj`, parameterised by exactly those two; once Layer 0.5 lands,
  `RTy_fun := RTy_fun_of_inj NfCode_inj TyOk_inj` and nothing else changes. `RTy_fun_eq` (§3)
  then follows.

* **Rocq's generated `RTy_ind` is useless, and every induction over `RTy` must avoid it.** It
  supplies *no* induction hypothesis in either Π case, because the recursive occurrences sit
  under `ex`/`and` — a nested position. The replacement, `RTy_strong_ind` in
  `WIP/DttLRBasics.v`, is hand-written as a `Fixpoint`: the guard checker *does* accept
  recursion through `forall`/`ex`/`and`. It is an ordinary axiom-free definition. Two usage
  gotchas: constructor arguments are implicit, so match patterns need `@rty_pi_rel …`, and
  `Set Implicit Arguments` makes the section hypotheses implicit too.

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
`RTy_fun_eq` is available.

**Every index of a semantic conjunct is quantified up to `eq_term`, not held fixed** — the
environment via `RSubN`, the info and the type via `RTmN`/`RTyN`:

```coq
RTmN G i A e := forall i0 A0, eqt sInfo i i0 -> TyOk G i0 A0 -> eqt (sTy G i0) A A0 -> RTm G i0 A0 e
RTyN G i A   := exists i0 A0 P, eqt sInfo i i0 /\ TyOk G i0 A0 /\ eqt (sTy G i0) A A0 /\ RTy G i0 A0 P
RSubN D G g  := exists G0, EnvOk G0 /\ eqt sEnv G G0 /\ RSub D G0 g
```

This is forced, not stylistic, and it is the one place a first pass got the contract wrong.
`csort_cong` varies all three indices, and with the **info** held fixed the corresponding
transfer is not merely unproved but **refutable modulo consistency** — `WIP/DttModelStruct.v`
proves it. `TyOk`'s info index is syntactic *by design* (a universe is pinned at `iCode l`, an
`El` at `iEl r l`), but `next0` makes `iCode L0` and `iEl rel L1` provably equal and `Ceq_term`
at `tyinfo` relates them, since it only demands equal `ninfo`s. So `ty G (iCode L0)` and
`ty G (iEl rel L1)` are provably equal sorts whose sets of normal representatives are
**disjoint**, and a transfer between them forces the closed universe `U irr L0` to be provably
equal to the `El` of a closed relevant `Pi` code. The **environment** index has a milder form of
the same disease: `RSub` is indexed by the *syntax* of `G`, so pushing it through an
environment equation asks, in the `ext` case, for reducibility of the entry at the other info —
i.e. for the normalization theorem itself.

With all three quantified, both directions of every transfer are transitivity alone, and nothing
in Layers 1–3 has to move: `TyOk` keeps its pinned infos, `RSub` keeps its syntactic index,
and the aliasing is absorbed by the wrappers.

`Ceq_sort` stays as in the old plan:

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

Obligation count: `cterm_cong` 32, `cterm_by` 32, `csort_cong` 9, `csort_by` 0, structural 6
— **79** (STLC was 45). **28 are proved** and axiom-free: the 6 structural, the 9 `csort_cong`
(`csort_by` being vacuous), and the index fragment's 9 congruences + 3 equations.

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
| **P9** | extensions: ~~`ProofIrr`~~ (done, §1), `Sigma`, `Id`, `Computations` | — |
| **—** | `Cast` | **breaks §2**: `u0` is a code for a universe, so eliminators can land in `U`, code rigidity fails, and the whole architecture reverts to the induction–recursion problem. Do not add `Cast` without redesigning Layers 0.5 and 2 |

## 9a. A language gap: four missing substitution commutations

`ott_dtt`'s 28 equations contain **no `"app_rel subst"`, `"app_irr subst"`, `"lam_irr subst"` or
`"Emptyrec subst"`** (verified against the compiled language). So `(app_rel … f a)[w]`,
`(lam_irr … t)[w]` and `(Emptyrec … e)[w]` cannot be pushed inwards at all: those terms are
**stuck under an explicit substitution**, and consequently normal forms are not stable under
weakening — `NeET_wk`/`NfET_wk` are simply not provable, and the normalization statement itself
is false for the language as it stands, since a stuck `exp_subst` has no normal form.

`"app_rel subst"` is *derivable* (η, β, `"lam_rel subst"` and the σ-identity
`⟨id,a'⟩ ∘ w↑ = w ∘ ⟨id,a⟩`). The other three are not: `Pi_irr` has no η and `Emptyrec` has no η,
so nothing can move the substitution past them. `Lang/OTT/Pi.v`'s own comment says `lam_irr subst`
is "subsumed by proof irrelevance" — true in the full theory with `Lang/OTT/ProofIrr.v`, whose
single rule equates any two inhabitants of a proof-irrelevant type, but at the time this was
written `ProofIrr` was out of scope, so for `ott_dtt` the rules were genuinely absent.

(`ott_dtt` now *does* include proof irrelevance, in the `El`-sorted form — see §1 — so the
`lam_irr subst` and `app_irr subst` rules of `ott_subst_commute` are strictly speaking
redundant. They are kept: they are proved and axiom-free, they are what the normal-form
development actually rewrites with, and deriving each use from irrelevance instead would
buy nothing.)

**Fixed.** `src/Pyrosome/Lang/OTT/SubstCommute.v` supplies all four, proved and axiom-free, as a
separate extension rather than an edit to `Pi.v`/`Nat.v` — that leaves every already-compiled
language (`Sigma`, `Id`, `Cast`, `ProofIrr`, `Computations`) untouched. Upstreaming is a later
decision. Two things learned writing them:

* **The elaborator normalizes the declared conclusion sort.** Either spelling of an `app` rule's
  sort passes `compute_wf_rule`, and both come out stored as `ty_subst g (ty_subst ⟨id,a⟩ (El B))`.
* **A spelling divergence that matters more than the `next0` one.** `elab_rule` builds `under' g`
  over `ext G [rF,ι lF] (ty_subst g (El F))`, but *every* other binder commutation in the family —
  `Pi_rel subst`, `Pi_irr subst`, `lam_rel subst`, `Sig subst` — uses
  `ext G [rF,ι lF] (El G rF lF g[F])`. Equal by `El subst`, not the same term; left as elaborated,
  `g[app_rel …]` would reduce to a differently spelled context than `g[lam_rel …]` does, which is
  exactly the wart that breaks a syntactic normal-form argument. Both `app` rules are hand-written
  to the family's form.

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

**The cheap fix is to let the e-graph bridge it.** the e-graph (`egraph_sound`) discharges the
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

---

## 11. The review pass

After the proof closed, four reviews went over it looking for duplicated work, over-complex
definitions and circuitous strategies. What they found, and what was done:

**The single biggest defect was not a proof at all — it was the rule dispatch.** Every one of the
64 rule obligations pinned its rule by expanding `In (name, rule) ott_dtt` into a 73-fold
disjunction of fully-evaluated rules, *in the proof term*, so `Qed` paid again: 2.6 s per
invocation, ~68 invocations. Pinning by `named_list_lookup_err_in` + `in_all_fresh_same` instead
is 236× faster and O(1) in the proof term. **Layer 4b went from 221 s to 59 s.** For perspective,
`ModelPi.v`'s entire mathematical content — 5 000 lines, 17 obligations — type-checks in under
two seconds; the rest was dispatch.

**Three things were reconstructed by hand that already existed.**

* `NfWk.v` built shape relations with determinism proofs to pin a normal type, because the
  `∃A'. TyOk A' ∧ A[w] ≡ A'` form "cannot drive its own induction". True — but `TyOk_inj` (§4)
  does exactly that, and `NfWk.v` already imported it and already used it a hundred lines away.
  The detour was an artefact of build order: weakening was attempted before rigidity landed.
* `Erase.v` defined a second erasure system alongside `Rigid.v`'s interpretation relations, and
  `Inj.v` needed a simultaneous induction to keep the two in step. But `rigid_code`/`rigid_ty`/
  `rigid_env` already hand back the model's own derivations *for both sides at a common index*, so
  stating injectivity there makes the seam disappear rather than move. `Erase.v` is gone.
* The `cterm_by` recipe that two fragments independently discovered and wrote up as a finding is
  `Gluing/SyntacticModel.v`'s `synm_cterm_by` — in the same directory, generic, six lines. A small
  bridge (`Ceq_term_eqt`, `Ceq_args_syn`) hands every obligation its `eq_term` conjunct for free.
  `by_PiRel_eta` went from 109 lines to 4.

**One mismatch in a definition cost ~350 lines.** `Wk`'s one-step weakening was `wkn ∘ id`, while
η is stated with the bare `wkn`; a 263-line section existed to bridge that, for a single call
site. Adding a `wk_wkn` clause is safe exactly where a `wk_conv` clause would not be — the four
clauses keep pairwise-distinct head symbols, so `Wk` stays the *syntactic* class Layer 2 needs.
With it, `appAtRel … wkn e hd` **is** η's left-hand side and the conversion disappears entirely.

**Two suspicions were wrong, and checking them was worth more than the fixes.** `WIS` looks like a
redundant fourth substitution class; it is not — under the general class the image of a code
variable is only "some normal code", and turning that into a candidate is `RTyEx_of_NfCode`, the
theorem under proof. And `Rigid.v`'s junk-at-non-universe-slots representation is *forced* by
`snoc_wkn_hd`, not a convenience.

**A process lesson.** Five separate pieces of machinery were "independently re-derived" —
`ceq_refl_l` byte-identical in two files, four byte-identical dispatcher tactics, `RSub_wf`
duplicated with a justification contradicted eleven lines above it. That is the direct cost of
fanning work out across agents told not to depend on each other's files: the isolation that makes
parallel proof development safe is exactly what manufactures this duplication. Budget a
consolidation pass.

Net: 29 files → 28, 25 228 lines → 23 111, no `Admitted` and no `Axiom` at any point.
