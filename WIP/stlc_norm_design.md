# Relational model for normalization of `stlc_unit`

`stlc_unit = stlc ++ unit_lang ++ exp_subst ++ value_subst` (39 rules), meta-context `c = []`.
Openness is object-level: an "open term in context G" is a closed Pyrosome term of sort `#"exp" G A`.
Variables are `hd` and its `wkn`-shifts.

## 0. Shape table (verified against the compiled language, NOT the notation)

Contexts are stored most-recent-first and `con`'s argument list follows that order.
`hd`/`wkn`/`id`/`forget` carry index args in the `con` list though their `args` field is empty.

```
Sty  = scon "ty" []                     Senv = scon "env" []
Ssub G G' = scon "sub"  [G'; G]         Sval G A = scon "val" [A; G]
Sexp G A  = scon "exp"  [A; G]

Unit                 = con "unit" []                      : ty
Arr A B              = con "->"   [B; A]                  : ty
Emp                  = con "emp"  []                      : env
Ext G A              = con "ext"  [A; G]                  : env
Id G                 = con "id"   [G]                     : sub G G
Cmp G1 G2 G3 f g     = con "cmp"  [g; f; G3; G2; G1]      : sub G1 G3
Forget G             = con "forget" [G]                   : sub G emp
Wkn G A              = con "wkn"  [A; G]                  : sub (ext G A) G
Hd  G A              = con "hd"   [A; G]                  : val (ext G A) A
Snoc G G' g A v      = con "snoc" [v; A; g; G'; G]        : sub G (ext G' A)
ValSubst G G' g A v  = con "val_subst" [v; A; g; G'; G]   : val G A
ExpSubst G G' g A e  = con "exp_subst" [e; A; g; G'; G]   : exp G A
Ret G A v            = con "ret"  [v; A; G]               : exp G A
Tt  G                = con "tt"   [G]                     : val G unit
Lam G A B e          = con "lambda" [e; B; A; G]          : val G (-> A B)
App G A B e e'       = con "app"  [e'; e; B; A; G]        : exp G B
```

18 equations: `id_right, id_left, cmp_assoc, val_subst_id, val_subst_cmp, cmp_forget,
id_emp_forget, wkn_snoc, snoc_hd, cmp_snoc, snoc_wkn_hd` (value_subst);
`exp_subst_id, exp_subst_cmp, exp_subst ret` (exp_subst);
`exp_subst app, val_subst lambda, STLC-beta` (stlc); `val_subst tt` (unit).

## Central design decision

`ceq_term` **glues** the syntactic model to the reducibility predicate: every clause carries
`eq_term stlc_unit [] t e1 e2` as a conjunct. Consequences:

* "has a normal form" means *provably equal to a canonical form*, *not* "rewrites to". So the
  substitution equations are discharged **inside the theory** (`eq_term_by`, `eq_term_trans`, …).
  **No confluence or termination argument for the sigma-calculus is required.** This is what
  `WIP/Normalization.v` got stuck on (`R_trans` ends in `Fail Qed`, "depends on confluence!").
* `cterm_trans`/`cterm_sym`/`cterm_conv` become near-trivial.
* The relation is automatically invariant under provable equality.

## Layering (each layer depends only on earlier ones — no circularity)

### Layer 1 — `StlcNormalForms.v`: canonical forms and weakenings

Mutual inductives over `term` (untyped, indices are just carried):

```
Var  : term -> Prop            (* object-level variables *)
| var_hd  : Var (Hd G A)
| var_wkn : Var w -> Var (ValSubst (Ext G B) G (Wkn G B) A w)

NfV / NfE / NeE  (mutual)
| nfv_var : Var v -> NfV v
| nfv_tt  : NfV (Tt G)
| nfv_lam : NfE e -> NfV (Lam G A B e)
| nfe_ret : NfV v -> NfE (Ret G A v)
| nfe_ne  : NeE e -> NfE e
| nee_varapp : Var x -> NfE n -> NeE (App G A B (Ret G (Arr A B) x) n)
| nee_app    : NeE e -> NfE n -> NeE (App G A B e n)
```

Weakenings — a *syntactic* class, defined with **no reference to reducibility**. This is what
breaks the circularity that killed the earlier attempt (an arrow clause quantifying over arbitrary
reducible substitutions is not well-founded):

```
Wk : term -> term -> term -> Prop        (* Wk D G w  :  w : sub D G is a weakening *)
| wk_id   : Wk G G (Id G)
| wk_ext  : Wk D G w -> Wk (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) w)
| wk_lift : Wk D G w ->
    Wk (Ext D A) (Ext G A)
       (Snoc (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) w) A (Hd D A))
```

**CORRECTION (found while proving Layer 1).** `wk_lift` is REQUIRED. Without it, stability of normal
forms under weakening is *false* at `nfv_lam`: `val_subst lambda` rewrites `w[lambda A e]` to
`lambda A (e[<w o wkn, hd>])`, and `<w o wkn, hd>` is a `snoc`, not a `wkn`-composite, so the IH
cannot apply. With all three clauses `Wk` is exactly the order-preserving embeddings. It stays
purely syntactic, so Layer 2's well-foundedness is unaffected.

**CORRECTION (found while proving Layer 1).** The untyped `Var`/`NfV`/`NfE`/`NeE` admit NO typing
lemma: `Var (ValSubst (Ext G B) G (Wkn G B) A (Hd G' A))` holds for every `G'` and is ill-typed
unless `G' = G`, and no extra hypothesis repairs this without naming the indices. So Layer 1 also
provides index-carrying refinements `VarT G A x`, `NfVT/NfET/NeET G A e` with erasure maps
(`NfVT_NfV` etc.). All typing and weakening-stability lemmas are stated on the TYPED judgments.

Layers 2-4 MUST use the typed forms (`NfVT`, `NfET`) inside `RV`/`RE`. Using the untyped ones makes
`RV_wk` unprovable, since recovering `NfVT G A n` from `NfV n` plus `wf_term n (Sval G A)` needs a
sort-injectivity development (cf. the 353-line `OTT/Norm/SortInj.v`). The untyped predicates are
retained only because the final normalization statement quantifies over them.

Stability is stated up to `eq_term`, not syntactically — `w[x]` is a `val_subst` redex, not literally
a variable.

Obligations for this layer: `Wk` composes; `Wk D G w -> wf_term stlc_unit [] w (Ssub D G)`;
normal forms are stable under weakening.

### Layer 2 — `StlcLogRel.v`: reducibility, by recursion on the TYPE

Recursion is on `A` only (`Wk` is syntactic), so it is structural and well-founded.

```
RV : term -> term -> term -> Prop        (* RV G A v *)
RE : term -> term -> term -> Prop        (* RE G A e *)

RV G Unit      v := exists n, NfV n /\ eq_term _ [] (Sval G Unit) v n
RV G (Arr A B) v := (exists n, NfV n /\ eq_term _ [] (Sval G (Arr A B)) v n)
                 /\ (forall D w u, Wk D G w -> RV D A u ->
                       RE D B (App D A B (Ret D (Arr A B) (ValSubst D G w (Arr A B) v))
                                         (Ret D A u)))

RE G A e := exists n, NfE n /\ eq_term _ [] (Sexp G A) e n
         /\ (forall v, n = Ret G A v -> RV G A v)
```

The last conjunct is what lets **neutral** expressions be reducible for free — the standard CR
condition. Key lemmas (the "CR" package):

* `CR_reify`  : `RV G A v -> exists n, NfV n /\ eq_term .. v n` (immediate)
* `CR_reflect`: a neutral is reducible — `NeE e -> (has nf) -> RE G A e`, and `Var x -> RV G A x`
* `RV_wk`     : `RV G A v -> Wk D G w -> RV D A (ValSubst D G w A v)`  (by recursion on A)
* `RE_wk`     : likewise
* `RV_eq` / `RE_eq` : closed under `eq_term` on either side

### Layer 3 — `StlcRSub.v`: reducible substitutions, by recursion on the CONTEXT

Defined *after* `RV`, recursion on `G` (the codomain). No circularity.

```
RSub D Emp        g := eq_term _ [] (Ssub D Emp) g (Forget D)
RSub D (Ext G A)  g := exists g0 v, eq_term _ [] (Ssub D (Ext G A)) g (Snoc D G g0 A v)
                                 /\ RSub D G g0 /\ RV D A v
```

Note this *is* the canonical-form statement for substitutions: a reducible substitution is provably
a snoc-chain ending in `forget`. That is why `sub` needs no separate normal-form development.

Key lemmas: `RSub_id : EnvOk G -> RSub G G (Id G)` (needs `snoc_wkn_hd` and `CR_reflect` on
`hd`/`wkn`-shifts); `RSub_wk`; `RSub_cmp`.

### Layer 4 — `StlcModelOk.v`: the model and the theorem

```
ceq_sort t1 t2 := t1 = t2
ceq_term Sty        A1 A2 := A1 = A2 /\ TyOk A1
ceq_term Senv       G1 G2 := G1 = G2 /\ EnvOk G1
ceq_term (Ssub G G') g1 g2 := eq_term .. g1 g2 /\ forall D h, RSub D G h ->
                                RSub D G' (Cmp D G G' h g1)
ceq_term (Sval G A) v1 v2 := eq_term .. v1 v2 /\ forall D g, RSub D G g ->
                                RV D A (ValSubst D G g A v1)
ceq_term (Sexp G A) e1 e2 := eq_term .. e1 e2 /\ forall D g, RSub D G g ->
                                RE D A (ExpSubst D G g A e1)
ceq_term _ _ _ := False      (* no other sorts *)
```

Quantifying over reducible substitutions *in `ceq_term` itself* is essential: `CutTModel_ok`'s
`cterm_cong` concludes about the term, not a substitution instance, so the substitution closure has
to live in the relation rather than be a separate lemma.

`ceq_sort := (=)` makes `cterm_conv`, `csort_trans`, `csort_sym` trivial, and `csort_cong` follows
because `ceq_term` at `ty`/`env` forces syntactic equality. There are **no sort equations**, so
`csort_by` is vacuous. `c = []`, so `cterm_var` is vacuous.

Then `CutTModel_ok`: 16 `cterm_cong` cases + 18 `cterm_by` cases. The two that carry real content:

* **`lambda` cong** — needs `val_subst lambda` to push the substitution under the binder, then
  `STLC-beta`, then the IH at `Ext G A` applied to the extended substitution `Snoc .. g .. u`.
* **`STLC-beta`** — `App (Ret (Lam e)) (Ret v)` vs `ExpSubst (Snoc (Id G) v) e`: both sides get the
  same reducible content, using `RSub` extension.

**Normalization** (`StlcModelOk.v`, final):

```
Theorem stlc_unit_normalization : forall G A e,
  EnvOk G -> TyOk A -> wf_term stlc_unit [] e (Sexp G A) ->
  exists n, NfE n /\ eq_term stlc_unit [] (Sexp G A) e n.
```

Proof: `normalization_from_model` (Gluing/StlcNormalization.v) gives
`inhabited (ceq_term (Sexp G A) e e)`; destruct (goal is a Prop); instantiate the substitution
quantifier at `D := G`, `g := Id G` via `RSub_id`; `exp_subst_id` rewrites `e[id]` to `e`; read off
the normal form from `RE`.

## Build

```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome <file>
```

Never `Admitted`/`Axiom`. Verify each finished file with `Print Assumptions` on its main results —
must print "Closed under the global context".
