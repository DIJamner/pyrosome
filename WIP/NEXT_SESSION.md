# Next-session kickoff — OTT two-sided PER migration

## UPDATE 2026-06-07x — FILE 4 KRIPKE-BUILDER CLUSTER **COMPLETE** (all GREEN, coqc-verified, only `egraph_sound`). Every `LogicalRelation.v` RedTy_tot Pi-case builder is now well-typed against the real OTT rules. **NEXT = the fundamental lemma proper** (`wf_term ott [] e t -> reducible e`) by Pyrosome cut-elimination; discharges the Pi reflect/reify eta crux.

THIS SESSION (in `src/.../Norm/Pi/FundamentalLemma.v`, committed+pushed on `gluing-nbe`):
the entire under'-lift cluster, built bottom-up. Each is a `wf_term`/`eq_term`
over OPEN builder vars, all checker-free (the `change`→`eq_term_subst`→
`eq_term_by` recipe + `term_con_congruence`, never `eredex_steps_with`).
Helper sorts `s_env/s_sub/s_exp/s_ty` + driver `ott_build` (checker-free
wf builder with the cluster lemmas as leaves) added at top of the section.

  - `El_act_code_ty` `wkn_extc_wf` `cmp_g0_wf` — small companion typings.
  - `El_subst_eq` — "El subst" instance `ty_subst g (El F) = El (act_code)`.
  - **`ty_subst_g0_El_eq`** (THE CRUX) — dissolves `ounder`'s `hd`-leaf type
    mismatch: `ty_subst (cmp g wkn)(El F) = ty_subst wkn (El act_code)` via
    "ty_subst_cmp" + "El subst" under a `ty_subst wkn` congruence.
  - `hd_extc_wf` `ounder_wf` — the fiddly under'-lift `snoc (cmp g wkn) hd`.
  - `act_cod_wf` — codomain code pushed along `ounder` ("U subst" at `ounder`).
  - `ty_subst_id_El_eq` `snoc_a_wf` `cod_at_wf` — `act_cod` instantiated at the
    argument via `snoc a id` ("ty_subst_id" conv on the `a`-leaf).
  - **`Pi_rel_subst_eq`** — the full "Pi_rel subst" rule (huge RHS transcribed
    to `{{e}}`, matched on first try) `exp_subst g (Pi_rel..G) = Pi_rel..(act_code)(act_cod) D`.
  - `El_Pi_subst_eq` `act_member_wf` — push the Π function member, re-type via
    El-subst-then-Pi_rel-subst.
  - `El_act_cod_subst_eq` `mapp_wf` — `app_rel` over act_code/act_cod/act_member,
    re-typed to the `El (cod_at .. a)` the RedAtPi member relation consumes.

KEY RECIPES (reuse for the fundamental lemma's syntactic obligations):
- **checker-free rule application** = `pose s; change (… [/s/] …); eapply
  eq_term_subst; [ eq_term_by NAME | eq_subst_refl;ott_build | rule_in_ctx_wf ]`.
  For composite convs, `eq_term_trans` with an EXPLICIT `e12` (a bare evar
  middle defeats `change`) + `term_con_congruence` (eq_args: the one changed arg
  by the sub-lemma, rest `eq_term_refl;ott_build`).
- **builder typing** = `wf_term_by'` + a `repeat first[wf_args_cons2/cons | cbn |
  compute_wf_subjects | (apply <prev-builder>;eassumption) | eassumption |
  wf_term_by'…]`; for a leaf needing a conv (hd/a), peel with `wf_args_cons2`
  and `eapply wf_term_conv;[apply H | sort_cong;…<conv lemma>]`.
- con-arg orders: con storage = REVERSE of `{{e}}` surface order. The `o*`
  builders in LogicalRelation.v already encode the correct order — trust them;
  `s_sub tgt src = scon "sub" [src; tgt]`.

## UPDATE 2026-06-07w — FILE 4 BODY STARTED: first Kripke-builder typing `act_code_wf` LANDED (GREEN, coqc-verified, only `egraph_sound`). NEXT = the remaining builder typings (extc/act_member/act_cod/cod_at/mapp), then the fundamental lemma proper.

THIS SESSION (in `src/.../Norm/Pi/FundamentalLemma.v`, committed+pushed):
1. **`act_code_wf`** — the first deferred Kripke-builder correctness (UPDATE-v
   subgoal (a)): `act_code rF lF g G D F` (= `exp_subst F (U rF lF G) g`, pushing
   a domain code along `g : sub D G`) is well-typed as a code `exp D _ (U rF lF D)`
   in the future env `D`.  Proven `wf_term_conv` + `wf_term_by` (exp_subst) +
   a sort-congruence conversion whose only non-reflexive component is "U subst".
2. **`U_subst_eq`** — the "U subst" computation rule (`ty_subst g (U rF lF G) =
   U rF lF D`) under an EXPLICIT variable-only substitution.  The KEY GOTCHA this
   session: the project's `eredex_steps_with` / `cleanup_auto_elab` close their
   `wf_subst`/`eq_subst` side-goals with the COMPUTATIONAL wf checker
   (`compute_noconv_term_wf` → `compute_wf_term'`), which CANNOT evaluate the free
   env/level/sub VARIABLES (`D : env` ⇒ `Is_Some None` ⇒ "I : True expected
   Is_Some …").  So `eredex_steps_with` is UNUSABLE on open builder terms.  Fix:
   `change` the goal into the rule's `t[/s/] e1[/s/] e2[/s/]` form (so
   `eq_term_subst` applies without inverting the subst), then discharge the
   `wf_subst` from the variable hypotheses by `wf_subst_cons` + `compute_wf_subjects`
   + `assumption` (NO checker), and the rule-ctx `wf_ctx` via `rule_in_ctx_wf`.
3. **Reusable driver `ott_wf_args`** (peel `wf_args`, expose `Model.wf_term`,
   compute the `with_names_from` subst, close var leaves by `assumption` and con
   leaves by `Elab.wf_term_by'`) — the standard "hand-build a `wf_term` over open
   OTT terms" tactic; will be reused for every remaining builder.

GOTCHAS (will recur):
- **Stale rocq-mcp worker gives FALSE proof success**: `eredex_steps_with ott "U
  subst"` reported "No goals remaining" in coq-lsp but FAILED under coqc (the
  checker issue above).  TRUST coqc (`make -f Makefile.coq /ABS/PATH.vo`), not the
  MCP, for anything touching `compute_*_wf`.  `force_restart:true` on `rocq_start`
  fixed an earlier "imports not loaded" staleness.
- `Elab.wf_term_by'` (Elab.v) is REQUIRED transitively but NOT imported by file 4;
  use the qualified name.  `wf_term_by` alone can't be `eapply`'d at a con leaf
  (the `t[/with_names_from c' s/]` conclusion blocks unification); `wf_term_by'`
  keeps the type flexible with a `= … \/ eq_sort …` side-goal (`left; compute;
  reflexivity` for exact leaves).
- make's `.Makefile.coq.d` uses ABSOLUTE target paths; build with the abs `.vo`
  path.  If "No rule"/"Nothing to be done", `rm Makefile.coq Makefile.coq.conf
  .Makefile.coq.d; make Makefile.coq` then build the abs path.

**`extc_wf` also LANDED this session** (committed+pushed): `extc = ext D (El
(act_code …))` is a well-formed env; composes `act_code_wf` via the El-argument
leaf, same checker-free driver + an `(apply act_code_wf; eassumption)` leaf.  So
the reusable pattern for "builder typing" is now: drive with the checker-free
`first[… | (apply <prev-builder-wf>; eassumption) | Elab.wf_term_by' …]`, adding
one leaf per already-typed builder.

**KEY ENTANGLEMENT FINDING — the remaining builders are NOT independent; they
cluster around the `ounder` under'-lift.**  `mapp = app_rel rF lF lG (act_code)
(act_cod)(act_member) a D` requires `act_member : exp D _ (El (Pi_rel rF lF lG
(act_code)(act_cod) D))`.  But `act_member` is `exp_subst f g` whose NAIVE type is
`exp D _ (ty_subst g (El (Pi_rel … F C G)))`; converting that to the
`El (Pi_rel (act_code)(act_cod) D)` form `mapp` wants goes through "El subst" THEN
"Pi_rel subst", and **"Pi_rel subst" is exactly the rule whose codomain uses
`under'` (Pi.v:118-123: `exp_subst g (Pi_rel F B) = Pi_rel (exp_subst g F)
(exp_subst (under' g) B)`)**.  So `act_member`'s useful typing, `act_cod`, and
`cod_at` are all blocked on the SAME `ounder`/`under'` correctness — do them as
ONE cluster, not separately.

**NEXT (the under'-lift cluster, same file):**
1. **`ounder_wf`** — `ounder rF lF g G D F : sub (extc …) (ext G (El F))` is a
   well-typed object substitution.  This is THE fiddly one; `ounder = snoc (cmp g
   wkn) hd` (LogicalRelation.v:253-261).  Cross-check its annotations against the
   ELABORATED `under'` in `pi_rel_eta_rule` (Pi.v:47-49) and the "Pi_rel subst"
   RHS (Pi.v:120).  Likely needs `snoc`/`cmp`/`wkn`/`hd` companion typings (each a
   small `wf_term_by` like `act_code_wf`).
2. **`Pi_rel_subst_eq`** (U_subst_eq style) — `exp_subst g (Pi_rel rF lF lG F C G)
   = Pi_rel rF lF lG (act_code …)(act_cod …) D`, via the "Pi_rel subst" rule under
   an explicit variable subst (reuses `ounder_wf` for the codomain `act_cod`).
3. **`act_cod_wf`** / **`cod_at_wf`** — codomain code typings over `ounder`.
4. **`act_member_wf`** (naive type via `exp_subst`, then convert via
   `Pi_rel_subst_eq`) and **`mapp_wf`** (app_rel over the three).
Then the fundamental lemma proper (wf_term ⇒ reducible) by cut-elim; Pi
reflect/reify eta crux.

## UPDATE 2026-06-07v — OTT-CONCRETE Kripke RedTy LANDED in LogicalRelation.v (GREEN + axiom-free, committed+pushed). Builders verified vs built Base/Pi/Nat.vo; snoc-order corrected; base members concrete. NEXT = file 4 FundamentalLemma (where the deferred codomain under'-lift correctness gets checked).

THIS SESSION (committed+pushed on `gluing-nbe`):
1. **Built Pi.vo + Nat.vo** (were unbuilt; the Pi/ foundation is generic so the
   OTT lang .vo were never compiled). `make -f Makefile.coq /ABS/PATH.vo`.
2. **Verified ALL subst con-arg orders empirically** (WIP/ProbeSubst.v, deleted)
   against the built Base.vo `subst_ott`. KEY CORRECTION to memory
   ott-con-arg-orders: **`snoc` = [v; g; A; i; G'; G]** — the underlying subst
   `g` is at IDX 1, NOT idx 3 (the prior staged value was WRONG).
   `cmp` = [g; f; G3; G2; G1] (cmp g f : sub G1 G3; g:sub G2 G3, f:sub G1 G2).
   `exp_subst` [v;A;i;g;G';G] confirmed (v in G'=SOURCE, result G=TARGET,
   g:sub G G').
3. **OTT-CONCRETE RedTy_tot landed** in `src/.../Pi/LogicalRelation.v`,
   REPLACING the generic `RedTyDef` (the act/cod/mapp:term->term->term interface
   was too thin). Lives OUTSIDE `Section WithVar` (V fixed = string, pa = ott_pa;
   l still abstract w/ wf_lang l). Inlined Kripke operations, all from the
   verified builders:
     - `act_code rF lF g G D F` = exp_subst F (U rF lF G)(code_info lF) g G D.
     - `extc` = ext (El(act_code)) (info rF (iota lF)) D  [binder info is the
       TERM info `info rF (iota lF)`, NOT code_info — UPDATE-u said code_info,
       that was wrong; corrected here].
     - `act_member` (pushes f : El(Pi_rel..) along g; uses the El-of-Pi type +
       info rel (iota lG), NOT the code annotations).
     - `ounder` = snoc (cmp g wkn) hd, fully annotated (the under'-lift).
     - `act_cod` = exp_subst C (U rel lG extG)(code_info lG) ounder extG extD.
     - `cod_at` = exp_subst act_cod (U rel lG extD)(code_info lG)(snoc a id ..) extD D.
     - `mapp` = app_rel rF lF lG (act_code)(act_cod)(act_member) a D.
   `rtt_pi` carries G A B rF lF lG F C F' C' + the two reds-to-Pi_rel witnesses
   (single rF/lF/lG shared by both sides). Sig packaging + RedTy_nat/ne/pi smart
   ctors + custom RedTy_rect (threads Kripke dom+cod IHs) all GREEN + Closed
   under the global context.
4. **Base members concrete**: `RedNatMem` (rnm_zero / rnm_suc / rnm_ne) replaces
   the placeholder; `RedNe` wraps ne_eq. `nat_sort G` = exp sort of El(Nat) at L0.
   Empty members deferred (proof-irrelevant; trivial PER) — add when needed.

**file 4 `FundamentalLemma.v` FOUNDATION LANDED (committed+pushed):**
`ott := ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info` + `wf_lang ott`
proved (bottom-up `wf_lang_concat`; `lang_ext_monotonicity` weakens `ott_pi_wf`
over `ott_nat`; `compute_all_fresh`).  GOTCHA: `Open Scope string` (from the
imported OTT lang files) shadows list `++` — annotate `(... ++ ...)%list`.
`wf_lang_concat`'s l1/l2 are IMPLICIT (no `_ _`).  `ott_wf` inherits the standard
`egraph_sound` axiom from the OTT lang wf proofs (the LR machinery stays
axiom-free).

**NEXT = file 4 BODY (the fundamental lemma).** instantiate `l := ott` and prove
`wf_term ott [] e t -> RedTy/RedTm ...` by Pyrosome cut-elim
(Theory/CutElim/CutFreeInd/WfCutElim) on canonical derivations. The hard sub-
goals: (a) the act_code/cod_at/under' terms are well-typed (the under'-lift
direction + annotations — check vs Pi.v "Pi_rel subst" line 120 + the elaborated
under' in pi_rel_eta_rule lines 47-49); (b) reflect/reify adequacy at Pi (the
eta crux — type-directed, NOT via whstep, since `step` orients the eta rule too;
may need `redex` to exclude "Pi_rel eta" by name). Then file 5 Decidable =
decidability of eq_term for OTT.

(Superseded: UPDATE-u's "carry rF/lF/lG/G/D in rtt_pi" plan — DONE this session.
G/D are not stored in rtt_pi: G is an index, D is bound per-Kripke-instance.)

## UPDATE 2026-06-07u — KRIPKE RedTy LR LANDED in LogicalRelation.v (GREEN + axiom-free, committed+pushed `dc83735`). Build repaired, con-orders verified, ott_pa + builders staged (WIP/LRProto3.v `e1634ca`). NEXT = rewrite RedTy OTT-CONCRETE (option b: inline builders, carry rF/lF/lG/G/D in rtt_pi), then base member relations, then file 4.

THIS SESSION'S RESULTS (all committed+pushed on `gluing-nbe`):
1. **Kripke RedTy LR landed** — `src/.../Pi/LogicalRelation.v` now has the file-3
   core: a single plain inductive `RedTy_tot : term(env G) -> term -> term ->
   (term->term->Type) -> Type` with the member relation as OUTPUT index (Sig
   trick) — NO universe tower, NO PolyRedPack+adequacy split.  Pi case KRIPKE
   over object subs from the start.  Sig packaging + smart ctors
   (RedTy_nat/RedTy_ne/RedTy_pi) + custom `RedTy_rect` (threads Kripke dom+cod
   IHs); `RedTy_rect` Closed under the global context (axiom-free).  Currently
   GENERIC over a type-former interface (RNat/RPi/RNatMem + osub/act/extc/cod/
   mapp).  Validated first in WIP/LRProto2.v (`c4fc2e7`).
2. **Build repaired** — Makefile.coq regenerated; Base.vo built (the EGraph
   Theory cascade was stale).  Use `make -f Makefile.coq /ABS/PATH.vo` (.d uses
   absolute paths).
3. **All con-arg orders VERIFIED empirically** → memory `ott-con-arg-orders`.
4. **ott_pa + con builders + base recognizers staged** — WIP/LRProto3.v (GREEN).

**KEY DESIGN FINDING — the generic interface is too thin; go OTT-CONCRETE
(option b).**  Instantiating the committed RedTy for OTT showed `act`/`cod`/`mapp
: term->term->term` cannot be defined: OTT `exp_subst` con-terms = [v; A; i; g;
src; tgt] need the SOURCE/TARGET envs AND the code's U-type `A`=U_{rF,lF} + info
`i`=info rel (next lF), which live ONLY in the rtt_pi telescope (rF lF lG G D).
And act-on-code vs act-on-member need different annotations.  So a generic
interface buys little.  **NEXT-SESSION PLAN: rewrite `RedTy_tot` OTT-concrete**
(V:=string, l/wfl/ott_pa fixed or l abstract), carrying rF lF lG in `rtt_pi` and
inlining the WIP/LRProto3.v builders:
  - domain action: `act g F = oexp_subst F (oU rF lF G)(code_info lF) g G D`
    (g : sub G D, src=G home, tgt=D future; result code in env D).
  - extended env: `extc = oext (oEl rF lF D (act g F)) (code_info lF) D`.
  - codomain under g + at arg a: compose `exp_subst (under' g)` (codomain code C
    lives in `ext G (El F)`; lift g over the binder via `under'` = snoc (cmp wkn
    g) hd — CHECK against Pi.v:120 "Pi_rel subst" / the snoc/cmp/wkn/hd builders
    and verify `cmp` full con-order, injectivity ["G3";"G1"] is SHORT) then
    `exp_subst (snoc id a)`.  This is the genuinely fiddly part — direction +
    under'-lifting; correctness only checkable once the OTT subst lemmas/ott_full
    + wf_lang are available (so build Pi.vo/Nat.vo + assemble ott_full first, OR
    land the definition and defer correctness to file 4).
  - member app: `mapp f a = oapp_rel rF lF lG (act g F)(cod_code...) (act_member g f) a`
    (NB act on a MEMBER f : exp G (El(Pi ...)) uses info `rel (iota lG)` and type
    `El(Pi_rel ...)`, NOT the code annotations — separate builder).
  - base member relations to refine: Nat members = real zero/suc/neutral
    inductive (RNatMem placeholder now); Empty members (proof-irrelevant —
    trivial PER); the Ne (RedNe) wrapper over ne_eq is fine.
Then file 4 FundamentalLemma (needs ott_full + wf proof + the OTT subst lemmas),
file 5 Decidable.

(Superseded view: UPDATE-t's plan to keep a generic interface — the thinness
finding above redirects to OTT-concrete.)

## UPDATE 2026-06-07t — KRIPKE RedTy encoding VALIDATED (WIP/LRProto2.v, committed+pushed); build-repair of Base.vo/Pi.vo IN FLIGHT; con-arg orders mostly pinned. NEXT = finish build, verify subst con-orders, write the CONCRETE OTT RedTy in LogicalRelation.v.

**(1) Kripke encoding VALIDATED — `WIP/LRProto2.v` (committed `c4fc2e7`).**
Extends LRProto.v with the object-substitution Kripke quantification in the Pi
case (item 3 below — "build Kripke in from the START").  CONFIRMED: the clean
single-inductive + Sig-trick (member relation as OUTPUT index) STAYS strictly
positive when domain/codomain reducibility is quantified `forall G' (g : osub
G' G)`, with member relations `RDom`/`RCod` Kripke-indexed by `(G',g)`.  So we
do NOT need LogRel2's heavyweight `PolyRedPack`+adequacy split — a plain
`Inductive RedTy_tot : env -> tm -> tm -> (tm->tm->Type) -> Type` works.  Smart
ctors `RedTy_nat`/`RedTy_pi` + custom `RedTy_rect` (threads Kripke dom + cod
IHs) all typecheck; only axioms are the deliberate abstract substrate.  The Pi
member `RedAtPi G F C F' C' RDom RCod t u` quantifies `forall G' (g:osub G' G) a
a' (raa':RDom G' g a a'), RCod ... (app (act g t) a)(app (act g u) a')` —
mirrors LogRel2 `PiRedTmEq` but carries the relation as a param, not a pack.

**(2) Build repair IN FLIGHT.**  The OTT Pi/*.vo foundation files are all
GENERIC (no OTT-lang dep), so Base.vo/Pi.vo were NEVER built and are needed for
the concrete instantiation (+ all downstream).  Tools/EGraph {Defs, TypeInference,
ComputeWf, Theorems, ...} are STALE vs the Jun-4 rebuilt Theory (ClosedTerm) +
Utils/EGraph/Defs ⇒ "inconsistent assumptions" load errors.  FIX: regenerated
Makefile.coq/_CoqProject (`rm Makefile.coq Makefile.coq.conf .Makefile.coq.d;
make Makefile.coq`), then `make -f Makefile.coq <ABSOLUTE path>.vo` (the .d uses
ABSOLUTE paths — relative target = "No rule").  Build of Base.vo running
(rebuilds the EGraph Theorems/Semantics cascade — slow, ~30-60min).  After
Base.vo: `bash scripts/vbuild.sh` for the rest.

**(3) CON-ARG ORDERS pinned (reverse-of-declaration; FULL-arity injectivity
lists are reliable, SHORT ones are NOT).**  Verified rule: `con name s` has `s`
= the rule ctx in REVERSE declaration order (e.g. app_rel ctx
[G;rF;lF;lG;F;B;f;a] ⇒ s=[a;f;B;F;lG;lF;rF;G] = its injectivity list).
RELIABLE (full-arity injectivity in the Lang files):
  - `Pi_rel`  = [B;F;lG;lF;rF;G]            (5 expl + G)
  - `Pi_irr`  = [B;F;lF;rF;G]
  - `app_rel` = [a;f;B;F;lG;lF;rF;G]        ⇒ FUNCTION `f` at index 1
  - `app_irr` = [a;f;B;F;lF;rF;G]           ⇒ `f` at index 1
  - `lam_rel` = [t;B;F;lG;lF;rF;G], `lam_irr`=[t;B;F;lF;rF;G]
  - `Emptyrec`= [e;A;lA;rA;G]               ⇒ Empty-proof `e` at index 0
  - `Nat`=[G], `Empty`=[G], `zero`=[G], `suc`=[n;G]
  - `snoc` = [v;A;i;g;G';G] (full), `id`=[G], `ext`=[A;G], `El`=[e;l;r;G],
    `U`=[l;r;G], `exp`=[A;i;G]
NOT YET VERIFIED (short injectivity `ty_subst`/`exp_subst`=["i";"G"]) — must
`Compute (named_list_lookup dflt subst_ott "exp_subst")` once Base.vo builds.
INFERENCE (from base Subst.v decl order + tyinfo param insertion): unparam
exp_subst ctx [G;G';g;A;v]→+i→ likely [v;A;i;g;G';G] (term `v` at idx 0);
ty_subst [G;G';g;A]→+i→ likely [A;i;g;G';G] (type `A` at idx 0).  CONFIRM before
trusting.

**(4) pa selector for OTT (eliminators → principal-arg index; else None):**
  app_rel↦Some 1, app_irr↦Some 1, Emptyrec↦Some 0, exp_subst↦Some 0,
  ty_subst↦Some 0 (confirm idx 0 after (3)).  All canonical formers/intro
  (Nat,Empty,Pi_rel,Pi_irr,zero,suc,lam_rel,lam_irr,U,El,snoc,id,cmp,wkn,hd,
  ext,emp,forget,info,...) ↦ None.

**(5) CONCRETE instantiation plan for LogicalRelation.v (port LRProto2 with the
file's real `reds`/`ne_eq`):** type codes = exps at sort `U`; LR indexed by
object env `G:term` (sort `env`) + two codes A,B.
  - `is_nat B`   := `reds B nb` ∧ nb whnf-headed `Nat`.
  - `is_pi A F C`:= A whnf= `Pi_rel`/`Pi_irr` w/ domain code F, codomain code C.
  - `act g X`    := `exp_subst g X` (with the verified con order).
  - `cod_subst C a` := `exp_subst (snoc id a) C` (codomain code instantiated).
  - member `app f a` := `app_rel rF lF lG (act g F)(act g B)(act g f) a` (needs
    the Pi data F,B,levels,relevance in scope — exposed by `is_pi`).
  - `ext G F`    := `ext G (El F)` ; `osub G' G g` := `wf_term l [] g (scon
    "sub" [G';G])` (object subst as a typed term).
  Then file 4 FundamentalLemma, 5 Decidable.

---
## UPDATE 2026-06-07s — file 3 `LogicalRelation.v` FOUNDATION landed (GREEN+axiom-free, committed+pushed); LR inductive ENCODING validated in WIP/LRProto.v. NEXT = instantiate the type-LR for OTT (exact con-arg orders + Kripke object-subs).

Two things landed this session.

**(1) `src/Pyrosome/Lang/OTT/Norm/Pi/LogicalRelation.v` — FOUNDATION, committed
+ pushed, GREEN + axiom-free** (`bash scripts/vbuild.sh <file>`).  Generic over
`wf_lang l` + `pa`:
- `reds a b := star whstep a b /\ whnf b` — the Pyrosome-native analog of
  metamltt `WfRedTy`/`WfRedTm`.  KEY: whnf carried EXISTENTIALLY, NO
  deterministic normalizer baked in.  `reds_sound` (⊆ eq_term) is FREE from
  `star_whstep_sound`; `reds_wf` from `star_whstep_wf`; `reds_refl` for whnfs.
  Where metamltt uses `whnf_det`, we will instead use Pyrosome constructor
  INJECTIVITY on the common reduct (two whnfs of one term are eq_term-equal ⇒
  same head by sort/term injectivity) — so confluence of whstep is NEVER needed.
- `ne_eq t a b := neutral a /\ neutral b /\ eq_term l [] t a b` — RESOLVES
  UPDATE-n open Q2: neutrals compared by `eq_term` (the pivot's declarative
  equality) + a "both stuck" gate, NOT a separate `~ne` inductive.  Proven a PER
  (`ne_eq_sym`/`_trans` from eq_term; `ne_eq_refl` for well-typed neutrals).

**(2) `WIP/LRProto.v` — the reducibility-inductive ENCODING is VALIDATED**
(builds; only axioms are the deliberate abstract-substrate `Parameter`s).  This
de-risks THE central design step.  CONFIRMED facts about the encoding:
- **NO universe tower.**  OTT's Tarski universe has NO universe CODE (`U` is a
  `ty`, never an `exp` — checked Base.v), so type codes are only
  `Nat`/`Empty`/`Pi_*`/neutrals.  The impredicative recursion that forces
  metamltt's Small/Large stratification is ABSENT ⇒ the type-LR is a SINGLE
  PLAIN inductive `RedTy_tot`, not a level-indexed tower.  Big simplification vs
  the value-domain dev.
- **metamltt's `Rel_tot`+`Sig` member-relation trick PORTS.**  `RedTy_tot A B R`
  carries the member relation `R : tm->tm->Type` as an OUTPUT index; package
  `RedTy A B := { R & RedTy_tot A B R }`, project `RedTy_R`.  This avoids
  indexing the term-member relation by a type derivation (the thing that breaks
  naive mutual inductives).  Strict positivity of the DEPENDENT-CODOMAIN Pi
  premise (`forall a a', RDom a a' -> ... RedTy_tot (cod C a) (cod C' a') ...`)
  is ACCEPTED.  Smart constructors (`RedTy_nat`/`RedTy_pi`) + a custom
  `RedTy_rect` that threads the domain IH and the (a,a')-indexed codomain IH all
  type-check, `Type`-valued.
- Member records ported: `RedAtNat`/`RedAtNe` (carry `ne_eq`), `RedAtPi F C F'
  C' RDom RCod t u` (reduce to f,g; `forall a a' (raa':RDom a a'), RCod ...
  (app f a)(app g a')`).

**NEXT (instantiate the validated encoding for OTT, in the real file):**
1. **Pin the exact con-arg orders.**  The injectivity lists in the Lang files
   are NOT reliable full-arity (e.g. `ty_subst`→`["i";"G"]` is short; `app_rel`→
   8 entries is full).  VERIFY by elaborating/printing a real term (rocq MCP, or
   inspect `ott_pi`/`subst_ott` values).  Needed: `Pi_rel`/`Pi_irr` (domain code
   F, codomain code B, levels, env), `Nat`/`Empty`, `app_rel`/`app_irr` (for the
   member `app` term + `pa` index = function position), `lam_rel`,
   `ty_subst (snoc id a) (El B)` (= the `cod_subst` for the Pi member, straight
   from app_rel's OUTPUT type in Pi.v:172), `exp_subst`/`ty_subst` (`pa`→Some,
   the always-reducing formers).
2. **Instantiate `pa`** for OTT (UPDATE-r's standing NEXT): app_rel/app_irr →
   function index, Emptyrec → Empty-proof index, exp_subst/ty_subst → substituted
   -term index; all else `None`.  Build a `pa`-specialised corollary file or fold
   into LogicalRelation.
3. **Decide Kripke now vs later.**  LRProto's Pi case is NON-Kripke (closed
   args only) — enough to STATE the LR and for the fundamental lemma's forward
   direction, but reflect/reify (under-binder, fresh neutral var) NEED the
   object-substitution Kripke quantification: `forall (G':env)(g:sub G' G),
   RedTy (F[/g/]) (F'[/g/])` for the domain, codomain similarly with `under g`.
   RECOMMENDATION: build the object-sub Kripke into the Pi case FROM THE START
   (adding it later = inductive change = rebuild; the value dev's pain was partly
   bolt-on renaming).  This replaces metamltt's `forall Δ wf ρ` with object subs.
4. Then file 4 FundamentalLemma, 5 Decidable.

Note: `step`/`redex` orient EVERY `term_eq_rule` incl. "Pi_rel eta" (Pi.v:39-65)
— eta is NOT meant to be a reduction.  Eta-as-contraction only fires on the
exact eta-expanded shape so it is mostly harmless for soundness, but the LR must
handle eta TYPE-DIRECTED at the Pi member (not via `whstep`).  Watch this when
instantiating; may want `redex` to exclude the eta rule by name.



Did exactly the UPDATE-q NEXT step.  Everything in
`src/Pyrosome/Lang/OTT/Norm/Pi/Reduction.v` (build: `bash scripts/vbuild.sh
src/Pyrosome/Lang/OTT/Norm/Pi/Reduction.v`).  All four new results
`Closed under the global context`.

WHAT LANDED (all generic over `wf_lang l` + a principal-arg selector `pa : V ->
option nat`; everything at Pyrosome `ctx = []`):
- `set_nth` (top-level list update at an index; identity if out of range).
- `eq_args_step_at` — the "one position steps, rest refl" congruence for
  `eq_args`.  **The non-occurrence gate the directive anticipated is NOT
  needed.**  The stepped arg `a` and its reduct `b` are CONVERTIBLE (the
  sort-erased IH gives `eq_term [] _ a b`), so every later-bound sibling's sort
  is preserved UP TO `eq_sort` (from `eq_args_implies_eq_subst` + the
  `eq_sort_subst` constructor); discharge the refl obligation with
  `wf_term_conv`.  So the congruence is fully GENERIC — no occurrence side-
  condition, no `pa`-shape assumption.  (Cleaner than UPDATE-q's plan.)
- `whstep` (inductive): `whstep_redex` (any `redex`) | `whstep_congr` (reduce
  the principal arg `nth_error args i` when `pa name = Some i`, result
  `con name (set_nth args i b)`).  Lives in `Reduction.v` (NOT Neutral.v) — it
  only needs `redex` + `pa`, not the neutral predicates.
- `whstep_sound : rel_sound V l (fun _ => whstep)` — the `whstep_head`
  obligation.  Congruence case = `invert_wf_term_con` → `eq_args_step_at` →
  `term_con_congruence`, with the rule type realigned across `set_nth` by the
  same `eq_sort_subst` conversion.
- `whstep_wf` / `star_whstep_wf` / `star_whstep_sound` (proved DIRECTLY via
  `eq_term_wf_r` + induction on `star`, not through OperationalBridge's sectioned
  `step_*` — see gotcha 3).

GOTCHAS hit (all resolved; will recur in file 3):
1. **`WfCutElim` must be imported QUALIFIED** (`From Pyrosome.Theory Require
   WfCutElim.`, NO `Import`) — its `Import` SHADOWS the bare `wf_term`/`wf_args`
   names this stack relies on (you get "term l : lang expected Type" and "Wrong
   argument name Model (possible name: V_Eqb)").  Use
   `WfCutElim.invert_wf_term_con`.
2. **`core_model_ok` needs `ModelImpls`** imported.  `eq_args_refl` takes its
   `Model_ok` as an EXPLICIT arg → call `apply (eq_args_refl (core_model_ok
   wfl))`.  `eq_args_implies_eq_subst` does NOT take `Model_ok` (unused there) →
   plain `apply`.  `(step := …)`/`(Model := …)` named-arg syntax only works for
   IMPLICIT args.
3. OperationalBridge's `step_wf`/`star_step_*` are sectioned over a SORTED
   `step : sort->term->term->Prop`; for the sort-erased `whstep` the `step`
   metavar can't be inferred from the goal and the leading explicit arg is `V`
   (not `l`).  Just reprove directly (3 short proofs) instead of fighting it.

NEXT = file 3/5 `LogicalRelation.v`: reducibility over `term` indexed by `sort`
(all at `ctx=[]`, object env in the sort), normalizing via `star whstep`.  Need
to INSTANTIATE `pa` for OTT (eliminators `app_rel`/`app_irr` → principal =
function position; the always-reducing `exp_subst`/`ty_subst` → `Some _`).  The
Neutral.v `neutral`/`whnf` predicates (file 2) drive the LR case split; reify/
reflect via reduction + type-directed eta.  See UPDATE-n FILE PLAN.

## UPDATE 2026-06-06q — FORK RESOLVED (Dustin): build `whstep`; `partial_eval` is OUT.

The file-3 fork below ("whstep vs partial_eval normalizer") is DECIDED: hand-rolled
weak-head `whstep` is NECESSARY; `partial_eval` is NOT useful for the LR. (This reverses
the earlier RECOMMENDED note that leaned on `partial_eval` as a black-box normalizer.)

WHY: `partial_eval_correct` gives SOUNDNESS ONLY (`eq_term l c t e (partial_eval …)`).
`partial_eval` is a fuel FUNCTION that returns `e` unchanged on fuel exhaustion / proof-
checker failure — NO whnf guarantee, NO determinism/confluence, and (the killer) it is
NOT an inductive relation. The reduction-on-syntax LR is defined by case analysis on the
whnf reached by reduction and proved by INDUCTION ON REDUCTIONS; it needs relation-level
facts a black-box function cannot give: anti-reduction / backward closure, the whnf-
driven LR clauses, weak-head determinism (a type reduces to a UNIQUE head former), and
reflect (a neutral is a stable normal form that does not step). The "its output is a
whnf = normalization = fundamental-lemma content anyway" rationale is CIRCULAR: defining
reducibility via `partial_eval` would itself require a normalization theorem, which
needs the reduction relation. `partial_eval` survives only as a possible later
executable-evaluator convenience in `Decidable.v`, certified from the already-
established normalization — never as the LR substrate.

NEXT CONCRETE STEP: write `whstep` = the head-congruence closure of `Reduction.v`'s
`redex`/`step`, reducing the principal arg of an eliminator spine via `Neutral.v`'s `pa`
selector. Its one real obligation is `whstep_head` soundness (invert via
`WfCutElim.v:194 invert_wf_term_con`, recurse on the principal arg, lift with
`term_con_congruence`; the `eq_args` "one position steps, rest refl" helper must be
non-occurrence-gated — TRUE for a function/scrutinee principal arg since siblings depend
on the DOMAIN, not the head). Then file 3 LogicalRelation over `star whstep`.

## UPDATE 2026-06-06p — PIVOT FILE 2/5 LANDED: `Neutral.v` GREEN + axiom-free.

`src/Pyrosome/Lang/OTT/Norm/Pi/Neutral.v` (committed).  Generic over a
principal-argument selector `pa : V -> option nat` (eliminator head ↦ index of
its head sub-term; non-eliminators ↦ `None`):
- `neutral` (inductive): `var x` | eliminator whose principal arg is neutral.
- `whnf e := neutral e \/ (con-headed by a non-eliminator)`.
- `neutral_whnf`, `var_neutral`/`var_whnf`, `neutral_inv`, `whnf_elim_neutral`
  (an eliminator-headed whnf is neutral).  All axiom-free.

DESIGN DECISIONS taken this session (per Dustin):
- (Q1, step index) Use the SORT-ERASED weak-head relation `whstep : term ->
  term -> Prop` and prove `rel_sound l (fun _ => whstep)`, recovering the sort
  from `wf_term` via the sort-uniqueness theorem `Theory/Core.v:1708
  term_sorts_eq` (+ `wf_term_subst_monotonicity:1255` for the redex
  presupposition `wf_term [] e1[/s/] t0[/s/]`).  This is cleaner than threading
  an existential sub-sort.  `whstep` itself NOT YET written — see NEXT.
- (Q2, whnf) Recommended model adopted: whnf = head-canonical-former or
  var-headed blocked elim, NO pending head substitution.  In OTT, `pa` must send
  `exp_subst`/`ty_subst` to `Some _` (they always reduce) so `whnf` never
  accepts an un-pushed substitution.  See the CAVEAT block atop Neutral.v.

DONE this session beyond the predicates: `Reduction.v` now also has the
sort-erased `redex` + `redex_sound` (recovers the sort via `term_sorts_eq` +
`eq_term_conv`, presupposition from `wf_term_subst_monotonicity`) — the design is
LOCKED IN and proven.

OPEN FORK BEFORE FILE 3 (decide first — it determines whether more reduction
machinery is even needed):  **does the LR normalize via a hand-rolled `whstep`,
or via `Compilers/PartialEval.v`'s `partial_eval` (already proven sound by
`partial_eval_correct`)?**
- If `partial_eval`: NO `whstep`/head-congruence needed.  The LR uses
  `partial_eval` as a black-box normalizer (soundness free); the only remaining
  obligation is that its output is a `whnf` (= normalization), which is the
  fundamental-lemma content anyway.  RECOMMENDED — avoids the fiddly congruence.
- If hand-rolled `whstep`: still must prove `whstep_head` soundness.  Plan:
  invert via `WfCutElim.v:194 invert_wf_term_con` (gives `In term_rule` +
  `wf_args` + `eq_sort \/ eq`), recurse on the principal arg (sort-erased IH),
  lift with `term_con_congruence`.  GOTCHA: the `eq_args` "one position steps,
  rest refl" helper needs the changed variable to NOT occur in head-ward
  (later-bound) sibling types — TRUE for a function/scrutinee principal arg
  (siblings depend on the DOMAIN, not the function) but a general lemma needs
  that non-occurrence as a hypothesis.  `invert_wf_term_con` + `set_nth` + a
  non-occurrence-gated `eq_args_set_nth` is the shape.

THEN files 3 LogicalRelation (the big design step: reducibility over `term`
indexed by `sort`, all at Pyrosome ctx=[], object env in the sort; reify/reflect
via reduction + type-directed eta), 4 FundamentalLemma, 5 Decidable.  `pa` (the
principal-arg selector) must be instantiated for OTT (eliminators app_rel/app_irr
+ the always-reducing exp_subst/ty_subst → Some _).

## UPDATE 2026-06-06o — PIVOT FILE 1/5 LANDED: `Reduction.v` GREEN + axiom-free.

`src/Pyrosome/Lang/OTT/Norm/Pi/Reduction.v` (committed).  Generic over any
`wf_lang l` (Pyrosome ctx = `[]`):
- `step : sort -> term -> term -> Prop` with one constructor `step_redex`: the
  redex is the LHS of a computation `term_eq_rule` instantiated by a CLOSED
  `wf_subst l [] s c`; it rewrites `e1[/s/] ↝ e2[/s/]` at type `t[/s/]`.
- `step_sound : rel_sound V l step` — proven via `eq_term_by` + `eq_term_subst`
  (s1=s2=s, `eq_subst_refl`, `wf_ctx` from `with_rule_in_wf_crush`).  Axiom-free.
- `step_wf` / `star_step_wf` / `star_step_sound` — specialised straight from
  `Compilers/OperationalBridge.v` (subject reduction + `↝* ⊆ eq_term` for free).

GOTCHAS for the next files: (a) the parametrized `Notation wf_subst l`/`wf_ctx l`
are NOT exported from Core — REDECLARE them locally (every consumer does, cf.
PartialEval.v).  (b) `OperationalBridge.rel_sound`/`star` take `V` POSITIONALLY
(`rel_sound V l step`), not `(V:=V)`.

DESIGN NOTE (Q1 resolved): `step` is the TOP-LEVEL oriented rule rewrite only — no
evaluation-context congruence yet.  Weak-head congruence (reduce the head of an
`app_rel`/`app_irr` spine) is DEFERRED to `Neutral.v`, where the OTT eliminator
spine structure is in scope; soundness there will go through `term_con_congruence`
(needs `eq_args` "one position steps, rest refl" — a reusable helper to write).

NEXT = file 2/5 `Neutral.v`: neutral & whnf predicates on `term` (head = var or
blocked elim), the head-congruence extension of `step`, determinism of weak-head
`step`.  Then LogicalRelation (3/5), FundamentalLemma (4/5), Decidable (5/5).

## UPDATE 2026-06-06n — PIVOT SUBSTRATE CORRECTED (Dustin): EVERYTHING over PYROSOME TERMS (`term`/`sort`/`eq_term`), NOT a de Bruijn `tm`. Remove value domain; rip out in place; target Pi.

**SUPERSEDES UPDATE-m's `tm` plan — that was WRONG.** Do NOT introduce a separate de
Bruijn `tm` (nor reuse `sval`). Work DIRECTLY on Pyrosome `@term V`/`@sort V`
(Theory/Term.v: `term = var V | con V (list term)`, NAMED vars, substitution `e[/s/]`)
in a language `l = ott_*`, and use Pyrosome's `eq_term l c t e1 e2` (Theory/Core.v) AS
the declarative equality. NO separate conversion judgment, NO `Syntax.v`, NO
`Declarative.v`, NO `Domain.v`. (This is what Dustin's earlier "why a separate
conversion when eq_term exists?" was steering toward — the answer is: don't have one.)

**WHY pivot (unchanged):** metamltt has no value domain — reduction-on-syntax LR; our
NbE value domain (`sval`+`Apply/Reflect/Reify`) is what made RR_pi_at painful. But the
SUBSTRATE is Pyrosome terms, not the paper's `tm`: port the TECHNIQUE (reduction +
reducibility LR + reify/reflect + fundamental lemma) instantiated on Pyrosome's own
syntax & judgments. Paper infra (Ltac2/Equations-UIP/ssreflect/autosubst) is
irrelevant — we never touch the paper's term type.

**REDUCTION = directed orientation of the lang's computation rules; ⊆ eq_term FOR
FREE.** Beta/computation are `term_eq_rule c lhs rhs t` entries in `ott_pi`/`ott_comp`
(Lang/OTT/Computations.v `ott_comp`). Define weak-head `step : sort -> term -> term ->
Prop` rewriting by those. **REUSE `Compilers/OperationalBridge.v`**: it already has
`star` (refl-trans closure), `rel_sound l R := wf_term l [] a t -> R t a b -> eq_term l
[] t a b`, and `step_sound`+`step_wf` ⇒ `star_step_sound`/`star_step_wf`. So once
`step` is sound (each step = `eq_term_by`) and preserves `wf_term` (subject reduction),
`↝* ⊆ eq_term` and wf-preservation are basically FREE. `Compilers/PartialEval.v`
(`partial_eval l c t fuel e` with `eq_term l c t e (partial_eval …)`) is a ready
fuel-evaluator to mine for the normalizer. ETA is NOT a reduction step — handle it
TYPE-DIRECTED in the LR/reify at function sorts (paper `ConvTmEta`).

**CONTEXT MODEL (Dustin, 2026-06-06n) — EVERYTHING is at Pyrosome `ctx = []`.** In
Pyrosome the `ctx` holds META-variables, NOT object variables; the OTT encoding puts
the OBJECT-level context/binding into the SORT as an `env` term. The surface sorts are
`scon "exp" [A; i; G]` (expr of type `A`, level `i`, in object env `G`), `scon "ty"
[i; G]`, `scon "sub" [Gd; Gc]`, `scon "env" []` (confirmed in Norm/Model.v `glue_*`).
So ALL judgments/reduction/LR/fundamental-lemma are stated at Pyrosome `ctx = []`
(exactly as the existing Model: `eq_term fo_lang [] t e1 e2`), and OBJECT open-ness is
the `env` `G` inside the sort. Consequences: (a) `OperationalBridge`'s `[]`-statements
fit DIRECTLY — no open-Pyrosome-ctx generalization needed; (b) "under a Pi binder" in
reify = EXTEND the object env `G` (a term-level op, e.g. the subst-calculus
`ext`/`snoc`), never extend the Pyrosome ctx; (c) renaming/weakening that mattered in
the value dev is now object-`env` weakening via `subst_ott`, not Pyrosome ctx renaming.
This RESOLVES open-Q3 below (always closed `[]`).

**FILE PLAN.** DELETE the entire value-domain tree in `OTT/Norm/Pi/` (and non-Pi
`OTT/Norm/` value files): Domain, Apply, ApplyLemmas, ApplySubst, ApplyConv, Reflect,
Reify, ReifyConv, EvalRel, Determinism, Typing(sval), Preservation(sval), RenSubst,
RenTyping, LogRel2*, Model(eval-glue), ModelOk, SortInj, Glue, Smoke. Surface langs
(Lang/OTT/*.v: Base/Nat/Pi/Computations/…) UNCHANGED. NEW (all over Pyrosome `term`,
lang `ott_full`):
- `Reduction.v`: weak-head `step`/`↝` from computation `term_eq_rule`s; `step_sound`
  (⊆ eq_term via eq_term_by) + `step_wf` (subject reduction); whnf predicate; via
  OperationalBridge get `↝* ⊆ eq_term`. Determinism/confluence as needed.
- `Neutral.v`: neutral & whnf predicates on `term` (head = var / blocked elim).
  Possibly structural `~annot`/`~ne` as DEFINED notions IF the LR needs
  annotation-insensitive neutral comparison — but declarative equality stays `eq_term`.
- `LogicalRelation.v` (+submodules): reducibility over `term` INDEXED BY `sort`, ALL
  at Pyrosome `ctx = []` (see CONTEXT MODEL below). The sort carries the OBJECT env, so
  the LR is indexed by sorts like `scon "ty" [i; G]` / `scon "exp" [A; i; G]` with `G`
  the object env. Reify/reflect via reduction (old RR_pi_at, reduction-based +
  type-directed eta); going under a Pi binder EXTENDS `G` (a term op), not the
  Pyrosome ctx.
- `FundamentalLemma.v`: `wf_term`/`eq_term` (at `ctx=[]`) ⇒ reducible (use Pyrosome
  cut-elimination Theory/CutElim.v/CutFreeInd.v/WfCutElim.v for canonical derivations/
  inversion + Theory/Renaming.v). Substitution lemmas are over the OBJECT subst
  calculus (`sub` terms / `subst_ott`), not Pyrosome meta-substitution.
- `Decidable.v`/`Corollaries.v`: normalization + **decidability of `eq_term` for OTT**
  (the payoff). A Pyrosome `Model` instance, if still wanted, is a corollary — likely
  drop the `norm_ceq`/eval-glue Model entirely.

**REUSE (Pyrosome, not the value dev):** `Compilers/OperationalBridge.v` (reduction
soundness/closure scaffolding), `Compilers/PartialEval.v` (fuel evaluator),
`Theory/CutElim.v`+`CutFreeInd.v`+`WfCutElim.v` (canonical derivations for the
fundamental lemma), `Theory/Renaming.v`, `Theory/ClosedTerm.v`/`ClosedCore.v`,
`basic_core_crush` (Core.v). The conv EQUIVALENCE is free (`eq_term` has
refl/sym/trans/conv/subst already). The metamltt LR ARCHITECTURE (reducibility shape,
reify/reflect, eta-at-Pi) is the conceptual guide. NOTHING from the
`sval`/`Apply`/`RenSubst` dev transfers as CODE (named ≠ de Bruijn).

**EXECUTION ORDER (each green before next):** Reduction → Neutral → LogicalRelation
(+subs) → FundamentalLemma → Decidable/Corollaries. No Syntax (term exists), no
Declarative (eq_term exists), no named↔deBruijn bridge.

**OPEN DESIGN Qs (decide at start of next session, before coding the LR):**
1. `step`: generic "rewrite by any oriented `term_eq_rule`" vs hand-listed weak-head
   `step` for the specific OTT computation rules (generic=reusable; hand-listed=easier
   determinism).
2. Does the LR need structural `~annot`/`~ne` at all, or can neutral members be
   compared by `eq_term` + a "stuck" predicate? (Paper needs `~ne` only because its `≡`
   is declarative-only; here `eq_term` IS declarative — maybe unneeded.)
3. [RESOLVED — see CONTEXT MODEL above] ALWAYS Pyrosome `ctx = []`; object open-ness
   is the `env` `G` in the sort. No open-Pyrosome-ctx generalization; under-binder =
   extend `G`.

**FIRST CONCRETE STEP next session:** read `Compilers/OperationalBridge.v` +
`PartialEval.v` fully; pick `step` (Q1); write `Reduction.v` (`step`+`step_sound`+
`step_wf`), build green via OperationalBridge.

---
## UPDATE 2026-06-06l — conv_ty_eta CORE PORT LANDED + green; construction-side = reflect-adequacy (NOT a separable bridge)

**CORE PORT DONE & COMMITTED (commit on `gluing-nbe`).**  The four WIP metatheory
lemmas are migrated into the real layering and the low stack is GREEN + axiom-free:
- `Typing.v`: `conv_ty_eta`/`conv_tm_eta`/`conv_ne_eta` standalone mutual inductive
  (after the `ne_below_*` defs, inside `Section Typing`) + Combined Scheme
  `conv_eta_mutind`; `n_conv` now consumes `conv_ty_eta Ge A B` (was `conv_nf A B`);
  `conv_eta_ne_below`/`_rev` (structural, axiom-free).
- `Preservation.v`: `conv_eta_shift` proven before `weaken_typing`; `ne_below_shift`
  + projections MOVED here from `RenSubst.v` (purely structural `sval_mutind`, needed
  low); `weaken_typing` n_conv shift case migrated.  NOTE: `conv_ty_eta_shift` has
  `c` IMPLICIT (Set Implicit Arguments) — call it `@conv_ty_eta_shift Ge A B cAB c T0 Hc`.
- `RenTyping.v`: `conv_eta_ren` (+ helper `ne_below_ren_val`) before `ren_typing`;
  `typing_ne_below` + `ren_typing` n_conv transport cases migrated.
GREEN through: Typing, Preservation, ApplySubst, RenSubst, RenTyping, LogRel2,
LogRel2Ind, LogRel2Red.  Build with `scripts/vbuild.sh <file.v>` (make is stale).

**FIRST BREAK = LogRel2Lemmas:79** (then LogRel2Sym:133-138, LogRel2Reflect:510/
560/757/767).  These FRESH `n_conv` constructions need `conv_ty_eta`/`conv_ne_eta`
where they previously built `conv_nf` via `cnf_ne`/`cnf_pi`.

**KEY FINDING — the construction-side is NOT a separable mechanical bridge; it IS
the reflect-adequacy core (RR_pi_at / Thm-11).**  Tried to scope a generic bridge
`conv_ne n m -> wf n T -> wf m T -> conv_ne_eta Ge T n m` (mutual TM/TY).  It does
NOT go through as a standalone induction:
- The hard case is `conv_tm_eta` at a RELEVANT Pi type.  The ONLY constructor there
  is `ctm_eta` (eta-expand).  So even a NEUTRAL argument at a Pi-typed position
  ([cne_eta_app]'s `a` at `dEl F` with `F = vPi…`) must eta-expand — reflexivity is
  not structural.
- The eta recursion is TYPE-DIRECTED: `ctm_eta`'s sub-goal is at the instantiated
  codomain `B' = B[ARG]`, which is NOT a structural subterm of `vPi F B` (subst can
  grow).  conv_nf-stability under Apply EXISTS (`ApplyConv.v`: Apply preserves
  conv_nf under conv_sub) so the *bodies* relate, but TERMINATION needs the LR's
  well-foundedness — i.e. this is exactly NbE reflect-adequacy, the circular-with-
  normalization thing the declarative-inductive choice was supposed to sidestep.
  The sidestep works for SHIFT/REN/ne_below (proven on the conversion's own
  derivation) but NOT for PRODUCING the conversion from raw `conv_ne`.
- Consequence: the sites split TWO ways.
  (i) **LogRel2Reflect:757/767** are INSIDE the reflect proof where the reflect IH
      (posIH) is in scope → they should PRODUCE `conv_ty_eta` from the recursive
      reflect results (cte_pi from domain reify-ty + codomain posIH; the eta-body
      n_conv from the IH).  This IS the RR_pi_at work — do it here, not via a bridge.
  (ii) **LogRel2Lemmas:79, LogRel2Sym:133-138, LogRel2Reflect:510** have NO reflect
      IH; they consume `NeConv` (= `conv_ne` + same-type typing).  To get
      `conv_ne_eta` here, `NeConv` ITSELF must carry the eta-conversion (the
      "annotate neutrals" item).  BLOCKER: `conv_ne_eta` is likely NOT symmetric
      (`cne_eta_app`'s result `Bres = Apply B [a]` is computed from the LEFT arg),
      and `NeConv` must be a PER (NeConv_sym).  So either prove a restricted
      symmetry / store both directions, or keep `conv_ne` in NeConv and supply the
      `conv_ne_eta` for `n_conv` from a per-site argument.
- Also surfaced: `typing_ctx_conv` (LogRel2Reflect:609) n_conv case did `exact cAB`
  — now NEEDS a `conv_ty_eta_ctx_conv` (cne_eta_var's `nth_error` changes under
  conv_ctx).  Minor but real.

**DECISION (Dustin, 2026-06-06l): "which one follows the paper" → OPTION 1, paper-
faithful.**  Cross-checked metamltt (`/tmp/metamltt`):
- `Declarative.v:166-203` — the declarative conv `≡` is a genuine EQUIVALENCE:
  `ConvTyRefl/Sym/Trans`, `ConvTmRefl/Sym/Trans`, and `ConvTmConv` (type conv) +
  `WfTmConv` are all CONSTRUCTORS of the one big `derivation` inductive.
- `Neutrals.v` — the LR carries the DECLARATIVE neutral conv `~ne` (`ConvNe`,
  single-typed).  `~ne` is congruence-only; `NeConvSym/Trans/ChChk/Correct` are
  LEMMAS.  KEY trick that makes Sym work past the computed result type:
  `ConvNeAppCong` concludes at a FREE `R` carrying BOTH `R ≡ Cod[a]` and
  `R ≡ Cod'[a']` (dual witness) — so symmetry just swaps them.
- `UpToAnnot.v:31` — `~annot` (= our conv_nf/conv_ne) → `≡` bridge `CorrectTm` is a
  TRIVIAL congruence induction (ConvTmAppCong + ConvTmConv), NO eta, NO termination
  problem (annot only changes annotations; same term structure).  The eta rule
  lives in the fundamental lemma, not the bridge.  **This demolishes the earlier
  "bridge needs normalization" worry.**

**KEYSTONE VALIDATED axiom-free in `WIP/ConvEtaPaper.v`** (committed): the minimally-
invasive port of the above to our value domain = ADD `refl`/`sym`/`trans` (+ a term
type-conversion `ctm_conv`) as CONSTRUCTORS to the committed conv_*_eta, keeping
`cne_eta_app`'s pinned `Bres` (symmetry now from the `cne_sym` CONSTRUCTOR, not from
inverting Bres — simpler than the paper's dual-witness `R`).  Validated: (i)
positivity OK with the equivalence constructors; (ii) `ne_below` transport must
become BIDIRECTIONAL (an `iff`) once `sym` is a constructor — and still goes through
(app cases = per-direction gate-threading, the union of the old fwd+bwd proofs).

**PORT PLAN:**
1. [DONE, committed] Typing.v: `cte_refl/sym/trans`, `ctm_refl/sym/trans/conv`,
   `cne_refl/sym/trans` added to the inductive; `conv_eta_ne_below`(+`_rev`)
   replaced by the single BIDIRECTIONAL `conv_eta_ne_below_iff`; both projections
   (`conv_ty_eta_ne_below`/`_rev`) derived from it (consumers unchanged).
2. [DONE, committed] Preservation `conv_eta_shift` / RenTyping `conv_eta_ren`:
   new constructor cases added (trivial closure; sym/trans/conv use the iff to
   recover ne_below of swapped sub-derivations).  GREEN+axiom-free through
   LogRel2Red.
3. [NEXT] Switch `NeConv` (LogRel2.v:87-88) `conv_ne n m` → `conv_ne_eta Ge T n m`
   + `RedNatEq`/`RedNeutralEq` base PERs (they carry NeConv, so automatic).  PER
   laws `NeConv_sym`/`_trans` (LogRel2Lemmas:90-97) become trivial: `cne_sym`/
   `cne_trans` constructors (drop `conv_ne_sym`/`conv_ne_trans`).
4. [NEXT] Fix the CONSUMER sites (cascade found by `grep conv_ne|cnf_ne|NeConv`):
   - LogRel2Lemmas:79 → `eapply cte_ne; exact (snd cnm)` (was `apply cnf_ne`).
   - LogRel2Sym:131-139 → `cne_sym` for the conv field; `eapply cte_ne` for the
     n_conv conversions (was `apply cnf_ne; exact [conv_ne_sym] cnm`).
   - LogRel2Ren:37-43 `NeConv_ren` → needs the `cne`-projection of `conv_eta_ren`
     (EXPOSE it: currently only `conv_ty_eta_ren`=proj1 is exported; add the
     conv_ne_eta ren projection).  ne_below precond comes from the carried
     `wf_neutral` via `typing_ne_below`.
   - `typing_ctx_conv`(Reflect:609) `exact cAB` → needs `conv_ty_eta_ctx_conv`
     (cte_var's `nth_error Ge k` changes under conv_ctx; add a ctx-conv transport
     for conv_*_eta, OR carry it — the conv_ctx relates types up to conv so this is
     a real but tractable transport lemma).
5. [NEXT — RR_pi_at, the research core] LogRel2Reflect CONSTRUCTS NeConv from raw
   `conv_ne` in many places (reflect_nat/empty/neEl/U/El @61-124, `Hvar`@329,
   the eta-body construction @700-769, sites @395-396/510).  With NeConv carrying
   `conv_ne_eta` these must PRODUCE `conv_ne_eta` from sub-parts — `cne_app`/`cne_eta_*`
   with the Apply premises + the reflect IH (posIH).  757/767 = cte_pi from domain
   reify-ty + codomain posIH; now sym/trans/ctm_conv are available to glue.  This
   is metamltt's Theorem 11 (Reflect) adequacy.
6. [NEXT] Model/ModelOk soundness: eta-conv (incl refl/sym/trans/conv) types
   denote the same type (sym/trans/refl obviously sound; the eta rule = the
   gluing-model eta law).

GREEN FRONTIER right now: Typing, Preservation, ApplySubst, RenSubst, RenTyping,
Reify, ApplyConv, ReifyConv, LogRel2, LogRel2Ind, LogRel2Red, LogRel2Lemmas,
LogRel2Irr, LogRel2Sym, LogRel2Ren (ALL axiom-free, incl LR_sym_gen).  Steps 1-4
DONE + committed.  Build single files with `scripts/vbuild.sh`.

REMAINING = LogRel2Reflect (step 5, RR_pi_at) + downstream (Glue, Smoke, Model,
ModelOk, SortInj).  **LogRel2Reflect scope (49 `conv_nf`/`cnf_` sites):** NeConv now
carries `conv_ne_eta`, so the reify-direction must be RE-AIMED at the declarative
conversion (paper: reify `⇓` produces `≡`, NOT `~annot`).  Concretely:
- FIRST BREAK reify_nat:44 / reify_neutral:50 / 395-396: they `destruct` the NeConv
  field (now `conv_ne_eta`) and feed `cnf_ne` (wants `conv_ne`).  conv_ne_eta→conv_nf
  is UNSOUND (eta-short vs eta-long) — so these reify lemmas must CONCLUDE
  `conv_*_eta` (e.g. `reify_neutral : RedNeutralEq Ge T a b -> conv_tm_eta Ge T a b`),
  not `conv_nf`.  Cascades to `reify_tm`/`reify_ty` (the RRCar engine ~169-340,
  `conv_nf_ty` → a `conv_sty_eta`) and the Pi reflect (dom_reify_ty:636,
  Hcod:683, the eta-body construction 700-775).
- The eta-falsity that blocked R1 DISSOLVES: `Hcod : conv_nf BA BB` (off-diagonal
  FALSE) becomes `conv_ty_eta Ge BA BB` produced by the codomain reflect IH (posIH);
  `cte_pi` builds the Pi conv from domain reify-ty + that codomain conv; the n_conv
  retypes via cte_ne/cte_pi + cne_conv (all now available).
- conv_nf/conv_ne / Reify / ApplyConv / ReifyConv themselves STAY (structural
  ~annot is still a real notion; just no longer what the LR carries).  May still be
  used internally by reify if a structural step is wanted, but the LR-facing
  conclusions move to conv_*_eta.
- `typing_ctx_conv`:609 still needs `conv_ty_eta_ctx_conv` (cte_var changes under
  conv_ctx); 526/547/560 use conv_nf in `conv_ctx` (cc_dEl) — decide whether
  conv_ctx stays structural or moves to conv_ty_eta.
This is metamltt Theorem 11 (Reify/Reflect) adequacy — the central open problem; do
it as a focused phase, prototyping the re-aimed reify signatures in WIP first.

## UPDATE 2026-06-06k — conv_ty_eta METATHEORY DE-RISKED in WIP (ne_below side-conds ⇒ STANDALONE, no fusion)

**Refined the UPDATE-j plan and validated it in `WIP/ConvEtaProto.v` (compiles,
axiom-free under the repo -R map).**  The eta rule `ctm_eta` + neutral-app rules
carry `Reflect`/`Apply_val`/`Vapp` premises; TWO facts force `ne_below_val`
side-conditions on them — (1) ne_below transport `ne_below f ⇒ ne_below g` across
`ctm_eta` is structurally UNPROVABLE (`g` relates to `f` only via the BETA-REDUCED
apps `fa`/`ga`; `Vapp` can't be inverted backward), and (2) `Reflect_ren`'s
signature DEMANDS `ne_below_ty`/`ne_below_ne`.  KEY: `ne_below` premises (NOT full
typing) suffice, so `conv_*_eta` stays a **STANDALONE** mutual inductive — `n_conv`
referencing it is one-directional, **NO fusion** into the `has_svalty`/`wf_neutral`
block (the UPDATE-j "co-define with typing" instinct was over-cautious; the real
driver was this scopedness gap, which side-conds fix more cheaply).

**VALIDATED (all axiom-free vs the real Apply/Reflect/Vapp metatheory):**
- inductive `conv_ty_eta`/`conv_tm_eta`/`conv_ne_eta` with `ne_below_val (length
  Ge) F/f/g` side-conds on `ctm_eta` — type-checks, positivity OK.
- `conv_ty_eta_ne_below`     (fwd transport)  → RenTyping.v:263.
- `conv_ty_eta_ne_below_rev` (bwd transport)  → RenTyping.v:425 (replaces the
  `conv_nf_sym`+`conv_nf_ne_below` combo; conv_ty_eta may NOT be symmetric since
  `cne_eta_app`'s result type `Bres` is computed from the LEFT arg).
- `conv_ty_eta_shift`        (binder insert at cutoff c, via `wk_ctx`) →
  Preservation.v:661.  `ctm_eta` case = `t_lam_eta`'s shift PLUS two `Vapp` shifts
  (`Vapp_shift := snd (fst Apply_shift_commute)`, aligned by `shift_val_comm0` +
  `shift_shift_comm`).

- `conv_ty_eta_ren`           (renaming)      → RenTyping.v:428.  DONE.  Mirrors
  `ren_typing`'s `t_lam_eta` (`Reflect_ren` + `Apply_val_ren_commute` + the
  `ren_ctx`/`ren_ok` plumbing) PLUS two `Vapp_ren` (`:= snd (fst Apply_ren_commute)`)
  with the same ren-commute alignment (`ren_shift_comm{0,1}_val`).  Needed ONE new
  helper, `ne_below_ren_val : ne_below_val N v -> ren_ok rho N m2 -> ne_below_val m2
  (ren_val rho v)` (3-liner via `ren_is_Apply_val` + `Apply_val_ne_below` +
  `ren_sub_nth`) — `t_lam_eta` has no ne_below side-conds so `ren_typing` never
  needed it; the `ctm_eta` side-conds must be re-established over the target ctx.

**METATHEORY COMPLETE.**  All four lemmas the `n_conv` switch needs are PROVEN +
axiom-free in `WIP/ConvEtaProto.v`.  No more prototype unknowns.

**THEN the core port (mechanical, multi-file rebuild ~1h):** (a) move the inductive
into a real file BELOW Typing (new `ConvEta.v` importing `Domain Apply Reflect
LogRel2Conv`, OR add `Apply Reflect` imports to `LogRel2Conv`); (b) `Typing.v`
`n_conv`: `conv_nf A B` → `conv_ty_eta Ge A B` (constructor count unchanged ⇒ Scheme/
`has_neutral_mutind` untouched); (c) `conv_ty_eta_ne_below`/`_rev` proven at/after
RenTyping (need `Apply_val_ne_below`/`Reflect_scoped`@RenSubst), `conv_ty_eta_shift`
in Preservation BEFORE `shift_typing`, `conv_ty_eta_ren` at RenTyping; (d) migrate the
n_conv consumer sites: Preservation:661, RenTyping:263/425/428 (transport — easy);
(e) FRESH n_conv constructions need the structural→declarative bridge with TYPING
available: LogRel2Sym:133-138 + LogRel2Reflect:510/610/757 = the HIGH "reify produces
conv_ty_eta" lemma (diagonal `conv_nf⇒conv_ty_eta` is NOT free for app-spine neutrals
— needs arg types from typing); (f) Model/ModelOk soundness (eta-conv dEl types denote
same type).  See memory [[ott-conv-ty-eta-declarative]].

## UPDATE 2026-06-06j — DUSTIN CHOSE conv_ty_eta (opt 2); REALIZATION = DECLARATIVE (mutual w/ typing)

Dustin's call on the UPDATE-i fork: **option 2 — a separate eta-closed DECLARATIVE
type-conversion judgment used by `n_conv`, `conv_nf` stays the final structural
decision, reify produces the conversion.**

**LAYERING FINDING (rules out the naive read-back realization).**  I first tried
`conv_ty_eta m A B := forall nA nB, ReifyTy m A nA -> ReifyTy m B nB -> conv_nf nA
nB` (read-back equality) in a low defs file.  This DOES NOT WORK with the current
file layering: `n_conv` is in `Typing.v`, so its conversion premise must be
SHIFT/REN-stable for the LOW typing metatheory — `Preservation.v` line 661 (typing
under shift) and `RenTyping.v` lines 263/423/260 (typing/scoping under renaming)
each have an `n_conv` case that transports the conversion.  But read-back stability
(`ReifyTy_shift`/`ReifyTy_ren`, which DO NOT EXIST yet) needs `Reflect`/`Apply`
shift-commutation, and `Reflect_ren` lives in `RenSubst.v` — ABOVE `Preservation`.
So `conv_ty_eta_shift` is UN-provable at the `Preservation` layer.  Confirmed deps:
`RenSubst → Preservation`, `Reflect_ren ∈ RenSubst`, `Apply_ren_comp ∈ RenSubst`;
only `Apply_val_shift0` is low (in `Preservation.v` itself).  Any eta-closed
conversion expressive enough needs application (`Apply`) — so it CANNOT be a purely
low structural inductive either.

**REALIZATION (matches Dustin's word "declarative"): co-define the conversion WITH
typing.**  Add a type-directed eta-closed conversion (`conv_ty_eta`/`conv_tm_eta`,
likely `conv_ne_eta`) in the SAME mutual block as `has_svalty`/`wf_neutral` in
`Typing.v` (paper's `Declarative.v`: `ConvTy`/`ConvTm`/`ConvNe` mutual with
`WfTm`).  Then its shift/ren stability is proven STRUCTURALLY in the SAME
`Preservation`/`RenTyping` inductions (no Reify/Reflect needed — the conversion's
own constructors drive it; the eta rule's codomain instance uses `Apply_val`,
whose shift is available low, exactly as `t_lam_eta` already does).  This dissolves
the layering wall.  `n_conv : wf_neutral Ge n (dEl A) -> conv_ty_eta Ge A B ->
wf_neutral Ge n (dEl B)`.

**BUILD SPEC (proposed constructor set for the eta-closed type-directed conversion;
prototype in WIP/ConvEtaProto.v before touching the core inductive):**
- `conv_ty_eta Ge : sval -> sval -> Prop` (type codes): congruence (cte_nat,
  cte_empty, cte_pi [dom + cod under binder], cte_piI, cte_ne via conv_ne_eta) +
  refl/sym/trans (or admissible).
- `conv_tm_eta Ge : svalty -> sval -> sval -> Prop` (TYPE-DIRECTED values): structural
  congruence at base/neutral + the ETA rule at relevant Pi: `conv_tm_eta Ge (dEl(vPi
  F B)) f g` when (eta-expand both: `conv_tm_eta (Ge,F) (dEl B') (f·var0) (g·var0)`
  via `Apply_val`/`Vapp`, mirroring `t_lam_eta`/`rfy_Pi`).  This is where eta is
  baked in — knowing the type makes it well-defined (the untyped version is not).
- `conv_ne_eta Ge : neutral -> neutral -> Prop`: cne-like, args related by
  `conv_tm_eta` at the annotation type.
- Then: (i) `conv_ty_eta_of_nf`/`refl` (diagonal), (ii) shift/ren stability proven
  alongside typing, (iii) HIGH lemma "reify/LR reify-ty produces conv_ty_eta", (iv)
  migrate `n_conv`, (v) re-green stack, (vi) Model soundness (read-back-equal `dEl`
  types denote the same type ⇒ eta-conv types do too).

This is a big central-definition change (enlarges the core typing inductive ⇒ full
OTT/Pi rebuild) — multi-session.  Tasks #1–#5 created.  Prototype the conversion
inductive + its key closure (Pi typing bridge: `conv_ty_eta Ge (vPi FA BA)(vPi FB
BB)` from domain + codomain-at-bare-var conversions) in WIP first
(`WIP/ConvEtaProto.v`).

**WHY DECLARATIVE/INDUCTIVE, NOT read-back-equality (the TOTALITY trap).**  A
read-back `conv_ty_eta := forall nA nB, ReifyTy A nA -> ReifyTy B nB -> conv_nf nA
nB` is *almost* layerable low (`Reflect_weaken`@Preservation:451 + `Apply_val_shiftc`
make `ReifyTy_shift` provable at the Preservation layer; `Reflect_ren`@RenSubst makes
`ReifyTy_ren` provable at the RenTyping layer).  BUT `RenTyping.v:263`'s `n_conv`
case needs `conv_ty_eta_ne_below` (`ne_below A` ⇒ `ne_below B`), and from the
UNIVERSAL read-back form that requires instantiating at SOME read-backs of A,B —
i.e. **ReifyTy TOTALITY** (every scoped code has a read-back) ≈ normalization,
circular here.  The EXISTENTIAL form (read-backs EXIST + conv_nf) carries them but
then PRODUCING `conv_ty_eta` from LR reify-ty needs totality too.  The DECLARATIVE
INDUCTIVE conversion sidesteps totality entirely: `ne_below`/shift/ren stability are
proven STRUCTURALLY on the conversion's own derivation (no read-back).  This is
exactly why the paper's typing conversion is declarative, not read-back equality.

## UPDATE 2026-06-06i — R1 PLAN HITS A TYPING-CONVERSION WALL; FORK FOR DUSTIN

**The UPDATE-h/g plan (port `reifyReflect`: bare reflect + read-back reify-ty)
does NOT close the relevant-Pi case.**  Pinned down the exact obstruction (it is
the unresolved "watch" item the UPDATE-g plan itself flagged in its step 5 — *"the
typing rule `n_conv`'s conversion side — confirm it composes with the read-back
conv"*; it does NOT compose):

- At a Pi node the RIGHT member's typing is *only* obtainable from the LEFT typing.
  `NeConv` is SINGLE-typed (paper `RelAtNe`), so a reflected neutral `m` is typed
  ONLY at the LEFT Pi: `wm : wf_neutral Ge m (dEl (vPi FA BA))`.  But the member
  goal `PiRedTmEq PA (vNe n) (vNe m)` requires `has_svalty Ge (vNe m) (dEl (vPi FB
  BB))` (the RIGHT Pi).  The ONLY bridge is `n_conv` (Typing.v), which needs
  **RAW `conv_nf (vPi FA BA) (vPi FB BB)`** = raw `conv_nf FA FB` (= `dom_reify_ty`,
  fine) **+ raw `conv_nf BA BB`** (= R1).
- raw `conv_nf BA BB` is OFF-DIAGONAL-FALSE — it is precisely the R1 eta-falsity
  ([[ott-r2-hereditary-eta]]): off-diagonal codomain codes can be eta-short-vs-eta-
  long and `conv_nf` has no eta rule.
- Read-back reify-ty only ever yields `conv_nf` of the **read-backs** (`ReifyTy`
  eta-expands), NEVER of the raw codes.  So switching reify-ty to read-back makes
  the *reify-ty THEOREM* true but does NOTHING for the *typing bridge* inside the
  Pi REFLECT, which consumes RAW `conv_nf` via `n_conv`.  Bare reflect and the old
  eta-long reflect hit this IDENTICALLY (the old `eta_bodies` only "worked" by
  assuming the false `Hcod : conv_nf BA BB` Context).

**ROOT CAUSE.**  Our `n_conv` (and the neutral annotations) use the STRUCTURAL
`conv_nf` (paper Def-13 `∼annot`, which is sound ONLY on already-reified eta-long
forms).  The paper's `WfTmConv`/`ConvTmConv` use the **eta-closed DECLARATIVE `≡`**
(`ConvTy`/`ConvTm`), which is exactly what `reifyReflect`'s reify-ty (DnTy) produces
— so in the paper the thing reify produces and the thing typing-conversion consumes
are the SAME eta-closed judgment.  In our dev they are DIFFERENT: reify produces
read-back-`conv_nf`, typing needs raw-`conv_nf`.  THIS is the fork.

**FORK (a genuine architectural decision; surfaced to Dustin):**
1. **Make `n_conv`'s conversion ETA-CLOSED = "same read-back."**  Change `n_conv`
   to require `(forall nA nB, ReifyTy m A nA -> ReifyTy m B nB -> conv_nf nA nB)`
   instead of raw `conv_nf A B`.  This is eta-closed by construction (ReifyTy
   eta-expands neutral args via `Reify`/`rne_app`), and it is EXACTLY what the
   read-back reify-ty produces — so the Pi typing bridge closes directly from
   `posIH`/`domIH` reify-ty.  COST: edit Typing.v `n_conv`; re-green the domain
   layer (Apply/Determinism/Preservation/Reflect/RenTyping consumers of `n_conv`);
   RE-CHECK soundness vs `Norm/Model.v`+`ModelOk.v` (do read-back-equal `dEl`
   types denote the same type? — should, read-back is semantics-preserving).
   Caveat: totality of `ReifyTy` is sidestepped by the universal form (vacuous if
   no read-back), but usefulness wants read-backs to exist where invoked.
   RECOMMENDED — directly dissolves the wall, paper-faithful in spirit.
2. **Separate eta-closed declarative type-conversion judgment** `conv_ty_eta` used
   by `n_conv`; keep `conv_nf` as the final structural decision; prove reify
   produces `conv_ty_eta`.  Closest to the paper's two-judgment shape; most new
   infrastructure (a whole new mutually-defined conversion + its metatheory).
3. **Investigate whether reducible-Pi codomain CODES are read-back-stable**
   (eta-long), so raw `conv_nf` = read-back `conv_nf` and raw R1 becomes provable
   with `n_conv` kept structural.  LIGHTEST if true; RISKY — likely FALSE (the
   off-diagonal eta counterexample applies to type codes too: a codomain code can
   carry an eta-short neutral arg at a function type).
4. **Defer the whole Pi reflect + R1 past the fundamental lemma** (like
   transitivity/transport); keep the current green file with R1/R3 as open
   residuals and build the fundamental lemma around the non-Pi content first.

Current file `LogRel2Reflect.v` is GREEN + axiom-free with R1 (`Hcod : conv_nf BA
BB`) and R3 (`RR_app2 = Happ`) as the two abstract residuals of `RR_pi_res`; R1 is
now KNOWN-unprovable as stated, so `RR_pi_res`/`RR_pi_step` can never be discharged
without resolving the fork above.

## UPDATE 2026-06-06h — cross-checked the paper's Coq (metamltt); R1 = port reifyReflect

Cloned the paper's dev (`git clone --branch fscd2026
https://gitlab.inria.fr/josselin.poiret/metamltt.git`; network OK via git, NOT
WebFetch).  The reify-reflect is `theories/LogicalRelation/ReifyReflect.v`,
`Theorem reifyReflect` (~line 161), `induction r using LR_rect`, THREE components:
  1. reify-ty: `Γ ⊢ A ⇓ B` (DnTy = declarative `≡` + whnf-norm + subterm-norm);
  2. reify-tm: `∀ a b, ⊩ a≡b:A≡B → Γ ⊢ a ⇓ b ⦂ A≡B` (DnTm; eta via `ConvTmEta`);
  3. **reflect: `∀ a b, a ~ne b ⦂ A → ⊩ a≡b : A≡B` — BARE-neutral membership.**
KEY: their reflect gives the BARE neutrals as members.  OUR RRCar reflect gives
ETA-LONG values (`∃ vn vm, Reflect n vn × Reflect m vm × P vn vm`) — an artifact
of the is_lam gate.  The gate is gone, so reflect should become bare-membership.
- Pi reify-ty: `reflectDom (tRel0 ~ne tRel0)` (= bare reflect of the bound var,
  `X`'s 3rd comp) builds `varred`; then `X0` (posIH) at `wk_ren`+`tRel0` gives
  the codomain reify-ty `CodNf`.  EXACTLY "reflect-to-bare bound var ⇒ posIH at
  it ⇒ R1".  posTy at the bare var = the codomain itself (no eta subst).
- Pi reflect: `apply LR_Pi_R; econstructor` builds the PiRedTm record for the
  bare neutrals; app clause via `X0` (codomain reflect) on `nApp`, domain norm
  via `X`.  SIMPLER than our `eta_bodies`/`t_lam_eta` (which can largely go).
- Pi reify-tm: `reifyCod` (codomain reify-tm IH) on `tApp .. f (tRel0)`
  (eta-expand via application) + bare bound var.  Our `reify_tm_pi` instead uses
  the eta-LONG reflect (`pi_bound_var_reflects`); re-basing on bare reflect would
  re-do it in the paper's style (cleaner, decoupled from the eta-long Reflect).

SO R1 = port `reifyReflect`: (i) RRCar reflect → bare membership; (ii) reify-ty →
read-back/DnTy style (raw `conv_nf_ty` is unsound on un-reified codes — neutral
ARGS need eta via `Reify`, cf. `rne_app`); (iii) re-derive reify-tm on the bare
bound var.  Substantial restructure of `RR_gen`+`RR_pi_case` (eta_bodies removed),
but fully TEMPLATED by ReifyReflect.v and likely net-simplifying.  Reference dev
at /tmp/metamltt (re-clone if gone).

## UPDATE 2026-06-06g — is_lam GATE REMOVED (paper-faithful); R1 precisely scoped

**GATE REMOVED (committed+pushed, whole LogRel2* chain + Glue green, RR_gen
`Closed under the global context`).**  Per Dustin's call + the *Divide and Check*
paper (Poiret–Maillard–Tabareau, hal-05495420, PDF at /root/divide-and-check.pdf,
code https://gitlab.inria.fr/josselin.poiret/metamltt/-/tree/fscd2026/theories):
the paper's **Def 10** (reducible conversion at function types) is **GATELESS** —
no `is_lam`, no neutral case — because the eta-law means the witness need not
distinguish neutral from lambda members.  Our `is_lam` gate (ec0f8f6) was the
deviation.  Removed it from `PiRedTmEq`; reversed all gate destructs/constructs
(`RedTmEq_wf{,_gen}`, `LogRel2Sym` fwd/bwd, `LogRel2Ren` `ren_pack_fwd`,
`RR_pi_case` REFLECT); re-proved `reify_tm_pi` gatelessly (members general,
`rfy_Pi` eta-expands either way).

**R1 IS BIGGER THAN THE "posIH at a bare-var member" SHORTCUT — precise scope.**
Reading the paper's Def 8 + `∼ne` (§3.1) pins it down:
- Paper deep-conversion `t A⇓B u := (Γ⊢t≡u:A) × (Γ⊢A≡B) × ⇓A t × ⇓B u`
  (DECLARATIVE `≡` with eta + deep normalization), and `∼ne`'s `NeApp` relates
  arguments by `a A⇓A' a'` (eta lives in `≡`/normalizing read-back); annotations
  only pairwise-convertible.  Our `conv_nf`/`conv_ne` is the *structural*
  comparison of ALREADY-REIFIED (eta-long) NFs — sound ONLY on reified terms.
- Hence reify-**ty** (RRCar's 3rd component, currently RAW `conv_nf_ty A B`) is
  WRONG on raw codomain codes for the SAME eta reason R2-raw was; it must become
  a **read-back** form (ReifyTy/ReifyNe, which eta-expand neutral args via
  `Reify`), parallel to what was done for reify-tm.
- The Π codomain read-back is structural at the BARE bound var (paper `PiTyNf`;
  our `rty_Pi` is already correct — do NOT change it).  Closing it needs a
  reify-ty IH at the BARE bound var ⇒ needs **reflect-to-bare** (Theorem 11's
  Reflect proper: `Γ ⊢ a ∼ne b : A → Γ ⊩ a ≡ b`, neutrals reducible AS
  THEMSELVES).  `RR_gen` currently only reflects neutrals to their ETA-LONG
  values (`refl_Pi`), NOT as bare members.

**PLAN for R1 (a coordinated RR_gen extension, ~the Reflect half of Thm 11):**
1. Add a 4th component to `RRCar`: reflect-to-bare
   `forall n m, NeConv Ge A n m -> P (vNe n) (vNe m)`.
2. Reformulate RRCar's reify-ty (3rd) component to read-back:
   `forall nA nB, <ReifyTy-readback A nA> -> <readback B nB> -> conv_nf_ty nA nB`.
3. Re-prove `RR_gen` all cases incl. the 4th component:
   - base/neutral (LRnat/empty/ne): bare neutral directly a member (RedNeutralEq).
   - universe (LRU0/1): codes.
   - Pi (`RR_pi_case`): reflect-to-bare via the GATELESS app clause + posIH's
     reflect-to-bare at the codomain on `nApp`; typing the right member at the
     right Pi uses the SAME node's reify-ty (R1, proven first via domIH's 4th
     component giving the bare DOMAIN var + posIH reify-ty at it).  Circularity
     breaks because domIH/posIH are proper IHs (smaller types).
4. R1 (`Hcod`) then = domIH 4th comp (bare domain var, `snoc_wkn_hd_list` ⇒
   posTy=BA/BB) + posIH read-back reify-ty.  Drop the `Hcod` Context.
5. Watch: the typing rule `n_conv`'s conversion side — confirm it composes with
   the read-back conv (it uses `conv_nf` on the type; the reflected-member typing
   bridge in `eta_bodies` already does this).
R3 (`RR_app2`) likely also yields once reflect-to-bare exists.

## UPDATE 2026-06-06f — R2 (reify-tm at Pi) DISCHARGED, axiom-free; R1 analysis

**R2 DONE (committed+pushed, `LogRel2Reflect.v` green + `Closed under the global
context`):** `reify_tm_pi` proves the read-back reify-tm at Pi via the validated
recipe (invert both `rfy_Pi`; align reflected bound vars with `Reflect_det`; pull
the codomain members reducibly-related through the `PiRedTmEq` app clause `Happm`
+ `Vapp_det`; close by `posIH` reify-tm after aligning `posTyA/posTyB = B'/B'0`
via `Apply_val_det`).  The `Hreify_tm` Context is GONE; `RR_pi_res` /
`RR_pi_at_from_res` now carry only **(R1) `conv_nf BA BB`** and **(R3) `RR_app2`**.
Imported `RenTyping` (for `has_svalty_ne_below`/`typing_ne_below`; no cycle).
Helper facts that worked: `up_shsub`+`Apply_val_shift_eq` give the
`up (wkn_list)`↦`shift_val 1 1` codomain witness; `ne_below_ctx Ge` follows from
`wf_senv Ge` via `wf_svalty_scoped`; `Hwf k HT` (T inferred, only 2 args).

**R1 IS THE ENTANGLED CODOMAIN REIFY-TY — analysis (NEEDS A DESIGN CALL):**
`Hcod : conv_nf BA BB` is the codomain code reify-ty (RRCar's third component is
`conv_nf_ty A B` = raw `conv_nf` of the codes; at Pi `cnf_pi` splits it into
`conv_nf FA FB` (= `dom_reify_ty`, FINE) and `conv_nf BA BB` (= R1)).
- R1 on RAW codes has the SAME eta falsity R2 had: codomain codes can be
  eta-short-vs-eta-long and `conv_nf` has no eta rule.  So reify-ty must ALSO
  become a read-back form (parallel to reify-tm).
- BUT even read-back, the Pi codomain read-back (`ReifyTy (S m) BA BA'` in
  `rty_Pi`) reads BA at the BARE bound var (var0 stays var0).  `posIH` only gives
  reify-ty about `posTyA = BA[ARG]` with `ARG` the ETA-LONG reflection of var0 —
  NOT the bare-var codomain.  So R1 needs a reify-ty IH at the BARE bound var,
  which the current `PolyRedPack` doesn't expose (bare var0 is not a `PiRedTmEq`
  member at higher domains: `is_lam` gate).
- `ReifyConv.ReifyTy_conv` does NOT help: it only PROPAGATES an existing
  `conv_nf c c2`; it cannot establish it.
- LIKELY FIX (type-level analog of option A): change `rty_Pi`/`rty_PiI` in
  `Reify.v` to REFLECT the bound var and read back the INSTANCE (`posTy`),
  mirroring `rfy_Pi` for terms — then `posIH` applies directly and R1 follows by
  the R2 recipe.  Cost: `Reify.v` (`rty_Pi`), `Reify_det`, `ReifyConv` re-proofs,
  + reformulate RRCar reify-ty to read-back + re-green all RR_gen cases.  ALT:
  defer R1 + the reify-ty component post-fundamental like transitivity.

**R3 (`RR_app2`, the reflect-side beta-reduct/RedSub closure) — still the hardest;
never closed even single-sided.  Untouched this session.**

## UPDATE 2026-06-06e — OPTION A (NbE read-back) CHOSEN; adequacy layer BUILT

Dustin chose option (A): a type-directed reify (read-back) FUNCTION/relation that
eta-expands at Pi, with reify-tm restated on read-backs.  Reason: R2 (`P a b ->
conv_nf a b` on raw members) is FALSE even with the `is_lam` gate — member bodies
can be eta-short bare neutrals at NESTED function codomains (machine-verified
counterexample; see [[ott-r2-hereditary-eta]]).

**DONE this session (3 new files, all green + axiom-free, committed+pushed):**
- `Reify.v` — `ReifyTy`/`Reify`/`ReifyNe` mutual read-back relations (dual of
  `Reflect`; eta-expands at relevant Pi via `rfy_Pi`, structural elsewhere) +
  `Reify_det` (determinism).
- `ApplyConv.v` — `Apply_conv`: `Apply` is a CONGRUENCE for conv under
  pointwise-conv substitutions (`conv_sub`, with length).  Proved by induction on
  the Apply DERIVATION (not the type) — dodges the dependent-codomain
  non-termination.  Keystone for read-back congruence.  Also `conv_sub_refl/
  cons/up/nth`, `conv_tyc`.
- `ReifyConv.v` — `Reflect_conv` + `Reify_conv` (ReifyTy/Reify/ReifyNe): Reflect
  and Reify map conv-related inputs (at conv-related types `conv_svty`, Empty_set
  on dU/dEl mismatch) to conv-related normal forms.  Eta cases use `Apply_conv` +
  `Reflect_conv`.  Projections `ReifyTy_conv`/`Reify_conv_val`/`ReifyNe_conv`,
  `Apply_conv_val`/`Apply_conv_Vapp`.

**RRCar REWIRE DONE (2026-06-06e, committed+pushed, green+axiom-free):**
`LogRel2Reflect.v` RRCar reify-tm is now the read-back form
`(forall a b na nb, P a b -> Reify A a na -> Reify B b nb -> conv_nf na nb)`;
`RR_gen` re-greened all cases (base via `Reify_conv_val`, universe via
`ReifyTy_conv`, line-762 consumer via `Reflect_conv`).  R2 residual (`Hreify_tm`/
`RR_pi_res` middle) rethreaded to the read-back form — now TRUE/provable.

**NEXT = discharge the 3 residuals `RR_pi_res` (now all provable), in
`LogRel2Reflect.v`'s `RRPiDev` section (all IHs `domIH`/`posIH` in scope):**
- (R2) read-back reify-tm at Pi — VALIDATED INTERACTIVELY, recipe (mirrors
  eta_bodies, REIFY direction):
  ```
  intros a b na nb Hab Hra Hrb.
  destruct Hab as [[[Hta Htb] [[ba Ea] [bb Eb]]] Happm]. subst a b.
  inversion Hra as [...rfy_Pi: ARGa B'a faa bodya HARa HAPa HVAa HBDa]; subst.
  inversion Hrb as [...rfy_Pi: ARGb B'b fbb bodyb HARb HAPb HVAb HBDb]; subst.
  apply cnf_lam.   (* goal: conv_nf bodya bodyb *)
  destruct (pi_bound_var_reflects PA ws0 afA0 afB0 HwfD (domIH ...))
    as [ARGn [ARGm [[Hargn Hargm] rab]]]. rewrite HL in Hargn,Hargm.
  pose proof (Reflect_det Hargn HARa); subst ARGn.   (* ARGn = ARGa *)
  pose proof (Reflect_det Hargm HARb); subst ARGm.   (* ARGm = ARGb *)
  (* rab : redTmEq (shpRed PA ws0 afA0 afB0) ARGa ARGb -- DONE up to here *)
  ```
  **CRUCIAL: do NOT use Apply_conv on the bodies** — the members `vLam ba`/
  `vLam bb` are NOT conv-related (eta-short vs eta-long), so `conv_nf faa fbb`
  via Apply_conv is FALSE.  Instead get `faa`/`fbb` REDUCIBLY related via the app
  clause `Happm` instantiated at `Delta=Dlt`, `sg=wkn`, args `ARGa`/`ARGb`, witnesses
  `FA':=shift FA` (afA0), `BA':=shift_1 BA`, `fsg:=shift(vLam ba)` (Apply_val_wkn,
  scopedness via `has_svalty_ne_below` Hta + `ne_below_ctx` from Hwf), `rab`; then
  `Vapp_det` aligns its `v`/`w` with `faa`/`fbb` (HVAa/HVAb); then `posIH ... rab Hwf`'s
  read-back reify-tm with HBDa/HBDb (after aligning `B'a = posTyA PA rab` via
  `Apply_val_det` on HAPa vs `posAppA`) gives `conv_nf bodya bodyb`.
  Then drop the `Hreify_tm` Context (prove R2 as a Lemma in RRPiDev after Hcod).
- (R1) `conv_nf BA BB`: already proved as `dom_reify_ty`/`Hcod` analog — actually
  R1 is the codomain `conv_nf BA BB`; revisit whether `posIH` reify-ty at the
  bound var gives it (was the entangled one).
- (R3) `RR_app2` (eta application clause / beta-reduct closure): the reflect-side;
  hardest (never closed even single-sided) — but now `Reify`/`Apply_conv`/
  `Reflect_conv` are available.
Then prove R2 INSIDE `RR_pi_case` and drop the `Hreify_tm` Context; close
`RR_pi_res`/`RR_pi_step`; instantiate the tower (`RR0`/`RR1`/`RR2`) + user
`reflect_red`/`reify_tm`/`reify_ty`.

OLD plan (superseded, kept for reference) — the integration into `LogRel2Reflect.v`:
1. Change `RRCar`'s reify-tm clause from `(forall a b, P a b -> conv_nf a b)` to
   the read-back form.  RECOMMENDED: UNIVERSAL form (no totality needed):
   `(forall a b na nb, P a b -> Reify (length Ge) A a na -> Reify (length Ge) B b nb -> conv_nf na nb)`.
   (Totality of Reify on reducible members can be a SEPARATE lemma for the final
   completeness theorem; the universal form keeps RR_gen totality-free.)
2. Re-green `RR_gen` all cases:
   - base/neutral cases: invert the two `Reify` (→ `vNe (ReifyNe ·)`), close via
     `ReifyNe_conv` from the members' `conv_ne` (RedNeutralEq).
   - universe code cases: via `ReifyTy_conv` / `Reify_conv_val`.
   - Pi case: invert both `Reify` (→ `rfy_Pi`, bodies = reify of the members
     applied to the reflected bound vars); the bodies are conv by the codomain
     reify IH (`posIH`) applied to the app-clause results (the eta_bodies
     machinery, now TRUE because reify eta-expands).  R1/R3 fold in here.
3. Internal consumer `eta_bodies` line ~762 (`conv_nf ARGn ARGm` for `cne_app`):
   now DIRECT via `Reflect_conv` (Reflect of nVar0 at conv-related domains) — no
   longer needs the reify-tm component.
4. Fix `RecRR1`/`RR0`/`RRbot`/tower + `RR_pi_res`/`RR_pi_at_from_res` to the new
   clause; drop the `Hreify_tm` Context; discharge R1/R2/R3; unblock RR1/RR2 tower
   + user `reflect_red`/`reify_tm`/`reify_ty`.
Dependency: `LogRel2Reflect.v` should import `Reify ReifyConv` (no cycle: ReifyConv
depends only on Apply/Reflect/Reify/ApplyConv/LogRel2Conv).
Then Ph5 fundamental lemma → gluing `Model.v`/`ModelOk.v` ⇒ `eq_term` decidability.

---


Paste this as the opening prompt (or just read it) to resume the OTT/Norm/Pi
migration to a two-sided PER-of-conversion logical relation (Divide and Check).

---

**Resume the OTT/Norm/Pi migration to the two-sided PER-of-conversion logical
relation.** Goal: decidable conversion for OTT. Branch `gluing-nbe`. Read
`WIP/ConvRelPlan.md` (design + live STATUS) and the `[[ott-convrel-pivot]]`
memory first.

## UPDATE 2026-06-06d — `is_lam` GATE LANDED (read [[ott-pi-reify-gate-blocker]])

Machine-verified that residual (R2) (Pi reify-tm) was FALSE under the UNgated
`PiRedTmEq` (it admitted eta-short bare-neutral members; `conv_nf (vLam _)(vNe _)`
has no rule).  Per Dustin's call, added the paper-faithful `is_lam` member gate
(`PiRedTmEq` members must be lambdas).  Whole `LogRel2*` chain + `Glue` re-greened,
axiom-free.  R1/R2/R3 are now TRUE/achievable but STILL need the VR/reify-adequacy
layer (the gate removed the falsity, not the work).  **NEXT = build the VR layer
(reducible substitutions + reify adequacy), discharge R1/R2/R3, then prove R2
inside `RR_pi_case` and drop the `Hreify_tm` Context.**  Details in ConvRelPlan
STATUS "GATE LANDED".

## State (all committed + pushed on `gluing-nbe`, all axiom-free)

- **Ph1 DONE** — `src/Pyrosome/Lang/OTT/Norm/Pi/LogRel2.v`: the two-sided PER core
  (`LRPack.redTmEq`, two-sided `PolyRedPack`/`PiRedTmEq`/`PolyRedPackAdequate`,
  two-sided `LR` graph + finite tower + `RedTyEq`/`RedTmEq`/`RedSubEq`). Kernel
  accepts `LR` (positivity holds). `NeConv` neutral base is PROVISIONAL (strict
  diagonal) — becomes the genuine `∼ne` in Ph3.
- **UNIVERSE REFACTOR DONE** — `LogRel2.v` now uses the universe-poly **3-level
  UNFOLDED tower** (lower relations as separate params `rec0`/`rec1`, `LRU` split
  into `LRU0`/`LRU1`, no value-level `match`; ladder `i0<i,i1<i,i<j,j0<=i,j1<=i`,
  NO `i0=i1`). Whole `LogRel2*` chain is `Set Universe Polymorphism` +
  `Unset Strict Universe Declaration`. Validated first in `WIP/UnivProto.v`.
- **Ph2 IRRELEVANCE DONE** — `LogRel2Irr.v` (axiom-free): `LR_irrelevant_gen`
  (bidirectional `IrrCar` over `LR_mut`, 7 cases incl. Pi + `LRU0`/`LRU1`),
  `LR2_irrelevant` + `RedTmEq_irr` (Def 7). REMAINING Ph2: transport + renaming
  stability.
- **Ph4 PER SYMMETRY DONE & axiom-free** — `src/.../LogRel2Sym.v` (NO LONGER
  blocked). `LR_sym_gen` builds the swapped `PolyRedPack` (`sym_pack`/`sym_adeq`
  — the `LRPack`-field storage the old encoding forbade) and discharges the Pi
  `bwd` via `LR_irrelevant_gen` + `Apply_val_det`; tower `LRbot/LR0/LR1_sym`
  (`RecSym1`); top-level `RedTyEq_sym` + `RedTmEq_sym`.
- **Ph0 NEUTRAL ANNOTATIONS DONE & green** — `(F,B)` on `nApp`/`nAppI`, whole
  domain layer + `LogRel2*` re-greened (commits `a24ad6d`, `3c68002`). Single-
  sided `LogRel*` chain retired to `WIP/OTT_LogRel_single_sided/` (commit
  `220ce2a`; out of the build, kept as reference for renaming/subst algebra).
- **TRANSITIVITY BLOCKED (finding)** — needs general Apply totality (≈
  normalization); see `ConvRelPlan.md` STATUS. Defer to post-fundamental (Ph5).

## State update (2026-06-05): RENAMING STABILITY COMPLETE

`LogRel2Ren.v` is fully built, axiom-free, green.  The renaming-stability
presheaf for the two-sided LR is DONE: top-level `RedTyEq_ren` / `RedTmEq_ren`
(`LR2 Ge A B P` ↦ `LR2 Ge' A[rho] B[rho]` + forward value map), via
`LR_ren_gen` (by `LR_mut`), the renamed Pi pack `ren_pack`/`ren_adeq`/
`ren_pack_fwd` (reuse `PA0` at the composite `comp_sub sg2 rho`), the
composite-sub algebra, and the REVERSE composition `Apply_ren_uncomp_sc`.
See `ConvRelPlan.md` STATUS for the full structure and the two key findings
(forward-only carrier; reverse-comp needs no Apply-totality, distinguishing
renaming from transitivity).

## State update (2026-06-05): Ph3 FOUNDATION DONE

`LogRel2Conv.v` is built, axiom-free, green: the genuine structural
neutral/normal-form conversion `conv_nf`/`conv_ne` (paper Def 13 `∼annot`)
replacing the provisional strict-diagonal `NeConv`.  Annotations related
recursively (not required equal); untyped+structural is complete here because
`Reflect` bakes eta into normal forms; independent of `LR` (positivity-safe).
Proven `conv_refl`/`conv_sym`/`conv_trans` + diagonal embeddings
`conv_ne_of_eq`/`conv_nf_of_eq` + scheme `conv_mutind`.

## State update (2026-06-05): Ph3 SWAP COMPLETE

The genuine `conv_ne` is now wired into `LR` across all 7 `LogRel2*` files,
axiom-free and green; the provisional strict-diagonal `NeConv` is GONE.  The
base neutral relation is now **TWO-TYPED** (`NeConv Ge T S n m` /
`RedNeutralEq Ge T S`) — forced by a typing-conversion wall (`has_svalty` has no
conversion rule, so `RedTmEq_wf`'s `LRne` case couldn't type the right member at
`dEl(vNe m)` from a left-typed relation).  Added `conv_ren` (renaming stability
of conv).  See `ConvRelPlan.md` STATUS "Ph3 SWAP — DONE" for the per-file
landing notes and the verified axiom-free list.

## State update (2026-06-05): Ph3 PROPER — BASE + UNIVERSE CASES DONE

`LogRel2Reflect.v` is built, axiom-free, green: the self-contained LEAVES of
mutual reify/reflect (Theorem 11), i.e. every case that does NOT recurse through
Pi members.
- REIFY: `reify_nat` / `reify_neutral` (base PER member ⟹ `conv_nf`).
- REFLECT (base El): `reflect_nat` / `reflect_empty` / `reflect_neEl`.
- REFLECT (universe): `reflect_U` (neutral CODES reducibly convertible at U; the
  substantive case — builds the NEW reducible type `dEl(vNe·)` via `LRne`,
  `lvl_of_cases` picks `LR0`/`LR1`) + companion `reflect_neEl_ty` (type-FORMATION
  `RedTyEq Ge (dEl(vNe n))(dEl(vNe m))`).

## DONE THIS SESSION (2026-06-06) — engine + eta design

`LogRel2Reflect.v` now carries the FULL `LR_mut`-driven combined reify/reflect
induction `RR_gen` (axiom-free, green), with motive `RRCar` =
  - REFLECT (TYPE-DIRECTED): `NeConv Ge A B n m ⟹ { vn vm & Reflect (length Ge) A
    n vn * Reflect (length Ge) B m vm * P vn vm }` — identity at base/code/U
    (`refl_Nat`/`refl_Empty`/`refl_neEl`/`refl_U`), eta-long at relevant Pi
    (`refl_Pi`);
  - REIFY-tm: `P a b ⟹ conv_nf a b`;
  - REIFY-ty: `conv_nf_ty A B` (the codes; `unit` at U).
All 5 NON-Pi cases discharged; both Pi cases abstracted as `RR_pi_at` /
`RR_piI_at` (universals `RR_pi_step`/`RR_piI_step`).  Tower kit `RRbot`/
`NeElBuild_LR`/`NeElBuild_vac` + `RR0 : RecRR1 LR0` (level-0 instance) green.

**ETA QUESTION RESOLVED (paper-faithful).**  The paper does NOT add eta to
conversion; `conv_nf`/`conv_ne` stay UNTYPED+structural (Def 13 `∼annot`).  Eta is
BAKED INTO NORMAL FORMS by `Reflect` (relevant-function values are always `vLam`,
never bare `vNe`) — hence the type-directed REFLECT motive above, and REIFY-tm at
`vPi` only ever hits `cnf_lam`.

**UNIVERSE FINDING.**  `RR1`/`RR2` + user `reflect_red`/`reify_tm`/`reify_ty`
CANNOT close from the ABSTRACT `Hpi` premise (a bound hypothesis is monomorphic
⇒ can't supply the poly tower's per-level `LR0`/`LR1` instances ⇒ rigid universe
clash; `RR0` dodges via `rec0 = LRbot`).  So discharging `RR_pi_at` as a genuine
axiom-free POLY LEMMA is BOTH the math crux AND the universe-unblocker for the
whole tower — no separate refactor.

## DONE THIS SESSION (2026-06-06b) — plumbing + CRUX BLOCKER verified

1. **PLUMBING DONE & green (committed+pushed).** `RRCar` now threads `wf_senv Ge`
   (the leading `wf_senv Ge ->`, mirroring single-sided `reflect_motive`); only
   the relevant-Pi case consumes it.  `RR_gen` re-greened (`intros Hwf` per case;
   the universe REIFY-tm feeds `Hwf` to the lower-tower delegate `HR0`/`HR1`).
   `RR_pi_at`/`RR_piI_at` stay abstract; file green + axiom-free.
2. **CRUX BLOCKER FOUND & VERIFIED — the `has_svalty` typing-conversion wall.**
   `RR_pi_at`'s REFLECT/REIFY both need to reflect the eta bound variable `nVar 0`
   into the DOMAIN pack at `dEl FA' ≡ dEl FB'` via `domIH`'s REFLECT, whose
   premise `NeConv Delta (dEl FA')(dEl FB')(nVar 0)(nVar 0)` requires `nVar 0`
   typed at BOTH `dEl FA'` AND `dEl FB'`.  `wf_neutral _ (nVar 0) T` is ONLY
   provable by `n_var`, which pins `nth_error Delta 0 = Some T` — so impossible
   unless `FA' = FB'` SYNTACTICALLY, while off-diagonal (`conv_nf`-related but
   unequal) is the whole point of two-sided.  No conversion rule on
   `has_svalty`/`wf_neutral` (verified via `Print`).  Single-sided dodged it (one
   domain).  PROVABLE leaf confirmed in dev: `conv_nf FA FB` (domain-codes reify)
   from `domIH` at the identity sub.  Full detail + the airtight argument in
   `ConvRelPlan.md` STATUS ("CRUX BLOCKER FOUND & VERIFIED").

## HOW THE PAPER ACTUALLY RESOLVES IT (read the FSCD2026 code)

Source: Poiret/Maillard/Tabareau `metamltt`, branch `fscd2026`
(`Neutrals.v`/`LogicalRelation.v`/`Declarative.v`/`FundamentalLemma.v`; PDF
hal-05495420).  Typed conversion IS required (their `Declarative.v` has
`WfTmConv : Γ⊢t⦂A → Γ⊢A≡B → Γ⊢t⦂B` + `ConvTmConv`), confirming the diagnosis —
but the SHAPE is NOT our two-typed-NeConv-plus-n_conv-with-conv_nf:
1. **Neutrals are SINGLE-TYPED.**  `ConvNe` = `Γ ⊢ n ~ne n' ⦂ R` (ONE result
   type) with declarative `≡`-premises baked in per rule.  Variable rule
   `ConvNeRel`: `in_ctx Γ n A` + `decl(Γ⊢R≡A)` (var ~ itself at ANY R convertible
   to its context type).  App rule `ConvNeAppCong`: annotations only
   `decl(Γ⊢Dom≡Dom')`/`decl(Γ,,Dom⊢Cod≡Cod')` + `decl(Γ⊢R≡Cod[a])` +
   `decl(Γ⊢R≡Cod'[a'])`.  The neutral TERM relation `RelAtNe Γ A t u` is
   single-typed too (both members reduce to neutrals at the SAME A = left whnf;
   `Rel_tot_Ne` uses the left rep `Ane`).  Two-sidedness is reserved for
   STRUCTURED types (`RelAtPi Γ Dom Cod Dom' Cod'`).  ⇒ our two-typed
   `NeConv Ge T S n m` (the `[[ott-logrel2-two-typed-neutral]]` workaround) is the
   ROOT DIVERGENCE that created the wall.
2. **Conversion = full DECLARATIVE `≡`** (`ConvTy`/`ConvTm`), not structural
   `conv_nf`.  Soundness automatic (it's the spec).
3. **The variable uses a VALID/reducible CONTEXT** `⊨ Γ` (a `TelRed` telescope of
   per-variable reducibility witnesses).  `varRed : Γ ⊨ tRel n ≡ tRel n ⦂ A`
   proves the var reducible at its SINGLE context type A, pulled from the context
   + `irrelevance`.  The var is NEVER typed/reflected at two types; under a binder
   the fresh var enters the domain relation as a related PAIR from the EXTENDED
   valid context — not by manufacturing a `(FA',FB')` NeConv on the spot.

PAPER-FAITHFUL FIX (an architectural pivot, bigger than `n_conv`): (i) move the
neutral conversion to SINGLE-typed (`~ne ⦂ R`) with `≡`-premises + a typing-
conversion rule (`WfTmConv`/`ConvTmConv` analogues on `has_svalty`); (ii) adopt a
valid-context telescope (`⊨ Γ`) so variables are reducible at their single type.
This dissolves BOTH the variable wall AND the escape wall that originally forced
two-typing (escape then lands typing at the single carried type, conversion
bridges).  Modules to mirror: their `LogicalRelation/ReifyReflect`, `Irrelevance`,
`Transport`, `Symmetry`, `Transitivity`, `Telescope` are SEPARATE — our monolithic
plan should likely split similarly.

## DONE (2026-06-06) — PAPER-FAITHFUL SINGLE-TYPED MIGRATION; WALL DISSOLVED

Dustin chose the paper's single-typed-neutral + typed-conversion architecture
(not the cheap patch).  Landed, axiom-free, whole `LogRel2*` chain + domain layer
+ `Glue` green:
- `n_conv` added to `wf_neutral` (Typing.v) = value-world `WfTmConv`; domain layer
  re-greened with conv-stability helpers `conv_shift`/`conv_ne_below`/`conv_ren`.
- `NeConv`/`RedNeutralEq` made SINGLE-typed (LEFT type; paper `RelAtNe`); `LRne`
  relation single-typed; escape (`RedTmEq_wf`) + symmetry (`LR_sym_gen`) bridge to
  the right type via `n_conv` + `conv_ne`.
- `RRCar` REFLECT premise single-typed at LEFT type.
- **`pi_bound_var_reflects`** (axiom-free) demonstrates the wall is GONE: the eta
  bound variable reflects from a SINGLE left typing, the domain IH returns both
  reflections + the domain member.

## DONE (2026-06-06c) — RR_pi_at REDUCED to 3 reify/reflect residuals (axiom-free)

`LogRel2Reflect.v` now PROVES the relevant-Pi crux `RR_pi_at` MODULO three
explicitly-isolated residuals (the two-sided port of single-sided
`reflect_pi_step_from_reify`).  All NEW content axiom-free + green:
- `RedTmEq_wf_gen` — level-generic escape (`@LR lvl rec0 rec1`, not just `LR2`).
- `conv_ctx` + `typing_ctx_conv` — CONTEXT CONVERSION metatheorem (typing stable
  under pointwise-`conv_nf` context entries).  Bridges the two-sided gap: the
  RIGHT eta-body is reflected in the LEFT-domain context but `t_lam_eta` for the
  RIGHT Pi needs the RIGHT-domain context (differ only at the convertible front
  domain).
- `eta_bodies` — the two-sided eta-expansion: from a `NeConv` pair at the LEFT Pi
  builds `vLam body_n`/`vLam body_m`, both `refl_Pi` reflects, both `t_lam_eta`
  typings, and the codomain member (via `pi_bound_var_reflects`,
  `Apply_reflect_cod`, `n_app`/`n_conv`, `typing_ctx_conv`).
- `dom_reify_ty` — domain reify-ty leaf (`conv_nf FA FB` from `domIH` at id sub).
- `RR_pi_case` + `RR_pi_res` + **`RR_pi_at_from_res`** — `RR_pi_at` follows from
  `RR_pi_res`, i.e. the three residuals:
    (R1) `conv_nf BA BB`  (codomain reify-ty for RAW codes),
    (R2) `forall a b, PiRedTmEq PA a b -> conv_nf a b`  (function reify-tm),
    (R3) `RR_app2`  (the eta-expansion application clause; two-sided analog of
         single-sided `reflect_pi_app_step`).

**NEXT = discharge the three `RR_pi_res` residuals (the genuine VR-layer core).**
(R1)+(R3) are entangled reify/reflect adequacy for the eta substitution (NOT a
renaming for higher-order domains; see `WIP/ReifyDev.v`), needing a
validity/reducible-substitution (VR) layer + reducibility-eta-irrelevance.  (R2)
needs casing on the members + the codomain reify IH.  Closing all three fully
discharges `RR_pi_at` and unblocks the `RR1`/`RR2` tower +
`reflect_red`/`reify_tm`/`reify_ty`.  Full detail in `WIP/ConvRelPlan.md` STATUS.

## Superseded fork — RE-PLAN around the single-typed-neutral pivot (RESOLVED above)

The earlier 3-option fork is SUPERSEDED: the paper neither keeps two-typed
neutrals nor uses structural conv_nf.  Decision for Dustin: adopt the paper's
single-typed-neutral + valid-context architecture (a real migration of `NeConv`/
the base relation + a new `⊨ Γ` telescope), vs a cheaper local patch.  Old
options retained below for reference (the paper points away from all three):
- **(a)** add `t_conv`/`n_conv` (typed conversion) to `has_svalty`/`wf_neutral`
  — standard OTT; lets `nVar 0 : dEl FA'` transport to `dEl FB'` via
  `conv_nf FA' FB'`; BIG domain-layer ripple (Apply/Determinism/Preservation/
  Reflect/RenTyping + `LogRel2*`) and soundness vs `Norm/Model.v`+`ModelOk.v`
  MUST be re-checked (is structural `conv_nf`-conversion of types model-valid?).
- **(b)** weaken `RRCar`'s REFLECT premise to one-sided typing + `conv_ne`,
  recovering the other side's typing from the relation — but escape
  `RedTmEq_wf`'s `LRne` case needs BOTH sides (the reason the neutral base went
  two-typed); would need a different escape route.
- **(c)** prove `RR_pi_at` only for the DIAGONAL (`FA=FB`,`BA=BB`) and reach
  off-diagonal via symmetry/transport — but transport+trans are deferred
  (normalization-strength) and `RR_gen`'s `LRpi` case is GENERAL, so a diagonal
  `RR_pi_at` does not plug into `RR_gen` as-is.

Once resolved: the eta construction itself ports from single-sided
`reflect_pi_step_from_app` (`wf_ssub_wkn`/`Apply_val_wkn`/`Apply_reflect_cod`/
`refl_Pi`/`t_lam_eta`), TWO-SIDED (build `vLam body_n`/`vLam body_m` via the
dom/cod IHs; `conv_ren`+`Reflect_ren` for transport; app-clause beta-reduct
closed by relating the two `posIH` reflections via the PER + `conv_ne`).  The
codomain reify `conv_nf BA BB` also waits on the resolution (it needs the
reflected-var domain member to instantiate `posIH`).  Helper signatures are all
confirmed in-scope from `ApplyLemmas`/`ApplySubst`/`RenSubst`/`RenTyping`/
`LogRel2Ren` (note: `wf_ssub_id` has `Ge` IMPLICIT — use `@wf_ssub_id Ge Hwf`).
Then the tower (`RR1`/`RR2`) + user `reflect_red`/`reify_tm`/`reify_ty` close.

Then the fundamental lemma (Ph5) → connect to gluing `Model.v`/`ModelOk.v` ⇒
`eq_term` decidability.  Transport (Lemma 12) + transitivity stay deferred (Ph5).
`vPiI`/`vLamI` reify deferred to Ph6.

## Build (per CLAUDE.md — never run full `make` during dev)
```
coqc -R coqutil/src/coqutil coqutil -R canonical-binary-tries/ Tries \
     -R src/Utils Utils -R src/Pyrosome Pyrosome \
     src/Pyrosome/Lang/OTT/Norm/Pi/<File>.v
```
(The Rocq MCP works on project files via `rocq_start(file=...)`; it does NOT pick
up loadpaths for a brand-new unbuilt file, so compile new files with `coqc`
first.) Always `git push` after each green commit.
