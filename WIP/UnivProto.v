(* ===================================================================== *)
(* WIP/UnivProto.v  --  Step 2 prototype for UNIVERSE_FIX_PLAN.md Step 1B. *)
(*                                                                         *)
(* GOAL: validate the 3-level UNFOLDED encoding of the two-sided LR tower   *)
(* BEFORE touching the green LogRel2.v chain.  We replicate ONLY the        *)
(* universe-relevant skeleton of LogRel2.v:                                 *)
(*   - [RedRel], [LRPack] (relation field at a unified universe [i]),       *)
(*   - a toy [PolyRedPack] (domain pack + one codomain pack) + adequacy,    *)
(*   - [LR] with [LRnat], [LRpi], and the universe cases SPLIT into         *)
(*     [LRU0]/[LRU1] over SEPARATE lower-relation PARAMETERS [rec0]/[rec1]  *)
(*     (no value-level [match] -> no branch-universe collapse),             *)
(*   - the [LR0]/[LR1]/[LR2] tower via concrete instantiations (no match).  *)
(*                                                                         *)
(* DECISIVE TESTS (the things that FAIL in the current monomorphic encoding):*)
(*   (T1) the whole tower [LR0]/[LR1]/[LR2] typechecks (the match-collapse   *)
(*        version cannot -- see UNIVERSE_FIX_PLAN.md Section 3);             *)
(*   (T2) positivity holds (kernel accepts [LR]);                           *)
(*   (T3) the symmetry-shaped obligation typechecks: store an [LRU0]         *)
(*        universe witness into a *domain* [LRPack] field at the TOP         *)
(*        relation universe -- i.e. an [LR2] derivation of a Pi whose        *)
(*        domain IS a universe.  This is exactly what fails today.          *)
(* ===================================================================== *)

Set Universe Polymorphism.       (* REQUIRED: monomorphic re-uses one univ set
                                    across LR0/LR1/LR2 -> same collapse. *)
Set Printing Universes.

(* ----- toy "domain" of values/types: Set-level, universe-neutral ----- *)
Inductive D : Set :=
| dN                       (* the "Nat" code *)
| dPi   (f b : D)          (* Pi code with domain code f, codomain code b *)
| dU    (n : nat)          (* universe U_n *)
| dEl   (c : D).           (* El of a code *)

(* ----- the finite level tower (unchanged shape from LogRel2.v) ----- *)
Inductive TypeLevel : Set := tl0 | tl1 | tl2.
Inductive TLlt : TypeLevel -> TypeLevel -> Prop :=
| lt01 : TLlt tl0 tl1 | lt12 : TLlt tl1 tl2 | lt02 : TLlt tl0 tl2.

Definition lvl_of (n : nat) : TypeLevel :=
  match n with 0 => tl0 | 1 => tl1 | _ => tl0 end.

(* ----- the conversion pack: relation field at universe [i] ----- *)
Record LRPack@{i} (A B : D) : Type :=
  { redTmEq : D -> D -> Type@{i} }.
Arguments redTmEq {A B}.

(* ----- the graph type: relation arg at [i], output at [j] ----- *)
Definition RedRel@{i j} :=
  D -> D -> (D -> D -> Type@{i}) -> Type@{j}.

(* a trivial base relation for the [LRnat] case (universe-neutral) *)
Definition TrivRel : D -> D -> Type := fun _ _ => unit.

(* ----- toy two-sided poly pack: domain pack + one codomain pack ----- *)
(* We drop the Kripke quantifiers of the real PolyRedPack -- they are      *)
(* universe-irrelevant (all over small index types).  What MATTERS for the *)
(* universe analysis is preserved: [shpRed] STORES an [LRPack@{i}] (so the  *)
(* pack-field universe is [i]); [posRed] consumes an opaque [redTmEq] and   *)
(* produces another [LRPack@{i}] (LR never occurs negatively).             *)
Record PolyRedPack@{i j} (FA BA FB BB : D) : Type@{j} :=
  { shpRed : LRPack@{i} (dEl FA) (dEl FB)
  ; posRed : forall a b, redTmEq (shpRed) a b ->
      { BresA : D & { BresB : D & LRPack@{i} (dEl BresA) (dEl BresB) } } }.
Arguments shpRed {FA BA FB BB} _.
Arguments posRed {FA BA FB BB} _ _ _ _.

(* codomain pack accessor (mirrors posPack) *)
Definition posPack@{i j} FA BA FB BB (PA : PolyRedPack@{i j} FA BA FB BB)
    a b (r : redTmEq (shpRed PA) a b)
  : LRPack@{i} (dEl (projT1 (posRed PA a b r)))
               (dEl (projT1 (projT2 (posRed PA a b r)))) :=
  projT2 (projT2 (posRed PA a b r)).
Arguments posPack {FA BA FB BB} PA a b r.

(* the Pi term-conversion relation, computed FROM the pack (a Definition). *)
Definition PiRedTmEq@{i j} (FA BA FB BB : D) (PA : PolyRedPack@{i j} FA BA FB BB)
  : D -> D -> Type@{i} :=
  fun f g =>
    forall a b (r : redTmEq (shpRed PA) a b),
      redTmEq (posPack PA a b r) f g.
Arguments PiRedTmEq {FA BA FB BB} PA.

(* adequacy: the stored packs are themselves in the graph [R] (positive). *)
Record PolyRedPackAdequate@{i j} (R : RedRel@{i j})
       (FA BA FB BB : D) (PA : PolyRedPack@{i j} FA BA FB BB) : Type@{j} :=
  { shpAd : R (dEl FA) (dEl FB) (redTmEq (shpRed PA))
  ; posAd : forall a b (r : redTmEq (shpRed PA) a b),
      R (dEl (projT1 (posRed PA a b r)))
        (dEl (projT1 (projT2 (posRed PA a b r))))
        (redTmEq (posPack PA a b r)) }.
Arguments PolyRedPackAdequate R {FA BA FB BB} PA.

(* ===================================================================== *)
(* THE UNFOLDED inductive: lower relations are SEPARATE PARAMETERS at      *)
(* DISTINCT universes; [LRU] is SPLIT per source level.  No [match] on the *)
(* level value -> the kernel records NO constraint forcing [i0 = i1].      *)
(* ===================================================================== *)
Inductive LR@{i0 j0 i1 j1 i j}
    (lvl  : TypeLevel)
    (rec0 : RedRel@{i0 j0})
    (rec1 : RedRel@{i1 j1}) : RedRel@{i j} :=
| LRnat : LR lvl rec0 rec1 (dEl dN) (dEl dN) (fun (_ _ : D) => unit)
| LRpi  : forall FA BA FB BB (PA : PolyRedPack@{i j} FA BA FB BB),
    PolyRedPackAdequate (LR lvl rec0 rec1) PA ->
    LR lvl rec0 rec1 (dEl (dPi FA BA)) (dEl (dPi FB BB)) (PiRedTmEq PA)
| LRU0  : forall n, TLlt tl0 lvl -> lvl_of n = tl0 ->
    LR lvl rec0 rec1 (dEl (dU n)) (dEl (dU n))
       (fun c d => { P : D -> D -> Type@{i0} & rec0 (dEl c) (dEl d) P })
| LRU1  : forall n, TLlt tl1 lvl -> lvl_of n = tl1 ->
    LR lvl rec0 rec1 (dEl (dU n)) (dEl (dU n))
       (fun c d => { P : D -> D -> Type@{i1} & rec1 (dEl c) (dEl d) P }).

(* ===================================================================== *)
(* THE TOWER via concrete instantiations (no match, no dispatch fn).       *)
(* Unused [recK] slots get a constructorless dummy [LRbot]; its [TLlt tlK   *)
(* lvl] guard is false at the bottom so its witness is never built.        *)
(* ===================================================================== *)
Definition LRbot@{i j} : RedRel@{i j} := fun _ _ _ => False.

Definition LR0 : RedRel := LR tl0 LRbot LRbot.   (* LRU0/LRU1 gated off *)
Definition LR1 : RedRel := LR tl1 LR0   LRbot.   (* LRU0 -> LR0; LRU1 off *)
Definition LR2 : RedRel := LR tl2 LR0   LR1.     (* LRU0 -> LR0; LRU1 -> LR1 *)

Definition RedTyEq (A B : D) : Type := { P : D -> D -> Type & LR2 A B P }.

(* ===================================================================== *)
(* (T3) THE DECISIVE SYMMETRY-SHAPED TEST.                                 *)
(* Build an [LR2] derivation of a Pi whose DOMAIN is the universe [U0].     *)
(* Its [shpRed] is a domain [LRPack] whose [redTmEq] field STORES the       *)
(* universe-reducibility relation (the [LRU0] witness, living at [j0]).     *)
(* The adequacy [shpAd] is discharged by [LRU0] itself.  If this Defines,   *)
(* the pack-field universe [i2] admits the witness universe [j0] (gap       *)
(* closed: j0 <= i2), which is precisely what the match-collapse forbids.   *)
(* ===================================================================== *)

(* the universe-reducibility relation at source level 0, exactly as [LRU0]
   exposes it for [rec0 := LR0]. *)
Definition Uwitness0 : D -> D -> Type :=
  fun c d => { P : D -> D -> Type & LR0 (dEl c) (dEl d) P }.

(* a domain pack for [U0 = dU 0] whose conversion relation IS [Uwitness0].
   Storing [Uwitness0] (at the witness universe) into an [LRPack] field (at
   the top relation universe) is the storage that fails today. *)
Definition dom_pack_U0 : LRPack (dEl (dU 0)) (dEl (dU 0)) :=
  {| redTmEq := Uwitness0 |}.

(* a trivial codomain pack (Nat) -- only its existence/universe matters. *)
Definition cod_pack_N : LRPack (dEl dN) (dEl dN) :=
  {| redTmEq := TrivRel |}.

(* the swapped/derived poly pack: domain = U0, codomain = Nat. *)
Definition PA_uni : PolyRedPack (dU 0) dN (dU 0) dN :=
  {| shpRed := dom_pack_U0
   ; posRed := fun a b _ => existT _ dN (existT _ dN cod_pack_N) |}.

(* adequacy: [shpAd] needs [LR2 (dEl (dU 0)) (dEl (dU 0)) Uwitness0], which
   is EXACTLY [LRU0] at [lvl = tl2], [rec0 = LR0], [n = 0]. *)
Definition adq_uni : PolyRedPackAdequate LR2 PA_uni.
Proof.
  unshelve econstructor.
  - (* shpAd : LR2 (dEl (dU 0)) (dEl (dU 0)) (redTmEq dom_pack_U0) *)
    (* redTmEq dom_pack_U0 = Uwitness0 definitionally *)
    exact (LRU0 tl2 LR0 LR1 0 lt02 eq_refl).
  - (* posAd : trivial Nat codomain pack *)
    intros a b r. exact (LRnat tl2 LR0 LR1).
Defined.

(* THE PAYOFF: an [LR2] derivation of [Pi (U0) Nat ~ Pi (U0) Nat] whose
   domain-pack field stores a universe witness.  Typechecks iff the gap is
   closed. *)
Definition test_swap
  : LR2 (dEl (dPi (dU 0) dN)) (dEl (dPi (dU 0) dN)) (PiRedTmEq PA_uni)
  := LRpi tl2 LR0 LR1 (dU 0) dN (dU 0) dN PA_uni adq_uni.

(* (T2) positivity sanity: ask for the inductive's eliminator + its recorded
   universe constraints.  The dump shows  i0<i, i1<i, i<j, j0<=i, j1<=i  with
   NO  i0=i1  constraint -- the match-collapse of the monomorphic encoding is
   gone (cf. UNIVERSE_FIX_PLAN.md Section 3). *)
Check @LR_ind.

(* (T3) the symmetry-shaped storage typechecks: a universe witness (at the
   lower level's output universe j0) stored into a domain pack field (at the
   top relation universe i) -- gap closed. *)
Check @test_swap.

(* (T1) the full tower's universe instances + ladder. *)
About LR2.

(* ===================================================================== *)
(* RESULT (2026-06-05).  coqc exit 0.  Step 1B VALIDATED:                  *)
(*   (T1) the LR0/LR1/LR2 tower typechecks -- [About LR2] shows 18 univs    *)
(*        with the strictly-increasing ladder per level:                   *)
(*          i0(u1) < j0(u2) <= i2(u),  i1(u3) < j1(u4) <= i2(u),  i2 < j2,  *)
(*        and NO constraint equating the per-level relation universes.      *)
(*   (T2) [LR_ind] exists (kernel accepts LR); its constraints are          *)
(*          i0<i, i1<i, i<j, j0<=i, j1<=i   -- crucially NO  i0=i1.         *)
(*   (T3) [test_swap] : an LR2 derivation of a Pi whose DOMAIN El is a      *)
(*        universe, whose shpRed domain pack stores the LRU0 witness        *)
(*        (relation at the lower output universe j0) into an LRPack field    *)
(*        at the top relation universe i2.  j0 <= i2 holds => the storage    *)
(*        the monomorphic match-collapse FORBIDS now typechecks.            *)
(* Conclusion: the unfolded (rec0/rec1 params + split LRU0/LRU1) encoding    *)
(* under Set Universe Polymorphism closes the symmetry universe gap.        *)
(* Port to src/.../LogRel2.v per UNIVERSE_FIX_PLAN.md Step 3.               *)
(* ===================================================================== *)
