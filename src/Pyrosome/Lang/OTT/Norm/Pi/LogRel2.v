Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply Typing Preservation LogRel2Conv.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* UNIVERSE-POLYMORPHIC encoding (UNIVERSE_FIX_PLAN.md Step 1B), validated  *)
(* in WIP/UnivProto.v.  The relation universe [i] and the inductive's       *)
(* output universe [j] are made explicit; the lower-level relations are     *)
(* passed as SEPARATE PARAMETERS [rec0]/[rec1] (NOT a dispatching [rec]     *)
(* function — its value-level [match] collapsed the per-level universes),   *)
(* and [LRU] is SPLIT into [LRU0]/[LRU1].  This closes the PER-symmetry     *)
(* universe gap (storing a universe witness into a domain pack field).      *)
(* ===================================================================== *)
Set Universe Polymorphism.
(* Helper bodies ([is_ren], [sigT], [prod], ...) are now polymorphic too and
   introduce their own universes; relax strict declaration so the [@{i j}]
   binders need only name the universes we actually constrain (the kernel
   still checks full consistency). *)
Unset Strict Universe Declaration.

(* ===================================================================== *)
(* TWO-SIDED PER-of-conversion logical relation (Divide and Check, Poiret  *)
(* -Maillard-Tabareau 2026).  This is the additive Phase-1 rebuild of      *)
(* [LogRel.v]: every single-sided membership predicate [redTm : sval ->     *)
(* Type] becomes a two-sided relation [redTmEq : sval -> sval -> Type], the *)
(* PER of reducible CONVERSION at a pair of types [A ≡ B].  A type is        *)
(* reducible iff it is reducibly convertible to itself; reducible           *)
(* membership of [v] is the reflexive point [redTmEq v v].                  *)
(*                                                                         *)
(* The positivity discipline is IDENTICAL to [LogRel.v]: the inductive       *)
(* [LR] occurs only POSITIVELY (via [PolyRedPackAdequate] and [rec] in       *)
(* [LRU]); the negative argument occurrences (domain conversion of [a],[b]   *)
(* feeding the codomain) go through the [redTmEq] FIELD of an opaque         *)
(* [LRPack], not through [LR].  The application clause of [PiRedTmEq] stays   *)
(* gated by [is_ren] (renamings only), exactly as the single-sided           *)
(* [PiRedTmPred] -- arbitrary reducible substitutions would reintroduce      *)
(* [LR] negatively.                                                          *)
(*                                                                         *)
(* PHASE-1 SCOPE: define the relation and CONFIRM Rocq accepts the [LR]      *)
(* inductive (positivity = the riskiest design point).  The neutral-base     *)
(* conversion [NeConv] is PROVISIONAL (the strict diagonal); Phase-3 (after  *)
(* the Phase-0 neutral annotations) replaces it with the genuine [∼ne].      *)
(* ===================================================================== *)

(* A `pack` carries the term-CONVERSION relation as opaque DATA: [redTmEq a b]
   reads "a ≡ b at A ≡ B". *)
Record LRPack@{i} (Ge : senv) (A B : svalty) : Type :=
  { redTmEq : sval -> sval -> Type@{i} }.

(* The graph: `[P] is the correct reducible-conversion relation for the type
   pair [A],[B] at [Ge]`.  Relation arg at [i], output at [j]. *)
Definition RedRel@{i j} :=
  senv -> svalty -> svalty -> (sval -> sval -> Type@{i}) -> Type@{j}.

(* The finite universe tower, unchanged from [LogRel.v]. *)
Inductive TypeLevel : Set := tl0 | tl1 | tl2.
Inductive TLlt : TypeLevel -> TypeLevel -> Prop :=
| lt01 : TLlt tl0 tl1 | lt12 : TLlt tl1 tl2 | lt02 : TLlt tl0 tl2.

Definition lvl_of (l : term) : TypeLevel :=
  match l with
  | con n _ => if eqb n "L1" then tl1 else tl0
  | _ => tl0
  end.

(* ---------------------------------------------------------------------- *)
(* GENUINE neutral conversion (Phase 3): both neutrals well-typed -- at     *)
(* (possibly DISTINCT but convertible) types [T] (for [n]) and [S] (for     *)
(* [m]) -- and structurally convertible by [conv_ne] (LogRel2Conv.v, the    *)
(* paper's [∼annot], relating type annotations up to conversion).  The two  *)
(* type indices are forced by escape: [has_svalty] has no conversion rule,  *)
(* so the right member must be typed at the right type [S = dEl (vNe m)],    *)
(* not the left [dEl (vNe n)].  At base/code types [T = S] (diagonal).      *)
Definition NeConv (Ge : senv) (T S : svalty) (n m : neutral) : Type :=
  (wf_neutral Ge n T * wf_neutral Ge m S * conv_ne n m)%type.

(* Two-sided base relations.  [RedNatEq] is the PER of convertible naturals;
   [RedNeutralEq] the PER of convertible neutrals at a fixed type. *)
Inductive RedNatEq (Ge : senv) : sval -> sval -> Type :=
| rne_zero : RedNatEq Ge vZero vZero
| rne_suc  : forall v w, RedNatEq Ge v w -> RedNatEq Ge (vSuc v) (vSuc w)
| rne_ne   : forall n m, NeConv Ge (dEl vNat) (dEl vNat) n m -> RedNatEq Ge (vNe n) (vNe m).

Inductive RedNeutralEq (Ge : senv) (T S : svalty) : sval -> sval -> Type :=
| rneT : forall n m, NeConv Ge T S n m -> RedNeutralEq Ge T S (vNe n) (vNe m).

(* The renaming gate (purely syntactic, no [LR] reference), unchanged. *)
Definition is_ren (sg : ssub) : Type :=
  { rho : list nat & sg = map (fun k => vNe (nVar k)) rho }.

(* ---------------------------------------------------------------------- *)
(* Two-sided domain/codomain data for a pair of Pi codes [vPi FA BA] ≡      *)
(* [vPi FB BB].  [shpRed] produces the domain CONVERSION pack relating the  *)
(* substituted domains [FA'],[FB'].  [posRed] consumes a domain conversion  *)
(* [a ≡ b] and produces BOTH substituted codomains (one with [a], one with  *)
(* [b]) together with their [Apply_val] witnesses and the codomain          *)
(* conversion pack.  All over full well-typed substitutions [sg] (the       *)
(* renaming gate lives on the term clause [PiRedTmEq], as in [LogRel.v]).   *)
Record PolyRedPack@{i j} (Ge : senv) (FA BA FB BB : sval) : Type@{j} :=
  { shpRed : forall Delta sg FA' FB',
      wf_ssub Delta sg Ge ->
      Apply_val (length Delta) sg FA FA' ->
      Apply_val (length Delta) sg FB FB' ->
      LRPack@{i} Delta (dEl FA') (dEl FB')
  ; posRed : forall Delta sg a b FA' FB'
      (ws : wf_ssub Delta sg Ge)
      (afA : Apply_val (length Delta) sg FA FA')
      (afB : Apply_val (length Delta) sg FB FB'),
      redTmEq (shpRed ws afA afB) a b ->
      { BresA & { BresB &
        ( Apply_val (length Delta) (a :: sg) BA BresA
        * Apply_val (length Delta) (b :: sg) BB BresB
        * LRPack@{i} Delta (dEl BresA) (dEl BresB) )%type } } }.

(* Named accessors for the five components of [posRed]. *)
Definition posTyA Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB) Delta sg a b FA' FB'
   (ws : wf_ssub Delta sg Ge)
   (afA : Apply_val (length Delta) sg FA FA') (afB : Apply_val (length Delta) sg FB FB')
   (rab : redTmEq (shpRed PA ws afA afB) a b) : sval :=
  projT1 (@posRed Ge FA BA FB BB PA Delta sg a b FA' FB' ws afA afB rab).
Arguments posTyA {Ge FA BA FB BB} PA {Delta sg a b FA' FB' ws afA afB} rab.

Definition posTyB Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB) Delta sg a b FA' FB'
   (ws : wf_ssub Delta sg Ge)
   (afA : Apply_val (length Delta) sg FA FA') (afB : Apply_val (length Delta) sg FB FB')
   (rab : redTmEq (shpRed PA ws afA afB) a b) : sval :=
  projT1 (projT2 (@posRed Ge FA BA FB BB PA Delta sg a b FA' FB' ws afA afB rab)).
Arguments posTyB {Ge FA BA FB BB} PA {Delta sg a b FA' FB' ws afA afB} rab.

Definition posAppA Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB) Delta sg a b FA' FB'
   (ws : wf_ssub Delta sg Ge)
   (afA : Apply_val (length Delta) sg FA FA') (afB : Apply_val (length Delta) sg FB FB')
   (rab : redTmEq (shpRed PA ws afA afB) a b)
  : Apply_val (length Delta) (a :: sg) BA (posTyA PA rab) :=
  fst (fst (projT2 (projT2 (@posRed Ge FA BA FB BB PA Delta sg a b FA' FB' ws afA afB rab)))).
Arguments posAppA {Ge FA BA FB BB} PA {Delta sg a b FA' FB' ws afA afB} rab.

Definition posAppB Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB) Delta sg a b FA' FB'
   (ws : wf_ssub Delta sg Ge)
   (afA : Apply_val (length Delta) sg FA FA') (afB : Apply_val (length Delta) sg FB FB')
   (rab : redTmEq (shpRed PA ws afA afB) a b)
  : Apply_val (length Delta) (b :: sg) BB (posTyB PA rab) :=
  snd (fst (projT2 (projT2 (@posRed Ge FA BA FB BB PA Delta sg a b FA' FB' ws afA afB rab)))).
Arguments posAppB {Ge FA BA FB BB} PA {Delta sg a b FA' FB' ws afA afB} rab.

Definition posPack Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB) Delta sg a b FA' FB'
   (ws : wf_ssub Delta sg Ge)
   (afA : Apply_val (length Delta) sg FA FA') (afB : Apply_val (length Delta) sg FB FB')
   (rab : redTmEq (shpRed PA ws afA afB) a b)
  : LRPack Delta (dEl (posTyA PA rab)) (dEl (posTyB PA rab)) :=
  snd (projT2 (projT2 (@posRed Ge FA BA FB BB PA Delta sg a b FA' FB' ws afA afB rab))).
Arguments posPack {Ge FA BA FB BB} PA {Delta sg a b FA' FB' ws afA afB} rab.

(* The reducible-conversion relation at a Pi type pair, computed FROM the pack
   data (a Definition, not the inductive).  [f ≡ g] iff both are typed and,
   under every renaming [sg] and every domain conversion [a ≡ b], the
   applications [f a] and [g b] are reducibly convertible at the codomain.
   No neutral case: at negative types eta is baked in, which dissolves the
   bare-neutral-vs-eta-long mismatch of the single-sided development. *)
Definition PiRedTmEq (Ge : senv) (FA BA FB BB : sval) (PA : PolyRedPack Ge FA BA FB BB)
  : sval -> sval -> Type :=
  fun f g =>
    (has_svalty Ge f (dEl (vPi FA BA)) * has_svalty Ge g (dEl (vPi FB BB)) *
     (forall Delta sg a b FA' FB' BA' BB' fsg gsg
        (ws : wf_ssub Delta sg Ge) (rn : is_ren sg)
        (afA : Apply_val (length Delta) sg FA FA')
        (afB : Apply_val (length Delta) sg FB FB')
        (afBA : Apply_val (S (length Delta)) (up sg) BA BA')
        (afBB : Apply_val (S (length Delta)) (up sg) BB BB')
        (afsf : Apply_val (length Delta) sg f fsg)
        (afsg : Apply_val (length Delta) sg g gsg)
        (rab : redTmEq (shpRed PA ws afA afB) a b),
        { v & { w &
          ( Vapp (length Delta) FA' BA' fsg a v
          * Vapp (length Delta) FB' BB' gsg b w
          * redTmEq (posPack PA rab) v w )%type } }))%type.

(* Adequacy: the packs stored in [PA] are themselves in the graph [R]. *)
Record PolyRedPackAdequate@{i j} (R : RedRel@{i j}) (Ge : senv) (FA BA FB BB : sval)
       (PA : PolyRedPack@{i j} Ge FA BA FB BB) : Type@{j} :=
  { shpAd : forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
              (afA : Apply_val (length Delta) sg FA FA')
              (afB : Apply_val (length Delta) sg FB FB'),
      R Delta (dEl FA') (dEl FB') (redTmEq (shpRed PA ws afA afB))
  ; posAd : forall Delta sg a b FA' FB'
              (ws : wf_ssub Delta sg Ge)
              (afA : Apply_val (length Delta) sg FA FA')
              (afB : Apply_val (length Delta) sg FB FB')
              (rab : redTmEq (shpRed PA ws afA afB) a b),
      R Delta (dEl (posTyA PA rab)) (dEl (posTyB PA rab))
        (redTmEq (posPack PA rab)) }.
Arguments shpAd {R Ge FA BA FB BB PA} adq {Delta sg FA' FB'} ws afA afB : rename.
Arguments posAd {R Ge FA BA FB BB PA} adq {Delta sg a b FA' FB'} ws afA afB rab : rename.

(* The two-sided graph inductive.  [LR] occurs only positively.  The two
   lower-level relations are passed as SEPARATE PARAMETERS [rec0] (level 0)
   and [rec1] (level 1) at DISTINCT universes; [LRU] is SPLIT into [LRU0]
   (source level [tl0], uses [rec0]) and [LRU1] (source level [tl1], uses
   [rec1]).  No value-level [match] -> the kernel records NO constraint
   forcing the per-level relation universes equal (UNIVERSE_FIX_PLAN Step 1B). *)
Inductive LR
    (lvl : TypeLevel)
    (rec0 : RedRel@{i0 j0})
    (rec1 : RedRel@{i1 j1}) : RedRel@{i j} :=
| LRnat   : forall Ge, @LR lvl rec0 rec1 Ge (dEl vNat) (dEl vNat) (RedNatEq Ge)
| LRempty : forall Ge,
    @LR lvl rec0 rec1 Ge (dEl vEmpty) (dEl vEmpty) (RedNeutralEq Ge (dEl vEmpty) (dEl vEmpty))
| LRne    : forall Ge n m r l, NeConv Ge (dU r l) (dU r l) n m ->
    @LR lvl rec0 rec1 Ge (dEl (vNe n)) (dEl (vNe m)) (RedNeutralEq Ge (dEl (vNe n)) (dEl (vNe m)))
| LRpiI   : forall Ge FA BA FB BB,
    wf_svalty Ge (dEl (vPiI FA BA)) -> wf_svalty Ge (dEl (vPiI FB BB)) ->
    @LR lvl rec0 rec1 Ge (dEl (vPiI FA BA)) (dEl (vPiI FB BB))
       (fun f g => (has_svalty Ge f (dEl (vPiI FA BA))
                  * has_svalty Ge g (dEl (vPiI FB BB)))%type)
| LRpi    : forall Ge FA BA FB BB (PA : PolyRedPack@{i j} Ge FA BA FB BB),
    wf_svalty Ge (dEl (vPi FA BA)) -> wf_svalty Ge (dEl (vPi FB BB)) ->
    PolyRedPackAdequate (@LR lvl rec0 rec1) PA ->
    @LR lvl rec0 rec1 Ge (dEl (vPi FA BA)) (dEl (vPi FB BB)) (PiRedTmEq PA)
| LRU0    : forall Ge r l (h : TLlt tl0 lvl) (e : lvl_of l = tl0),
    @LR lvl rec0 rec1 Ge (dU r l) (dU r l)
       (fun c d => (has_svalty Ge c (dU r l) * has_svalty Ge d (dU r l) *
                 { P : sval -> sval -> Type@{i0} & rec0 Ge (dEl c) (dEl d) P })%type)
| LRU1    : forall Ge r l (h : TLlt tl1 lvl) (e : lvl_of l = tl1),
    @LR lvl rec0 rec1 Ge (dU r l) (dU r l)
       (fun c d => (has_svalty Ge c (dU r l) * has_svalty Ge d (dU r l) *
                 { P : sval -> sval -> Type@{i1} & rec1 Ge (dEl c) (dEl d) P })%type).

(* ===================================================================== *)
(* Finite-tower kit (unchanged shape from [LogRel.v]).                     *)
(* ===================================================================== *)

(* Unused [recK] slots get the constructorless dummy [LRbot]; its [TLlt tlK
   lvl] guard is false at that level so the [LRU]-witness is never built.  The
   tower instances stay UNIVERSE-POLYMORPHIC (each occurrence picks its own
   instance of the non-collapsing inductive [LR]); the downstream symmetry
   proof keeps the whole [LogRel2*] chain polymorphic so the instances align
   (see [LogRel2Sym.v]). *)
Definition LRbot : RedRel := fun _ _ _ _ => False.

Definition LR0 : RedRel := @LR tl0 LRbot LRbot.   (* LRU0/LRU1 gated off *)
Definition LR1 : RedRel := @LR tl1 LR0   LRbot.   (* LRU0 -> LR0; LRU1 off *)
Definition LR2 : RedRel := @LR tl2 LR0   LR1.     (* LRU0 -> LR0; LRU1 -> LR1 *)

(* Top-level two-sided reducibility. *)
Definition RedTyEq (Ge : senv) (A B : svalty) : Type :=
  { P : sval -> sval -> Type & LR2 Ge A B P }.
Definition RedTmOfEq {Ge A B} (RT : RedTyEq Ge A B) (a b : sval) : Type :=
  projT1 RT a b.
Definition RedTmEq (Ge : senv) (A B : svalty) (a b : sval) : Type :=
  { P : sval -> sval -> Type & (LR2 Ge A B P * P a b)%type }.

(* Reducible-conversion substitutions [sgA ≡ sgB : Ge <- Delta]: pointwise
   reducible conversion of the two substitutions' entries, at the substituted
   type pair.  (Two-sided refinement of [LogRel.v]'s [RedSub].) *)
Definition RedSubEq (Delta : senv) (sgA sgB : ssub) (Ge : senv) : Type :=
  (length sgA = length Ge) * (length sgB = length Ge) *
  (forall k T, nth_error Ge k = Some T ->
     { TA' & { TB' &
       ((Apply_ty (length Delta) sgA T TA' * Apply_ty (length Delta) sgB T TB')
        * RedTyEq Delta TA' TB'
        * RedTmEq Delta TA' TB'
            (nth_default (vNe (nVar 0)) sgA k)
            (nth_default (vNe (nVar 0)) sgB k))%type } }).
