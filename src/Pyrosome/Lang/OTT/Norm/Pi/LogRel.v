Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply Typing Preservation.
Import Core.Notations.

(* ===================================================================== *)
(* Logical relation (reducibility) over the Pi semantic value domain,      *)
(* for the regime-2 totality argument (Fundamental Lemma ⇒ totality of      *)
(* [Apply_*]/[Vapp]/[Reflect] ⇒ unblocks [subst_has_svalty]'s [n_app]).     *)
(*                                                                         *)
(* The relation is induction-RECURSIVE in spirit (the Pi clause mentions    *)
(* term-reducibility of the argument, a negative occurrence), which Rocq    *)
(* cannot express natively.  We use the CoqHott/logrel-coq encoding:        *)
(*                                                                         *)
(*   - an [LRPack] bundles the term-reducibility relation as opaque DATA    *)
(*     (a [sval -> Type] field), with NO reference to the inductive;        *)
(*   - [RedRel] is the GRAPH `this candidate relation is the correct one    *)
(*     for this type`; the relation is an INDEX, not stored negatively;     *)
(*   - the Pi constructor [LRpi] stores a [PolyRedPack] (data: domain pack  *)
(*     + codomain producer) PLUS a separate [PolyRedPackAdequate] proof     *)
(*     that those packs lie in the graph [LR rec] (here [LR] occurs only    *)
(*     POSITIVELY).  The codomain producer's `argument reducible`           *)
(*     hypothesis is the domain pack's [redTm] FIELD applied — positive.    *)
(*                                                                         *)
(* Per the design, the Pi clause quantifies over FULL explicit              *)
(* substitutions [sg : Delta <- Ge] (via the proven [wf_ssub]), uniformly   *)
(* subsuming application ([sg = id_list]) and reflection ([sg = wkn_list]). *)
(* Universe stratification uses a lower-level recursor [rec] over the       *)
(* finite tower [TypeLevel] (mirrors logrel-mltt's [ι0 < ι1 < ∞]).          *)
(*                                                                         *)
(* STATUS: the DEFINITIONS below are accepted by Rocq (positivity OK for    *)
(* both [LRpi]'s pack/adequacy and [LRU]'s use of [rec]).  Remaining for    *)
(* the milestone: the finite-tower kit instantiation of [rec], the          *)
(* top-level [RedTy]/[RedTm]/[RedTmEq] projections, and the closure lemmas  *)
(* (escape, [RedTy_subst], [reflect_red], [Apply_total_red]) in             *)
(* [Pi/LogRelLemmas.v].                                                     *)
(* ===================================================================== *)

(* A `pack` carries the term-reducibility relation as opaque DATA. *)
Record LRPack (Ge : senv) (T : svalty) : Type :=
  { redTm : sval -> Type }.

(* The graph: `[P] is the correct reducibility predicate for [T] at [Ge]`. *)
Definition RedRel : Type := senv -> svalty -> (sval -> Type) -> Type.

(* The finite universe tower (mirrors logrel-mltt's TypeLevel ι0<ι1<inf):
   tlvl levels [iota L0] (0), [iota L1] (1), [inf] (2), with [next l] one above
   [iota l].  The universe [dU r l] lives at level [next l] and its codes' El
   types are reducible at the strictly smaller level [iota l]. *)
Inductive TypeLevel : Set := tl0 | tl1 | tl2.
Inductive TLlt : TypeLevel -> TypeLevel -> Prop :=
| lt01 : TLlt tl0 tl1 | lt12 : TLlt tl1 tl2 | lt02 : TLlt tl0 tl2.

(* Reducible naturals / reducible neutrals (base cases, no levels, no IR). *)
Inductive RedNat (Ge : senv) : sval -> Type :=
| rn_zero : RedNat Ge vZero
| rn_suc  : forall v, RedNat Ge v -> RedNat Ge (vSuc v)
| rn_ne   : forall n, wf_neutral Ge n (dEl vNat) -> RedNat Ge (vNe n).

Inductive RedNeutral (Ge : senv) (T : svalty) : sval -> Type :=
| rne : forall n, wf_neutral Ge n T -> RedNeutral Ge T (vNe n).

(* Domain/codomain data for a Pi type, quantified over full (well-typed)
   explicit substitutions [sg : Delta <- Ge] (subsuming weakening via wkn_list).
   The codomain producer's argument hypothesis [redTm (shpRed ws af) a] is the
   domain pack's FIELD applied — positive, not the inductive. *)
Record PolyRedPack (Ge : senv) (F B : sval) : Type :=
  { shpRed : forall Delta sg F',
      wf_ssub Delta sg Ge -> Apply_val (length Delta) sg F F' -> LRPack Delta (dEl F')
  ; posRed : forall Delta sg a F' Bres
      (ws : wf_ssub Delta sg Ge) (af : Apply_val (length Delta) sg F F'),
      redTm (shpRed ws af) a ->
      Apply_val (length Delta) (a :: sg) B Bres ->
      LRPack Delta (dEl Bres) }.

(* The reducibility predicate computed FROM the pack data (a Definition, not the
   inductive): the extensional function clause. *)
Definition PiRedTmPred (Ge : senv) (F B : sval) (PA : PolyRedPack Ge F B) : sval -> Type :=
  fun f =>
    (has_svalty Ge f (dEl (vPi F B)) *
     (forall Delta sg a F' fsg Bres
        (ws : wf_ssub Delta sg Ge) (af : Apply_val (length Delta) sg F F')
        (afs : Apply_val (length Delta) sg f fsg)
        (hB : Apply_val (length Delta) (a :: sg) B Bres)
        (ra : redTm (shpRed PA ws af) a),
        { v & (Vapp (length Delta) fsg a v *
               redTm (posRed PA ws af ra hB) v)%type }))%type.

(* Adequacy: the packs stored in [PA] are themselves in the graph [R]. *)
Record PolyRedPackAdequate (R : RedRel) (Ge : senv) (F B : sval)
       (PA : PolyRedPack Ge F B) : Type :=
  { shpAd : forall Delta sg F' (ws : wf_ssub Delta sg Ge)
              (af : Apply_val (length Delta) sg F F'),
      R Delta (dEl F') (redTm (shpRed PA ws af))
  ; posAd : forall Delta sg a F' Bres
              (ws : wf_ssub Delta sg Ge) (af : Apply_val (length Delta) sg F F')
              (ra : redTm (shpRed PA ws af) a)
              (hB : Apply_val (length Delta) (a :: sg) B Bres),
      R Delta (dEl Bres) (redTm (posRed PA ws af ra hB)) }.

(* The graph inductive, parameterized by the current level [lvl] and a recursor
   [rec] giving the relation at STRICTLY SMALLER levels (logrel-coq style).
   [LR] occurs only positively (via adequacy, and [rec]'s use in [LRU]). *)
Inductive LR (lvl : TypeLevel) (rec : forall l', TLlt l' lvl -> RedRel) : RedRel :=
| LRnat   : forall Ge, @LR lvl rec Ge (dEl vNat) (RedNat Ge)
| LRempty : forall Ge, @LR lvl rec Ge (dEl vEmpty) (RedNeutral Ge (dEl vEmpty))
| LRne    : forall Ge n r l, wf_neutral Ge n (dU r l) ->
    @LR lvl rec Ge (dEl (vNe n)) (RedNeutral Ge (dEl (vNe n)))
| LRpiI   : forall Ge F B, wf_svalty Ge (dEl (vPiI F B)) ->
    @LR lvl rec Ge (dEl (vPiI F B)) (fun v => has_svalty Ge v (dEl (vPiI F B)))
| LRpi    : forall Ge F B (PA : PolyRedPack Ge F B),
    PolyRedPackAdequate (@LR lvl rec) PA ->
    @LR lvl rec Ge (dEl (vPi F B)) (PiRedTmPred PA)
| LRU     : forall Ge r l l' (h : TLlt l' lvl),
    (* a code [c : dU r l] is reducible iff its El is reducible one level down *)
    @LR lvl rec Ge (dU r l)
       (fun c => has_svalty Ge c (dU r l) *
                 { P : sval -> Type & rec l' h Ge (dEl c) P })%type.
