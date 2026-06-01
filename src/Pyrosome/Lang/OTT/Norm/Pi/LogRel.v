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

Notation term := (@term string).

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
(* STATUS: the definitions below are accepted by Rocq (positivity OK for    *)
(* both [LRpi]'s pack/adequacy and [LRU]'s use of [rec]); the finite-tower   *)
(* kit ([LR0]/[LR1]/[LR2] + [rec0..2]) and top-level [RedTy]/[RedTm]/        *)
(* [RedSub] are defined below.  Escape ([RedTy_wf]/[RedTm_wf]) is in         *)
(* [Pi/LogRelLemmas.v].  Remaining for the milestone: a CUSTOM nested        *)
(* induction principle for [LR] (supplying IHs for the adequacy             *)
(* sub-derivations, cf. logrel-coq's [Induction.v]), then [RedTy_subst]/     *)
(* [RedSub_*], [reflect_red] (totality of [Reflect]), and [Apply_total_red]  *)
(* (totality of [Apply_*] on reducible inputs) — and [RedTmEq] for the       *)
(* gluing model.                                                            *)
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

(* The level at which codes of the universe [dU r l] have their El: codes in
   U_{r,L0} have El at [iota L0] (tl0), codes in U_{r,L1} at [iota L1] (tl1).
   (The universe [dU r l] itself is a type one level up, at [next l].) *)
Definition lvl_of (l : term) : TypeLevel :=
  match l with
  | con n _ => if eqb n "L1" then tl1 else tl0
  | _ => tl0
  end.

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
    wf_svalty Ge (dEl (vPi F B)) ->          (* escape fact, stored (logrel-coq style) *)
    PolyRedPackAdequate (@LR lvl rec) PA ->
    @LR lvl rec Ge (dEl (vPi F B)) (PiRedTmPred PA)
| LRU     : forall Ge r l (h : TLlt (lvl_of l) lvl),
    (* a code [c : dU r l] is reducible iff its El is reducible at the code's
       level [lvl_of l] (strictly below the universe's level), via [rec]. *)
    @LR lvl rec Ge (dU r l)
       (fun c => has_svalty Ge c (dU r l) *
                 { P : sval -> Type & rec (lvl_of l) h Ge (dEl c) P })%type.

(* ===================================================================== *)
(* Finite-tower kit: instantiate the recursor [rec] by hand (the tower is    *)
(* tl0 < tl1 < tl2 = ι0 < ι1 < ∞).  Work at the TOP level [tl2], which        *)
(* subsumes all formers (only [LRU] consults [lvl], and tl0,tl1 < tl2);       *)
(* [LRU]'s delegation level [lvl_of l] is pinned, so the relation stays       *)
(* functional.                                                               *)
(* ===================================================================== *)

Lemma no_lt_tl0 : forall l', TLlt l' tl0 -> False.
Proof. intros l' H; inversion H. Qed.

Definition rec0 (l' : TypeLevel) (h : TLlt l' tl0) : RedRel :=
  False_rect RedRel (no_lt_tl0 h).
Definition LR0 : RedRel := @LR tl0 rec0.

(* every [l' < tl1] is [tl0], so the level-0 relation is the only delegate *)
Definition rec1 (l' : TypeLevel) (h : TLlt l' tl1) : RedRel := LR0.
Definition LR1 : RedRel := @LR tl1 rec1.

Definition rec2 (l' : TypeLevel) (h : TLlt l' tl2) : RedRel :=
  match l' with tl0 => LR0 | tl1 => LR1 | tl2 => LR0 end.
Definition LR2 : RedRel := @LR tl2 rec2.

(* Top-level reducibility: a type is reducible when some candidate relation is
   in the graph at the top level; a value is reducible at that candidate. *)
Definition RedTy (Ge : senv) (T : svalty) : Type := { P : sval -> Type & LR2 Ge T P }.
Definition RedTmOf {Ge T} (RT : RedTy Ge T) (v : sval) : Type := projT1 RT v.
Definition RedTm (Ge : senv) (T : svalty) (v : sval) : Type :=
  { P : sval -> Type & (LR2 Ge T P * P v)%type }.

(* Reducible substitutions [g : Ge <- Delta] (the [g : G => G'] carrier): the
   reducible refinement of [wf_ssub], producing the substituted type's
   reducibility and the entry's reducibility. *)
Definition RedSub (Delta : senv) (sg : ssub) (Ge : senv) : Type :=
  (length sg = length Ge) *
  (forall k T, nth_error Ge k = Some T ->
     { T' & ((Apply_ty (length Delta) sg T T' * RedTy Delta T')
             * RedTm Delta T' (nth_default (vNe (nVar 0)) sg k))%type }).
