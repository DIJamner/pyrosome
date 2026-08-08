Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttModel.
Import Core.Notations.

(* =====================================================================
   LAYER 1: the fragment, its normal forms, and weakenings.

   This file plays the role of BOTH Stlc/Syntax.v's [TyOk]/[EnvOk] and
   Stlc/NormalForms.v's [NfVT]/[NfET]/[NeET]/[Wk].  They cannot be separated
   here: in a dependent theory type formation mentions terms, so the
   type-shape predicate and the term normal-form predicate are MUTUAL.  That
   is the concrete answer to structural generalization (3).

   THE PHASE-1 FRAGMENT.  Everything below fixes the universe level to [L0].
   [TyOk] therefore carves out exactly two strata:

     - the universe        [U G r L0]   at info [iU  = info rel (iota L1)]
     - a decoded code      [El G r L0 e] at info [iE r = info r  (iota L0)]

   with [e] a NORMAL CODE ([NfCode]): Nat, Empty, Pi_rel/Pi_irr over normal
   codes, or a neutral of universe type.  This is the exact analogue of the
   STLC proof's [TyOk], which likewise carved [unit]/[->] out of the sort
   [ty] and stated the theorem only for that fragment.  The restriction is
   NOT cosmetic; see the design doc, "the Pi level bug": [Pi_rel]'s domain
   level [lF] is unconstrained in Lang/OTT/Pi.v (the Agda source's [lF <= l]
   side condition was dropped), so at level L1 a type may quantify over
   types of STRICTLY GREATER level and no level-indexed logical relation can
   be stratified.  Restricting to L0 makes the stratification trivially
   valid.

   NORMALIZED INDICES.  Normal forms carry normalized [tyinfo] indices
   ([iU] is [info rel (iota L1)], not the as-written [info rel (next L0)]).
   The two are equal only via the "next0" equation, so several typing
   lemmas below genuinely need [wf_term_conv]; that is expected and is
   itself a witness that [Ceq_sort] cannot be [eq].
   ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* Level-0 abbreviations                                                *)
(* ------------------------------------------------------------------ *)

(* the info of a level-0 CODE (i.e. of an element of [U _ L0]) *)
Definition iU : term := oInfo oRel (oIota oL1).
(* the info of an ELEMENT of a level-0 type at relevance [r] *)
Definition iE (r : term) : term := oInfo r (oIota oL0).

Definition tU (G r : term) : term := oU G r oL0.
Definition tEl (G r e : term) : term := oEl G r oL0 e.

(* the sort of level-0 codes, and of elements of the type named by [e] *)
Definition sU (G r : term) : sort := sExp G iU (tU G r).
Definition sE (G r e : term) : sort := sExp G (iE r) (tEl G r e).

(* context extension by the type named by the code [F] *)
Definition oExtC0 (G r F : term) : term := oExt G (iE r) (tEl G r F).

(* the instantiating substitution [<id, a> : sub G (extC0 G r F)] *)
Definition oInst0 (G r F a : term) : term :=
  oSnoc G G (iE r) (tEl G r F) (oId G) a.

(* [app_rel]'s conclusion type at level 0, verbatim from the compiled rule *)
Definition tAppRel (G rF F B a : term) : term :=
  oTySubst G (oExtC0 G rF F) (oInst0 G rF F a) (iE oRel)
    (oEl (oExtC0 G rF F) oRel oL0 B).
Definition tAppIrr (G rF F B a : term) : term :=
  oTySubst G (oExtC0 G rF F) (oInst0 G rF F a) (iE oIrr)
    (oEl (oExtC0 G rF F) oIrr oL0 B).

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* THE MUTUAL BLOCK                                                     *)
(*                                                                      *)
(* [EnvOk G]        : G is a normal environment                         *)
(* [TyOk G i A]     : A is a normal type at info i in G                 *)
(* [NfCode G r e]   : e is a normal level-0 code of relevance r         *)
(* [VarT G i A x]   : x is an object-level variable (hd + wkn-shifts)   *)
(* [NeET G i A e]   : e is a neutral term                               *)
(* [NfET G i A e]   : e is a normal term                                *)
(*                                                                      *)
(* Compare Stlc/Syntax.v, where [TyOk]/[EnvOk] were two INDEPENDENT        *)
(* inductives over closed syntax and Layer 1's [NfVT]/[NfET]/[NeET]      *)
(* were a separate mutual block.  Here all six are one block.            *)
(*                                                                      *)
(* NOTE on a clause the STLC proof needed and this one does NOT: STLC's  *)
(* [nee_lamapp] -- a normal function VALUE applied to a NEUTRAL argument  *)
(* is stuck -- exists because SimpleVSTLC is CALL BY VALUE and its beta   *)
(* rule fires only when both sides are [ret]s.  OTT's "Pi_rel beta"      *)
(* fires for an ARBITRARY argument, so [app_rel (lam_rel t) a] is never  *)
(* stuck and there is no such clause.  There is also no value/expression *)
(* split at all: OTT has one term sort [exp], not [val] + [exp].         *)
(* ------------------------------------------------------------------ *)

Inductive EnvOk : term -> Prop :=
| envok_emp : EnvOk oEmp
| envok_ext : forall G i A, EnvOk G -> TyOk G i A -> EnvOk (oExt G i A)

with TyOk : term -> term -> term -> Prop :=
| tyok_U : forall G r, EnvOk G -> RelNf r -> TyOk G iU (tU G r)
| tyok_El : forall G r e, NfCode G r e -> TyOk G (iE r) (tEl G r e)

with NfCode : term -> term -> term -> Prop :=
| nfcode_nat : forall G, EnvOk G -> NfCode G oRel (oNat G)
| nfcode_empty : forall G, EnvOk G -> NfCode G oIrr (oEmpty G)
| nfcode_pi_rel : forall G rF F B,
    NfCode G rF F ->
    NfCode (oExtC0 G rF F) oRel B ->
    NfCode G oRel (oPiRel G rF oL0 oL0 F B)
| nfcode_pi_irr : forall G rF F B,
    NfCode G rF F ->
    NfCode (oExtC0 G rF F) oIrr B ->
    NfCode G oIrr (oPiIrr G rF oL0 F B)
| nfcode_ne : forall G r e, NeET G iU (tU G r) e -> NfCode G r e

with VarT : term -> term -> term -> term -> Prop :=
| vart_hd : forall G i A,
    VarT (oExt G i A) i (oTySubst (oExt G i A) G (oWkn G i A) i A) (oHd G i A)
| vart_wkn : forall G i A i0 A0 x,
    VarT G i0 A0 x ->
    VarT (oExt G i A) i0 (oTySubst (oExt G i A) G (oWkn G i A) i0 A0)
      (oExpSubst (oExt G i A) G (oWkn G i A) i0 A0 x)

with NeET : term -> term -> term -> term -> Prop :=
| neet_var : forall G i A x, VarT G i A x -> NeET G i A x
| neet_app_rel : forall G rF F B f a,
    NeET G (iE oRel) (tEl G oRel (oPiRel G rF oL0 oL0 F B)) f ->
    NfET G (iE rF) (tEl G rF F) a ->
    NeET G (iE oRel) (tAppRel G rF F B a) (oAppRel G rF oL0 oL0 F B f a)
| neet_app_irr : forall G rF F B f a,
    NeET G (iE oIrr) (tEl G oIrr (oPiIrr G rF oL0 F B)) f ->
    NfET G (iE rF) (tEl G rF F) a ->
    NeET G (iE oIrr) (tAppIrr G rF F B a) (oAppIrr G rF oL0 F B f a)
| neet_emptyrec : forall G rA A e,
    NeET G (iE oIrr) (tEl G oIrr (oEmpty G)) e ->
    NfCode G rA A ->
    NeET G (iE rA) (tEl G rA A) (oEmptyrec G rA oL0 A e)

with NfET : term -> term -> term -> term -> Prop :=
| nfet_ne : forall G i A e, NeET G i A e -> NfET G i A e
| nfet_code : forall G r e, NfCode G r e -> NfET G iU (tU G r) e
| nfet_zero : forall G, EnvOk G -> NfET G (iE oRel) (tEl G oRel (oNat G)) (oZero G)
| nfet_suc : forall G n,
    NfET G (iE oRel) (tEl G oRel (oNat G)) n ->
    NfET G (iE oRel) (tEl G oRel (oNat G)) (oSuc G n)
| nfet_lam_rel : forall G rF F B t,
    NfET (oExtC0 G rF F) (iE oRel) (oEl (oExtC0 G rF F) oRel oL0 B) t ->
    NfET G (iE oRel) (tEl G oRel (oPiRel G rF oL0 oL0 F B))
      (oLamRel G rF oL0 oL0 F B t)
| nfet_lam_irr : forall G rF F B t,
    NfET (oExtC0 G rF F) (iE oIrr) (oEl (oExtC0 G rF F) oIrr oL0 B) t ->
    NfET G (iE oIrr) (tEl G oIrr (oPiIrr G rF oL0 F B))
      (oLamIrr G rF oL0 F B t).

Scheme EnvOk_min := Minimality for EnvOk Sort Prop
  with TyOk_min := Minimality for TyOk Sort Prop
  with NfCode_min := Minimality for NfCode Sort Prop
  with VarT_min := Minimality for VarT Sort Prop
  with NeET_min := Minimality for NeET Sort Prop
  with NfET_min := Minimality for NfET Sort Prop.
Combined Scheme Nf_mutind from
  EnvOk_min, TyOk_min, NfCode_min, VarT_min, NeET_min, NfET_min.

(* ------------------------------------------------------------------ *)
(* Weakenings                                                           *)
(*                                                                      *)
(* [Wk D G w] : the substitution [w : sub D G] is a weakening.  As in    *)
(* the STLC proof this is a PURELY SYNTACTIC class -- no clause mentions *)
(* reducibility -- and it is closed under going under a binder           *)
(* ([wk_lift]).                                                         *)
(*                                                                      *)
(* THE DEPENDENT DIFFERENCE.  [wk_lift]'s domain type must be WEAKENED:  *)
(* lifting [w : sub D G] past a binder of type [A] over [G] produces a   *)
(* substitution [sub (ext D i A[w]) (ext G i A)], not [sub (ext D i A)   *)
(* (ext G i A)].  And the head variable it snocs, [hd D i A[w]], has     *)
(* type [A[w][wkn]] where the [snoc] rule demands [A[wkn o w]]; those    *)
(* agree only by [ty_subst_cmp].  So unlike Stlc/NormalForms.v's [Wk],    *)
(* THIS class does not typecheck by [wf_by] alone -- [Wk_wf] below needs *)
(* [wf_term_conv].  Every weakening/typing lemma in the dependent        *)
(* setting acquires such a conversion; that is the routine (not the      *)
(* hard) part of the generalization.                                    *)
(* ------------------------------------------------------------------ *)

Definition oWkTy (D G w i A : term) : term := oTySubst D G w i A.

Inductive Wk : term -> term -> term -> Prop :=
| wk_id : forall G, Wk G G (oId G)
| wk_ext : forall D G i A w,
    Wk D G w ->
    Wk (oExt D i A) G (oCmp (oExt D i A) D G (oWkn D i A) w)
| wk_lift : forall D G i A w,
    Wk D G w ->
    Wk (oExt D i (oWkTy D G w i A)) (oExt G i A)
      (oSnoc (oExt D i (oWkTy D G w i A)) G i A
         (oCmp (oExt D i (oWkTy D G w i A)) D G
            (oWkn D i (oWkTy D G w i A)) w)
         (oHd D i (oWkTy D G w i A))).

(* ================================================================== *)
(* STATEMENTS ONLY BELOW THIS LINE                                     *)
(* ================================================================== *)

(* ---- typing of the fragment ---- *)

Lemma EnvOk_wf G : EnvOk G -> wft G sEnv.
Admitted.

Lemma TyOk_wf G i A : TyOk G i A -> wft A (sTy G i).
Admitted.

Lemma TyOk_EnvOk G i A : TyOk G i A -> EnvOk G.
Admitted.

Lemma NfCode_wf G r e : NfCode G r e -> wft e (sU G r).
Admitted.

Lemma NfCode_EnvOk G r e : NfCode G r e -> EnvOk G.
Admitted.

Lemma NfCode_RelNf G r e : NfCode G r e -> RelNf r.
Admitted.

Lemma VarT_wf G i A x : VarT G i A x -> EnvOk G -> wft x (sExp G i A).
Admitted.

(* The type of a variable is a normal type in the SAME environment -- the
   dependent analogue of Stlc/NormalForms.v's [VarT_TyOk].  Note the shift:
   the type stored in the context lives in the SHORTER environment and has
   to be weakened, so this is genuinely a statement about [TyOk] being
   closed under weakening ([TyOk_wk] below), not a projection. *)
Lemma VarT_TyOk G i A x : VarT G i A x -> EnvOk G -> TyOk G i A.
Admitted.

Lemma NeET_TyOk G i A e : NeET G i A e -> EnvOk G -> TyOk G i A.
Admitted.

Lemma Nf_wf
  : (forall G, EnvOk G -> wft G sEnv)
    /\ (forall G i A, TyOk G i A -> wft A (sTy G i))
    /\ (forall G r e, NfCode G r e -> wft e (sU G r))
    /\ (forall G i A x, VarT G i A x -> EnvOk G -> wft x (sExp G i A))
    /\ (forall G i A e, NeET G i A e -> EnvOk G -> wft e (sExp G i A))
    /\ (forall G i A e, NfET G i A e -> EnvOk G -> wft e (sExp G i A)).
Admitted.

(* ---- weakenings ---- *)

Lemma Wk_dom D G w : Wk D G w -> EnvOk D -> EnvOk G.
Admitted.

Lemma Wk_wf D G w : Wk D G w -> EnvOk D -> EnvOk G -> wft w (sSub D G).
Admitted.

(* The composite of two weakenings is PROVABLY EQUAL to a weakening (it is
   not syntactically one).  Same statement shape as the STLC proof. *)
Lemma Wk_cmp D G w1 G' w2
  : Wk D G w1 -> Wk G G' w2 -> EnvOk D ->
    exists w, Wk D G' w /\ eqt (sSub D G') (oCmp D G G' w1 w2) w.
Admitted.

(* ---- stability of the fragment under weakening ----

   In the dependent setting the TYPE moves too, so each statement produces
   both a shifted normal form and a shifted normal type.  [TyOk_wk] has no
   counterpart in the STLC proof (there, types were closed). *)

Lemma TyOk_wk D G w i A
  : TyOk G i A -> Wk D G w -> EnvOk D ->
    exists A', TyOk D i A' /\ eqt (sTy D i) (oTySubst D G w i A) A'.
Admitted.

Lemma NfCode_wk D G w r e
  : NfCode G r e -> Wk D G w -> EnvOk D ->
    exists e', NfCode D r e'
               /\ eqt (sU D r) (oExpSubst D G w iU (tU G r) e) e'.
Admitted.

Lemma VarT_wk D G w i A x
  : VarT G i A x -> Wk D G w -> EnvOk D ->
    exists A' x',
      TyOk D i A' /\ VarT D i A' x'
      /\ eqt (sTy D i) (oTySubst D G w i A) A'
      /\ eqt (sExp D i A') (oExpSubst D G w i A x) x'.
Admitted.

Lemma Nf_wk
  : (forall G i A e, NeET G i A e ->
       forall D w, Wk D G w -> EnvOk D -> EnvOk G ->
         exists A' e', TyOk D i A' /\ NeET D i A' e'
                       /\ eqt (sTy D i) (oTySubst D G w i A) A'
                       /\ eqt (sExp D i A') (oExpSubst D G w i A e) e')
    /\ (forall G i A e, NfET G i A e ->
       forall D w, Wk D G w -> EnvOk D -> EnvOk G ->
         exists A' e', TyOk D i A' /\ NfET D i A' e'
                       /\ eqt (sTy D i) (oTySubst D G w i A) A'
                       /\ eqt (sExp D i A') (oExpSubst D G w i A e) e').
Admitted.
