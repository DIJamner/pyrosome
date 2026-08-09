Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.NormalForms.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 2: reducibility.

   Gluing/Stlc/LogRel.v defines [RV] by structural recursion on the TYPE.
   That fails here twice: the codomain of a Pi is an INSTANTIATION
   [B[<id,a>]], not bounded by [|Pi F B|]; and types contain terms, so no
   syntactic measure decreases through the universe clause.

   The replacement is an ordinary strictly-positive [Prop] inductive
   relating a NORMAL TYPE to a CANDIDATE (a predicate on terms).  Three
   things make it work:

   * No measure at all -- the well-foundedness is strict positivity.  The
     hypothesis "a is a reducible argument" is [Pd D w a]: a bound
     PARAMETER applied, not a recursive occurrence of [RTy].  So the
     negative occurrence that forces induction-recursion in
     Abel-Ohman-Vezzosi becomes a negative occurrence of a constructor
     parameter, which strict positivity permits.  [RTy] itself occurs only
     in conclusions of universally quantified hypotheses (under [ex] and
     [and]), i.e. strictly positively.

   * The universe clause does not mention [RTy].  [rty_U]'s candidate is
     "provably equal to a syntactic normal code" ([HasNfCode], Layer 1),
     not "names a reducible type".  That is what kills the would-be
     negative occurrence of [RTy] in its own universe clause -- the exact
     point at which the abandoned attempt had to introduce universe
     polymorphism and two separate recursors, and then found the crux
     inexpressible.  The bridge back (every normal code names a reducible
     type) is the separate lemma [RTyEx_of_NfCode], a plain induction on
     [NfCode], and it is sound only because Layer 1's normal codes are an
     inductively generated class closed under substitution -- see
     WIP/dtt_norm_design.md section 2.

   * [Prop] throughout.  The candidate index lives in [Type] but the
     inductive is in impredicative [Prop] and is eliminated only into
     [Prop].  The single [Prop]/[Type] bridge in the whole development is
     Gluing/CutModelSound.v's [inhabited], unchanged.

   ETA.  The Pi clause carries NO "and it has a normal form" conjunct.
   Without eta one has to, because a neutral at a Pi type is already
   normal and nothing forces a member of the candidate to be one.  With
   eta the normal form of an inhabitant of a Pi type IS its eta-expansion,
   so "has a normal form" is derivable -- which is exactly what makes
   escape and reflect a single mutual induction on the [RTy] derivation.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* The terms the Pi clause has to name                                  *)
(* ------------------------------------------------------------------ *)

(* [w : sub D G] applied to the domain code [F : U G rF lF]. *)
Definition wkCode (D G w rF lF F : term) : term :=
  oExpSubst D G w (iCode lF) (oU G rF lF) F.

(* [<w, a> : sub D (extC G rF lF F)] -- the substitution that instantiates
   the binder with [a] while weakening the rest along [w]. *)
Definition instAt (D G rF lF F w a : term) : term :=
  oSnoc D G (iEl rF lF) (oEl G rF lF F) w a.

(* The codomain type at [(D, w, a)], as the raw substitution instance.  No
   normal representative is named HERE: the clause below quantifies one
   into existence, which is what keeps [RTy]'s type index syntactic. *)
Definition codAtRel (D G rF lF lG F B w a : term) : term :=
  oTySubst D (oExtC G rF lF F) (instAt D G rF lF F w a) (iEl oRel lG)
           (oEl (oExtC G rF lF F) oRel lG B).

Definition codAtIrr (D G rF lF F B w a : term) : term :=
  oTySubst D (oExtC G rF lF F) (instAt D G rF lF F w a) (iEl oIrr oL0)
           (oEl (oExtC G rF lF F) oIrr oL0 B).

(* [w] applied to the codomain code [B], living in [extC G rF lF F]: the
   binder must be lifted, which is [oLift]. *)
Definition wkCodCodeRel (D G w rF lF lG F B : term) : term :=
  oExpSubst (oExtC D rF lF (wkCode D G w rF lF F)) (oExtC G rF lF F)
            (oLift D G w rF lF F) (iCode lG)
            (oU (oExtC G rF lF F) oRel lG) B.

Definition wkCodCodeIrr (D G w rF lF F B : term) : term :=
  oExpSubst (oExtC D rF lF (wkCode D G w rF lF F)) (oExtC G rF lF F)
            (oLift D G w rF lF F) (iCode oL0)
            (oU (oExtC G rF lF F) oIrr oL0) B.

(* [w] applied to the function [e] itself. *)
Definition wkFunRel (D G w rF lF lG F B e : term) : term :=
  oExpSubst D G w (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) e.

Definition wkFunIrr (D G w rF lF F B e : term) : term :=
  oExpSubst D G w (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e.

(* The application the Pi clause is about: [e], weakened to [D], applied to
   the reducible argument [a].  Written with the RAW substituted domain and
   codomain codes rather than named normal forms -- every candidate this
   development builds is closed under provable equality, so nothing is lost
   and one existential per clause is saved. *)
Definition appAtRel (D G rF lF lG F B w e a : term) : term :=
  oAppRel D rF lF lG
          (wkCode D G w rF lF F)
          (wkCodCodeRel D G w rF lF lG F B)
          (wkFunRel D G w rF lF lG F B e)
          a.

Definition appAtIrr (D G rF lF F B w e a : term) : term :=
  oAppIrr D rF lF
          (wkCode D G w rF lF F)
          (wkCodCodeIrr D G w rF lF F B)
          (wkFunIrr D G w rF lF F B e)
          a.

(* ------------------------------------------------------------------ *)
(* The relation                                                         *)
(* ------------------------------------------------------------------ *)

(* [RTy G i A P] : [A] is a normal type of sort [ty G i] whose reducible
   inhabitants are exactly [P].  [Pd D w] is the domain candidate at the
   weakening [w : sub D G]; [Pc D w a] the codomain candidate there, at the
   reducible argument [a]. *)
Inductive RTy : term -> term -> term -> (term -> Prop) -> Prop :=

| rty_U : forall G r l P,
    EnvOk G -> RelNf r -> LvlNf l ->
    (forall c, P c <-> HasNfCode G r l c) ->
    RTy G (iCode l) (oU G r l) P

| rty_nat : forall G P,
    EnvOk G ->
    (forall e, P e <-> HasNf G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e) ->
    RTy G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) P

| rty_empty : forall G P,
    EnvOk G ->
    (forall e, P e <-> HasNe G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e) ->
    RTy G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) P

(* A type named by a NEUTRAL code.  By Layer 1 that means a variable. *)
| rty_var : forall G r l c P,
    VarT G (iCode l) (oU G r l) c ->
    (forall e, P e <-> HasNe G (iEl r l) (oEl G r l c) e) ->
    RTy G (iEl r l) (oEl G r l c) P

| rty_pi_rel :
  forall G rF lF lG F B P
         (Pd : term -> term -> term -> Prop)
         (Pc : term -> term -> term -> term -> Prop),
    RelNf rF -> LvlNf lF -> LvlNf lG ->
    NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oRel lG B ->
    (* the domain is reducible at every weakening *)
    (forall D w, Wk D G w -> EnvOk D ->
       exists F', NfCode D rF lF F'
               /\ eqt (sCode D rF lF) (wkCode D G w rF lF F) F'
               /\ RTy D (iEl rF lF) (oEl D rF lF F') (Pd D w)) ->
    (* the codomain is reducible at every weakening and reducible argument *)
    (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
       exists C, TyOk D (iEl oRel lG) C
              /\ eqt (sTy D (iEl oRel lG)) (codAtRel D G rF lF lG F B w a) C
              /\ RTy D (iEl oRel lG) C (Pc D w a)) ->
    (* the candidate: no HasNf conjunct -- see the header on eta *)
    (forall e, P e <->
       (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
          Pc D w a (appAtRel D G rF lF lG F B w e a))) ->
    RTy G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) P

(* [Pi_irr] has no eta rule in [ott_pi], so a neutral there IS normal and
   the candidate must say so explicitly -- the "HasNf" conjunct that the
   relevant Pi does without. *)
| rty_pi_irr :
  forall G rF lF F B P
         (Pd : term -> term -> term -> Prop)
         (Pc : term -> term -> term -> term -> Prop),
    RelNf rF -> LvlNf lF ->
    NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oIrr oL0 B ->
    (forall D w, Wk D G w -> EnvOk D ->
       exists F', NfCode D rF lF F'
               /\ eqt (sCode D rF lF) (wkCode D G w rF lF F) F'
               /\ RTy D (iEl rF lF) (oEl D rF lF F') (Pd D w)) ->
    (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
       exists C, TyOk D (iEl oIrr oL0) C
              /\ eqt (sTy D (iEl oIrr oL0)) (codAtIrr D G rF lF F B w a) C
              /\ RTy D (iEl oIrr oL0) C (Pc D w a)) ->
    (forall e, P e <->
       (HasNf G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e
        /\ forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
             Pc D w a (appAtIrr D G rF lF F B w e a))) ->
    RTy G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) P.

(* ------------------------------------------------------------------ *)
(* Reducibility of terms, up to provable type equality                  *)
(* ------------------------------------------------------------------ *)

(* At a SYNTACTIC normal type: universally quantified over the candidate,
   which is the form congruence cases consume.  Syntactic functionality
   ([RTy_fun], an ordinary induction: the six clauses are pairwise disjoint
   by head symbol) makes it equivalent to the existential form. *)
Definition RTm (G i A e : term) : Prop :=
  forall P, RTy G i A P -> P e.

(* At an ARBITRARY type: quantified over the normal representatives.  Two
   provably-equal sorts then have literally the same set of normal
   representatives, which is what makes the [Ceq_sort] transfer of Layer 4a
   free; and Layer 0.5's [TyOk_inj] says that set is a singleton, which is
   what makes this usable at all (see WIP/dtt_norm_design.md section 3).

   THE INFO INDEX MUST BE QUANTIFIED TOO, and this is not cosmetic.  The
   first version of these definitions held [i] fixed, and the resulting
   [Ceq_sort] transfer for the sort [ty G i] is REFUTABLE modulo
   consistency -- a fact src/Pyrosome/Gluing/Dtt/ModelStruct.v proves rather than merely
   asserts.  The reason: [TyOk]'s info index is syntactic BY DESIGN (a
   universe is pinned at [iCode l], an [El] at [iEl r l]), but "next0"
   makes [iCode L0] and [iEl rel L1] provably equal, and [Ceq_term] at
   [tyinfo] relates them -- it only demands equal [ninfo]s.  So
   [ty G (iCode L0)] and [ty G (iEl rel L1)] are provably equal sorts whose
   sets of normal representatives are DISJOINT, and a transfer between them
   would force the closed universe [U irr L0] to be provably equal to the
   [El] of a closed relevant [Pi] code.

   Quantifying [i] as well fixes it outright: both definitions are then
   stable under [eqt sInfo] in the index in BOTH directions by transitivity
   alone, which is exactly what the two directions of [Ceq_sort] need, and
   nothing in Layers 1-3 has to move -- [TyOk] keeps its pinned infos and
   the aliasing is absorbed here. *)
Definition RTmN (G i A e : term) : Prop :=
  forall i0 A0,
    eqt sInfo i i0 -> TyOk G i0 A0 -> eqt (sTy G i0) A A0 -> RTm G i0 A0 e.

(* "A is a reducible type", up to provable equality -- of the type AND of
   the info. *)
Definition RTyN (G i A : term) : Prop :=
  exists i0 A0 P,
    eqt sInfo i i0 /\ TyOk G i0 A0 /\ eqt (sTy G i0) A A0 /\ RTy G i0 A0 P.
