Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttSyntax WIP.DttNf WIP.DttLR.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 3: reducible substitutions.

   [RSub D G g] : the substitution [g : sub D G] is reducible.  The
   recursion is on the CODOMAIN environment [G] alone, and the relation is
   defined AFTER Layer 2, so there is no circularity.

   As everywhere here the clauses are stated up to [eq_term], which makes
   [RSub] simultaneously the CANONICAL-FORM statement for substitutions: a
   reducible substitution is provably equal to a [snoc]-chain whose spine
   is [forget] and whose entries are reducible.  That is why [sub] needs no
   separate normal-form development in Layer 1.

   The one difference from Gluing/Stlc/RSub.v is dependency: the entry [v]
   at an [ext G0 i A] must be reducible at [A] ALREADY SUBSTITUTED by the
   tail [g0], not at [A] itself.  [RTmN] absorbs the fact that
   [ty_subst g0 A] is not a normal type by quantifying over its normal
   representatives. *)

Local Notation eqt := (eq_term ott_dtt []).

(* The match is on the ARGUMENT-LIST SHAPE first and only then on the head
   symbol (via [eqb], not a literal string pattern): a zero-argument
   constructor named [emp] gets the empty clause, a three-argument
   constructor named [ext] gets the extension clause, and every other shape
   -- including a right-shaped constructor at the wrong name -- falls
   through to [False] rather than being trivially satisfied.  [G0] stays a
   structural subterm of [G] regardless of which head symbol is actually
   there, so the recursion is guarded. *)
Fixpoint RSub (D G g : term) {struct G} : Prop :=
  match G with
  | con n [] =>
      if eqb n "emp" then eqt (sSub D oEmp) g (oForget D) else False
  | con n [A; i; G0] =>
      if eqb n "ext" then
        exists g0 v,
          eqt (sSub D (oExt G0 i A)) g (oSnoc D G0 i A g0 v)
          /\ RSub D G0 g0
          /\ RTmN D i (oTySubst D G0 g0 i A) v
      else False
  | _ => False
  end.

(* ------------------------------------------------------------------ *)
(* The intended reading of the two clauses                              *)
(* ------------------------------------------------------------------ *)

Lemma RSub_emp_intro D g
  : eqt (sSub D oEmp) g (oForget D) -> RSub D oEmp g.
Proof. unfold oEmp; cbn [RSub]; intro H; exact H. Qed.

Lemma RSub_emp_elim D g
  : RSub D oEmp g -> eqt (sSub D oEmp) g (oForget D).
Proof. unfold oEmp; cbn [RSub]; intro H; exact H. Qed.

Lemma RSub_ext_intro D G i A g
  : (exists g0 v,
        eqt (sSub D (oExt G i A)) g (oSnoc D G i A g0 v)
        /\ RSub D G g0
        /\ RTmN D i (oTySubst D G g0 i A) v) ->
    RSub D (oExt G i A) g.
Proof. unfold oExt; cbn [RSub]; intro H; exact H. Qed.

Lemma RSub_ext_elim D G i A g
  : RSub D (oExt G i A) g ->
    exists g0 v,
      eqt (sSub D (oExt G i A)) g (oSnoc D G i A g0 v)
      /\ RSub D G g0
      /\ RTmN D i (oTySubst D G g0 i A) v.
Proof. unfold oExt; cbn [RSub]; intro H; exact H. Qed.

(* Case on which clause a reducible substitution satisfies without
   inspecting [G] beyond that -- this is what lets the rest of the
   development case on an ARBITRARY [RSub D G g] hypothesis. *)
Lemma RSub_inv D G g
  : RSub D G g ->
    (G = oEmp /\ eqt (sSub D oEmp) g (oForget D))
    \/ (exists G0 i A g0 v,
           G = oExt G0 i A
           /\ eqt (sSub D (oExt G0 i A)) g (oSnoc D G0 i A g0 v)
           /\ RSub D G0 g0
           /\ RTmN D i (oTySubst D G0 g0 i A) v).
Proof.
  destruct G as [x | n [| A [| i [| G0 [| ? ?]]]]]; cbn [RSub]; try (intros []).
  - destruct (eqb_boolspec _ n "emp") as [->|Hne]; [ | intros [] ].
    intro H; left; split; [ reflexivity | exact H ].
  - destruct (eqb_boolspec _ n "ext") as [->|Hne]; [ | intros [] ].
    intros [g0 [v [Heq [Hg0 Hv]]]]; right.
    exists G0, i, A, g0, v; repeat split; assumption.
Qed.

(* [RSub] is closed under provable equality of the substitution: both
   clauses hand back an equation whose left-hand side is [g] itself, so
   this needs no induction and no side condition on [G]. *)
Lemma RSub_eq D G g g'
  : RSub D G g -> eqt (sSub D G) g g' -> RSub D G g'.
Proof.
  intros H Heq.
  apply RSub_inv in H
    as [[-> Hf] | [G0 [i [A [g0 [v [-> [Hs [Hg0 Hv]]]]]]]]].
  - apply RSub_emp_intro.
    eapply eq_term_trans; [ apply eq_term_sym; exact Heq | exact Hf ].
  - apply RSub_ext_intro; exists g0, v; repeat split; try assumption.
    eapply eq_term_trans; [ apply eq_term_sym; exact Heq | exact Hs ].
Qed.
