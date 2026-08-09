Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 3: reducible substitutions.

   [RSub D G g] : the substitution [g : sub D G] is reducible.  The
   recursion is on the CODOMAIN environment [G] alone, and the relation is
   defined AFTER Layer 2, so there is no circularity.  Note the index [G]
   is the environment's SYNTAX: the [ext] clause is pinned to an [oExt],
   which is what [RSubN] below has to relax.

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

Inductive RSub : term -> term -> term -> Prop :=
| rsub_emp : forall D g,
    eqt (sSub D oEmp) g (oForget D) ->
    RSub D oEmp g
| rsub_ext : forall D G i A g g0 v,
    eqt (sSub D (oExt G i A)) g (oSnoc D G i A g0 v) ->
    RSub D G g0 ->
    RTmN D i (oTySubst D G g0 i A) v ->
    RSub D (oExt G i A) g.

(* ------------------------------------------------------------------ *)
(* The intended reading of the two clauses                              *)
(* ------------------------------------------------------------------ *)

Lemma RSub_emp_intro D g
  : eqt (sSub D oEmp) g (oForget D) -> RSub D oEmp g.
Proof. apply rsub_emp. Qed.

Lemma RSub_ext_intro D G i A g
  : (exists g0 v,
        eqt (sSub D (oExt G i A)) g (oSnoc D G i A g0 v)
        /\ RSub D G g0
        /\ RTmN D i (oTySubst D G g0 i A) v) ->
    RSub D (oExt G i A) g.
Proof. intros [g0 [v [Heq [Hg0 Hv]]]]; eapply rsub_ext; eassumption. Qed.

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
  destruct 1 as [ D g Hf | D G0 i A g g0 v Hs Hg0 Hv ];
    [ left; split; [ reflexivity | exact Hf ]
    | right; exists G0, i, A, g0, v; repeat split; assumption ].
Qed.

Lemma RSub_emp_elim D g
  : RSub D oEmp g -> eqt (sSub D oEmp) g (oForget D).
Proof.
  intro H; apply RSub_inv in H
    as [[_ Hf] | [G0 [i [A [g0 [v [Habs _]]]]]]];
    [ exact Hf | unfold oEmp, oExt in Habs; safe_invert Habs ].
Qed.

Lemma RSub_ext_elim D G i A g
  : RSub D (oExt G i A) g ->
    exists g0 v,
      eqt (sSub D (oExt G i A)) g (oSnoc D G i A g0 v)
      /\ RSub D G g0
      /\ RTmN D i (oTySubst D G g0 i A) v.
Proof.
  intro H; apply RSub_inv in H
    as [[Habs _] | [G0 [i0 [A0 [g0 [v [Habs [Hs [Hg0 Hv]]]]]]]]];
    [ unfold oEmp, oExt in Habs; safe_invert Habs | ].
  unfold oExt in Habs; safe_invert Habs.
  exists g0, v; repeat split; assumption.
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

(* ------------------------------------------------------------------ *)
(* [RSubN]: reducible substitution, up to provable equality of the       *)
(* CODOMAIN ENVIRONMENT                                                  *)
(* ------------------------------------------------------------------ *)

(* [RSub] is indexed by the SYNTAX of [G], so it is not stable under
   provable equality of [G] -- and [csort_cong] at the sort [sub G G']
   varies exactly that.  The wrapper below restores stability the same way
   [RTmN]/[RTyN] (src/Pyrosome/Gluing/Dtt/LogRel.v) do for the info and the type: quantify a
   normal representative and identify it up to [eq_term].  Both directions
   of the [Ceq_sort] transfer are then transitivity alone.

   This is not cosmetic either: without it the [sub] transfer would have to
   push [RSub] through an environment equation clause by clause, and in the
   [ext] case that asks for reducibility of the entry at the OTHER info --
   i.e. for the normalization theorem itself. *)

Lemma sSub_cong G1 G2 G1' G2'
  : eqt sEnv G1 G2 -> eqt sEnv G1' G2' ->
    eq_sort ott_dtt [] (sSub G1 G1') (sSub G2 G2').
Proof. intros; scong_step "sub" [G1'; G1] [G2'; G2]. Qed.

Definition RSubN (D G g : term) : Prop :=
  exists G0, EnvOk G0 /\ eqt sEnv G G0 /\ RSub D G0 g.

Lemma RSubN_of_RSub D G g : EnvOk G -> RSub D G g -> RSubN D G g.
Proof.
  intros HG HR; exists G; repeat split; try assumption.
  apply eq_term_refl, EnvOk_wf; assumption.
Qed.

Lemma RSubN_elim D G g
  : RSubN D G g -> exists G0, EnvOk G0 /\ eqt sEnv G G0 /\ RSub D G0 g.
Proof. exact (fun H => H). Qed.

(* The point of the wrapper: stability under equality of the environment,
   in both directions, by transitivity alone. *)
Lemma RSubN_env D G G' g
  : RSubN D G g -> eqt sEnv G G' -> RSubN D G' g.
Proof.
  intros [G0 (HG0 & Heq & HR)] Heq'.
  exists G0; repeat split; try assumption.
  eapply eq_term_trans; [ apply eq_term_sym; exact Heq' | exact Heq ].
Qed.

Lemma RSubN_eq D G g g'
  : RSubN D G g -> eqt (sSub D G) g g' -> RSubN D G g'.
Proof.
  intros [G0 (HG0 & Heq & HR)] Heq'.
  assert (wf_term ott_dtt [] D sEnv) as HD
    by (eapply wft_sub_dom; eapply eqt_wf_l; exact Heq').
  exists G0; repeat split; try assumption.
  eapply RSub_eq; [ exact HR | ].
  eapply eq_term_conv; [ exact Heq' | ].
  apply sSub_cong; [ apply eq_term_refl; exact HD | exact Heq ].
Qed.
