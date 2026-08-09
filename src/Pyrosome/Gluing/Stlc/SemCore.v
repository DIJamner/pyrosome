Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing.Stlc Require Import Syntax Normalization NormalForms Eqns LogRel RSub.
Import Core.Notations.

(* Layer 4, semantic core.

   [ModelCong.v]'s congruence obligations and [ModelEq.v]'s equation
   obligations are developed independently -- neither file imports the other
   -- but each needs exactly the same TWO facts about reducibility: applying
   two reducible expressions is again reducible ([RE_app]), and a substituted
   lambda is reducible ([RV_lam_sub]/[RV_lam]).  Both are where the real work
   of Layer 4 happens: [RE_app] is where the "stuck" canonical forms of
   Gluing/Stlc/NormalForms.v ([neet_app], [neet_lamapp]) actually get produced,
   and [RV_lam_sub] is where a substitution gets pushed under a binder and the
   beta equations of Gluing/Stlc/Eqns.v get consumed.  Stating them once, here,
   is what lets the congruence and equation proofs stay genuinely independent
   of each other while still sharing the one place their semantics has
   content. *)

Local Notation eqt := (eq_term stlc_unit []).
Local Notation wft := (wf_term stlc_unit []).

(* ================================================================== *)
(* Applying two reducible expressions                                  *)
(* ================================================================== *)

(* This is where Layer 1's [neet_lamapp] clause earns its keep: the middle
   case combines a function that is the [ret] of a reducible value with a
   NEUTRAL argument, and the result is stuck without being an application of
   a neutral. *)
Lemma RE_app G A B E E'
  : EnvOk G -> TyOk A -> TyOk B ->
    RE G (Arr A B) E -> RE G A E' -> RE G B (App G A B E E').
Proof.
  intros HG HA HB HE HE'.
  assert (wft G Senv) as HwG by (apply EnvOk_wf; assumption).
  assert (wft A Sty) as HwA by (apply TyOk_wf; assumption).
  assert (wft B Sty) as HwB by (apply TyOk_wf; assumption).
  assert (wft E (Sexp G (Arr A B))) as HwE by (eapply RE_wf; eassumption).
  assert (wft E' (Sexp G A)) as HwE' by (eapply RE_wf; eassumption).
  destruct (RE_cases HE) as [[v [Hv Heqv]] | [n [Hn Heqn]]].
  - assert (wft v (Sval G (Arr A B))) as Hwv by (eapply RV_wf; eassumption).
    destruct (RE_cases HE') as [[u [Hu Hequ]] | [m [Hm Heqm]]].
    + assert (wft u (Sval G A)) as Hwu by (eapply RV_wf; eassumption).
      eapply RE_eq; [ eapply RV_apply; eassumption | ].
      apply eq_term_sym; apply cong_App;
        [ wfa | wfa | wfa | exact Heqv | exact Hequ ].
    + destruct (CR_reify Hv) as [nv [Hnv Heqnv]].
      assert (wft nv (Sval G (Arr A B))) as Hwnv by (eapply eqt_wf_r; eassumption).
      assert (wft m (Sexp G A)) as Hwm by (eapply eqt_wf_r; eassumption).
      eapply RE_ne with (n := App G A B (Ret G (Arr A B) nv) m);
        [ apply neet_lamapp; assumption | | assumption | assumption ].
      apply cong_App; [ wfa | wfa | wfa | | exact Heqm ].
      eapply eq_term_trans; [ exact Heqv | ].
      apply cong_Ret; [ wfa | wfa | exact Heqnv ].
  - assert (wft n (Sexp G (Arr A B))) as Hwn by (eapply eqt_wf_r; eassumption).
    destruct (CR_reify_E HE') as [m [Hm Heqm]].
    assert (wft m (Sexp G A)) as Hwm by (eapply eqt_wf_r; eassumption).
    eapply RE_ne with (n := App G A B n m);
      [ apply neet_app; assumption | | assumption | assumption ].
    apply cong_App; [ wfa | wfa | wfa | exact Heqn | exact Heqm ].
Qed.

(* ================================================================== *)
(* A substituted lambda is reducible                                   *)
(* ================================================================== *)

(* The general form: the target context [D] and the substitution [g : sub D
   G] are both explicit parameters, so the Kripke clause of [RV_arr] --
   reducibility at every weakening of [D] -- can be established directly
   from it, without first specializing to [D := G]/[g := id]. *)
Lemma RV_lam_sub G A B e D g
  : (forall D' m, EnvOk D' -> RSub D' (Ext G A) m ->
                  RE D' B (ExpSubst D' (Ext G A) m B e)) ->
    EnvOk D -> EnvOk G -> TyOk A -> TyOk B -> RSub D G g ->
    wft e (Sexp (Ext G A) B) ->
    RV D (Arr A B) (ValSubst D G g (Arr A B) (Lam G A B e)).
Proof.
  intros He HD HG HA HB Hg Hwe.
  assert (wft g (Ssub D G)) as Hwg by (eapply RSub_wf; eassumption).
  apply RV_arr.
  - (* the normal form: reify the body under the lifted substitution *)
    assert (EnvOk (Ext D A)) as HDA by (constructor; assumption).
    assert (RSub (Ext D A) (Ext G A)
              (Snoc (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) g) A (Hd D A)))
      as Hlift by (apply RSub_lift; assumption).
    destruct (CR_reify_E (He _ _ HDA Hlift)) as [n [Hn Heqn]].
    exists (Lam D A B n); split.
    + apply nfvt_lam; assumption.
    + eapply eq_term_trans; [ apply eq_val_subst_lambda; wfa | ].
      apply cong_Lam; [ wfa | wfa | wfa | exact Heqn ].
  - (* the Kripke clause: shift along [w], then beta *)
    intros D' w u Hw HD' Hu.
    assert (wft w (Ssub D' D)) as Hww by (eapply Wk_wf; eassumption).
    assert (wft u (Sval D' A)) as Hwu by (eapply RV_wf; eassumption).
    assert (RSub D' G (Cmp D' D G w g)) as Hg''
        by (eapply RSub_wk; eassumption).
    assert (wft (Cmp D' D G w g) (Ssub D' G)) as Hwg'' by wfa.
    assert (RSub D' (Ext G A) (Snoc D' G (Cmp D' D G w g) A u)) as Hsn
        by (apply RSub_ext; assumption).
    eapply RE_eq; [ exact (He _ _ HD' Hsn) | ].
    apply eq_term_sym.
    eapply eq_term_trans.
    { apply cong_App; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
      apply cong_Ret; [ wfa | wfa | apply eq_val_subst_cmp; wfa ]. }
    apply eq_beta_lift; wfa.
Qed.

(* [RV_lam] is exactly [RV_lam_sub] with its target-context/substitution
   parameters ([D], [g]) pulled to a trailing [forall] and renamed ([G],
   [g]), and its own environment argument renamed [Y] -- the same fact,
   reassociated so that [ModelCong.cong_obligation]'s [lambda] case, which
   applies it by name via [apply RV_lam; assumption], sees an unchanged
   statement. *)
Lemma RV_lam Y A B e
  : EnvOk Y -> TyOk A -> TyOk B -> wft e (Sexp (Ext Y A) B) ->
    (forall D s, EnvOk D -> RSub D (Ext Y A) s ->
                 RE D B (ExpSubst D (Ext Y A) s B e)) ->
    forall G g, EnvOk G -> RSub G Y g ->
      RV G (Arr A B) (ValSubst G Y g (Arr A B) (Lam Y A B e)).
Proof.
  intros HY HA HB Hwe Hsem G g HG Hg.
  apply RV_lam_sub; assumption.
Qed.
