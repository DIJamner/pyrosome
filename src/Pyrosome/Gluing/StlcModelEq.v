Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound
  StlcModel StlcNormalization StlcNormalForms StlcEqns StlcLogRel StlcRSub
  StlcCeq.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC SimpleUnit.
Import Core.Notations.

(* Layer 4b: the EQUATIONAL half of [CutTModel_ok] for [stlc_unit].

   This file proves exactly the [cterm_by] obligation of [CutTModel_ok] at
   [l := stlc_unit], [c := []], [CM := StlcCM]:

     In (name, term_eq_rule c' e1 e2 t) stlc_unit ->
     ceq_args c' s1 s2 ->
     Ceq_term t[/with_names_from c' s2/]
              e1[/with_names_from c' s1/] e2[/with_names_from c' s2/]

   It deliberately does NOT build the [Instance]; the congruence half and the
   assembly live elsewhere.

   The shape of every proof is dictated by [Ceq_term] (Gluing/StlcCeq.v), which
   is a conjunction of

     (a) an EQUATION [eqt t e1[/s1/] e2[/s2/]], and
     (b) a SEMANTIC conjunct that constrains only the LEFT term [e1[/s1/]].

   (a) is always [congruence on e1 along the argument equations] followed by
   [the language's own equation, instantiated at s2] -- i.e. a direct hit in
   Gluing/StlcEqns.v.  (b) is where the content is: it must be established for
   [e1[/s1/]] from the semantic conjuncts of the arguments, transporting along
   the equation with [RV_eq]/[RE_eq]/[RSub_eq].

   Only three of the eighteen equations carry real content, and they all
   funnel through the three lemmas in the "semantic core" section below:
   [RE_app] (needed by [exp_subst app]), [eq_beta_lift] and [RV_lam_sub]
   (needed by [val_subst lambda] and [STLC-beta]). *)

Local Notation eqt := (eq_term stlc_unit []).
Local Notation wft := (wf_term stlc_unit []).

(* ================================================================== *)
(* 0.  A Prop-valued mirror of [ceq_args]                              *)
(* ================================================================== *)

(* [ceq_args] is Type-valued (CutTModel's carriers are), while [Ceq_term] is a
   Prop.  Eliminating the Type-valued inductive into Prop is fine, but the
   resulting existential/conjunctive inversion principles cannot mention
   [ceq_args] itself.  Mirroring it in Prop once, up front, is what makes the
   uniform [dargs] destructor below possible. *)
Inductive Pceq_args : ctx -> list term -> list term -> Prop :=
| Pceq_args_nil : Pceq_args [] [] []
| Pceq_args_cons : forall c' es1 es2,
    Pceq_args c' es1 es2 ->
    forall name t e1 e2,
      Ceq_term t[/with_names_from c' es2/] e1 e2 ->
      Pceq_args ((name,t)::c') (e1::es1) (e2::es2).

Lemma ceq_args_Pceq_args c' s1 s2
  : ceq_args (CM := StlcCM) c' s1 s2 -> Pceq_args c' s1 s2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma Pceq_args_nil_inv s1 s2 : Pceq_args [] s1 s2 -> s1 = [] /\ s2 = [].
Proof. inversion 1; auto. Qed.

Lemma Pceq_args_cons_inv name t c' s1 s2
  : Pceq_args ((name,t)::c') s1 s2 ->
    exists x1 x2 l1 l2,
      s1 = x1::l1 /\ s2 = x2::l2
      /\ Pceq_args c' l1 l2
      /\ Ceq_term t[/with_names_from c' l2/] x1 x2.
Proof. inversion 1; subst; eauto 10. Qed.

(* Peel a [Pceq_args] at a concrete rule context down to one [Ceq_term] per
   argument. *)
Ltac dargs H :=
  repeat (apply Pceq_args_cons_inv in H;
          let x1 := fresh "x" in
          let x2 := fresh "y" in
          let l1 := fresh "l" in
          let l2 := fresh "l" in
          let Hc := fresh "Hc" in
          destruct H as [x1 [x2 [l1 [l2 [? [? [H Hc]]]]]]]; subst);
  apply Pceq_args_nil_inv in H; destruct H as [? ?]; subst.

(* Peeling leaves every sort and term as an unevaluated substitution redex.
   Reducing them once, here, is what keeps the final [apply]s cheap and
   first-order (see the performance trap in WIP/stlc_norm_design.md). *)
Ltac norm_ceq :=
  repeat match goal with
    | [ H : Ceq_term ?t ?a ?b |- _ ] =>
        let t' := eval vm_compute in t in
        let a' := eval vm_compute in a in
        let b' := eval vm_compute in b in
        progress change_no_check (Ceq_term t' a' b') in H
    end;
  match goal with
  | [ |- Ceq_term ?t ?a ?b ] =>
      let t' := eval vm_compute in t in
      let a' := eval vm_compute in a in
      let b' := eval vm_compute in b in
      change_no_check (Ceq_term t' a' b')
  end.

(* ================================================================== *)
(* 1.  Reading [Ceq_term] clause by clause                             *)
(* ================================================================== *)

(* [Ceq_term] at [ty]/[env] forces syntactic equality, so the index arguments
   of a rule instance collapse; that is what makes the left-hand and
   right-hand sorts of an obligation agree. *)
Ltac ceq_prep :=
  repeat match goal with
    | [ H : Ceq_term Senv _ _ |- _ ] =>
        apply Ceq_env_e in H; destruct H as [? ?]; subst
    | [ H : Ceq_term Sty _ _ |- _ ] =>
        apply Ceq_ty_e in H; destruct H as [? ?]; subst
    end.

(* Expose the well-formedness of both sides of every remaining argument
   hypothesis, so that [wfa] can find them by [eassumption]. *)
Ltac ceq_wf :=
  repeat
    match goal with
    | [ H : Ceq_term (Ssub ?G ?G') ?a ?b |- _ ] =>
        assert_fails (assert (wft a (Ssub G G')) by assumption);
        pose proof (eqt_wf_l (proj1 (Ceq_sub_e H)));
        pose proof (eqt_wf_r (proj1 (Ceq_sub_e H)))
    | [ H : Ceq_term (Sval ?G ?A) ?a ?b |- _ ] =>
        assert_fails (assert (wft a (Sval G A)) by assumption);
        pose proof (eqt_wf_l (proj1 (Ceq_val_e H)));
        pose proof (eqt_wf_r (proj1 (Ceq_val_e H)))
    | [ H : Ceq_term (Sexp ?G ?A) ?a ?b |- _ ] =>
        assert_fails (assert (wft a (Sexp G A)) by assumption);
        pose proof (eqt_wf_l (proj1 (Ceq_exp_e H)));
        pose proof (eqt_wf_r (proj1 (Ceq_exp_e H)))
    end.

(* ================================================================== *)
(* 2.  Replacing the LEFT term by a provably equal one                 *)
(* ================================================================== *)

(* Both conjuncts of [Ceq_term] are invariant under provable equality of the
   left term: the equation by transitivity, the semantic conjunct because the
   substitution instance is a congruence.  Nine of the eighteen obligations
   are nothing but an instance of one of these three lemmas.  No [EnvOk]/
   [TyOk] hypothesis on the indices is needed: [RSub_wf]/[RSub_eq]/[RV_eq]
   (Gluing/StlcRSub.v, Gluing/StlcLogRel.v) are side-condition-free, and
   [wft_sub_inv]/[wft_val_inv]/[wft_exp_inv] (Gluing/StlcNormalForms.v)
   recover well-formedness of [G]/[G']/[A] straight from [Ha]. *)

Lemma Ceq_sub_left G G' a a' b
  : Ceq_term (Ssub G G') a' b -> eqt (Ssub G G') a a' -> Ceq_term (Ssub G G') a b.
Proof.
  intros Hab Ha.
  apply Ceq_sub_e in Hab as [Heq Hsem].
  assert (wft a (Ssub G G')) as Hwa by (eapply eqt_wf_l; eassumption).
  assert (wft a' (Ssub G G')) as Hwa' by (eapply eqt_wf_r; eassumption).
  destruct (@wft_sub_inv _ _ _ Hwa) as [HwG HwG'].
  apply ceq_sub.
  - eapply eq_term_trans; eassumption.
  - intros D h HD Hh.
    assert (wft h (Ssub D G)) as Hwh by (eapply RSub_wf; eassumption).
    eapply RSub_eq; [ exact (Hsem D h HD Hh) | ].
    apply cong_Cmp; [ wfa | wfa | wfa | apply eq_term_refl; wfa | ].
    apply eq_term_sym; exact Ha.
Qed.

Lemma Ceq_val_left G A a a' b
  : Ceq_term (Sval G A) a' b -> eqt (Sval G A) a a' -> Ceq_term (Sval G A) a b.
Proof.
  intros Hab Ha.
  apply Ceq_val_e in Hab as [Heq Hsem].
  assert (wft a (Sval G A)) as Hwa by (eapply eqt_wf_l; eassumption).
  assert (wft a' (Sval G A)) as Hwa' by (eapply eqt_wf_r; eassumption).
  destruct (@wft_val_inv _ _ _ Hwa) as [HwG HwA].
  apply ceq_val.
  - eapply eq_term_trans; eassumption.
  - intros D g HD Hg.
    assert (wft g (Ssub D G)) as Hwg by (eapply RSub_wf; eassumption).
    eapply RV_eq; [ exact (Hsem D g HD Hg) | ].
    apply cong_ValSubst; [ wfa | wfa | wfa | apply eq_term_refl; wfa | ].
    apply eq_term_sym; exact Ha.
Qed.

Lemma Ceq_exp_left G A a a' b
  : Ceq_term (Sexp G A) a' b -> eqt (Sexp G A) a a' -> Ceq_term (Sexp G A) a b.
Proof.
  intros Hab Ha.
  apply Ceq_exp_e in Hab as [Heq Hsem].
  assert (wft a (Sexp G A)) as Hwa by (eapply eqt_wf_l; eassumption).
  assert (wft a' (Sexp G A)) as Hwa' by (eapply eqt_wf_r; eassumption).
  destruct (@wft_exp_inv _ _ _ Hwa) as [HwG HwA].
  apply ceq_exp.
  - eapply eq_term_trans; eassumption.
  - intros D g HD Hg.
    assert (wft g (Ssub D G)) as Hwg by (eapply RSub_wf; eassumption).
    eapply RE_eq; [ exact (Hsem D g HD Hg) | ].
    apply cong_ExpSubst; [ wfa | wfa | wfa | apply eq_term_refl; wfa | ].
    apply eq_term_sym; exact Ha.
Qed.

(* ================================================================== *)
(* 3.  The semantic core                                               *)
(* ================================================================== *)

(* ---- application of two reducible expressions ---- *)

(* This is where Layer 1's [neet_lamapp] clause earns its keep: the middle
   case combines a function that is the [ret] of a reducible value with a
   NEUTRAL argument, and the result is stuck without being an application of
   a neutral. *)
Lemma RE_app G A B ef ea
  : RE G (Arr A B) ef -> RE G A ea -> EnvOk G -> TyOk A -> TyOk B ->
    RE G B (App G A B ef ea).
Proof.
  intros Hf Ha HG HA HB.
  assert (wft ef (Sexp G (Arr A B))) as Hwf by (eapply RE_wf; eassumption).
  assert (wft ea (Sexp G A)) as Hwa by (eapply RE_wf; eassumption).
  destruct (RE_cases Hf) as [[vf [Hvf Heqf]] | [nf [Hnf Heqf]]].
  - assert (wft vf (Sval G (Arr A B))) as Hwvf by (eapply RV_wf; eassumption).
    destruct (RE_cases Ha) as [[va [Hva Heqa]] | [na [Hna Heqa]]].
    + (* ret / ret : a genuine beta redex, handled by [RV_apply] *)
      assert (wft va (Sval G A)) as Hwva by (eapply RV_wf; eassumption).
      eapply RE_eq; [ eapply RV_apply; eassumption | ].
      apply cong_App; [ wfa | wfa | wfa | | ];
        apply eq_term_sym; assumption.
    + (* ret / neutral : stuck, [neet_lamapp] *)
      destruct (CR_reify Hvf) as [nv [Hnv Heqv]].
      assert (wft nv (Sval G (Arr A B))) as Hwnv by (eapply eqt_wf_r; eassumption).
      assert (wft na (Sexp G A)) as Hwna by (eapply eqt_wf_r; eassumption).
      eapply RE_ne with (n := App G A B (Ret G (Arr A B) nv) na);
        [ apply neet_lamapp; assumption | | assumption | assumption ].
      apply cong_App; [ wfa | wfa | wfa | | exact Heqa ].
      eapply eq_term_trans; [ exact Heqf | ].
      apply cong_Ret; [ wfa | wfa | exact Heqv ].
  - (* neutral function : stuck, [neet_app] *)
    destruct (CR_reify_E Ha) as [na [Hna Heqa]].
    assert (wft nf (Sexp G (Arr A B))) as Hwnf by (eapply eqt_wf_r; eassumption).
    assert (wft na (Sexp G A)) as Hwna by (eapply eqt_wf_r; eassumption).
    eapply RE_ne with (n := App G A B nf na);
      [ apply neet_app; assumption | | assumption | assumption ].
    apply cong_App; [ wfa | wfa | wfa | exact Heqf | exact Heqa ].
Qed.

(* ---- instantiating a lifted substitution ---- *)

(* [<id, u> o <wkn o g, hd> = <g, u>].  This is the equational heart of the
   two lambda cases: it is what turns "substitute under the binder, then beta"
   into "extend the substitution by the argument". *)
Lemma eq_lift_inst D G g A u
  : EnvOk D -> EnvOk G -> TyOk A -> wft g (Ssub D G) -> wft u (Sval D A) ->
    eqt (Ssub D (Ext G A))
      (Cmp D (Ext D A) (Ext G A)
         (Snoc D D (Id D) A u)
         (Snoc (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) g) A (Hd D A)))
      (Snoc D G g A u).
Proof.
  intros HD HG HA Hg Hu.
  eapply eq_term_trans; [ apply eq_cmp_snoc; wfa | ].
  apply cong_Snoc; [ wfa | wfa | wfa | | ].
  - eapply eq_term_trans; [ apply eq_cmp_assoc; wfa | ].
    eapply eq_term_trans;
      [ apply cong_Cmp;
        [ wfa | wfa | wfa | apply eq_wkn_snoc; wfa | apply eq_term_refl; wfa ]
      | ].
    apply eq_id_left; wfa.
  - apply eq_snoc_hd; wfa.
Qed.

(* Beta at a substituted lambda: [(g[lambda e]) u = e[<g,u>]]. *)
Lemma eq_beta_lift D G g A B u e
  : EnvOk D -> EnvOk G -> TyOk A -> TyOk B ->
    wft g (Ssub D G) -> wft u (Sval D A) -> wft e (Sexp (Ext G A) B) ->
    eqt (Sexp D B)
      (App D A B (Ret D (Arr A B) (ValSubst D G g (Arr A B) (Lam G A B e)))
         (Ret D A u))
      (ExpSubst D (Ext G A) (Snoc D G g A u) B e).
Proof.
  intros HD HG HA HB Hg Hu He.
  eapply eq_term_trans.
  { apply cong_App; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
    apply cong_Ret; [ wfa | wfa | apply eq_val_subst_lambda; wfa ]. }
  eapply eq_term_trans; [ apply eq_stlc_beta; wfa | ].
  eapply eq_term_trans; [ apply eq_exp_subst_cmp; wfa | ].
  apply cong_ExpSubst; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
  apply eq_lift_inst; wfa.
Qed.

(* ---- a substituted lambda is reducible ---- *)

(* The one place a substitution has to be pushed under a binder.  [RSub_lift]
   produces EXACTLY the substitution the [val_subst lambda] equation
   generates, which is why the normal-form half goes through unchanged. *)
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

(* ================================================================== *)
(* 4.  One lemma per equation                                          *)
(* ================================================================== *)

(* Naming convention: the [X1]/[Y1] pairs are the left- and right-hand values
   of an index argument.  [ceq_prep] identifies them; they are kept apart in
   the statements only because the obligation itself presents [e1] at [s1] and
   [e2]/[t] at [s2]. *)

(* ---- value_subst ---- *)

Lemma by_id_right X Y X' Y' f1 f2
  : Ceq_term (Ssub Y Y') f1 f2 ->
    Ceq_term Senv X' Y' -> Ceq_term Senv X Y ->
    Ceq_term (Ssub Y Y') (Cmp X X' X' f1 (Id X')) f2.
Proof.
  intros Hf HG' HG; ceq_prep; ceq_wf.
  eapply Ceq_sub_left; [ exact Hf | ].
  apply eq_id_right; wfa.
Qed.

Lemma by_id_left X Y X' Y' f1 f2
  : Ceq_term (Ssub Y Y') f1 f2 ->
    Ceq_term Senv X' Y' -> Ceq_term Senv X Y ->
    Ceq_term (Ssub Y Y') (Cmp X X X' (Id X) f1) f2.
Proof.
  intros Hf HG' HG; ceq_prep; ceq_wf.
  eapply Ceq_sub_left; [ exact Hf | ].
  apply eq_id_left; wfa.
Qed.

Lemma by_cmp_assoc X1 Y1 X2 Y2 X3 Y3 X4 Y4 f1 f2 g1 g2 h1 h2
  : Ceq_term (Ssub Y3 Y4) h1 h2 ->
    Ceq_term (Ssub Y2 Y3) g1 g2 ->
    Ceq_term (Ssub Y1 Y2) f1 f2 ->
    Ceq_term Senv X4 Y4 -> Ceq_term Senv X3 Y3 ->
    Ceq_term Senv X2 Y2 -> Ceq_term Senv X1 Y1 ->
    Ceq_term (Ssub Y1 Y4)
      (Cmp X1 X2 X4 f1 (Cmp X2 X3 X4 g1 h1))
      (Cmp Y1 Y3 Y4 (Cmp Y1 Y2 Y3 f2 g2) h2).
Proof.
  intros Hh Hg Hf H4 H3 H2 H1; ceq_prep; ceq_wf.
  apply ceq_sub.
  - eapply eq_term_trans;
      [ apply cong_Cmp;
        [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hf)) | ]
      | apply eq_cmp_assoc; wfa ].
    apply cong_Cmp;
      [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hg)) | apply (proj1 (Ceq_sub_e Hh)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y1)) as Hwk by (eapply RSub_wf; eassumption).
    assert (RSub D Y2 (Cmp D Y1 Y2 k f1)) as K1
        by (eapply (proj2 (Ceq_sub_e Hf)); eassumption).
    assert (wft (Cmp D Y1 Y2 k f1) (Ssub D Y2)) as Hw1 by wfa.
    assert (RSub D Y3 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1)) as K2
        by (eapply (proj2 (Ceq_sub_e Hg)); eassumption).
    assert (wft (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1) (Ssub D Y3)) as Hw2 by wfa.
    assert (RSub D Y4
              (Cmp D Y3 Y4 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1) h1)) as K3
        by (eapply (proj2 (Ceq_sub_e Hh)); eassumption).
    eapply RSub_eq; [ exact K3 | ].
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_cmp_assoc; wfa | ].
    apply eq_cmp_assoc; wfa.
Qed.

Lemma by_val_subst_id X Y A1 A2 v1 v2
  : Ceq_term (Sval Y A2) v1 v2 -> Ceq_term Sty A1 A2 -> Ceq_term Senv X Y ->
    Ceq_term (Sval Y A2) (ValSubst X X (Id X) A1 v1) v2.
Proof.
  intros Hv HA HG; ceq_prep; ceq_wf.
  eapply Ceq_val_left; [ exact Hv | ].
  apply eq_val_subst_id; wfa.
Qed.

Lemma by_val_subst_cmp X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2 A1 A2 v1 v2
  : Ceq_term (Sval Y3 A2) v1 v2 ->
    Ceq_term Sty A1 A2 ->
    Ceq_term (Ssub Y2 Y3) g1 g2 ->
    Ceq_term (Ssub Y1 Y2) f1 f2 ->
    Ceq_term Senv X3 Y3 -> Ceq_term Senv X2 Y2 -> Ceq_term Senv X1 Y1 ->
    Ceq_term (Sval Y1 A2)
      (ValSubst X1 X2 f1 A1 (ValSubst X2 X3 g1 A1 v1))
      (ValSubst Y1 Y3 (Cmp Y1 Y2 Y3 f2 g2) A2 v2).
Proof.
  intros Hv HA Hg Hf H3 H2 H1; ceq_prep; ceq_wf.
  apply ceq_val.
  - eapply eq_term_trans;
      [ apply cong_ValSubst;
        [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hf)) | ]
      | apply eq_val_subst_cmp; wfa ].
    apply cong_ValSubst;
      [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hg)) | apply (proj1 (Ceq_val_e Hv)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y1)) as Hwk by (eapply RSub_wf; eassumption).
    assert (RSub D Y2 (Cmp D Y1 Y2 k f1)) as K1
        by (eapply (proj2 (Ceq_sub_e Hf)); eassumption).
    assert (wft (Cmp D Y1 Y2 k f1) (Ssub D Y2)) as Hw1 by wfa.
    assert (RSub D Y3 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1)) as K2
        by (eapply (proj2 (Ceq_sub_e Hg)); eassumption).
    assert (wft (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1) (Ssub D Y3)) as Hw2 by wfa.
    assert (RV D A2
              (ValSubst D Y3 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1) A2 v1)) as HV
        by (eapply (proj2 (Ceq_val_e Hv)); eassumption).
    eapply RV_eq; [ exact HV | ].
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_val_subst_cmp; wfa | ].
    apply eq_val_subst_cmp; wfa.
Qed.

Lemma by_cmp_forget X Y X' Y' g1 g2
  : Ceq_term (Ssub Y Y') g1 g2 ->
    Ceq_term Senv X' Y' -> Ceq_term Senv X Y ->
    Ceq_term (Ssub Y Emp) (Cmp X X' Emp g1 (Forget X')) (Forget Y).
Proof.
  intros Hg HG' HG; ceq_prep; ceq_wf.
  apply ceq_sub.
  - apply eq_cmp_forget; wfa.
  - intros D h HD Hh.
    assert (wft h (Ssub D Y)) as Hwh by (eapply RSub_wf; eassumption).
    apply RSub_emp_intro.
    eapply eq_term_trans; [ apply eq_cmp_assoc; wfa | ].
    apply eq_cmp_forget; wfa.
Qed.

Lemma by_id_emp_forget : Ceq_term (Ssub Emp Emp) (Id Emp) (Forget Emp).
Proof.
  apply ceq_sub.
  - apply eq_id_emp_forget.
  - intros D h HD Hh.
    assert (EnvOk Emp) as HE by constructor.
    assert (wft h (Ssub D Emp)) as Hwh by (eapply RSub_wf; eassumption).
    eapply RSub_eq; [ exact Hh | ].
    apply eq_term_sym; apply eq_id_right; wfa.
Qed.

Lemma by_wkn_snoc X Y X' Y' g1 g2 A1 A2 v1 v2
  : Ceq_term (Sval Y A2) v1 v2 ->
    Ceq_term Sty A1 A2 ->
    Ceq_term (Ssub Y Y') g1 g2 ->
    Ceq_term Senv X' Y' -> Ceq_term Senv X Y ->
    Ceq_term (Ssub Y Y')
      (Cmp X (Ext X' A1) X' (Snoc X X' g1 A1 v1) (Wkn X' A1)) g2.
Proof.
  intros Hv HA Hg HG' HG; ceq_prep; ceq_wf.
  eapply Ceq_sub_left; [ exact Hg | ].
  apply eq_wkn_snoc; wfa.
Qed.

Lemma by_snoc_hd X Y X' Y' g1 g2 A1 A2 v1 v2
  : Ceq_term (Sval Y A2) v1 v2 ->
    Ceq_term Sty A1 A2 ->
    Ceq_term (Ssub Y Y') g1 g2 ->
    Ceq_term Senv X' Y' -> Ceq_term Senv X Y ->
    Ceq_term (Sval Y A2)
      (ValSubst X (Ext X' A1) (Snoc X X' g1 A1 v1) A1 (Hd X' A1)) v2.
Proof.
  intros Hv HA Hg HG' HG; ceq_prep; ceq_wf.
  eapply Ceq_val_left; [ exact Hv | ].
  apply eq_snoc_hd; wfa.
Qed.

Lemma by_cmp_snoc X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2 A1 A2 v1 v2
  : Ceq_term (Sval Y2 A2) v1 v2 ->
    Ceq_term Sty A1 A2 ->
    Ceq_term (Ssub Y2 Y3) g1 g2 ->
    Ceq_term (Ssub Y1 Y2) f1 f2 ->
    Ceq_term Senv X3 Y3 -> Ceq_term Senv X2 Y2 -> Ceq_term Senv X1 Y1 ->
    Ceq_term (Ssub Y1 (Ext Y3 A2))
      (Cmp X1 X2 (Ext X3 A1) f1 (Snoc X2 X3 g1 A1 v1))
      (Snoc Y1 Y3 (Cmp Y1 Y2 Y3 f2 g2) A2 (ValSubst Y1 Y2 f2 A2 v2)).
Proof.
  intros Hv HA Hg Hf H3 H2 H1; ceq_prep; ceq_wf.
  apply ceq_sub.
  - eapply eq_term_trans;
      [ apply cong_Cmp;
        [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hf)) | ]
      | apply eq_cmp_snoc; wfa ].
    apply cong_Snoc;
      [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hg)) | apply (proj1 (Ceq_val_e Hv)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y1)) as Hwk by (eapply RSub_wf; eassumption).
    assert (RSub D Y2 (Cmp D Y1 Y2 k f1)) as K1
        by (eapply (proj2 (Ceq_sub_e Hf)); eassumption).
    assert (wft (Cmp D Y1 Y2 k f1) (Ssub D Y2)) as Hw1 by wfa.
    assert (RSub D Y3 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1)) as K2
        by (eapply (proj2 (Ceq_sub_e Hg)); eassumption).
    assert (RV D A2 (ValSubst D Y2 (Cmp D Y1 Y2 k f1) A2 v1)) as HV
        by (eapply (proj2 (Ceq_val_e Hv)); eassumption).
    assert (RSub D (Ext Y3 A2)
              (Snoc D Y3 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1) A2
                 (ValSubst D Y2 (Cmp D Y1 Y2 k f1) A2 v1))) as HS
        by (apply RSub_ext; assumption).
    eapply RSub_eq; [ exact HS | ].
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_cmp_assoc; wfa | ].
    apply eq_cmp_snoc; wfa.
Qed.

Lemma by_snoc_wkn_hd X Y A1 A2
  : Ceq_term Sty A1 A2 -> Ceq_term Senv X Y ->
    Ceq_term (Ssub (Ext Y A2) (Ext Y A2))
      (Snoc (Ext X A1) X (Wkn X A1) A1 (Hd X A1)) (Id (Ext Y A2)).
Proof.
  intros HA HG; ceq_prep; ceq_wf.
  apply ceq_sub.
  - apply eq_snoc_wkn_hd; wfa.
  - intros D h HD Hh.
    assert (EnvOk (Ext Y A2)) as HYA by (constructor; assumption).
    assert (wft h (Ssub D (Ext Y A2))) as Hwh by (eapply RSub_wf; eassumption).
    eapply RSub_eq; [ exact Hh | ].
    apply eq_term_sym.
    eapply eq_term_trans;
      [ apply cong_Cmp;
        [ wfa | wfa | wfa | apply eq_term_refl; wfa | apply eq_snoc_wkn_hd; wfa ]
      | ].
    apply eq_id_right; wfa.
Qed.

(* ---- exp_subst ---- *)

Lemma by_exp_subst_id X Y A1 A2 e1 e2
  : Ceq_term (Sexp Y A2) e1 e2 -> Ceq_term Sty A1 A2 -> Ceq_term Senv X Y ->
    Ceq_term (Sexp Y A2) (ExpSubst X X (Id X) A1 e1) e2.
Proof.
  intros He HA HG; ceq_prep; ceq_wf.
  eapply Ceq_exp_left; [ exact He | ].
  apply eq_exp_subst_id; wfa.
Qed.

Lemma by_exp_subst_cmp X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2 A1 A2 e1 e2
  : Ceq_term (Sexp Y3 A2) e1 e2 ->
    Ceq_term Sty A1 A2 ->
    Ceq_term (Ssub Y2 Y3) g1 g2 ->
    Ceq_term (Ssub Y1 Y2) f1 f2 ->
    Ceq_term Senv X3 Y3 -> Ceq_term Senv X2 Y2 -> Ceq_term Senv X1 Y1 ->
    Ceq_term (Sexp Y1 A2)
      (ExpSubst X1 X2 f1 A1 (ExpSubst X2 X3 g1 A1 e1))
      (ExpSubst Y1 Y3 (Cmp Y1 Y2 Y3 f2 g2) A2 e2).
Proof.
  intros He HA Hg Hf H3 H2 H1; ceq_prep; ceq_wf.
  apply ceq_exp.
  - eapply eq_term_trans;
      [ apply cong_ExpSubst;
        [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hf)) | ]
      | apply eq_exp_subst_cmp; wfa ].
    apply cong_ExpSubst;
      [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hg)) | apply (proj1 (Ceq_exp_e He)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y1)) as Hwk by (eapply RSub_wf; eassumption).
    assert (RSub D Y2 (Cmp D Y1 Y2 k f1)) as K1
        by (eapply (proj2 (Ceq_sub_e Hf)); eassumption).
    assert (wft (Cmp D Y1 Y2 k f1) (Ssub D Y2)) as Hw1 by wfa.
    assert (RSub D Y3 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1)) as K2
        by (eapply (proj2 (Ceq_sub_e Hg)); eassumption).
    assert (wft (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1) (Ssub D Y3)) as Hw2 by wfa.
    assert (RE D A2
              (ExpSubst D Y3 (Cmp D Y2 Y3 (Cmp D Y1 Y2 k f1) g1) A2 e1)) as HE
        by (eapply (proj2 (Ceq_exp_e He)); eassumption).
    eapply RE_eq; [ exact HE | ].
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_exp_subst_cmp; wfa | ].
    apply eq_exp_subst_cmp; wfa.
Qed.

Lemma by_exp_subst_ret X Y X' Y' g1 g2 A1 A2 v1 v2
  : Ceq_term (Ssub Y' Y) g1 g2 ->
    Ceq_term Senv X' Y' ->
    Ceq_term (Sval Y A2) v1 v2 ->
    Ceq_term Sty A1 A2 ->
    Ceq_term Senv X Y ->
    Ceq_term (Sexp Y' A2)
      (ExpSubst X' X g1 A1 (Ret X A1 v1))
      (Ret Y' A2 (ValSubst Y' Y g2 A2 v2)).
Proof.
  intros Hg HG' Hv HA HG; ceq_prep; ceq_wf.
  apply ceq_exp.
  - eapply eq_term_trans; [ apply eq_exp_subst_ret; wfa | ].
    apply cong_Ret; [ wfa | wfa | ].
    apply cong_ValSubst;
      [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hg)) | apply (proj1 (Ceq_val_e Hv)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y')) as Hwk by (eapply RSub_wf; eassumption).
    assert (RSub D Y (Cmp D Y' Y k g1)) as K1
        by (eapply (proj2 (Ceq_sub_e Hg)); eassumption).
    assert (wft (Cmp D Y' Y k g1) (Ssub D Y)) as Hw1 by wfa.
    assert (RV D A2 (ValSubst D Y (Cmp D Y' Y k g1) A2 v1)) as HV
        by (eapply (proj2 (Ceq_val_e Hv)); eassumption).
    eapply RE_ret; [ exact HV | | assumption | assumption ].
    eapply eq_term_trans; [ apply eq_exp_subst_cmp; wfa | ].
    apply eq_exp_subst_ret; wfa.
Qed.

(* ---- stlc ---- *)

Lemma by_exp_subst_app X Y X' Y' g1 g2 A1 A2 B1 B2 ef1 ef2 ea1 ea2
  : Ceq_term (Ssub Y' Y) g1 g2 ->
    Ceq_term Senv X' Y' ->
    Ceq_term (Sexp Y A2) ea1 ea2 ->
    Ceq_term (Sexp Y (Arr A2 B2)) ef1 ef2 ->
    Ceq_term Sty B1 B2 -> Ceq_term Sty A1 A2 -> Ceq_term Senv X Y ->
    Ceq_term (Sexp Y' B2)
      (ExpSubst X' X g1 B1 (App X A1 B1 ef1 ea1))
      (App Y' A2 B2 (ExpSubst Y' Y g2 (Arr A2 B2) ef2)
         (ExpSubst Y' Y g2 A2 ea2)).
Proof.
  intros Hg HG' Hea Hef HB HA HG; ceq_prep; ceq_wf.
  apply ceq_exp.
  - eapply eq_term_trans; [ apply eq_exp_subst_app; wfa | ].
    apply cong_App; [ wfa | wfa | wfa | | ].
    + apply cong_ExpSubst;
        [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hg)) | apply (proj1 (Ceq_exp_e Hef)) ].
    + apply cong_ExpSubst;
        [ wfa | wfa | wfa | apply (proj1 (Ceq_sub_e Hg)) | apply (proj1 (Ceq_exp_e Hea)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y')) as Hwk by (eapply RSub_wf; eassumption).
    assert (RSub D Y (Cmp D Y' Y k g1)) as K1
        by (eapply (proj2 (Ceq_sub_e Hg)); eassumption).
    assert (wft (Cmp D Y' Y k g1) (Ssub D Y)) as Hw1 by wfa.
    assert (RE D (Arr A2 B2)
              (ExpSubst D Y (Cmp D Y' Y k g1) (Arr A2 B2) ef1)) as HF
        by (eapply (proj2 (Ceq_exp_e Hef)); eassumption).
    assert (RE D A2 (ExpSubst D Y (Cmp D Y' Y k g1) A2 ea1)) as HA'
        by (eapply (proj2 (Ceq_exp_e Hea)); eassumption).
    assert (RE D B2
              (App D A2 B2 (ExpSubst D Y (Cmp D Y' Y k g1) (Arr A2 B2) ef1)
                 (ExpSubst D Y (Cmp D Y' Y k g1) A2 ea1))) as HR
        by (apply RE_app; assumption).
    eapply RE_eq; [ exact HR | ].
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_exp_subst_cmp; wfa | ].
    apply eq_exp_subst_app; wfa.
Qed.

Lemma by_val_subst_lambda X Y X' Y' g1 g2 A1 A2 B1 B2 e1 e2
  : Ceq_term (Ssub Y' Y) g1 g2 ->
    Ceq_term Senv X' Y' ->
    Ceq_term (Sexp (Ext Y A2) B2) e1 e2 ->
    Ceq_term Sty B1 B2 -> Ceq_term Sty A1 A2 -> Ceq_term Senv X Y ->
    Ceq_term (Sval Y' (Arr A2 B2))
      (ValSubst X' X g1 (Arr A1 B1) (Lam X A1 B1 e1))
      (Lam Y' A2 B2
         (ExpSubst (Ext Y' A2) (Ext Y A2)
            (Snoc (Ext Y' A2) Y (Cmp (Ext Y' A2) Y' Y (Wkn Y' A2) g2) A2
               (Hd Y' A2))
            B2 e2)).
Proof.
  intros Hg HG' He HB HA HG; ceq_prep; ceq_wf.
  assert (EnvOk (Ext Y A2)) as HYA by (constructor; assumption).
  assert (EnvOk (Ext Y' A2)) as HYA' by (constructor; assumption).
  apply ceq_val.
  - eapply eq_term_trans; [ apply eq_val_subst_lambda; wfa | ].
    apply cong_Lam; [ wfa | wfa | wfa | ].
    apply cong_ExpSubst; [ wfa | wfa | wfa | | apply (proj1 (Ceq_exp_e He)) ].
    apply cong_Snoc; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
    apply cong_Cmp;
      [ wfa | wfa | wfa | apply eq_term_refl; wfa | apply (proj1 (Ceq_sub_e Hg)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y')) as Hwk by (eapply RSub_wf; eassumption).
    assert (RSub D Y (Cmp D Y' Y k g1)) as K1
        by (eapply (proj2 (Ceq_sub_e Hg)); eassumption).
    assert (wft (Cmp D Y' Y k g1) (Ssub D Y)) as Hw1 by wfa.
    assert (RV D (Arr A2 B2)
              (ValSubst D Y (Cmp D Y' Y k g1) (Arr A2 B2) (Lam Y A2 B2 e1)))
      as HV
        by (apply RV_lam_sub;
            [ intros D' m HD' Hm; eapply (proj2 (Ceq_exp_e He)); eassumption
            | assumption .. ]).
    eapply RV_eq; [ exact HV | ].
    apply eq_term_sym.
    apply eq_val_subst_cmp; wfa.
Qed.

Lemma by_stlc_beta X Y A1 A2 B1 B2 e1 e2 v1 v2
  : Ceq_term (Sval Y A2) v1 v2 ->
    Ceq_term (Sexp (Ext Y A2) B2) e1 e2 ->
    Ceq_term Sty B1 B2 -> Ceq_term Sty A1 A2 -> Ceq_term Senv X Y ->
    Ceq_term (Sexp Y B2)
      (App X A1 B1 (Ret X (Arr A1 B1) (Lam X A1 B1 e1)) (Ret X A1 v1))
      (ExpSubst Y (Ext Y A2) (Snoc Y Y (Id Y) A2 v2) B2 e2).
Proof.
  intros Hv He HB HA HG; ceq_prep; ceq_wf.
  assert (EnvOk (Ext Y A2)) as HYA by (constructor; assumption).
  apply ceq_exp.
  - eapply eq_term_trans; [ | apply eq_stlc_beta; wfa ].
    apply cong_App; [ wfa | wfa | wfa | | ].
    + apply cong_Ret; [ wfa | wfa | ].
      apply cong_Lam; [ wfa | wfa | wfa | apply (proj1 (Ceq_exp_e He)) ].
    + apply cong_Ret; [ wfa | wfa | apply (proj1 (Ceq_val_e Hv)) ].
  - intros D k HD Hk.
    assert (wft k (Ssub D Y)) as Hwk by (eapply RSub_wf; eassumption).
    assert (RV D A2 (ValSubst D Y k A2 v1)) as HV
        by (eapply (proj2 (Ceq_val_e Hv)); eassumption).
    assert (wft (ValSubst D Y k A2 v1) (Sval D A2)) as Hwu by wfa.
    assert (RSub D (Ext Y A2) (Snoc D Y k A2 (ValSubst D Y k A2 v1))) as HS
        by (apply RSub_ext; assumption).
    assert (RE D B2
              (ExpSubst D (Ext Y A2) (Snoc D Y k A2 (ValSubst D Y k A2 v1))
                 B2 e1)) as HE
        by (eapply (proj2 (Ceq_exp_e He)); eassumption).
    eapply RE_eq; [ exact HE | ].
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_exp_subst_app; wfa | ].
    eapply eq_term_trans.
    { apply cong_App; [ wfa | wfa | wfa | | ];
        apply eq_exp_subst_ret; wfa. }
    apply eq_beta_lift; wfa.
Qed.

(* ---- unit ---- *)

Lemma by_val_subst_tt X Y X' Y' g1 g2
  : Ceq_term (Ssub Y' Y) g1 g2 ->
    Ceq_term Senv X' Y' -> Ceq_term Senv X Y ->
    Ceq_term (Sval Y' Unit) (ValSubst X' X g1 Unit (Tt X)) (Tt Y').
Proof.
  intros Hg HG' HG; ceq_prep; ceq_wf.
  apply ceq_val.
  - apply eq_val_subst_tt; wfa.
  - intros D k HD Hk.
    assert (wft k (Ssub D Y')) as Hwk by (eapply RSub_wf; eassumption).
    apply RV_unit.
    exists (Tt D); split; [ apply nfvt_tt | ].
    eapply eq_term_trans; [ apply eq_val_subst_cmp; wfa | ].
    apply eq_val_subst_tt; wfa.
Qed.

(* ================================================================== *)
(* 5.  Decomposing rule membership                                     *)
(* ================================================================== *)

(* Performance note (see WIP/stlc_norm_design.md, "Traps").  A driver that
   leaves [named_list_lookup_err stlc_unit name] unreduced costs tens of
   seconds per [apply].  Here the name is first pinned down by case analysis
   on [map fst stlc_unit] -- a list of 39 strings, so the disjunction stays
   small -- and only then is the lookup [vm_compute]d, once, at a concrete
   name. *)

Lemma stlc_unit_all_fresh : all_fresh stlc_unit.
Proof. eapply wf_lang_ext_all_fresh; exact stlc_unit_wf. Qed.

Lemma stlc_unit_lookup (name : string) r
  : In (name, r) stlc_unit -> Some r = named_list_lookup_err stlc_unit name.
Proof.
  intro H; apply all_fresh_named_list_lookup_err_in;
    [ typeclasses eauto | exact stlc_unit_all_fresh | exact H ].
Qed.

(* ================================================================== *)
(* 6.  The obligation                                                  *)
(* ================================================================== *)

Lemma by_obligation
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) stlc_unit ->
    ceq_args (CM := StlcCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
      e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hargs.
  apply ceq_args_Pceq_args in Hargs.
  pose proof (stlc_unit_lookup Hin) as Hl.
  apply pair_fst_in in Hin.
  vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]);
    try contradiction;
    subst name;
    vm_compute in Hl;
    try discriminate Hl;
    inversion Hl; subst; clear Hl;
    dargs Hargs;
    norm_ceq.
  all: solve
         [ apply by_id_right; assumption
         | apply by_id_left; assumption
         | apply by_cmp_assoc; assumption
         | apply by_val_subst_id; assumption
         | apply by_val_subst_cmp; assumption
         | apply by_cmp_forget; assumption
         | apply by_id_emp_forget
         | apply by_wkn_snoc; assumption
         | apply by_snoc_hd; assumption
         | apply by_cmp_snoc; assumption
         | apply by_snoc_wkn_hd; assumption
         | apply by_exp_subst_id; assumption
         | apply by_exp_subst_cmp; assumption
         | apply by_exp_subst_ret; assumption
         | apply by_exp_subst_app; assumption
         | apply by_val_subst_lambda; assumption
         | apply by_stlc_beta; assumption
         | apply by_val_subst_tt; assumption
         (* the four rules below leave an index of the equation unconstrained
            by the conclusion (e.g. [cmp_forget]'s intermediate environment),
            so the instance has to be read off the hypotheses. *)
         | eapply by_cmp_forget; eassumption
         | eapply by_wkn_snoc; eassumption
         | eapply by_snoc_hd; eassumption
         | eapply by_val_subst_tt; eassumption ].
Qed.

(* Sanity check: this is literally the [cterm_by] field of
   [CutTModel_ok stlc_unit [] (CM := StlcCM)], so the file that assembles the
   instance can plug [by_obligation] straight in. *)
Definition by_obligation_is_cterm_by
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) stlc_unit ->
    ceq_args (CM := StlcCM) c' s1 s2 ->
    ceq_term (CutTModel := StlcCM) t[/with_names_from c' s2/]
      e1[/with_names_from c' s1/] e2[/with_names_from c' s2/]
  := by_obligation.
