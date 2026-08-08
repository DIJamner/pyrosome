Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
From Pyrosome.Gluing.Stlc Require Import Syntax Normalization NormalForms Eqns LogRel RSub SemCore Ceq.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC SimpleUnit.
Import Core.Notations.

(* Layer 4b: the STRUCTURAL half of [CutTModel_ok] for [stlc_unit], [c := []],
   [CM := StlcCM].

   Each field of the class is proved here as a standalone top-level lemma; a
   separate file assembles the [Instance] (the [cterm_by] half -- the 18
   equation instances -- is developed independently).

   Everything goes through the constructors and clause lemmas of
   Gluing/Stlc/Ceq.v ([ceq_ty] ... [ceq_exp], [Ceq_ty_e] ... [Ceq_exp_e]);
   [Ceq_term] is never inverted by hand outside of those five lemmas, and
   [RVarr] is never unfolded either.  The two obligations with real semantic
   content -- [lambda] and [app] -- lean on [RV_lam]/[RE_app] from
   Gluing/Stlc/SemCore.v, which is also what [ModelEq.v]'s equation
   obligations reduce to. *)

Local Notation eqt := (eq_term stlc_unit []).
Local Notation wft := (wf_term stlc_unit []).

(* ================================================================== *)
(* 1.  Decomposing the rule-membership hypothesis                      *)
(* ================================================================== *)

(* The language is a closed 39-element list, so [In] is a concrete
   disjunction.  Pinning it with [vm_compute] first is what keeps this cheap:
   left unreduced, each rule instance costs ~35s at [apply] time, and
   [with_rule_in_wf_crush] does not terminate on this language at all. *)

Ltac nrm :=
  repeat match goal with
  | [ H : Ceq_term ?t ?a ?b |- _ ] =>
      let t' := eval vm_compute in t in
      tryif constr_eq t t' then fail else change_no_check (Ceq_term t' a b) in H
  | [ |- Ceq_term ?t ?a ?b ] =>
      let t' := eval vm_compute in t in
      tryif constr_eq t t' then fail else change_no_check (Ceq_term t' a b)
  end.

Ltac decomp :=
  match goal with
  | [ Hin : In _ stlc_unit |- _ ] =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin|Hin]); try discriminate;
      inversion Hin; subst; clear Hin
  end;
  repeat match goal with
         | [ H : ceq_args (_::_) _ _ |- _ ] => inversion H; subst; clear H
         | [ H : ceq_args [] _ _ |- _ ] => inversion H; subst; clear H
         end;
  cbn [ceq_term ceq_sort StlcCM] in *; nrm.

(* Every index argument of every rule is at [ty] or [env], where [Ceq_term]
   forces syntactic equality; discharging those first collapses the two
   argument lists. *)
Ltac ceq_ty_env :=
  repeat match goal with
  | [ H : Ceq_term _ _ _ |- _ ] =>
      first [ apply Ceq_ty_e in H | apply Ceq_env_e in H ];
      destruct H as [? ?]; subst
  end.

(* ================================================================== *)
(* 2.  The obligations                                                 *)
(* ================================================================== *)

(* [cterm_var]: the ambient meta-context is empty (openness is object-level),
   so there are no variables to relate. *)
Lemma var_obligation
  : forall n t, In (n, t) (@nil (string * sort)) -> Ceq_term t (var n) (var n).
Proof. intros n t H; destruct H. Qed.

(* [csort_by]: [stlc_unit] has no sort equations at all. *)
Lemma sort_by_obligation
  : forall c' name t1 t2 s1 s2,
    In (name, sort_eq_rule c' t1 t2) stlc_unit ->
    ceq_args (CM := StlcCM) c' s1 s2 ->
    Ceq_sort t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
Proof.
  intros c' name t1 t2 s1 s2 Hin Hargs.
  vm_compute in Hin; repeat (destruct Hin as [Hin|Hin]);
    first [ discriminate | destruct Hin ].
Qed.

(* [csort_cong]: every sort rule's context consists of [ty]/[env] entries
   only, so the two argument lists are syntactically equal. *)
Lemma sort_cong_obligation
  : forall c' name args s1 s2,
    In (name, sort_rule c' args) stlc_unit ->
    ceq_args (CM := StlcCM) c' s1 s2 ->
    Ceq_sort (scon name s1) (scon name s2).
Proof.
  intros c' name args s1 s2 Hin Hargs.
  decomp; ceq_ty_env; reflexivity.
Qed.

Lemma sort_trans_obligation
  : forall t1 t12 t2, Ceq_sort t1 t12 -> Ceq_sort t12 t2 -> Ceq_sort t1 t2.
Proof. unfold Ceq_sort; intros t1 t12 t2 H1 H2; etransitivity; eassumption. Qed.

Lemma sort_sym_obligation : forall t1 t2, Ceq_sort t1 t2 -> Ceq_sort t2 t1.
Proof. unfold Ceq_sort; intros t1 t2 H; symmetry; exact H. Qed.

Lemma term_conv_obligation
  : forall t1 t2 e1 e2, Ceq_sort t1 t2 -> Ceq_term t1 e1 e2 -> Ceq_term t2 e1 e2.
Proof. unfold Ceq_sort; intros t1 t2 e1 e2 Ht H; subst; exact H. Qed.

Lemma term_trans_obligation
  : forall t e1 e12 e2, Ceq_term t e1 e12 -> Ceq_term t e12 e2 -> Ceq_term t e1 e2.
Proof.
  intros t e1 e12 e2 H1 H2; destruct H1.
  - apply Ceq_ty_e in H2 as [<- ?]; apply ceq_ty; assumption.
  - apply Ceq_env_e in H2 as [<- ?]; apply ceq_env; assumption.
  - apply Ceq_sub_e in H2 as [Hc _]; apply ceq_sub; [ eapply eq_term_trans; eassumption | assumption ].
  - apply Ceq_val_e in H2 as [Hc _]; apply ceq_val; [ eapply eq_term_trans; eassumption | assumption ].
  - apply Ceq_exp_e in H2 as [Hc _]; apply ceq_exp; [ eapply eq_term_trans; eassumption | assumption ].
Qed.

(* The semantic conjunct of every clause constrains only the LEFT term; the
   corresponding fact for the right one is recovered by transporting along the
   equation, via [RSub_eq]/[RV_eq] (Gluing/Stlc/RSub.v, Gluing/Stlc/LogRel.v).
   Both are side-condition-free, which is exactly what this obligation needs:
   its hypothesis constrains only the left-hand term, so nothing here supplies
   [EnvOk]/[TyOk] for the sort's indices, only their well-formedness. *)
Lemma term_sym_obligation
  : forall t e1 e2, Ceq_term t e1 e2 -> Ceq_term t e2 e1.
Proof.
  intros t e1 e2 H; destruct H as [ A HA | G HG
                                   | G G' g1 g2 Ha Hb
                                   | G A v1 v2 Ha Hb
                                   | G A e1 e2 Ha Hb ].
  - apply ceq_ty; assumption.
  - apply ceq_env; assumption.
  - assert (wft g1 (Ssub G G')) as Hw1 by (eapply eqt_wf_l; eassumption).
    destruct (@wft_sub_inv _ _ _ Hw1) as [HwG HwG'].
    apply ceq_sub; [ apply eq_term_sym; exact Ha | ].
    intros D h HD Hh.
    assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
    assert (wft h (Ssub D G)) as Hwh by (apply RSub_wf; assumption).
    apply RSub_eq with (g := Cmp D G G' h g1); [ apply Hb; assumption | ].
    apply cong_Cmp;
      [ assumption | assumption | assumption
      | apply eq_term_refl; assumption | exact Ha ].
  - assert (wft v1 (Sval G A)) as Hw1 by (eapply eqt_wf_l; eassumption).
    destruct (@wft_val_inv _ _ _ Hw1) as [HwG HwA].
    apply ceq_val; [ apply eq_term_sym; exact Ha | ].
    intros D g HD Hg.
    assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
    assert (wft g (Ssub D G)) as Hwg by (apply RSub_wf; assumption).
    apply RV_eq with (v := ValSubst D G g A v1); [ apply Hb; assumption | ].
    apply cong_ValSubst;
      [ assumption | assumption | assumption
      | apply eq_term_refl; assumption | exact Ha ].
  - assert (wft e1 (Sexp G A)) as Hw1 by (eapply eqt_wf_l; eassumption).
    destruct (@wft_exp_inv _ _ _ Hw1) as [HwG HwA].
    apply ceq_exp; [ apply eq_term_sym; exact Ha | ].
    intros D g HD Hg.
    assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
    assert (wft g (Ssub D G)) as Hwg by (apply RSub_wf; assumption).
    apply RE_eq with (e := ExpSubst D G g A e1); [ apply Hb; assumption | ].
    apply cong_ExpSubst;
      [ assumption | assumption | assumption
      | apply eq_term_refl; assumption | exact Ha ].
Qed.

(* [cterm_cong]: the 16 term constructors of [stlc_unit].
   The goals come out in the language's own order:
     app, lambda, ->, tt, unit, ret, exp_subst, hd, wkn, snoc,
     ext, forget, emp, val_subst, cmp, id. *)
Lemma cong_obligation
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) stlc_unit ->
    ceq_args (CM := StlcCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hargs.
  decomp; ceq_ty_env.
  - (* app *)
    apply Ceq_exp_e in X0 as [Heq1 Hsem1].
    apply Ceq_exp_e in X2 as [Heq2 Hsem2].
    assert (wft e9 Senv) as Hw9 by (apply EnvOk_wf; assumption).
    assert (wft e7 Sty) as Hw7 by (apply TyOk_wf; assumption).
    assert (wft e5 Sty) as Hw5 by (apply TyOk_wf; assumption).
    assert (wft e0 (Sexp e9 (Arr e7 e5))) as Hwe0 by (eapply eqt_wf_l; eassumption).
    assert (wft e1 (Sexp e9 e7)) as Hwe1 by (eapply eqt_wf_l; eassumption).
    apply ceq_exp.
    + apply cong_App; [ wfa | wfa | wfa | exact Heq2 | exact Heq1 ].
    + intros D g HD Hg.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft g (Ssub D e9)) as Hwg by (apply RSub_wf; assumption).
      apply RE_eq with (e := App D e7 e5 (ExpSubst D e9 g (Arr e7 e5) e0)
                                         (ExpSubst D e9 g e7 e1)).
      * apply RE_app;
          [ assumption | assumption | assumption
          | apply Hsem2; assumption | apply Hsem1; assumption ].
      * apply eq_term_sym; apply eq_exp_subst_app; wfa.
  - (* lambda *)
    apply Ceq_exp_e in X0 as [Heq1 Hsem1].
    assert (wft e7 Senv) as Hw7 by (apply EnvOk_wf; assumption).
    assert (wft e5 Sty) as Hw5 by (apply TyOk_wf; assumption).
    assert (wft e3 Sty) as Hw3 by (apply TyOk_wf; assumption).
    assert (wft e1 (Sexp (Ext e7 e5) e3)) as Hwe1 by (eapply eqt_wf_l; eassumption).
    apply ceq_val.
    + apply cong_Lam; [ wfa | wfa | wfa | exact Heq1 ].
    + intros D g HD Hg; apply RV_lam; assumption.
  - (* -> *)
    apply ceq_ty; apply tyok_arr; assumption.
  - (* tt *)
    assert (wft e2 Senv) as Hw2 by (apply EnvOk_wf; assumption).
    apply ceq_val.
    + apply eq_term_refl; apply wf_Tt; assumption.
    + intros D g HD Hg.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft g (Ssub D e2)) as Hwg by (apply RSub_wf; assumption).
      apply RV_unit; exists (Tt D); split;
        [ apply nfvt_tt | apply eq_val_subst_tt; wfa ].
  - (* unit *)
    apply ceq_ty; apply tyok_unit.
  - (* ret *)
    apply Ceq_val_e in X0 as [Heq1 Hsem1].
    assert (wft e5 Senv) as Hw5 by (apply EnvOk_wf; assumption).
    assert (wft e3 Sty) as Hw3 by (apply TyOk_wf; assumption).
    assert (wft e1 (Sval e5 e3)) as Hwe1 by (eapply eqt_wf_l; eassumption).
    apply ceq_exp.
    + apply cong_Ret; [ wfa | wfa | exact Heq1 ].
    + intros D g HD Hg.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft g (Ssub D e5)) as Hwg by (apply RSub_wf; assumption).
      apply RE_ret with (v := ValSubst D e5 g e3 e1);
        [ apply Hsem1; assumption
        | apply eq_exp_subst_ret; wfa
        | assumption | assumption ].
  - (* exp_subst *)
    apply Ceq_exp_e in X0 as [Heq1 Hsem1].
    apply Ceq_sub_e in X3 as [Heq3 Hsem3].
    assert (wft e9 Senv) as Hw9 by (apply EnvOk_wf; assumption).
    assert (wft e7 Senv) as Hw7 by (apply EnvOk_wf; assumption).
    assert (wft e3 Sty) as Hw3 by (apply TyOk_wf; assumption).
    assert (wft e1 (Sexp e7 e3)) as Hwe1 by (eapply eqt_wf_l; eassumption).
    assert (wft e4 (Ssub e9 e7)) as Hwe4 by (eapply eqt_wf_l; eassumption).
    apply ceq_exp.
    + apply cong_ExpSubst; [ wfa | wfa | wfa | exact Heq3 | exact Heq1 ].
    + intros D g HD Hg.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft g (Ssub D e9)) as Hwg by (apply RSub_wf; assumption).
      apply RE_eq with (e := ExpSubst D e7 (Cmp D e9 e7 g e4) e3 e1).
      * apply Hsem1; [ assumption | apply Hsem3; assumption ].
      * apply eq_term_sym; apply eq_exp_subst_cmp; wfa.
  - (* hd *)
    assert (wft e3 Senv) as Hw3 by (apply EnvOk_wf; assumption).
    assert (wft e2 Sty) as Hw2 by (apply TyOk_wf; assumption).
    apply ceq_val.
    + apply eq_term_refl; apply wf_Hd; assumption.
    + intros D g HD Hg; apply RSub_hd; assumption.
  - (* wkn *)
    assert (wft e3 Senv) as Hw3 by (apply EnvOk_wf; assumption).
    assert (wft e2 Sty) as Hw2 by (apply TyOk_wf; assumption).
    apply ceq_sub.
    + apply eq_term_refl; apply wf_Wkn; assumption.
    + intros D h HD Hh; apply RSub_proj; assumption.
  - (* snoc *)
    apply Ceq_val_e in X0 as [Heq1 Hsem1].
    apply Ceq_sub_e in X3 as [Heq3 Hsem3].
    assert (wft e9 Senv) as Hw9 by (apply EnvOk_wf; assumption).
    assert (wft e7 Senv) as Hw7 by (apply EnvOk_wf; assumption).
    assert (wft e3 Sty) as Hw3 by (apply TyOk_wf; assumption).
    assert (wft e1 (Sval e9 e3)) as Hwe1 by (eapply eqt_wf_l; eassumption).
    assert (wft e4 (Ssub e9 e7)) as Hwe4 by (eapply eqt_wf_l; eassumption).
    apply ceq_sub.
    + apply cong_Snoc; [ wfa | wfa | wfa | exact Heq3 | exact Heq1 ].
    + intros D h HD Hh.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft h (Ssub D e9)) as Hwh by (apply RSub_wf; assumption).
      apply RSub_eq with
        (g := Snoc D e7 (Cmp D e9 e7 h e4) e3 (ValSubst D e9 h e3 e1)).
      * apply RSub_ext;
          [ apply Hsem3; assumption | apply Hsem1; assumption
          | assumption | assumption | assumption ].
      * apply eq_term_sym; apply eq_cmp_snoc; wfa.
  - (* ext *)
    apply ceq_env; apply envok_ext; assumption.
  - (* forget *)
    assert (wft e2 Senv) as Hw2 by (apply EnvOk_wf; assumption).
    apply ceq_sub.
    + apply eq_term_refl; apply wf_Forget; assumption.
    + intros D h HD Hh.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft h (Ssub D e2)) as Hwh by (apply RSub_wf; assumption).
      apply RSub_emp_intro; apply eq_cmp_forget; wfa.
  - (* emp *)
    apply ceq_env; apply envok_emp.
  - (* val_subst *)
    apply Ceq_val_e in X0 as [Heq1 Hsem1].
    apply Ceq_sub_e in X3 as [Heq3 Hsem3].
    assert (wft e9 Senv) as Hw9 by (apply EnvOk_wf; assumption).
    assert (wft e7 Senv) as Hw7 by (apply EnvOk_wf; assumption).
    assert (wft e3 Sty) as Hw3 by (apply TyOk_wf; assumption).
    assert (wft e1 (Sval e7 e3)) as Hwe1 by (eapply eqt_wf_l; eassumption).
    assert (wft e4 (Ssub e9 e7)) as Hwe4 by (eapply eqt_wf_l; eassumption).
    apply ceq_val.
    + apply cong_ValSubst; [ wfa | wfa | wfa | exact Heq3 | exact Heq1 ].
    + intros D g HD Hg.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft g (Ssub D e9)) as Hwg by (apply RSub_wf; assumption).
      apply RV_eq with (v := ValSubst D e7 (Cmp D e9 e7 g e4) e3 e1).
      * apply Hsem1; [ assumption | apply Hsem3; assumption ].
      * apply eq_term_sym; apply eq_val_subst_cmp; wfa.
  - (* cmp *)
    apply Ceq_sub_e in X0 as [Heq1 Hsem1].
    apply Ceq_sub_e in X2 as [Heq2 Hsem2].
    assert (wft e9 Senv) as Hw9 by (apply EnvOk_wf; assumption).
    assert (wft e7 Senv) as Hw7 by (apply EnvOk_wf; assumption).
    assert (wft e5 Senv) as Hw5 by (apply EnvOk_wf; assumption).
    assert (wft e0 (Ssub e9 e7)) as Hwe0 by (eapply eqt_wf_l; eassumption).
    assert (wft e1 (Ssub e7 e5)) as Hwe1 by (eapply eqt_wf_l; eassumption).
    apply ceq_sub.
    + apply cong_Cmp; [ wfa | wfa | wfa | exact Heq2 | exact Heq1 ].
    + intros D h HD Hh.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft h (Ssub D e9)) as Hwh by (apply RSub_wf; assumption).
      apply RSub_eq with (g := Cmp D e7 e5 (Cmp D e9 e7 h e0) e1).
      * apply Hsem1; [ assumption | apply Hsem2; assumption ].
      * apply eq_term_sym; apply eq_cmp_assoc; wfa.
  - (* id *)
    assert (wft e2 Senv) as Hw2 by (apply EnvOk_wf; assumption).
    apply ceq_sub.
    + apply eq_term_refl; apply wf_Id; assumption.
    + intros D h HD Hh.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft h (Ssub D e2)) as Hwh by (apply RSub_wf; assumption).
      apply RSub_eq with (g := h); [ assumption | ].
      apply eq_term_sym; apply eq_id_right; wfa.
Qed.
