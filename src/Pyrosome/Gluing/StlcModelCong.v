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

(* Layer 4b: the STRUCTURAL half of [CutTModel_ok] for [stlc_unit], [c := []],
   [CM := StlcCM].

   Each field of the class is proved here as a standalone top-level lemma; a
   separate file assembles the [Instance] (the [cterm_by] half -- the 18
   equation instances -- is developed independently).

   Everything goes through the constructors and clause lemmas of
   Gluing/StlcCeq.v ([ceq_ty] ... [ceq_exp], [Ceq_ty_e] ... [Ceq_exp_e]);
   [Ceq_term] is never inverted by hand outside of those five lemmas, and
   [RVarr] is never unfolded either. *)

Local Notation eqt := (eq_term stlc_unit []).
Local Notation wft := (wf_term stlc_unit []).

(* ================================================================== *)
(* 1.  Sort inversion                                                  *)
(* ================================================================== *)

(* [RSub_eq]/[RV_eq] of the lower layers carry [EnvOk]/[TyOk] side conditions
   that the symmetry obligation cannot supply (its hypothesis constrains only
   the left-hand term, and neither [RSub] nor [RV] forces its index to be
   [EnvOk]/[TyOk]).  What IS recoverable is plain well-formedness of the
   indices, by inverting the sort of the subject; that is enough, and it is
   what this section provides. *)

Lemma eqt_wf_sort t e1 e2 : eqt t e1 e2 -> wf_sort stlc_unit [] t.
Proof.
  intro H; eapply eq_term_wf_sort; try typeclasses eauto;
    [ exact stlc_unit_wf | constructor | exact H ].
Qed.

Lemma wft_wf_sort e t : wft e t -> wf_sort stlc_unit [] t.
Proof. intro H; eapply eqt_wf_sort; apply eq_term_refl; exact H. Qed.

Ltac sort_inv H :=
  inversion H; subst;
  match goal with
  | [ Hin : In _ stlc_unit |- _ ] =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin|Hin]); try discriminate;
      inversion Hin; subst; clear Hin
  end;
  repeat match goal with
         | [ Ha : wf_args _ (_::_) _ |- _ ] => inversion Ha; subst; clear Ha
         end;
  cbn [Model.wf_term core_model] in *;
  split; assumption.

Lemma wf_sort_sub_inv G G' : wf_sort stlc_unit [] (Ssub G G') -> wft G Senv /\ wft G' Senv.
Proof. unfold Ssub; intro H; sort_inv H. Qed.

Lemma wf_sort_val_inv G A : wf_sort stlc_unit [] (Sval G A) -> wft G Senv /\ wft A Sty.
Proof. unfold Sval; intro H; sort_inv H. Qed.

Lemma wf_sort_exp_inv G A : wf_sort stlc_unit [] (Sexp G A) -> wft G Senv /\ wft A Sty.
Proof. unfold Sexp; intro H; sort_inv H. Qed.

Lemma wft_sub_inv G G' g : wft g (Ssub G G') -> wft G Senv /\ wft G' Senv.
Proof. intro H; apply wf_sort_sub_inv; eapply wft_wf_sort; exact H. Qed.

Lemma wft_val_inv G A v : wft v (Sval G A) -> wft G Senv /\ wft A Sty.
Proof. intro H; apply wf_sort_val_inv; eapply wft_wf_sort; exact H. Qed.

Lemma wft_exp_inv G A e : wft e (Sexp G A) -> wft G Senv /\ wft A Sty.
Proof. intro H; apply wf_sort_exp_inv; eapply wft_wf_sort; exact H. Qed.

(* ================================================================== *)
(* 2.  Side-condition-free forms of [RSub_wf]/[RSub_eq]/[RV_eq]        *)
(* ================================================================== *)

Lemma RSub_inv D G g
  : RSub D G g ->
    (G = Emp /\ eqt (Ssub D Emp) g (Forget D))
    \/ (exists G0 A g0 v, G = Ext G0 A
          /\ eqt (Ssub D (Ext G0 A)) g (Snoc D G0 g0 A v)
          /\ RSub D G0 g0 /\ RV D A v).
Proof.
  intro H; destruct G as [x|n l]; [ destruct H | ]; unfold RSub in H;
    repeat (cbv beta iota in H;
            first [ lazymatch type of H with False => destruct H end
                  | match type of H with
                    | context [ match ?x with _ => _ end ] => is_var x; destruct x
                    end ]).
  - left; split; [ reflexivity | exact H ].
  - right; destruct H as [g0 [v [Heq [Hg0 Hv]]]].
    exists t0, t, g0, v;
      split; [ reflexivity
             | split; [ exact Heq | split; [ exact Hg0 | exact Hv ] ] ].
Qed.

Lemma RSub_wf' D G g : RSub D G g -> wft g (Ssub D G).
Proof.
  intro H; apply RSub_inv in H as [[-> Heq] | [G0 [A [g0 [v [-> [Heq _]]]]]]];
    eapply eqt_wf_l; eassumption.
Qed.

Lemma RSub_eq' D G g g' : RSub D G g -> eqt (Ssub D G) g g' -> RSub D G g'.
Proof.
  intros H Heq;
    apply RSub_inv in H as [[-> He] | [G0 [A [g0 [v [-> [He [Hg0 Hv]]]]]]]].
  - apply RSub_emp_intro; eapply eq_term_trans;
      [ apply eq_term_sym; exact Heq | exact He ].
  - apply RSub_ext_intro; exists g0, v; split; [ | split; assumption ].
    eapply eq_term_trans; [ apply eq_term_sym; exact Heq | exact He ].
Qed.

(* A purely syntactic arrow test, used to case on the type without a [TyOk]
   hypothesis: at a non-arrow type the type-directed half of [RV] is [True]. *)
Definition is_arr (A : term) : bool :=
  match A with
  | con "->" [_; _] => true
  | _ => false
  end.

Ltac arr_split H :=
  unfold is_arr in H;
  repeat (cbv beta iota in H;
          first [ discriminate
                | solve [ intros; exact I ]
                | match type of H with
                  | context [ match ?x with _ => _ end ] => is_var x; destruct x
                  end ]).

Lemma is_arr_true A : is_arr A = true -> exists A0 B, A = Arr A0 B.
Proof.
  intro H; destruct A as [x|n l]; [ discriminate | ];
    unfold is_arr in H;
    repeat (cbv beta iota in H;
            first [ discriminate
                  | match type of H with
                    | context [ match ?x with _ => _ end ] => is_var x; destruct x
                    end ]);
    eexists; eexists; reflexivity.
Qed.

Lemma is_arr_false A : is_arr A = false -> forall G v, RVarr G A v.
Proof.
  intro H; destruct A as [x|n l]; [ intros; exact I | ]; arr_split H.
Qed.

Lemma RV_eq' G A v v' : RV G A v -> eqt (Sval G A) v v' -> RV G A v'.
Proof.
  intros Hv Heq.
  assert (exists n, NfVT G A n /\ eqt (Sval G A) v' n) as Hnf'.
  { destruct (CR_reify Hv) as [n [Hn Hvn]]; exists n; split; [ exact Hn | ].
    eapply eq_term_trans; [ apply eq_term_sym; exact Heq | exact Hvn ]. }
  destruct (is_arr A) eqn:Hia.
  2:{ split; [ exact Hnf' | apply is_arr_false; exact Hia ]. }
  apply is_arr_true in Hia as [A0 [B HA]]; subst A.
  assert (wft v (Sval G (Arr A0 B))) as Hwv by (eapply RV_wf; eassumption).
  destruct (@wft_val_inv _ _ _ Hwv) as [HwG HwAB].
  apply RV_arr; [ exact Hnf' | ].
  intros D w u Hw HD Hu.
  assert (EnvOk G) as HG by (eapply Wk_dom; eassumption).
  assert (wft w (Ssub D G)) as Hww by (eapply Wk_wf; eassumption).
  assert (wft u (Sval D A0)) as Hwu by (eapply RV_wf; eassumption).
  destruct (@wft_val_inv _ _ _ Hwu) as [HwD HwA0].
  pose proof (RV_arr_app Hv Hw HD Hu) as Hre.
  assert (wft (App D A0 B
                 (Ret D (Arr A0 B) (ValSubst D G w (Arr A0 B) v)) (Ret D A0 u))
            (Sexp D B)) as Hwapp by (eapply RE_wf; eassumption).
  destruct (@wft_exp_inv _ _ _ Hwapp) as [_ HwB].
  eapply RE_eq; [ exact Hre | ].
  apply cong_App; [ assumption | assumption | assumption | | ].
  - apply cong_Ret; [ assumption | assumption | ].
    apply cong_ValSubst;
      [ assumption | assumption | assumption
      | apply eq_term_refl; assumption | exact Heq ].
  - apply eq_term_refl; apply wf_Ret; assumption.
Qed.

(* ================================================================== *)
(* 3.  The two cases with real content: [lambda] and [app]             *)
(* ================================================================== *)

(* Post-composing the lifted substitution with the beta substitution
   [<id, u>] collapses to [<g, u>].  This is the whole computation behind the
   [lambda] congruence: pushing a substitution under a binder produces the
   lift, and the subsequent beta step consumes it. *)
Lemma eq_beta_lift G Y g A u
  : wft G Senv -> wft Y Senv -> wft A Sty ->
    wft g (Ssub G Y) -> wft u (Sval G A) ->
    eqt (Ssub G (Ext Y A))
      (Cmp G (Ext G A) (Ext Y A)
         (Snoc G G (Id G) A u)
         (Snoc (Ext G A) Y (Cmp (Ext G A) G Y (Wkn G A) g) A (Hd G A)))
      (Snoc G Y g A u).
Proof.
  intros HG HY HA Hg Hu.
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

(* Applying a substituted lambda to a value: push the substitution under the
   binder ([val_subst lambda]), fire [STLC-beta], then reassociate. *)
Lemma eq_lam_beta G Y g A B e u
  : wft G Senv -> wft Y Senv -> wft A Sty -> wft B Sty ->
    wft g (Ssub G Y) -> wft e (Sexp (Ext Y A) B) -> wft u (Sval G A) ->
    eqt (Sexp G B)
      (App G A B (Ret G (Arr A B) (ValSubst G Y g (Arr A B) (Lam Y A B e)))
           (Ret G A u))
      (ExpSubst G (Ext Y A) (Snoc G Y g A u) B e).
Proof.
  intros HG HY HA HB Hg He Hu.
  eapply eq_term_trans.
  { apply cong_App; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
    apply cong_Ret; [ wfa | wfa | apply eq_val_subst_lambda; wfa ]. }
  eapply eq_term_trans; [ apply eq_stlc_beta; wfa | ].
  eapply eq_term_trans; [ apply eq_exp_subst_cmp; wfa | ].
  apply cong_ExpSubst;
    [ wfa | wfa | wfa | apply eq_beta_lift; wfa | apply eq_term_refl; wfa ].
Qed.

(* The [lambda] congruence's semantic half. *)
Lemma RV_lam Y A B e
  : EnvOk Y -> TyOk A -> TyOk B -> wft e (Sexp (Ext Y A) B) ->
    (forall D s, EnvOk D -> RSub D (Ext Y A) s ->
                 RE D B (ExpSubst D (Ext Y A) s B e)) ->
    forall G g, EnvOk G -> RSub G Y g ->
      RV G (Arr A B) (ValSubst G Y g (Arr A B) (Lam Y A B e)).
Proof.
  intros HY HA HB Hwe Hsem G g HG Hg.
  assert (wft Y Senv) as HwY by (apply EnvOk_wf; assumption).
  assert (wft A Sty) as HwA by (apply TyOk_wf; assumption).
  assert (wft B Sty) as HwB by (apply TyOk_wf; assumption).
  assert (wft G Senv) as HwG by (apply EnvOk_wf; assumption).
  assert (wft g (Ssub G Y)) as Hwg by (apply RSub_wf'; assumption).
  assert (RE (Ext G A) B
            (ExpSubst (Ext G A) (Ext Y A)
               (Snoc (Ext G A) Y (Cmp (Ext G A) G Y (Wkn G A) g) A (Hd G A))
               B e)) as Hre.
  { apply Hsem; [ constructor; assumption | apply RSub_lift; assumption ]. }
  destruct (CR_reify_E Hre) as [m [Hm Hem]].
  apply RV_arr.
  - exists (Lam G A B m); split.
    + apply nfvt_lam; assumption.
    + eapply eq_term_trans; [ apply eq_val_subst_lambda; wfa | ].
      apply cong_Lam; [ wfa | wfa | wfa | exact Hem ].
  - intros D w u Hw HD Hu.
    assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
    assert (wft w (Ssub D G)) as Hww by (eapply Wk_wf; eassumption).
    assert (wft u (Sval D A)) as Hwu by (eapply RV_wf; eassumption).
    assert (RSub D Y (Cmp D G Y w g)) as Hg' by (eapply RSub_wk; eassumption).
    assert (wft (Cmp D G Y w g) (Ssub D Y)) as Hwg' by wfa.
    assert (RSub D (Ext Y A) (Snoc D Y (Cmp D G Y w g) A u)) as Hs
      by (apply RSub_ext; assumption).
    pose proof (Hsem D (Snoc D Y (Cmp D G Y w g) A u) HD Hs) as Hfin.
    eapply RE_eq; [ exact Hfin | ].
    apply eq_term_sym.
    eapply eq_term_trans.
    { apply cong_App; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
      apply cong_Ret; [ wfa | wfa | apply eq_val_subst_cmp; wfa ]. }
    apply eq_lam_beta; wfa.
Qed.

(* The [app] congruence's semantic half.  The function either reduces to a
   [ret] of a reducible value -- and then the argument either does too (a real
   beta step, via [RV_apply]) or is neutral, making the whole application
   stuck-but-neutral by [neet_lamapp] -- or is itself neutral, in which case
   [neet_app] applies. *)
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
(* 4.  Decomposing the rule-membership hypothesis                      *)
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
(* 5.  The obligations                                                 *)
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
   equation.  That transport is where the side-condition-free [RSub_eq'] and
   [RV_eq'] of section 2 are needed: nothing here supplies [EnvOk]/[TyOk] for
   the sort's indices, only their well-formedness. *)
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
    assert (wft h (Ssub D G)) as Hwh by (apply RSub_wf'; assumption).
    apply RSub_eq' with (g := Cmp D G G' h g1); [ apply Hb; assumption | ].
    apply cong_Cmp;
      [ assumption | assumption | assumption
      | apply eq_term_refl; assumption | exact Ha ].
  - assert (wft v1 (Sval G A)) as Hw1 by (eapply eqt_wf_l; eassumption).
    destruct (@wft_val_inv _ _ _ Hw1) as [HwG HwA].
    apply ceq_val; [ apply eq_term_sym; exact Ha | ].
    intros D g HD Hg.
    assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
    assert (wft g (Ssub D G)) as Hwg by (apply RSub_wf'; assumption).
    apply RV_eq' with (v := ValSubst D G g A v1); [ apply Hb; assumption | ].
    apply cong_ValSubst;
      [ assumption | assumption | assumption
      | apply eq_term_refl; assumption | exact Ha ].
  - assert (wft e1 (Sexp G A)) as Hw1 by (eapply eqt_wf_l; eassumption).
    destruct (@wft_exp_inv _ _ _ Hw1) as [HwG HwA].
    apply ceq_exp; [ apply eq_term_sym; exact Ha | ].
    intros D g HD Hg.
    assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
    assert (wft g (Ssub D G)) as Hwg by (apply RSub_wf'; assumption).
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
      assert (wft g (Ssub D e9)) as Hwg by (apply RSub_wf'; assumption).
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
      assert (wft g (Ssub D e2)) as Hwg by (apply RSub_wf'; assumption).
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
      assert (wft g (Ssub D e5)) as Hwg by (apply RSub_wf'; assumption).
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
      assert (wft g (Ssub D e9)) as Hwg by (apply RSub_wf'; assumption).
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
      assert (wft h (Ssub D e9)) as Hwh by (apply RSub_wf'; assumption).
      apply RSub_eq' with
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
      assert (wft h (Ssub D e2)) as Hwh by (apply RSub_wf'; assumption).
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
      assert (wft g (Ssub D e9)) as Hwg by (apply RSub_wf'; assumption).
      apply RV_eq' with (v := ValSubst D e7 (Cmp D e9 e7 g e4) e3 e1).
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
      assert (wft h (Ssub D e9)) as Hwh by (apply RSub_wf'; assumption).
      apply RSub_eq' with (g := Cmp D e7 e5 (Cmp D e9 e7 h e0) e1).
      * apply Hsem1; [ assumption | apply Hsem2; assumption ].
      * apply eq_term_sym; apply eq_cmp_assoc; wfa.
  - (* id *)
    assert (wft e2 Senv) as Hw2 by (apply EnvOk_wf; assumption).
    apply ceq_sub.
    + apply eq_term_refl; apply wf_Id; assumption.
    + intros D h HD Hh.
      assert (wft D Senv) as HwD by (apply EnvOk_wf; assumption).
      assert (wft h (Ssub D e2)) as Hwh by (apply RSub_wf'; assumption).
      apply RSub_eq' with (g := h); [ assumption | ].
      apply eq_term_sym; apply eq_id_right; wfa.
Qed.
