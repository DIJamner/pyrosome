Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab.
From Pyrosome.Gluing Require Import StlcModel StlcNormalization StlcNormalForms.
Import Core.Notations.

(* ================================================================== *)
(* LAYER 2: reducibility, by recursion on the TYPE                     *)
(* ================================================================== *)

(* [RV G A v] : the value [v : val G A] is reducible.
   [RE G A e] : the expression [e : exp G A] is reducible.

   Both are defined by structural recursion on the TYPE [A] alone.  The
   quantifier in the arrow clause ranges over WEAKENINGS [Wk D G w], a purely
   syntactic class (Layer 1), never over reducible substitutions, so the
   recursion really is on [A] and nothing else.

   As in Layer 1 everything is stated up to [eq_term]: "has a normal form"
   means "is provably equal to a canonical form".  Consequently every clause
   below is automatically invariant under provable equality ([RV_eq]/[RE_eq]),
   and no confluence or termination argument is required anywhere. *)

Local Notation wft := (wf_term stlc_unit []).
Local Notation eqt := (eq_term stlc_unit []).

(* ------------------------------------------------------------------ *)
(* Small glue: extracting well-formedness from a provable equation      *)
(* ------------------------------------------------------------------ *)

Lemma eqt_wf_l t e1 e2 : eqt t e1 e2 -> wft e1 t.
Proof.
  intro H; eapply eq_term_wf_l; try typeclasses eauto;
    [ exact stlc_unit_wf | constructor | exact H ].
Qed.

Lemma eqt_wf_r t e1 e2 : eqt t e1 e2 -> wft e2 t.
Proof.
  intro H; eapply eq_term_wf_r; try typeclasses eauto;
    [ exact stlc_unit_wf | constructor | exact H ].
Qed.

(* ------------------------------------------------------------------ *)
(* The relation                                                         *)
(* ------------------------------------------------------------------ *)

(* [RVarr] is the type-directed HALF of [RV]: the extra condition imposed at
   an arrow type (and nothing at all at a base type).  Splitting it off this
   way is a presentational device -- [RV] itself is then a plain [Definition],
   so [RV G A v] can be unfolded even when [A] is a variable, which is what
   makes [CR_reify] hold with no hypothesis on [A].  The recursive
   occurrences of [RV]/[RE] are inlined here (curried, since the fixpoint
   cannot mention [RV] itself); [RV_unit_iff] and [RV_arr_iff] below state the
   intended reading of the two clauses, and are proved by unfolding alone. *)
Fixpoint RVarr (G A v : term) {struct A} : Prop :=
  match A with
  | con "->" [B; A0] =>
      forall D w u,
        Wk D G w -> EnvOk D ->
        (* [RV D A0 u], inlined *)
        (exists n, NfVT D A0 n /\ eqt (Sval D A0) u n) ->
        RVarr D A0 u ->
        (* [RE D B (App D A0 B (Ret D A (w[v])) (Ret D A0 u))], inlined *)
        exists m,
          NfET D B m
          /\ eqt (Sexp D B)
               (App D A0 B (Ret D A (ValSubst D G w A v)) (Ret D A0 u)) m
          /\ (forall v', m = Ret D B v' ->
                (exists n, NfVT D B n /\ eqt (Sval D B) v' n) /\ RVarr D B v')
  | _ => True
  end.

Definition RV (G A v : term) : Prop :=
  (exists n, NfVT G A n /\ eqt (Sval G A) v n) /\ RVarr G A v.

Definition RE (G A e : term) : Prop :=
  exists n, NfET G A n
         /\ eqt (Sexp G A) e n
         /\ (forall v, n = Ret G A v -> RV G A v).

(* ---- the intended reading of the two clauses ---- *)

Lemma RV_unit_iff G v
  : RV G Unit v <-> exists n, NfVT G Unit n /\ eqt (Sval G Unit) v n.
Proof.
  unfold RV, Unit; cbn [RVarr]; split.
  - intros [H _]; exact H.
  - intro H; split; [ exact H | exact I ].
Qed.

Lemma RV_arr_iff G A B v
  : RV G (Arr A B) v
    <-> (exists n, NfVT G (Arr A B) n /\ eqt (Sval G (Arr A B)) v n)
        /\ (forall D w u,
              Wk D G w -> EnvOk D -> RV D A u ->
              RE D B (App D A B
                        (Ret D (Arr A B) (ValSubst D G w (Arr A B) v))
                        (Ret D A u))).
Proof.
  unfold RV, RE, Arr; cbn [RVarr]; split; intros [H1 H2]; (split; [exact H1|]).
  - intros D w u Hw HD [Hu1 Hu2]; apply H2; assumption.
  - intros D w u Hw HD Hu1 Hu2; apply H2; try assumption; split; assumption.
Qed.

(* ---- introduction / elimination interface ---- *)

(* CR_reify: a reducible value has a normal form.  No hypotheses at all. *)
Lemma CR_reify G A v
  : RV G A v -> exists n, NfVT G A n /\ eqt (Sval G A) v n.
Proof. intros [H _]; exact H. Qed.

Lemma CR_reify_E G A e
  : RE G A e -> exists n, NfET G A n /\ eqt (Sexp G A) e n.
Proof. intros [n [Hn [Heq _]]]; eauto. Qed.

Lemma RV_unit G v
  : (exists n, NfVT G Unit n /\ eqt (Sval G Unit) v n) -> RV G Unit v.
Proof. apply RV_unit_iff. Qed.

Lemma RV_arr G A B v
  : (exists n, NfVT G (Arr A B) n /\ eqt (Sval G (Arr A B)) v n) ->
    (forall D w u,
        Wk D G w -> EnvOk D -> RV D A u ->
        RE D B (App D A B
                  (Ret D (Arr A B) (ValSubst D G w (Arr A B) v))
                  (Ret D A u))) ->
    RV G (Arr A B) v.
Proof. intros; apply RV_arr_iff; split; assumption. Qed.

(* The arrow clause, as an elimination rule. *)
Lemma RV_arr_app G A B v D w u
  : RV G (Arr A B) v ->
    Wk D G w -> EnvOk D -> RV D A u ->
    RE D B (App D A B
              (Ret D (Arr A B) (ValSubst D G w (Arr A B) v))
              (Ret D A u)).
Proof. intro H; apply RV_arr_iff in H as [_ H]; auto. Qed.

(* ------------------------------------------------------------------ *)
(* Reducible terms are well typed                                       *)
(* ------------------------------------------------------------------ *)

Lemma RV_wf G A v : RV G A v -> wft v (Sval G A).
Proof. intros [[n [_ Heq]] _]; eapply eqt_wf_l; eassumption. Qed.

Lemma RE_wf G A e : RE G A e -> wft e (Sexp G A).
Proof. intros [n [_ [Heq _]]]; eapply eqt_wf_l; eassumption. Qed.

(* ------------------------------------------------------------------ *)
(* Closure under provable equality                                      *)
(* ------------------------------------------------------------------ *)

(* [RE] is invariant under [eq_term] with no side conditions: the witness
   normal form is unchanged. *)
Lemma RE_eq G A e e'
  : RE G A e -> eqt (Sexp G A) e e' -> RE G A e'.
Proof.
  intros [n [Hn [Heq Hret]]] Heq'.
  exists n; split; [ exact Hn | split; [ | exact Hret ] ].
  eapply eq_term_trans; [ apply eq_term_sym; exact Heq' | exact Heq ].
Qed.

Lemma RV_eq G A v v'
  : EnvOk G -> TyOk A -> RV G A v -> eqt (Sval G A) v v' -> RV G A v'.
Proof.
  intros HG HA Hv Heq.
  assert (wft v (Sval G A)) as Hwv by (eapply RV_wf; eassumption).
  assert (wft v' (Sval G A)) as Hwv' by (eapply eqt_wf_r; eassumption).
  destruct (CR_reify Hv) as [n [Hn Hvn]].
  assert (exists n, NfVT G A n /\ eqt (Sval G A) v' n) as Hnf'.
  { exists n; split; [ exact Hn | ].
    eapply eq_term_trans; [ apply eq_term_sym; exact Heq | exact Hvn ]. }
  destruct HA as [ | A1 A2 HA1 HA2 ].
  - (* Unit *)
    apply RV_unit; exact Hnf'.
  - (* Arr *)
    apply RV_arr; [ exact Hnf' | ].
    intros D w u Hw HD Hu.
    assert (wft u (Sval D A1)) as Hwu by (eapply RV_wf; eassumption).
    pose proof (RV_arr_app Hv Hw HD Hu) as Hre.
      eapply RE_eq; [ exact Hre | ].
      apply cong_App; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
      apply cong_Ret; [ wfa | wfa | ].
      apply cong_ValSubst; [ wfa | wfa | wfa | apply eq_term_refl; wfa | ].
      exact Heq.
Qed.

Corollary RE_eq_iff G A e e'
  : eqt (Sexp G A) e e' -> (RE G A e <-> RE G A e').
Proof.
  intro Heq; split; intro H; eapply RE_eq;
    try eassumption; apply eq_term_sym; assumption.
Qed.

Corollary RV_eq_iff G A v v'
  : EnvOk G -> TyOk A -> eqt (Sval G A) v v' -> (RV G A v <-> RV G A v').
Proof.
  intros HG HA Heq; split; intro H; eapply RV_eq;
    try eassumption; apply eq_term_sym; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* CR_reflect: neutrals are reducible                                   *)
(* ------------------------------------------------------------------ *)

(* A neutral expression is its own normal form, and it is not a [ret], so the
   third conjunct of [RE] is vacuous.  Hence no induction is needed here. *)
Lemma CR_reflect_E G A e
  : NeET G A e -> EnvOk G -> TyOk A -> RE G A e.
Proof.
  intros He HG HA.
  exists e; split; [ | split ].
  - apply nfet_ne; assumption.
  - apply eq_term_refl; eapply NeET_wf; eassumption.
  - intros v0 Hv0; exfalso.
    destruct He; unfold Ret, App in Hv0; congruence.
Qed.

(* The [eq_term]-closed form, which is how it is used in practice. *)
Lemma RE_ne G A e n
  : NeET G A n -> eqt (Sexp G A) e n -> EnvOk G -> TyOk A -> RE G A e.
Proof.
  intros Hn Heq HG HA.
  eapply RE_eq; [ eapply CR_reflect_E; eassumption | ].
  apply eq_term_sym; exact Heq.
Qed.

(* Object-level variables are reducible.  This is the crux of the layer: at an
   arrow type one must show that applying a variable to a reducible argument is
   again neutral, hence reducible. *)
Lemma CR_reflect_V G A x
  : VarT G A x -> EnvOk G -> RV G A x.
Proof.
  intros Hx HG.
  assert (TyOk A) as HA by (eapply VarT_TyOk; eassumption).
  assert (wft x (Sval G A)) as Hwx by (eapply VarT_wf; eassumption).
  destruct HA as [ | A1 A2 HA1 HA2 ].
  - apply RV_unit; exists x; split;
      [ apply nfvt_var; assumption | apply eq_term_refl; assumption ].
  - apply RV_arr.
    + exists x; split;
        [ apply nfvt_var; assumption | apply eq_term_refl; assumption ].
    + intros D w u Hw HD Hu.
      edestruct VarT_wk as [x' [Hx' Heqx]]; try eassumption.
      destruct (CR_reify Hu) as [nu [Hnu Hequ]].
      assert (EnvOk G) as HG' by assumption.
      eapply RE_ne with
        (n := App D A1 A2 (Ret D (Arr A1 A2) x') (Ret D A1 nu)).
      * apply neet_varapp; [ assumption | apply nfet_ret; assumption ].
      * apply cong_App; [ wfa | wfa | wfa | | ].
        -- apply cong_Ret; [ wfa | wfa | exact Heqx ].
        -- apply cong_Ret; [ wfa | wfa | exact Hequ ].
      * assumption.
      * assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* [RE] introduction from a value, and the case analysis it supports    *)
(* ------------------------------------------------------------------ *)

Lemma RE_ret G A e v
  : RV G A v -> eqt (Sexp G A) e (Ret G A v) -> EnvOk G -> TyOk A -> RE G A e.
Proof.
  intros Hv Heq HG HA.
  destruct (CR_reify Hv) as [nv [Hnv Heqv]].
  exists (Ret G A nv); split; [ | split ].
  - apply nfet_ret; assumption.
  - eapply eq_term_trans; [ exact Heq | ].
    apply cong_Ret; [ wfa | wfa | exact Heqv ].
  - intros v' Hv'; unfold Ret in Hv'; inversion Hv'; subst.
    eapply RV_eq; eassumption.
Qed.

(* Every reducible expression is provably equal either to the [ret] of a
   reducible value or to a neutral.  (This is the disjunctive reading of [RE];
   it is equivalent to the definition, by [RE_ret] and [RE_ne].) *)
Lemma RE_cases G A e
  : RE G A e ->
    (exists v, RV G A v /\ eqt (Sexp G A) e (Ret G A v))
    \/ (exists n, NeET G A n /\ eqt (Sexp G A) e n).
Proof.
  intros [n [Hn [Heq Hret]]].
  destruct Hn as [ G0 A0 v0 Hv0 | G0 A0 n0 Hn0 ].
  - left; exists v0; split; auto.
  - right; exists n0; split; auto.
Qed.

(* NOTE (for Layer 4).  [RE_cases] exposes the only gap in the canonical-form
   grammar of Layer 1.  In the [app] congruence one has to combine an
   expression that is a [ret] of a reducible value with an argument
   expression that is NEUTRAL.  The resulting term
     [app (ret (lambda A e)) n]     with [n] neutral
   is stuck -- STLC-beta only fires when BOTH sides are [ret]s -- but it is
   not in Layer 1's [NeET]/[NfET] grammar, whose [neet_app] clause requires
   the FUNCTION to be neutral.  Nothing in this layer depends on that clause
   set beyond the two constructors of [NfET] and the fact that every [NeET]
   subject is an [app], so adding the missing stuck form to Layer 1 (plus its
   weakening case in [NfT_wk]) leaves every proof below unchanged. *)

(* ------------------------------------------------------------------ *)
(* Stability under weakening                                            *)
(* ------------------------------------------------------------------ *)

Lemma RV_wk G A v D w
  : RV G A v -> Wk D G w -> EnvOk D -> EnvOk G -> TyOk A ->
    RV D A (ValSubst D G w A v).
Proof.
  intros Hv Hw HD HG HA.
  assert (wft v (Sval G A)) as Hwv by (eapply RV_wf; eassumption).
  assert (wft w (Ssub D G)) as Hww by (eapply Wk_wf; eassumption).
  (* the "has a normal form" conjunct, common to both clauses *)
  assert (exists n, NfVT D A n /\ eqt (Sval D A) (ValSubst D G w A v) n)
    as Hnf.
  { destruct (CR_reify Hv) as [n [Hn Heqn]].
    edestruct NfVT_wk as [n' [Hn' Heqn']]; try eassumption.
    exists n'; split; [ assumption | ].
    eapply eq_term_trans; [ | exact Heqn' ].
    apply cong_ValSubst; [ wfa | wfa | wfa | apply eq_term_refl; wfa | ].
    exact Heqn. }
  destruct HA as [ | A1 A2 HA1 HA2 ].
  - apply RV_unit; exact Hnf.
  - apply RV_arr; [ exact Hnf | ].
    intros D' w' u Hw' HD' Hu.
    assert (wft u (Sval D' A1)) as Hwu by (eapply RV_wf; eassumption).
    (* compose the two weakenings *)
    edestruct (Wk_cmp Hw' Hw HD') as [w'' [Hw'' Heqw]].
    assert (wft w' (Ssub D' D)) as Hww' by (eapply Wk_wf; eassumption).
    pose proof (RV_arr_app Hv Hw'' HD' Hu) as Hre.
    eapply RE_eq; [ exact Hre | ].
    apply cong_App; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
    apply cong_Ret; [ wfa | wfa | ].
    (* w'[w[v]] = (w' o w)[v] = w''[v] *)
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_val_subst_cmp; wfa | ].
    apply cong_ValSubst; [ wfa | wfa | wfa | exact Heqw | apply eq_term_refl; wfa ].
Qed.

Lemma RE_wk G A e D w
  : RE G A e -> Wk D G w -> EnvOk D -> EnvOk G -> TyOk A ->
    RE D A (ExpSubst D G w A e).
Proof.
  intros He Hw HD HG HA.
  assert (wft e (Sexp G A)) as Hwe by (eapply RE_wf; eassumption).
  assert (wft w (Ssub D G)) as Hww by (eapply Wk_wf; eassumption).
  destruct He as [n [Hn [Heq Hret]]].
  destruct Hn as [ G0 A0 v0 Hv0 | G0 A0 n0 Hn0 ].
  - (* the normal form is [ret v0]; [v0] is reducible, and so is its shift *)
    assert (RV G0 A0 v0) as Hrv0 by (apply Hret; reflexivity).
    edestruct NfVT_wk as [v' [Hv' Heqv']]; try eassumption.
    assert (RV D A0 v') as Hrv'.
    { eapply RV_eq;
        [ eassumption | eassumption
        | eapply RV_wk; eassumption
        | exact Heqv' ]. }
    exists (Ret D A0 v'); split; [ | split ].
    + apply nfet_ret; assumption.
    + eapply eq_term_trans;
        [ apply cong_ExpSubst;
          [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq ]
        | ].
      eapply eq_term_trans;
        [ apply eq_exp_subst_ret; wfa
        | apply cong_Ret; [ wfa | wfa | exact Heqv' ] ].
    + intros v1 Hv1; unfold Ret in Hv1; inversion Hv1; subst; assumption.
  - (* the normal form is neutral; so is its shift, and [RE]'s last conjunct
       is vacuous *)
    edestruct NeET_wk as [n' [Hn' Heqn']]; try eassumption.
    eapply RE_ne with (n := n'); try eassumption.
    eapply eq_term_trans;
      [ apply cong_ExpSubst;
        [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq ]
      | exact Heqn' ].
Qed.

(* ------------------------------------------------------------------ *)
(* Application of a reducible value to a reducible value                *)
(* ------------------------------------------------------------------ *)

(* The arrow clause instantiated at the identity weakening: this is the form
   Layer 4 consumes for the [app] congruence. *)
Lemma RV_apply G A B v u
  : RV G (Arr A B) v -> RV G A u -> EnvOk G -> TyOk A -> TyOk B ->
    RE G B (App G A B (Ret G (Arr A B) v) (Ret G A u)).
Proof.
  intros Hv Hu HG HA HB.
  assert (wft v (Sval G (Arr A B))) as Hwv by (eapply RV_wf; eassumption).
  assert (wft u (Sval G A)) as Hwu by (eapply RV_wf; eassumption).
  pose proof (RV_arr_app Hv (wk_id G) HG Hu) as Hre.
  eapply RE_eq; [ exact Hre | ].
  apply cong_App; [ wfa | wfa | wfa | | apply eq_term_refl; wfa ].
  apply cong_Ret; [ wfa | wfa | ].
  apply eq_val_subst_id; wfa.
Qed.
