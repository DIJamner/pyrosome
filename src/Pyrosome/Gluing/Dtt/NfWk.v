Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.Inj
  Pyrosome.Gluing.Dtt.NfTyping.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 1: STABILITY UNDER WEAKENING, AND CLOSURE OF
   NORMAL CODES UNDER SUBSTITUTION.

   CONTENTS (everything below is axiom-free).

     * [Wk_cmp]                    weakenings compose, up to eq_term;
     * [TyOk_wk] [NfCode_wk] [VarT_wk] [NeET_wk] [NfET_wk]
                                   the whole normal-form block is stable
                                   under weakening;
     * [CSub] [CSub_wf]            the class of substitutions the CODE
                                   fragment needs, and [NfCode_csubst] /
                                   [TyOk_subst];
     * [eq_app_rel_subst] [eq_app_irr_subst] [eq_lam_irr_subst]
       [eq_Emptyrec_subst]         the four commutations of
                                   [Lang/OTT/SubstCommute.v], repackaged
                                   in Syntax.v's vocabulary.

   THREE DESIGN POINTS, EACH FORCED.

   (1) THE [exists A', TyOk D i A' /\ A[w] = A'] FORM IS ENOUGH, BECAUSE
       LAYER 0.5 IDENTIFIES THE REPRESENTATIVE.  At [neet_app_rel] the
       head's type contributes the domain code [F'] of the weakened Pi, and
       the ARGUMENT must be typed at THAT [F'] -- syntactically, since
       [NfET]'s clauses dispatch on the head of the type.  Provable equality
       alone does not give that, but [Inj.TyOk_inj] / [Inj.NfCode_inj] do:
       two normal objects of the same sort that are provably equal are
       SYNTACTICALLY equal.  So at each such clause one BUILDS the canonical
       witness -- e.g. [El D rel lG (Pi_rel D rF lF lG F' B')], out of
       [NfCode_wk] on the components -- and [TyOk_pin] / [NfCode_pin] force
       the induction hypothesis's own representative to be it.  No shape
       relation, no determinism proof, and no separate "structural" and
       "existential" statements of the theorem.

   (2) [CSub] IS THE CLASS THAT SURVIVES, BECAUSE THE OBVIOUS ONE IS NOT
       CLOSED UNDER LIFTING.  The obvious class -- every entry an [NfET] at
       the entry's normal type -- does not survive going under a binder:
       the lift snocs the head variable, and [hd] at a [Pi_rel] type is not
       an [NfET], since eta-long normality forbids it.  But the code
       fragment only ever inspects the UNIVERSE-typed entries, and there
       [hd] IS normal (it is a normal code, by [nfcode_var]).  So [CSub]
       constrains its entries only when their normal type is a universe,
       and then only to HAVE a normal code ([HasNfCode], so that the class
       survives composition with a weakening).  [CSub_lift] is the payoff.
       Every consumer, in this file and downstream, goes through [CSub];
       nothing needs the stricter class, so it is not defined here.

   (3) THE VARIABLE CASE OF [NfCode_csubst] NEEDS LAYER 0.5.  Reading a code
       variable off a [snoc] gives a normal term at the entry's normal type,
       and turning that into an [NfCode D r l] needs the type to BE
       [oU D r l] syntactically.  The head and the level are syntactic (a
       [TyOk] at info [iCode l] can only be a [U _ _ l], since
       [oIota l0 <> oNext l]); THE RELEVANCE IS NOT.  [U_pull] / [U_push]
       are where [Inj.TyOk_inj] is cashed in.  So the design doc's
       "R2 dissolves ... provable in Layer 1 with no reducibility at all"
       is right about the reducibility but wrong about the layering:
       [NfCode_wk] is Layer 1, [NfCode_csubst] depends on Layer 0.5.
   ===================================================================== *)

Notation term := (@Term.term string).
Notation sort := (@Term.sort string).

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* Tactic glue: harvest the [wf_term] consequences of every judgement   *)
(* in the context, so that [wfa] can discharge the (many) side          *)
(* conditions of the equational lemmas.                                 *)
(* ------------------------------------------------------------------ *)

Ltac pose_wf p :=
  let t := type of p in
  lazymatch goal with
  | [ _ : t |- _ ] => fail
  | _ => pose proof p
  end.

Ltac wfs :=
  repeat match goal with
    | [ H : EnvOk ?G |- _ ] => pose_wf (EnvOk_wf H)
    | [ H : TyOk ?G ?i ?A |- _ ] => pose_wf (TyOk_wf H)
    | [ H : NfCode ?G ?r ?l ?c |- _ ] => pose_wf (NfCode_wf H)
    | [ H : VarT ?G ?i ?A ?x |- _ ] => pose_wf (VarT_wf H)
    | [ H : NeET ?G ?i ?A ?e |- _ ] => pose_wf (NeET_wf H)
    | [ H : NfET ?G ?i ?A ?e |- _ ] => pose_wf (NfET_wf H)
    | [ H : Wk ?D ?G ?w |- _ ] => pose_wf (Wk_wf H)
    | [ H : RelNf ?r |- _ ] => pose_wf (RelNf_wf H)
    | [ H : LvlNf ?l |- _ ] => pose_wf (LvlNf_wf H)
    | [ H : NfCode ?G ?r ?l ?c |- _ ] => pose_wf (NfCode_RelNf H)
    | [ H : NfCode ?G ?r ?l ?c |- _ ] => pose_wf (NfCode_LvlNf H)
    | [ H : TyOk ?G ?i (oU ?G' ?r ?l) |- _ ] =>
        pose_wf (RelNf_wf (proj1 (TyOk_U_inv H)))
    | [ H : TyOk ?G ?i (oU ?G' ?r ?l) |- _ ] =>
        pose_wf (LvlNf_wf (proj2 (TyOk_U_inv H)))
    | [ H : TyOk ?G ?i ?A |- _ ] => pose_wf (TyOk_EnvOk H)
    | [ H : NfCode ?G ?r ?l ?c |- _ ] => pose_wf (NfCode_EnvOk H)
    | [ H : VarT ?G ?i ?A ?x |- _ ] => pose_wf (VarT_TyOk H)
    | [ H : NeET ?G ?i ?A ?e |- _ ] => pose_wf (NeET_TyOk H)
    | [ H : NfET ?G ?i ?A ?e |- _ ] => pose_wf (NfET_TyOk H)
    | [ H : Wk ?D ?G ?w |- _ ] => pose_wf (Wk_dom H)
    | [ H : Wk ?D ?G ?w |- _ ] => pose_wf (Wk_cod H)
    | [ H : wft ?e (sExp ?G ?i ?A) |- _ ] => pose_wf (wft_exp_env H)
    | [ H : wft ?e (sExp ?G ?i ?A) |- _ ] => pose_wf (wft_exp_info H)
    | [ H : wft ?e (sExp ?G ?i ?A) |- _ ] => pose_wf (wft_exp_ty H)
    | [ H : wft ?A (sTy ?G ?i) |- _ ] => pose_wf (wft_ty_env H)
    | [ H : wft ?A (sTy ?G ?i) |- _ ] => pose_wf (wft_ty_info H)
    | [ H : wft ?g (sSub ?G ?G') |- _ ] => pose_wf (wft_sub_dom H)
    | [ H : wft ?g (sSub ?G ?G') |- _ ] => pose_wf (wft_sub_cod H)
    end.

(* The routine solver used throughout: harvest, then [wfa]. *)
Ltac wfx := wfs; wfa.

(* Convert an [eq_term] at an [exp] sort along an equality of the type. *)
Lemma eqt_conv_ty G i A1 A2 e1 e2
  : wft G sEnv -> wft i sInfo -> eqt (sTy G i) A1 A2 ->
    eqt (sExp G i A1) e1 e2 -> eqt (sExp G i A2) e1 e2.
Proof.
  intros; eapply eq_term_conv;
    [ eassumption | apply eq_sort_exp_ty; assumption ].
Qed.

(* ------------------------------------------------------------------ *)
(* The lifted weakening, as a named term                                *)
(* ------------------------------------------------------------------ *)

Definition oLiftW (D G w i A A' : term) : term :=
  oSnoc (oExt D i A') G i A (oCmp (oExt D i A') D G (oWkn D i A') w)
    (oHd D i A').

Lemma wk_lift' D G i A A' w
  : Wk D G w -> TyOk G i A -> TyOk D i A' ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    Wk (oExt D i A') (oExt G i A) (oLiftW D G w i A A').
Proof. intros; apply wk_lift; assumption. Qed.

(* [Syntax.oLift] is [oLiftW] at the shapes the binder rules use. *)
Lemma oLift_oLiftW G G' g rF lF F
  : oLift G G' g rF lF F
    = oLiftW G G' g (iEl rF lF) (oEl G' rF lF F)
        (oEl G rF lF (oCodeSubst G G' g rF lF F)).
Proof. reflexivity. Qed.

(* The [wf_term] of a lifted weakening's head variable, at the sort
   [snoc] demands.  (This is [NfTyping.eq_wk_lift_ty] packaged.) *)
Lemma wf_liftW_hd D G w i A A'
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    wft (oHd D i A')
      (sExp (oExt D i A') i
         (oTySubst (oExt D i A') G (oCmp (oExt D i A') D G (oWkn D i A') w)
            i A)).
Proof.
  intros HD HG Hi HA HA' Hw Heq.
  eapply wf_term_conv; [ apply wf_Hd; assumption | ].
  apply eq_sort_exp_ty.
  apply eq_wk_lift_ty; assumption.
Qed.

Lemma wf_liftW D G w i A A'
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    wft (oLiftW D G w i A A') (sSub (oExt D i A') (oExt G i A)).
Proof.
  intros; unfold oLiftW; apply wf_Snoc;
    [ apply wf_Ext; assumption | assumption | assumption | assumption
    | apply wf_Cmp;
      [ apply wf_Ext; assumption | assumption | assumption
      | apply wf_Wkn; assumption | assumption ]
    | apply wf_liftW_hd; assumption ].
Qed.

(* [lift(w) ; wkn = wkn ; w] *)
Lemma eq_liftW_wkn D G w i A A'
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sSub (oExt D i A') G)
      (oCmp (oExt D i A') (oExt G i A) G (oLiftW D G w i A A')
         (oWkn G i A))
      (oCmp (oExt D i A') D G (oWkn D i A') w).
Proof.
  intros; unfold oLiftW; apply eq_wkn_snoc;
    [ apply wf_Ext; assumption | assumption
    | apply wf_Cmp;
      [ apply wf_Ext; assumption | assumption | assumption
      | apply wf_Wkn; assumption | assumption ]
    | assumption | assumption
    | apply wf_liftW_hd; assumption ].
Qed.

(* [hd[lift(w)] = hd] *)
Lemma eq_liftW_hd D G w i A A'
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sExp (oExt D i A') i
           (oTySubst (oExt D i A') G
              (oCmp (oExt D i A') D G (oWkn D i A') w) i A))
      (oExpSubst (oExt D i A') (oExt G i A) (oLiftW D G w i A A') i
         (oTySubst (oExt G i A) G (oWkn G i A) i A) (oHd G i A))
      (oHd D i A').
Proof.
  intros; unfold oLiftW; apply eq_snoc_hd;
    [ apply wf_Ext; assumption | assumption
    | apply wf_Cmp;
      [ apply wf_Ext; assumption | assumption | assumption
      | apply wf_Wkn; assumption | assumption ]
    | assumption | assumption
    | apply wf_liftW_hd; assumption ].
Qed.

#[local] Hint Resolve wf_liftW wf_liftW_hd : dtt_wf.

Ltac er := apply eq_term_refl; wfx.

(* [A0[u] = A]  implies  [A0[wkn ; u] = A[wkn]] *)
Lemma eq_ty_wkncmp G G0 u i A A0
  : wft G sEnv -> wft G0 sEnv -> wft i sInfo -> wft u (sSub G G0) ->
    wft A (sTy G i) -> wft A0 (sTy G0 i) ->
    eqt (sTy G i) (oTySubst G G0 u i A0) A ->
    eqt (sTy (oExt G i A) i)
      (oTySubst (oExt G i A) G0 (oCmp (oExt G i A) G G0 (oWkn G i A) u) i A0)
      (oTySubst (oExt G i A) G (oWkn G i A) i A).
Proof.
  intros HG HG0 Hi Hu HA HA0 Heq.
  assert (wft (oExt G i A) sEnv) as HE by (apply wf_Ext; assumption).
  assert (wft (oWkn G i A) (sSub (oExt G i A) G)) as HW
      by (apply wf_Wkn; assumption).
  eapply eq_term_trans.
  - apply eq_term_sym; apply eq_ty_subst_cmp; assumption.
  - apply TySubst_cong with (A1 := oTySubst G G0 u i A0) (A2 := A);
      [ er | er | er | er | exact Heq ].
Qed.

(* The canonical sort of the head variable under a lift. *)
Lemma eq_ty_liftW_canon D G w i A A'
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sTy (oExt D i A') i)
      (oTySubst (oExt D i A') (oExt G i A) (oLiftW D G w i A A') i
         (oTySubst (oExt G i A) G (oWkn G i A) i A))
      (oTySubst (oExt D i A') D (oWkn D i A') i A').
Proof.
  intros HD HG Hi HA HA' Hw Heq.
  assert (wft (oExt D i A') sEnv) as HE by (apply wf_Ext; assumption).
  assert (wft (oExt G i A) sEnv) as HEG by (apply wf_Ext; assumption).
  assert (wft (oWkn D i A') (sSub (oExt D i A') D)) as HWD
      by (apply wf_Wkn; assumption).
  assert (wft (oWkn G i A) (sSub (oExt G i A) G)) as HWG
      by (apply wf_Wkn; assumption).
  assert (wft (oLiftW D G w i A A') (sSub (oExt D i A') (oExt G i A))) as HL
      by (apply wf_liftW; assumption).
  eapply eq_term_trans.
  - apply eq_ty_subst_cmp; assumption.
  - eapply eq_term_trans.
    + apply TySubst_cong
        with (g1 := oCmp (oExt D i A') (oExt G i A) G (oLiftW D G w i A A')
                      (oWkn G i A))
             (g2 := oCmp (oExt D i A') D G (oWkn D i A') w);
        [ er | er | apply eq_liftW_wkn; assumption | er | er ].
    + apply eq_term_sym; apply eq_wk_lift_ty; assumption.
Qed.

(* [hd[lift(w)] = hd], at [hd]'s own sort. *)
Lemma eq_liftW_hd' D G w i A A'
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sExp (oExt D i A') i (oTySubst (oExt D i A') D (oWkn D i A') i A'))
      (oExpSubst (oExt D i A') (oExt G i A) (oLiftW D G w i A A') i
         (oTySubst (oExt G i A) G (oWkn G i A) i A) (oHd G i A))
      (oHd D i A').
Proof.
  intros.
  assert (wft (oExt D i A') sEnv) by (apply wf_Ext; assumption).
  eapply eq_term_conv; [ apply eq_liftW_hd; assumption | ].
  apply eq_sort_exp_ty.
  apply eq_term_sym; apply eq_wk_lift_ty; assumption.
Qed.

(* [lift(w) ; (wkn ; u) = wkn ; (w ; u)] *)
Lemma eq_liftW_wkn_cmp D G G0 w u i A A'
  : wft D sEnv -> wft G sEnv -> wft G0 sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    wft u (sSub G G0) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sSub (oExt D i A') G0)
      (oCmp (oExt D i A') (oExt G i A) G0 (oLiftW D G w i A A')
         (oCmp (oExt G i A) G G0 (oWkn G i A) u))
      (oCmp (oExt D i A') D G0 (oWkn D i A') (oCmp D G G0 w u)).
Proof.
  intros HD HG HG0 Hi HA HA' Hw Hu Heq.
  assert (wft (oExt D i A') sEnv) as HE by (apply wf_Ext; assumption).
  assert (wft (oExt G i A) sEnv) as HEG by (apply wf_Ext; assumption).
  assert (wft (oWkn D i A') (sSub (oExt D i A') D)) as HWD
      by (apply wf_Wkn; assumption).
  assert (wft (oWkn G i A) (sSub (oExt G i A) G)) as HWG
      by (apply wf_Wkn; assumption).
  assert (wft (oLiftW D G w i A A') (sSub (oExt D i A') (oExt G i A))) as HL
      by (apply wf_liftW; assumption).
  eapply eq_term_trans.
  - apply eq_cmp_assoc; assumption.
  - eapply eq_term_trans.
    + apply Cmp_cong
        with (f1 := oCmp (oExt D i A') (oExt G i A) G (oLiftW D G w i A A')
                      (oWkn G i A))
             (f2 := oCmp (oExt D i A') D G (oWkn D i A') w)
             (g1 := u) (g2 := u);
        [ er | er | er | apply eq_liftW_wkn; assumption | er ].
    + apply eq_term_sym; apply eq_cmp_assoc; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Inverting a weakening whose domain is an extension                   *)
(* ------------------------------------------------------------------ *)

Lemma Wk_ext_inv' E Gt wt
  : Wk E Gt wt ->
    forall G0 i0 A0, E = oExt G0 i0 A0 ->
    (Gt = oExt G0 i0 A0 /\ wt = oId (oExt G0 i0 A0))
    \/ (Gt = G0 /\ TyOk G0 i0 A0 /\ wt = oWkn G0 i0 A0)
    \/ (exists w2, Wk G0 Gt w2 /\ TyOk G0 i0 A0
                   /\ wt = oCmp (oExt G0 i0 A0) G0 Gt (oWkn G0 i0 A0) w2)
    \/ (exists G1 A1 w2,
           Gt = oExt G1 i0 A1 /\ Wk G0 G1 w2
           /\ TyOk G1 i0 A1 /\ TyOk G0 i0 A0
           /\ eqt (sTy G0 i0) (oTySubst G0 G1 w2 i0 A1) A0
           /\ wt = oLiftW G0 G1 w2 i0 A1 A0).
Proof.
  destruct 1 as [ G HG | D i A HD HA | D G i A w HW HA
                | D G i A A' w HW HA HA' Heq ];
    intros G0 i0 A0 HE.
  - left; split; [ exact HE | rewrite HE; reflexivity ].
  - unfold oExt in HE; safe_invert HE.
    right; left; repeat split; assumption.
  - unfold oExt in HE; safe_invert HE.
    right; right; left; exists w; repeat split; assumption.
  - unfold oExt in HE; safe_invert HE.
    right; right; right; exists G, A, w; unfold oLiftW; repeat split;
      assumption.
Qed.

Lemma Wk_ext_inv G0 i0 A0 Gt wt
  : Wk (oExt G0 i0 A0) Gt wt ->
    (Gt = oExt G0 i0 A0 /\ wt = oId (oExt G0 i0 A0))
    \/ (Gt = G0 /\ TyOk G0 i0 A0 /\ wt = oWkn G0 i0 A0)
    \/ (exists w2, Wk G0 Gt w2 /\ TyOk G0 i0 A0
                   /\ wt = oCmp (oExt G0 i0 A0) G0 Gt (oWkn G0 i0 A0) w2)
    \/ (exists G1 A1 w2,
           Gt = oExt G1 i0 A1 /\ Wk G0 G1 w2
           /\ TyOk G1 i0 A1 /\ TyOk G0 i0 A0
           /\ eqt (sTy G0 i0) (oTySubst G0 G1 w2 i0 A1) A0
           /\ wt = oLiftW G0 G1 w2 i0 A1 A0).
Proof. intro H; eapply Wk_ext_inv'; [ exact H | reflexivity ]. Qed.

(* ================================================================== *)
(* Composition of weakenings                                           *)
(* ================================================================== *)

Lemma Wk_cmp D' D G w' w
  : Wk D' D w' -> Wk D G w -> EnvOk D' ->
    exists w'', Wk D' G w'' /\ eqt (sSub D' G) (oCmp D' D G w' w) w''.
Proof.
  intros HW'; revert G w.
  induction HW' as
    [ Gi HGi
    | Di ii Ai HDi HAi
    | Di Gi ii Ai wi HWi IH HAi
    | Di Gi ii Ai Ai' wi HWi IH HAi HAi' Heqi ];
    intros Gt wt Hwt HD'.
  - (* wk_id *)
    exists wt; split; [ assumption | ].
    apply eq_id_left; wfx.
  - (* wk_wkn *)
    exists (oCmp (oExt Di ii Ai) Di Gt (oWkn Di ii Ai) wt).
    split; [ apply wk_ext; assumption | er ].
  - (* wk_ext *)
    destruct (IH Gt wt Hwt (Wk_dom HWi)) as [w0 [Hw0 Heq0]].
    exists (oCmp (oExt Di ii Ai) Di Gt (oWkn Di ii Ai) w0).
    split; [ apply wk_ext; assumption | ].
    eapply eq_term_trans.
    + apply eq_term_sym; apply eq_cmp_assoc; wfx.
    + apply Cmp_cong
        with (f1 := oWkn Di ii Ai) (f2 := oWkn Di ii Ai)
             (g1 := oCmp Di Gi Gt wi wt) (g2 := w0);
        [ er | er | er | er | exact Heq0 ].
  - (* wk_lift *)
    assert (EnvOk Di) as HDi by (eapply Wk_dom; exact HWi).
    change (oSnoc (oExt Di ii Ai') Gi ii Ai
              (oCmp (oExt Di ii Ai') Di Gi (oWkn Di ii Ai') wi)
              (oHd Di ii Ai'))
      with (oLiftW Di Gi wi ii Ai Ai').
    apply Wk_ext_inv in Hwt.
    destruct Hwt as [ [HGt Hwt]
                    | [ [HGt [HA2 Hwt]]
                    | [ [w2 [HW2 [HA2 Hwt]]]
                      | [G1 [A1 [w2 [HGt [HW2 [HA1 [HA2 [Heq2 Hwt]]]]]]]] ] ] ];
      subst.
    + (* inner wk_id *)
      exists (oLiftW Di Gi wi ii Ai Ai'); split;
        [ apply wk_lift'; assumption | ].
      apply eq_id_right; wfx.
    + (* inner wk_wkn: [lift(w) ; wkn = wkn ; w] *)
      exists (oCmp (oExt Di ii Ai') Di Gi (oWkn Di ii Ai') wi).
      split; [ apply wk_ext; assumption | ].
      apply eq_liftW_wkn; [ wfx | wfx | wfx | wfx | wfx | wfx | exact Heqi ].
    + (* inner wk_ext *)
      destruct (IH Gt w2 HW2 HDi) as [w12 [Hw12 Heq12]].
      exists (oCmp (oExt Di ii Ai') Di Gt (oWkn Di ii Ai') w12).
      split; [ apply wk_ext; assumption | ].
      eapply eq_term_trans.
      * apply eq_liftW_wkn_cmp; wfx.
      * apply Cmp_cong
          with (f1 := oWkn Di ii Ai') (f2 := oWkn Di ii Ai')
               (g1 := oCmp Di Gi Gt wi w2) (g2 := w12);
          [ er | er | er | er | exact Heq12 ].
    + (* inner wk_lift *)
      destruct (IH G1 w2 HW2 HDi) as [w12 [Hw12 Heq12]].
      (* the new lift's type equation:  A1[w12] = Ai' *)
      assert (eqt (sTy Di ii) (oTySubst Di G1 w12 ii A1) Ai') as HeqT.
      { eapply eq_term_trans.
        - apply TySubst_cong
            with (g1 := w12) (g2 := oCmp Di Gi G1 wi w2) (A1 := A1) (A2 := A1);
            [ er | er | apply eq_term_sym; exact Heq12 | er | er ].
        - eapply eq_term_trans.
          + apply eq_term_sym; apply eq_ty_subst_cmp; wfx.
          + eapply eq_term_trans;
              [ apply TySubst_cong
                  with (g1 := wi) (g2 := wi)
                       (A1 := oTySubst Gi G1 w2 ii A1) (A2 := Ai);
                [ er | er | er | er | exact Heq2 ]
              | exact Heqi ]. }
      exists (oLiftW Di G1 w12 ii A1 Ai').
      split; [ apply wk_lift'; assumption | ].
      eapply eq_term_trans.
      * unfold oLiftW at 2; apply eq_cmp_snoc; wfx.
      * unfold oLiftW at 2.
        apply Snoc_cong;
          [ er | er | er | er
          | (* the substitution component *)
            eapply eq_term_trans;
            [ apply eq_liftW_wkn_cmp; wfx
            | apply Cmp_cong
                with (f1 := oWkn Di ii Ai') (f2 := oWkn Di ii Ai')
                     (g1 := oCmp Di Gi G1 wi w2) (g2 := w12);
              [ er | er | er | er | exact Heq12 ] ]
          | (* the head-variable component *)
            eapply eq_term_conv;
            [ eapply eq_term_trans;
              [ eapply eq_term_conv;
                [ apply ExpSubst_cong
                    with (g1 := oLiftW Di Gi wi ii Ai Ai')
                         (g2 := oLiftW Di Gi wi ii Ai Ai')
                         (A1 := oTySubst (oExt Gi ii Ai) G1
                                  (oCmp (oExt Gi ii Ai) Gi G1
                                     (oWkn Gi ii Ai) w2) ii A1)
                         (A2 := oTySubst (oExt Gi ii Ai) Gi
                                  (oWkn Gi ii Ai) ii Ai)
                         (v1 := oHd Gi ii Ai) (v2 := oHd Gi ii Ai);
                  [ er | er | er | er
                  | apply eq_ty_wkncmp; wfx
                  | er ]
                | apply eq_sort_exp_ty; apply eq_ty_liftW_canon; wfx ]
              | apply eq_liftW_hd'; wfx ]
            | apply eq_sort_exp_ty; apply eq_wk_lift_ty; wfx ] ].
Qed.

(* ================================================================== *)
(* THE "next0" BRIDGE, PAID FOR ONCE                                   *)
(*                                                                     *)
(* [iCode L0 = info rel (next L0)] and [info rel (iota L1)] are the two *)
(* spellings the elaborator left behind.  [NormalForms.v] pins every          *)
(* canonical form to the [iCode] spelling; "Nat subst", "Pi_irr" and    *)
(* "Pi_irr subst" use the other one.  The lemmas below restate exactly  *)
(* those rules in the [iCode] spelling, so that nothing downstream ever *)
(* has to see the mismatch again.                                      *)
(* ================================================================== *)

Lemma wf_U0i G r
  : wft G sEnv -> wft r sRelevance ->
    wft (oU G r oL0) (sTy G (oInfo oRel (oIota oL1))).
Proof.
  intros; eapply wf_term_conv; [ apply wf_U; auto using wf_L0 | ].
  apply sTy_cong; [ er | apply eq_info_next0 ].
Qed.

Lemma eq_sort_code0 G r
  : wft G sEnv -> wft r sRelevance ->
    eq_sort ott_dtt [] (sCode G r oL0)
      (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)).
Proof.
  intros; apply sExp_cong;
    [ er | apply eq_info_next0 | apply eq_term_refl; apply wf_U0i; assumption ].
Qed.

Lemma wft_c2i G r e
  : wft G sEnv -> wft r sRelevance -> wft e (sCode G r oL0) ->
    wft e (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)).
Proof.
  intros; eapply wf_term_conv; [ eassumption | apply eq_sort_code0; assumption ].
Qed.

Lemma wft_i2c G r e
  : wft G sEnv -> wft r sRelevance ->
    wft e (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)) ->
    wft e (sCode G r oL0).
Proof.
  intros; eapply wf_term_conv;
    [ eassumption | apply eq_sort_sym; apply eq_sort_code0; assumption ].
Qed.

Lemma eqt_i2c G r e1 e2
  : wft G sEnv -> wft r sRelevance ->
    eqt (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)) e1 e2 ->
    eqt (sCode G r oL0) e1 e2.
Proof.
  intros; eapply eq_term_conv;
    [ eassumption | apply eq_sort_sym; apply eq_sort_code0; assumption ].
Qed.

Lemma eqt_c2i G r e1 e2
  : wft G sEnv -> wft r sRelevance -> eqt (sCode G r oL0) e1 e2 ->
    eqt (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)) e1 e2.
Proof.
  intros; eapply eq_term_conv; [ eassumption | apply eq_sort_code0; assumption ].
Qed.

#[local] Hint Resolve wf_U0i wft_c2i wft_i2c : dtt_wf.

(* The substituted-universe sort is the universe sort. *)
Lemma eq_sort_Usub G G' g r l
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft r sRelevance -> wft l sLvl ->
    eq_sort ott_dtt []
      (sExp G (iCode l) (oTySubst G G' g (iCode l) (oU G' r l)))
      (sCode G r l).
Proof.
  intros; apply eq_sort_exp_ty; apply eq_U_subst; assumption.
Qed.

Lemma eqt_Usub_c G G' g r l e1 e2
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft r sRelevance -> wft l sLvl ->
    eqt (sExp G (iCode l) (oTySubst G G' g (iCode l) (oU G' r l))) e1 e2 ->
    eqt (sCode G r l) e1 e2.
Proof.
  intros; eapply eq_term_conv; [ eassumption | apply eq_sort_Usub; assumption ].
Qed.

(* "U subst" in the [iota L1] spelling. *)
Lemma eq_U_subst0i G G' g r
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') -> wft r sRelevance ->
    eqt (sTy G (oInfo oRel (oIota oL1)))
      (oTySubst G G' g (oInfo oRel (oIota oL1)) (oU G' r oL0))
      (oU G r oL0).
Proof.
  intros HG HG' Hg Hr.
  eapply eq_term_trans.
  - apply eq_term_sym.
    apply TySubst_cong
      with (G1 := G) (G2 := G) (G1' := G') (G2' := G') (g1 := g) (g2 := g)
           (i1 := iCode oL0) (i2 := oInfo oRel (oIota oL1))
           (A1 := oU G' r oL0) (A2 := oU G' r oL0);
      [ er | er | er | apply eq_info_next0
      | apply eq_term_refl; apply wf_U0i; assumption ].
  - eapply eq_term_conv.
    + apply eq_U_subst; auto using wf_L0.
    + apply sTy_cong; [ er | apply eq_info_next0 ].
Qed.

(* "Nat subst" in the [iCode] spelling. *)
Lemma eq_Nat_subst' G G' g
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    eqt (sCode G oRel oL0)
      (oExpSubst G G' g (iCode oL0) (oU G' oRel oL0) (oNat G')) (oNat G).
Proof.
  intros HG HG' Hg.
  apply eqt_i2c; [ assumption | apply wf_Rel | ].
  eapply eq_term_trans;
    [ | apply eq_Nat_subst with (G := G) (G' := G') (g := g); assumption ].
  eapply eq_term_conv.
  - apply ExpSubst_cong
      with (G1 := G) (G2 := G) (G1' := G') (G2' := G') (g1 := g) (g2 := g)
           (i1 := iCode oL0) (i2 := oInfo oRel (oIota oL1))
           (A1 := oU G' oRel oL0) (A2 := oU G' oRel oL0)
           (v1 := oNat G') (v2 := oNat G');
      [ er | er | er | apply eq_info_next0
      | apply eq_term_refl; apply wf_U0i; auto using wf_Rel
      | apply eq_term_refl; apply wft_c2i;
        [ assumption | apply wf_Rel | apply wf_Nat; assumption ] ].
  - apply eq_sort_exp_ty; apply eq_U_subst0i; auto using wf_Rel.
Qed.

(* The substituted domain code, and the lifted substitution, are well
   typed. *)
Lemma wf_CodeSubst G G' g r l F
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft r sRelevance -> wft l sLvl -> wft F (sCode G' r l) ->
    wft (oCodeSubst G G' g r l F) (sCode G r l).
Proof.
  intros; unfold oCodeSubst.
  eapply wf_term_conv;
    [ apply wf_ExpSubst; wfa | apply eq_sort_Usub; assumption ].
Qed.

#[local] Hint Resolve wf_CodeSubst : dtt_wf.

Lemma wf_oLift G G' g rF lF F
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft rF sRelevance -> wft lF sLvl -> wft F (sCode G' rF lF) ->
    wft (oLift G G' g rF lF F)
      (sSub (oExtC G rF lF (oCodeSubst G G' g rF lF F)) (oExtC G' rF lF F)).
Proof.
  intros; rewrite oLift_oLiftW.
  apply wf_liftW; try wfa.
  apply eq_El_subst; assumption.
Qed.

#[local] Hint Resolve wf_oLift : dtt_wf.

(* "Pi_irr subst" in the [iCode] spelling, on both the conclusion and the
   codomain code. *)
Lemma eq_Pi_irr_subst' G G' g rF lF F B
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft rF sRelevance -> wft lF sLvl ->
    wft F (sCode G' rF lF) ->
    wft B (sCode (oExtC G' rF lF F) oIrr oL0) ->
    eqt (sCode G oIrr oL0)
      (oExpSubst G G' g (iCode oL0) (oU G' oIrr oL0) (oPiIrr G' rF lF F B))
      (oPiIrr G rF lF (oCodeSubst G G' g rF lF F)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iCode oL0) (oU (oExtC G' rF lF F) oIrr oL0) B)).
Proof.
  intros HG HG' Hg HrF HlF HF HB.
  assert (wft (oExtC G' rF lF F) sEnv) as HX' by wfa.
  assert (wft (oExtC G rF lF (oCodeSubst G G' g rF lF F)) sEnv) as HX by wfa.
  assert (wft B (sExp (oExtC G' rF lF F) (oInfo oRel (oIota oL1))
                   (oU (oExtC G' rF lF F) oIrr oL0))) as HBi
      by (apply wft_c2i; auto using wf_Irr).
  apply eqt_i2c; [ assumption | apply wf_Irr | ].
  eapply eq_term_trans.
  - (* bring the outer substitution's info to the [iota L1] spelling *)
    eapply eq_term_conv.
    + apply ExpSubst_cong
        with (G1 := G) (G2 := G) (G1' := G') (G2' := G') (g1 := g) (g2 := g)
             (i1 := iCode oL0) (i2 := oInfo oRel (oIota oL1))
             (A1 := oU G' oIrr oL0) (A2 := oU G' oIrr oL0)
             (v1 := oPiIrr G' rF lF F B) (v2 := oPiIrr G' rF lF F B);
        [ er | er | er | apply eq_info_next0
        | apply eq_term_refl; apply wf_U0i; auto using wf_Irr
        | apply eq_term_refl; apply wf_PiIrr; assumption ].
    + apply eq_sort_exp_ty; apply eq_U_subst0i; auto using wf_Irr.
  - eapply eq_term_trans.
    + apply eq_Pi_irr_subst; assumption.
    + (* bring the codomain's info back to the [iCode] spelling *)
      apply PiIrr_cong;
        [ er | er | er
        | apply eq_term_refl; apply wf_CodeSubst; assumption
        | apply eqt_c2i; [ assumption | apply wf_Irr | ] ].
      eapply eqt_Usub_c;
        [ exact HX | exact HX' | apply wf_oLift; assumption
        | apply wf_Irr | apply wf_L0 | ].
      apply ExpSubst_cong
        with (G1 := oExtC G rF lF (oCodeSubst G G' g rF lF F))
             (G2 := oExtC G rF lF (oCodeSubst G G' g rF lF F))
             (G1' := oExtC G' rF lF F) (G2' := oExtC G' rF lF F)
             (g1 := oLift G G' g rF lF F) (g2 := oLift G G' g rF lF F)
             (i1 := oInfo oRel (oIota oL1)) (i2 := iCode oL0)
             (A1 := oU (oExtC G' rF lF F) oIrr oL0)
             (A2 := oU (oExtC G' rF lF F) oIrr oL0)
             (v1 := B) (v2 := B);
        [ er | er | apply eq_term_refl; apply wf_oLift; assumption
        | apply eq_term_sym; apply eq_info_next0
        | apply eq_term_refl; apply wf_U; auto using wf_Irr, wf_L0
        | er ].
Qed.

(* ================================================================== *)
(* WEAKENING A NORMAL CODE / TYPE                                      *)
(*                                                                     *)
(* The theorem is stated in the plain                                  *)
(*     exists A', TyOk D i A' /\ [A[w]] provably equal to [A']         *)
(* form, and that form drives its own induction, because Layer 0.5     *)
(* IDENTIFIES the representative: [Inj.TyOk_inj] and [Inj.NfCode_inj]  *)
(* say that two normal objects of the same sort that are provably      *)
(* equal are SYNTACTICALLY equal.  [TyOk_pin] / [NfCode_pin] below are *)
(* those two theorems in the shape this file uses them.                *)
(*                                                                     *)
(* So wherever a clause needs the weakened type to have a particular   *)
(* SHAPE -- at [neet_app_rel] the argument must be typed at the domain *)
(* code that the head's type produced, and [NfET]'s clauses dispatch   *)
(* on the head of the type -- one BUILDS the canonical witness out of  *)
(* [TyOk_wk]/[NfCode_wk] on the components, and pins the induction     *)
(* hypothesis's own representative to it.                              *)
(* ================================================================== *)

(* ---- inversion helpers ---- *)

Lemma VarT_hd_or_sub G i A x
  : VarT G i A x ->
    (exists G0 i0 A0, x = oHd G0 i0 A0)
    \/ (exists G0 G1 w0 i0 A0 x0, x = oExpSubst G0 G1 w0 i0 A0 x0).
Proof. destruct 1; [ left | right ]; eauto 10. Qed.

Ltac no_var H :=
  apply VarT_hd_or_sub in H;
  destruct H as [ [? [? [? H]]] | [? [? [? [? [? [? H]]]]]] ];
  cbv [oHd oExpSubst oNat oEmpty oPiRel oPiIrr oU oEl] in H;
  discriminate H.

Lemma TyOk_inv G i A
  : TyOk G i A ->
    (exists r l, A = oU G r l /\ i = iCode l
                 /\ EnvOk G /\ RelNf r /\ LvlNf l)
    \/ (exists r l c, A = oEl G r l c /\ i = iEl r l /\ NfCode G r l c).
Proof.
  destruct 1 as [ G r l HG Hr Hl | G r l c Hc ].
  - left; exists r, l; repeat split; assumption.
  - right; exists r, l, c; repeat split; assumption.
Qed.

(* The INFO IS ALREADY PINNED here: this is the only [TyOk_El_inv] in the
   development, and it is deliberately the weaker of the two forms that
   used to exist -- it does not also conclude [i = iEl r l] for an
   arbitrary [i], because nothing needs that.  [TyOk_inv] above is the
   general form to reach for if it is ever wanted. *)
Lemma TyOk_El_inv G r l c : TyOk G (iEl r l) (oEl G r l c) -> NfCode G r l c.
Proof.
  intro H; apply TyOk_inv in H;
    destruct H as [ [r0 [l0 [HA _]]] | [r0 [l0 [c0 [HA [Hi Hc]]]]] ].
  - cbv [oU oEl] in HA; discriminate.
  - cbv [oEl] in HA; safe_invert HA; assumption.
Qed.

(* A normal type at a CODE info is a universe, and conversely. *)
Lemma TyOk_iCode_shape G l A : TyOk G (iCode l) A -> exists r, A = oU G r l.
Proof.
  intro H; apply TyOk_inv in H;
    destruct H as [ [r [l0 [HA [Hi _]]]] | [r [l0 [c [HA [Hi _]]]]] ].
  - exists r; cbv [iCode oInfo oNext] in Hi; safe_invert Hi; congruence.
  - cbv [iEl iCode oInfo oIota oNext] in Hi; discriminate.
Qed.

Lemma TyOk_U_info G i G' r l A : TyOk G i A -> A = oU G' r l -> i = iCode l.
Proof.
  intros H HA; apply TyOk_inv in H;
    destruct H as [ [r0 [l0 [HA0 [Hi _]]]] | [r0 [l0 [c [HA0 [Hi _]]]]] ].
  - cbv [oU] in HA0, HA; congruence.
  - cbv [oU oEl] in HA0, HA; congruence.
Qed.

(* A lifted weakening that is provably the identity is the identity. *)
Lemma eq_liftW_id G i A w
  : wft G sEnv -> wft i sInfo -> wft A (sTy G i) -> wft w (sSub G G) ->
    eqt (sSub G G) w (oId G) ->
    eqt (sSub (oExt G i A) (oExt G i A)) (oLiftW G G w i A A)
      (oId (oExt G i A)).
Proof.
  intros HG Hi HA Hw Hid.
  assert (wft (oExt G i A) sEnv) as HE by (apply wf_Ext; assumption).
  assert (wft (oWkn G i A) (sSub (oExt G i A) G)) as HW
      by (apply wf_Wkn; assumption).
  eapply eq_term_trans; [ | apply eq_snoc_wkn_hd; assumption ].
  unfold oLiftW; apply Snoc_cong;
    [ er | er | er | er
    | eapply eq_term_trans;
      [ apply Cmp_cong with (f1 := oWkn G i A) (f2 := oWkn G i A)
                            (g1 := w) (g2 := oId G);
        [ er | er | er | er | exact Hid ]
      | apply eq_id_right; assumption ]
    | apply eq_term_refl; apply wf_Hd; assumption ].
Qed.

(* ---- LAYER 0.5: THE NORMAL REPRESENTATIVE IS UNIQUE ----             *)
(*                                                                      *)
(* Everything the old [CodeSub]/[TySub] shape relations were built to    *)
(* supply -- determinism of the substituted type, and its head -- comes  *)
(* from these two, plus the canonical witness built by hand.            *)

Lemma TyOk_pin G i e A1 A2
  : TyOk G i A1 -> TyOk G i A2 ->
    eqt (sTy G i) e A1 -> eqt (sTy G i) e A2 -> A1 = A2.
Proof.
  intros H1 H2 E1 E2; eapply TyOk_inj; [ exact H1 | exact H2 | ].
  eapply eq_term_trans; [ apply eq_term_sym; exact E1 | exact E2 ].
Qed.

Lemma NfCode_pin G r l e c1 c2
  : NfCode G r l c1 -> NfCode G r l c2 ->
    eqt (sCode G r l) e c1 -> eqt (sCode G r l) e c2 -> c1 = c2.
Proof.
  intros H1 H2 E1 E2; eapply NfCode_inj; [ exact H1 | exact H2 | ].
  eapply eq_term_trans; [ apply eq_term_sym; exact E1 | exact E2 ].
Qed.

(* ---- the shape of a normal code, read off its head ---- *)

Lemma NfCode_pi_rel_inv' G r l c
  : NfCode G r l c ->
    forall rF lF lG F B, c = oPiRel G rF lF lG F B ->
      RelNf rF /\ LvlNf lF /\ LvlNf l
      /\ NfCode G rF lF F /\ NfCode (oExtC G rF lF F) oRel l B.
Proof.
  destruct 1 as
    [ G HG | G HG
    | G rF0 lF0 lG0 F0 B0 HrF HlF HlG HF HB
    | G rF0 lF0 F0 B0 HrF HlF HF HB
    | G r l c Hx ];
    intros rF lF lG F B Hc.
  - cbv [oNat oPiRel] in Hc; discriminate.
  - cbv [oEmpty oPiRel] in Hc; discriminate.
  - cbv [oPiRel] in Hc; safe_invert Hc; repeat split; assumption.
  - cbv [oPiIrr oPiRel] in Hc; discriminate.
  - rewrite Hc in Hx; no_var Hx.
Qed.

Lemma NfCode_pi_rel_inv G rF lF lG F B
  : NfCode G oRel lG (oPiRel G rF lF lG F B) ->
    RelNf rF /\ LvlNf lF /\ LvlNf lG
    /\ NfCode G rF lF F /\ NfCode (oExtC G rF lF F) oRel lG B.
Proof. intro H; eapply NfCode_pi_rel_inv'; [ exact H | reflexivity ]. Qed.

Lemma NfCode_pi_irr_inv' G r l c
  : NfCode G r l c ->
    forall rF lF F B, c = oPiIrr G rF lF F B ->
      RelNf rF /\ LvlNf lF
      /\ NfCode G rF lF F /\ NfCode (oExtC G rF lF F) oIrr oL0 B.
Proof.
  destruct 1 as
    [ G HG | G HG
    | G rF0 lF0 lG0 F0 B0 HrF HlF HlG HF HB
    | G rF0 lF0 F0 B0 HrF HlF HF HB
    | G r l c Hx ];
    intros rF lF F B Hc.
  - cbv [oNat oPiIrr] in Hc; discriminate.
  - cbv [oEmpty oPiIrr] in Hc; discriminate.
  - cbv [oPiRel oPiIrr] in Hc; discriminate.
  - cbv [oPiIrr] in Hc; safe_invert Hc; repeat split; assumption.
  - rewrite Hc in Hx; no_var Hx.
Qed.

Lemma NfCode_pi_irr_inv G rF lF F B
  : NfCode G oIrr oL0 (oPiIrr G rF lF F B) ->
    RelNf rF /\ LvlNf lF
    /\ NfCode G rF lF F /\ NfCode (oExtC G rF lF F) oIrr oL0 B.
Proof. intro H; eapply NfCode_pi_irr_inv'; [ exact H | reflexivity ]. Qed.

(* The two lifted weakenings of a type agree when the types do. *)
Lemma eq_liftW_cong D G w i A A1 A2
  : wft D sEnv -> wft G sEnv -> wft i sInfo -> wft A (sTy G i) ->
    wft A1 (sTy D i) -> wft A2 (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A1 ->
    eqt (sTy D i) (oTySubst D G w i A) A2 ->
    eqt (sSub (oExt D i A2) (oExt G i A))
      (oLiftW D G w i A A1) (oLiftW D G w i A A2).
Proof.
  intros HD HG Hi HA HA1 HA2 Hw H1 H2.
  assert (eqt (sTy D i) A1 A2) as H12
      by (eapply eq_term_trans; [ apply eq_term_sym; exact H1 | exact H2 ]).
  assert (eqt sEnv (oExt D i A1) (oExt D i A2)) as HE
      by (apply Ext_cong; [ er | er | exact H12 ]).
  unfold oLiftW; apply Snoc_cong;
    [ exact HE | er | er | er
    | apply Cmp_cong;
      [ exact HE | er | er
      | apply Wkn_cong; [ er | er | exact H12 ]
      | er ]
    | ].
  eapply eq_term_conv.
  - apply Hd_cong; [ er | er | exact H12 ].
  - apply eq_sort_exp_ty; apply eq_wk_lift_ty; assumption.
Qed.

(* ---- the canonical weakenings, once and for all ---- *)

(* Weakening an [El] of a normal code. *)
Lemma eq_El_wk D G w r l c c'
  : Wk D G w -> EnvOk D -> NfCode G r l c -> NfCode D r l c' ->
    eqt (sCode D r l) (oExpSubst D G w (iCode l) (oU G r l) c) c' ->
    eqt (sTy D (iEl r l))
      (oTySubst D G w (iEl r l) (oEl G r l c)) (oEl D r l c').
Proof.
  intros HW HD Hc Hc' Heqc.
  eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
  apply El_cong; [ er | er | er | exact Heqc ].
Qed.

(* Lifting a weakening over a binder whose domain code is [F], given the
   normal representative [F'] of [F[w]]. *)
Lemma Wk_liftC D G w rF lF F F'
  : Wk D G w -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (oCodeSubst D G w rF lF F) F' ->
    Wk (oExtC D rF lF F') (oExtC G rF lF F)
      (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
    /\ EnvOk (oExtC D rF lF F')
    /\ eqt (sTy D (iEl rF lF))
         (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F').
Proof.
  intros HW HD HF HF' HeqF.
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
    as HeqEl by (apply eq_El_wk; assumption).
  repeat split;
    [ apply wk_lift';
      [ assumption | apply tyok_El; assumption | apply tyok_El; assumption
      | exact HeqEl ]
    | apply envok_ext; [ assumption | apply tyok_El; assumption ]
    | exact HeqEl ].
Qed.

(* The substitution rules lift [g] with [oLift] (whose domain code is the
   UNREDUCED [g[F]]); the induction lifts it with [oLiftW] over the normal
   [F'].  This moves between the two.  Stated for an arbitrary [g] -- the
   body needs nothing but its [wf_term] -- and specialized to a weakening
   just below. *)
Lemma eq_lift_shift' D G g rF lF F F' i A v
  : wft D sEnv -> wft G sEnv -> wft g (sSub D G) ->
    NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (oCodeSubst D G g rF lF F) F' ->
    wft i sInfo -> wft A (sTy (oExtC G rF lF F) i) ->
    wft v (sExp (oExtC G rF lF F) i A) ->
    eqt (sExp (oExtC D rF lF F') i
           (oTySubst (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
              i A))
      (oExpSubst (oExtC D rF lF (oCodeSubst D G g rF lF F)) (oExtC G rF lF F)
         (oLift D G g rF lF F) i A v)
      (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         i A v).
Proof.
  intros HD HG Hg HF HF' HeqF Hi HA Hv.
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G g (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
    as HeqEl.
  { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
    apply El_cong; [ er | er | er | exact HeqF ]. }
  apply ExpSubst_cong
    with (G1 := oExtC D rF lF (oCodeSubst D G g rF lF F))
         (G2 := oExtC D rF lF F')
         (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
         (g1 := oLift D G g rF lF F)
         (g2 := oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (i1 := i) (i2 := i) (A1 := A) (A2 := A) (v1 := v) (v2 := v);
    [ apply Ext_cong; [ er | er | apply El_cong; [ er | er | er | exact HeqF ] ]
    | er
    | rewrite oLift_oLiftW;
      apply eq_liftW_cong
        with (A1 := oEl D rF lF (oCodeSubst D G g rF lF F))
             (A2 := oEl D rF lF F');
      [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
      | apply eq_El_subst; wfx | exact HeqEl ]
    | er | er | er ].
Qed.

Lemma eq_lift_shift D G w rF lF F F' i A v
  : Wk D G w -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (oCodeSubst D G w rF lF F) F' ->
    wft i sInfo -> wft A (sTy (oExtC G rF lF F) i) ->
    wft v (sExp (oExtC G rF lF F) i A) ->
    eqt (sExp (oExtC D rF lF F') i
           (oTySubst (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
              i A))
      (oExpSubst (oExtC D rF lF (oCodeSubst D G w rF lF F)) (oExtC G rF lF F)
         (oLift D G w rF lF F) i A v)
      (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         i A v).
Proof. intros; apply eq_lift_shift'; wfx. Qed.

(* The [Pi] cases of the code computation.  They are needed twice -- to
   RUN the induction below, and to READ ITS RESULT BACK at the [app]
   clauses -- so they are factored out here. *)

Lemma eq_pi_rel_wk D G w rF lF lG F B F' B'
  : Wk D G w -> EnvOk D ->
    NfCode G rF lF F -> NfCode (oExtC G rF lF F) oRel lG B ->
    NfCode D rF lF F' -> NfCode (oExtC D rF lF F') oRel lG B' ->
    eqt (sCode D rF lF) (oExpSubst D G w (iCode lF) (oU G rF lF) F) F' ->
    eqt (sCode (oExtC D rF lF F') oRel lG)
      (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (iCode lG) (oU (oExtC G rF lF F) oRel lG) B) B' ->
    eqt (sCode D oRel lG)
      (oExpSubst D G w (iCode lG) (oU G oRel lG) (oPiRel G rF lF lG F B))
      (oPiRel D rF lF lG F' B').
Proof.
  intros HW HD HF HB HF' HB' HeqF HeqB.
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
    as HeqEl by (apply eq_El_wk; assumption).
  eapply eq_term_trans; [ apply eq_Pi_rel_subst; wfx | ].
  apply PiRel_cong; [ er | er | er | er | exact HeqF | ].
  eapply eq_term_trans; [ | exact HeqB ].
  eapply eqt_Usub_c
    with (G' := oExtC G rF lF F)
         (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (r := oRel) (l := lG);
    [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
  apply eq_lift_shift; wfx.
Qed.

Lemma eq_pi_irr_wk D G w rF lF F B F' B'
  : Wk D G w -> EnvOk D ->
    NfCode G rF lF F -> NfCode (oExtC G rF lF F) oIrr oL0 B ->
    NfCode D rF lF F' -> NfCode (oExtC D rF lF F') oIrr oL0 B' ->
    eqt (sCode D rF lF) (oExpSubst D G w (iCode lF) (oU G rF lF) F) F' ->
    eqt (sCode (oExtC D rF lF F') oIrr oL0)
      (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (iCode oL0) (oU (oExtC G rF lF F) oIrr oL0) B) B' ->
    eqt (sCode D oIrr oL0)
      (oExpSubst D G w (iCode oL0) (oU G oIrr oL0) (oPiIrr G rF lF F B))
      (oPiIrr D rF lF F' B').
Proof.
  intros HW HD HF HB HF' HB' HeqF HeqB.
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
    as HeqEl by (apply eq_El_wk; assumption).
  eapply eq_term_trans; [ apply eq_Pi_irr_subst'; wfx | ].
  apply eqt_i2c; [ wfx | apply wf_Irr | ].
  apply PiIrr_cong; [ er | er | er | exact HeqF | ].
  apply eqt_c2i; [ wfx | apply wf_Irr | ].
  eapply eq_term_trans; [ | exact HeqB ].
  eapply eqt_Usub_c
    with (G' := oExtC G rF lF F)
         (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (r := oIrr) (l := oL0);
    [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
  apply eq_lift_shift; wfx.
Qed.

(* [Nat] and [Empty] at an [El]. *)

Lemma eq_El_nat_wk D G w
  : Wk D G w -> EnvOk D -> EnvOk G ->
    eqt (sTy D (iEl oRel oL0))
      (oTySubst D G w (iEl oRel oL0) (oEl G oRel oL0 (oNat G)))
      (oEl D oRel oL0 (oNat D)).
Proof.
  intros HW HD HG; apply eq_El_wk;
    [ exact HW | exact HD | apply nfcode_nat; exact HG
    | apply nfcode_nat; exact HD | apply eq_Nat_subst'; wfx ].
Qed.

Lemma eq_El_empty_wk D G w
  : Wk D G w -> EnvOk D -> EnvOk G ->
    eqt (sTy D (iEl oIrr oL0))
      (oTySubst D G w (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)))
      (oEl D oIrr oL0 (oEmpty D)).
Proof.
  intros HW HD HG; apply eq_El_wk;
    [ exact HW | exact HD | apply nfcode_empty; exact HG
    | apply nfcode_empty; exact HD | apply eq_Empty_subst; wfx ].
Qed.

(* A weakened universe is the universe: this is where the code fragment's
   variable clause cashes in [TyOk_pin]. *)
Lemma TyOk_wk_U D G w r l A'
  : Wk D G w -> EnvOk D -> RelNf r -> LvlNf l ->
    TyOk D (iCode l) A' ->
    eqt (sTy D (iCode l)) (oTySubst D G w (iCode l) (oU G r l)) A' ->
    A' = oU D r l.
Proof.
  intros HW HD Hr Hl HA' Heq.
  eapply TyOk_pin;
    [ exact HA' | apply tyok_U; assumption | exact Heq
    | apply eq_U_subst; wfx ].
Qed.

(* ---- the "one more wkn" step, shared by both variable clauses ---- *)

Lemma eq_wkn_step_ty D0 j C GG w0 i A A0 A''
  : wft D0 sEnv -> wft j sInfo -> wft C (sTy D0 j) -> wft GG sEnv ->
    wft w0 (sSub D0 GG) -> wft i sInfo -> wft A (sTy GG i) ->
    wft A0 (sTy D0 i) ->
    eqt (sTy D0 i) (oTySubst D0 GG w0 i A) A0 ->
    eqt (sTy (oExt D0 j C) i)
      (oTySubst (oExt D0 j C) GG
         (oCmp (oExt D0 j C) D0 GG (oWkn D0 j C) w0) i A) A'' ->
    eqt (sTy (oExt D0 j C) i)
      (oTySubst (oExt D0 j C) D0 (oWkn D0 j C) i A0) A''.
Proof.
  intros HD0 Hj HC HGG Hw0 Hi HA HA0 H1 H2.
  assert (wft (oExt D0 j C) sEnv) as HE by (apply wf_Ext; assumption).
  assert (wft (oWkn D0 j C) (sSub (oExt D0 j C) D0)) as HW
      by (apply wf_Wkn; assumption).
  eapply eq_term_trans; [ | exact H2 ].
  eapply eq_term_trans.
  - apply TySubst_cong
      with (G1 := oExt D0 j C) (G2 := oExt D0 j C) (G1' := D0) (G2' := D0)
           (g1 := oWkn D0 j C) (g2 := oWkn D0 j C) (i1 := i) (i2 := i)
           (A1 := A0) (A2 := oTySubst D0 GG w0 i A);
      [ er | er | er | er | apply eq_term_sym; exact H1 ].
  - apply eq_ty_subst_cmp; assumption.
Qed.

Lemma eq_wkn_step D0 j C GG w0 i A A0 x x0 A''
  : wft D0 sEnv -> wft j sInfo -> wft C (sTy D0 j) -> wft GG sEnv ->
    wft w0 (sSub D0 GG) -> wft i sInfo -> wft A (sTy GG i) ->
    wft A0 (sTy D0 i) -> wft x (sExp GG i A) -> wft x0 (sExp D0 i A0) ->
    eqt (sTy D0 i) (oTySubst D0 GG w0 i A) A0 ->
    eqt (sExp D0 i A0) (oExpSubst D0 GG w0 i A x) x0 ->
    eqt (sTy (oExt D0 j C) i)
      (oTySubst (oExt D0 j C) GG
         (oCmp (oExt D0 j C) D0 GG (oWkn D0 j C) w0) i A) A'' ->
    eqt (sExp (oExt D0 j C) i A'')
      (oExpSubst (oExt D0 j C) GG
         (oCmp (oExt D0 j C) D0 GG (oWkn D0 j C) w0) i A x)
      (oExpSubst (oExt D0 j C) D0 (oWkn D0 j C) i A0 x0).
Proof.
  intros HD0 Hj HC HGG Hw0 Hi HA HA0 Hx Hx0 H1 H2 H3.
  assert (wft (oExt D0 j C) sEnv) as HE by (apply wf_Ext; assumption).
  assert (wft (oWkn D0 j C) (sSub (oExt D0 j C) D0)) as HW
      by (apply wf_Wkn; assumption).
  eapply eq_term_conv;
    [ | apply eq_sort_exp_ty; eapply eq_wkn_step_ty with (GG := GG) (w0 := w0) (A := A);
          eassumption ].
  eapply eq_term_trans.
  - eapply eq_term_conv.
    + apply eq_term_sym; apply eq_exp_subst_cmp; assumption.
    + apply eq_sort_exp_ty; apply TySubst_cong
            with (G1 := oExt D0 j C) (G2 := oExt D0 j C) (G1' := D0) (G2' := D0)
                 (g1 := oWkn D0 j C) (g2 := oWkn D0 j C) (i1 := i) (i2 := i)
                 (A1 := oTySubst D0 GG w0 i A) (A2 := A0);
          [ er | er | er | er | exact H1 ].
  - apply ExpSubst_cong
      with (G1 := oExt D0 j C) (G2 := oExt D0 j C) (G1' := D0) (G2' := D0)
           (g1 := oWkn D0 j C) (g2 := oWkn D0 j C) (i1 := i) (i2 := i)
           (A1 := oTySubst D0 GG w0 i A) (A2 := A0)
           (v1 := oExpSubst D0 GG w0 i A x) (v2 := x0);
      [ er | er | er | er | exact H1 | exact H2 ].
Qed.

(* ---- weakening a head variable ---- *)

Lemma vart_hd_wk_gen D GG w
  : Wk D GG w ->
    forall G i A A', GG = oExt G i A ->
      EnvOk G -> TyOk G i A -> TyOk (oExt G i A) i A' ->
      eqt (sTy (oExt G i A) i)
          (oTySubst (oExt G i A) G (oWkn G i A) i A) A' ->
      (forall D0 w0, Wk D0 (oExt G i A) w0 ->
          exists A'', TyOk D0 i A''
                   /\ eqt (sTy D0 i)
                        (oTySubst D0 (oExt G i A) w0 i A') A'') ->
      exists A'' x', TyOk D i A''
                  /\ eqt (sTy D i) (oTySubst D GG w i A') A''
                  /\ VarT D i A'' x'
                  /\ eqt (sExp D i A'') (oExpSubst D GG w i A' (oHd G i A)) x'.
Proof.
  induction 1 as
    [ G0 HG0
    | D0 j C HD0 HC
    | D0 GG0 j C w0 HW0 IH HC
    | D1 G1 i1 A1 A1' w1 HW1 IH1 HA1 HA1' Heq1 ];
    intros G i A A' HGG HG HA HA' Heq Hpkg;
    assert (VarT (oExt G i A) i A' (oHd G i A)) as HVhd
        by (apply vart_hd; assumption).
  - (* wk_id *)
    subst G0.
    exists A', (oHd G i A).
    repeat split;
      [ exact HA'
      | apply eq_ty_subst_id; wfx
      | exact HVhd
      | apply eq_exp_subst_id; wfx ].
  - (* wk_wkn: the variable just takes one more [wkn] step *)
    subst D0.
    assert (Wk (oExt (oExt G i A) j C) (oExt G i A)
              (oWkn (oExt G i A) j C)) as HWfull
        by (apply wk_wkn; assumption).
    destruct (Hpkg _ _ HWfull) as [A'' [HTA'' HeqA'']].
    exists A'', (oExpSubst (oExt (oExt G i A) j C) (oExt G i A)
                   (oWkn (oExt G i A) j C) i A' (oHd G i A)).
    repeat split;
      [ exact HTA''
      | exact HeqA''
      | apply vart_wkn; [ exact HVhd | exact HC | exact HTA'' | exact HeqA'' ]
      | ].
    apply eq_term_refl.
    eapply wf_term_conv;
      [ | apply eq_sort_exp_ty; exact HeqA'' ].
    apply wf_ExpSubst; wfx.
  - (* wk_ext *)
    subst GG0.
    assert (Wk (oExt D0 j C) (oExt G i A)
              (oCmp (oExt D0 j C) D0 (oExt G i A) (oWkn D0 j C) w0)) as HWfull
        by (apply wk_ext; assumption).
    destruct (IH G i A A' eq_refl HG HA HA' Heq Hpkg)
      as [A0 [x0 [HTA0 [HeqA0 [HV0 Heq0]]]]].
    destruct (Hpkg _ _ HWfull) as [A'' [HTA'' HeqA'']].
    exists A'', (oExpSubst (oExt D0 j C) D0 (oWkn D0 j C) i A0 x0).
    repeat split;
      [ exact HTA''
      | exact HeqA''
      | apply vart_wkn;
        [ exact HV0 | exact HC | exact HTA'' |
          eapply eq_wkn_step_ty with (GG := oExt G i A) (w0 := w0) (A := A');
          wfx ]
      | eapply eq_wkn_step with (A := A') (x := oHd G i A); wfx ].
  - (* wk_lift *)
    unfold oExt in HGG; safe_invert HGG.
    assert (Wk (oExt D1 i A1') (oExt G i A) (oLiftW D1 G w1 i A A1')) as HWfull
        by (apply wk_lift'; assumption).
    destruct (Hpkg _ _ HWfull) as [A'' [HTA'' HeqA'']].
    assert (eqt (sTy (oExt D1 i A1') i)
              (oTySubst (oExt D1 i A1') D1 (oWkn D1 i A1') i A1') A'') as Hhd.
    { eapply eq_term_trans; [ | exact HeqA'' ].
      eapply eq_term_trans.
      - apply eq_term_sym;
        apply eq_ty_liftW_canon with (G := G) (w := w1) (A := A); wfx.
      - apply TySubst_cong
          with (G1 := oExt D1 i A1') (G2 := oExt D1 i A1')
               (G1' := oExt G i A) (G2' := oExt G i A)
               (g1 := oLiftW D1 G w1 i A A1') (g2 := oLiftW D1 G w1 i A A1')
               (i1 := i) (i2 := i)
               (A1 := oTySubst (oExt G i A) G (oWkn G i A) i A) (A2 := A');
          [ er | er | er | er | exact Heq ]. }
    exists A'', (oHd D1 i A1').
    repeat split;
      [ exact HTA''
      | exact HeqA''
      | apply vart_hd;
        [ eapply Wk_dom; exact HW1 | exact HA1' | exact HTA'' | exact Hhd ]
      | ].
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact Hhd ].
    eapply eq_term_trans;
      [ | apply eq_liftW_hd' with (G := G) (w := w1) (A := A); wfx ].
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply eq_ty_liftW_canon with (G := G) (w := w1) (A := A); wfx ].
    apply ExpSubst_cong
      with (G1 := oExt D1 i A1') (G2 := oExt D1 i A1')
           (G1' := oExt G i A) (G2' := oExt G i A)
           (g1 := oLiftW D1 G w1 i A A1') (g2 := oLiftW D1 G w1 i A A1')
           (i1 := i) (i2 := i)
           (A1 := A') (A2 := oTySubst (oExt G i A) G (oWkn G i A) i A)
           (v1 := oHd G i A) (v2 := oHd G i A);
      [ er | er | er | er
      | apply eq_term_sym; exact Heq
      | apply eq_term_refl; apply wf_Hd; wfx ].
Qed.

(* ---- weakening a [wkn]-shifted variable past a lift ---- *)

Section LiftStep.
  Context (D1 G w1 j B B' i A A' A0 A'' x x0 : term).
  Context (HD1 : wft D1 sEnv) (HG : wft G sEnv) (Hw1 : wft w1 (sSub D1 G))
          (Hj : wft j sInfo) (HB : wft B (sTy G j)) (HB' : wft B' (sTy D1 j))
          (Hi : wft i sInfo) (HA : wft A (sTy G i))
          (HA' : wft A' (sTy (oExt G j B) i))
          (HA0 : wft A0 (sTy D1 i))
          (HA'' : wft A'' (sTy (oExt D1 j B') i))
          (Hx : wft x (sExp G i A)) (Hx0 : wft x0 (sExp D1 i A0))
          (E1 : eqt (sTy D1 j) (oTySubst D1 G w1 j B) B')
          (E2 : eqt (sTy (oExt G j B) i)
                  (oTySubst (oExt G j B) G (oWkn G j B) i A) A')
          (E3 : eqt (sTy D1 i) (oTySubst D1 G w1 i A) A0)
          (E5 : eqt (sTy (oExt D1 j B') i)
                  (oTySubst (oExt D1 j B') (oExt G j B)
                     (oLiftW D1 G w1 j B B') i A') A'').

  Let E := oExt D1 j B'.
  Let GG := oExt G j B.
  Let L := oLiftW D1 G w1 j B B'.
  Let wG := oWkn G j B.
  Let wD := oWkn D1 j B'.

  Lemma lift_step_wfs
    : wft GG sEnv /\ wft E sEnv /\ wft wG (sSub GG G) /\ wft wD (sSub E D1)
      /\ wft L (sSub E GG).
  Proof.
    repeat split;
      [ apply wf_Ext; assumption | apply wf_Ext; assumption
      | apply wf_Wkn; assumption | apply wf_Wkn; assumption
      | apply wf_liftW; assumption ].
  Qed.

  Lemma lift_step_T1
    : eqt (sTy E i) (oTySubst E GG L i (oTySubst GG G wG i A)) A''.
  Proof.
    destruct lift_step_wfs as [HGG [HE [HwG [HwD HL]]]].
    eapply eq_term_trans; [ | exact E5 ].
    apply TySubst_cong
      with (G1 := E) (G2 := E) (G1' := GG) (G2' := GG) (g1 := L) (g2 := L)
           (i1 := i) (i2 := i) (A1 := oTySubst GG G wG i A) (A2 := A');
      [ er | er | er | er | exact E2 ].
  Qed.

  Lemma lift_step_T2
    : eqt (sTy E i) (oTySubst E G (oCmp E D1 G wD w1) i A) A''.
  Proof.
    destruct lift_step_wfs as [HGG [HE [HwG [HwD HL]]]].
    eapply eq_term_trans; [ | exact lift_step_T1 ].
    eapply eq_term_trans.
    - apply TySubst_cong
        with (G1 := E) (G2 := E) (G1' := G) (G2' := G)
             (g1 := oCmp E D1 G wD w1) (g2 := oCmp E GG G L wG)
             (i1 := i) (i2 := i) (A1 := A) (A2 := A);
        [ er | er
        | apply eq_term_sym; apply eq_liftW_wkn; assumption
        | er | er ].
    - apply eq_term_sym; apply eq_ty_subst_cmp; assumption.
  Qed.

  Lemma lift_step_T3
    : eqt (sTy E i) (oTySubst E D1 wD i (oTySubst D1 G w1 i A)) A''.
  Proof.
    destruct lift_step_wfs as [HGG [HE [HwG [HwD HL]]]].
    eapply eq_term_trans; [ | exact lift_step_T2 ].
    apply eq_ty_subst_cmp; assumption.
  Qed.

  Lemma lift_step_T4 : eqt (sTy E i) (oTySubst E D1 wD i A0) A''.
  Proof.
    destruct lift_step_wfs as [HGG [HE [HwG [HwD HL]]]].
    eapply eq_term_trans; [ | exact lift_step_T3 ].
    apply TySubst_cong
      with (G1 := E) (G2 := E) (G1' := D1) (G2' := D1)
           (g1 := wD) (g2 := wD) (i1 := i) (i2 := i)
           (A1 := A0) (A2 := oTySubst D1 G w1 i A);
      [ er | er | er | er | apply eq_term_sym; exact E3 ].
  Qed.

  Context (E4 : eqt (sExp D1 i A0) (oExpSubst D1 G w1 i A x) x0).

  Lemma lift_step_tm
    : eqt (sExp E i A'')
        (oExpSubst E GG L i A' (oExpSubst GG G wG i A x))
        (oExpSubst E D1 wD i A0 x0).
  Proof.
    destruct lift_step_wfs as [HGG [HE [HwG [HwD HL]]]].
    assert (wft (oExpSubst GG G wG i A x) (sExp GG i (oTySubst GG G wG i A)))
      as Hin by (apply wf_ExpSubst; assumption).
    assert (wft (oExpSubst D1 G w1 i A x) (sExp D1 i (oTySubst D1 G w1 i A)))
      as Hin1 by (apply wf_ExpSubst; assumption).
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := E) (G2 := E) (G1' := GG) (G2' := GG)
                 (g1 := L) (g2 := L) (i1 := i) (i2 := i)
                 (A1 := A') (A2 := oTySubst GG G wG i A)
                 (v1 := oExpSubst GG G wG i A x)
                 (v2 := oExpSubst GG G wG i A x);
          [ er | er | er | er | apply eq_term_sym; exact E2 | er ]
        | apply eq_sort_exp_ty; exact lift_step_T1 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_exp_subst_cmp; assumption
        | apply eq_sort_exp_ty; exact lift_step_T1 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := E) (G2 := E) (G1' := G) (G2' := G)
                 (g1 := oCmp E GG G L wG) (g2 := oCmp E D1 G wD w1)
                 (i1 := i) (i2 := i) (A1 := A) (A2 := A) (v1 := x) (v2 := x);
          [ er | er | apply eq_liftW_wkn; assumption | er | er | er ]
        | apply eq_sort_exp_ty; exact lift_step_T2 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_term_sym; apply eq_exp_subst_cmp; assumption
        | apply eq_sort_exp_ty; exact lift_step_T3 ]. }
    eapply eq_term_conv;
      [ apply ExpSubst_cong
          with (G1 := E) (G2 := E) (G1' := D1) (G2' := D1)
               (g1 := wD) (g2 := wD) (i1 := i) (i2 := i)
               (A1 := oTySubst D1 G w1 i A) (A2 := A0)
               (v1 := oExpSubst D1 G w1 i A x) (v2 := x0)
        ; [ er | er | er | er | exact E3 | exact E4 ]
      | apply eq_sort_exp_ty; exact lift_step_T4 ].
  Qed.

End LiftStep.

Lemma vart_wkn_wk_gen D GG w
  : Wk D GG w ->
    forall G i A x j B A', GG = oExt G j B ->
      VarT G i A x -> TyOk G j B -> TyOk (oExt G j B) i A' ->
      eqt (sTy (oExt G j B) i)
          (oTySubst (oExt G j B) G (oWkn G j B) i A) A' ->
      (forall D0 w0, Wk D0 G w0 ->
          exists A0 x0, TyOk D0 i A0
                     /\ eqt (sTy D0 i) (oTySubst D0 G w0 i A) A0
                     /\ VarT D0 i A0 x0
                     /\ eqt (sExp D0 i A0) (oExpSubst D0 G w0 i A x) x0) ->
      (forall D0 w0, Wk D0 (oExt G j B) w0 ->
          exists A'', TyOk D0 i A''
                   /\ eqt (sTy D0 i)
                        (oTySubst D0 (oExt G j B) w0 i A') A'') ->
      exists A'' x', TyOk D i A''
        /\ eqt (sTy D i) (oTySubst D GG w i A') A''
        /\ VarT D i A'' x'
        /\ eqt (sExp D i A'')
             (oExpSubst D GG w i A'
                (oExpSubst (oExt G j B) G (oWkn G j B) i A x)) x'.
Proof.
  induction 1 as
    [ G0 HG0
    | D0 k C HD0 HC
    | D0 GG0 k C w0 HW0 IH HC
    | D1 G1 i1 A1 A1' w1 HW1 IH1 HA1 HA1' Heq1 ];
    intros G i A x j B A' HGG Hx HB HA' Heq Hvpkg Htpkg;
    assert (VarT (oExt G j B) i A'
              (oExpSubst (oExt G j B) G (oWkn G j B) i A x)) as HVw
        by (apply vart_wkn; assumption).
  - (* wk_id *)
    subst G0.
    exists A', (oExpSubst (oExt G j B) G (oWkn G j B) i A x).
    repeat split;
      [ exact HA'
      | apply eq_ty_subst_id; wfx
      | exact HVw
      | apply eq_exp_subst_id; wfx ].
  - (* wk_wkn: one more [wkn] step *)
    subst D0.
    assert (Wk (oExt (oExt G j B) k C) (oExt G j B)
              (oWkn (oExt G j B) k C)) as HWfull
        by (apply wk_wkn; assumption).
    destruct (Htpkg _ _ HWfull) as [A'' [HTA'' HeqA'']].
    exists A'', (oExpSubst (oExt (oExt G j B) k C) (oExt G j B)
                   (oWkn (oExt G j B) k C) i A'
                   (oExpSubst (oExt G j B) G (oWkn G j B) i A x)).
    repeat split;
      [ exact HTA''
      | exact HeqA''
      | apply vart_wkn; [ exact HVw | exact HC | exact HTA'' | exact HeqA'' ]
      | ].
    apply eq_term_refl.
    eapply wf_term_conv;
      [ | apply eq_sort_exp_ty; exact HeqA'' ].
    apply wf_ExpSubst; wfx.
  - (* wk_ext *)
    subst GG0.
    assert (Wk (oExt D0 k C) (oExt G j B)
              (oCmp (oExt D0 k C) D0 (oExt G j B) (oWkn D0 k C) w0)) as HWfull
        by (apply wk_ext; assumption).
    destruct (IH G i A x j B A' eq_refl Hx HB HA' Heq Hvpkg Htpkg)
      as [A0 [x0 [HTA0 [HeqA0 [HV0 Heq0]]]]].
    destruct (Htpkg _ _ HWfull) as [A'' [HTA'' HeqA'']].
    exists A'', (oExpSubst (oExt D0 k C) D0 (oWkn D0 k C) i A0 x0).
    repeat split;
      [ exact HTA''
      | exact HeqA''
      | apply vart_wkn;
        [ exact HV0 | exact HC | exact HTA'' |
          eapply eq_wkn_step_ty with (GG := oExt G j B) (w0 := w0) (A := A');
          wfx ]
      | eapply eq_wkn_step
          with (A := A')
               (x := oExpSubst (oExt G j B) G (oWkn G j B) i A x); wfx ].
  - (* wk_lift *)
    unfold oExt in HGG; safe_invert HGG.
    assert (Wk (oExt D1 j A1') (oExt G j B) (oLiftW D1 G w1 j B A1')) as HWfull
        by (apply wk_lift'; assumption).
    destruct (Hvpkg _ _ HW1) as [A0 [x0 [HTA0 [HeqA0 [HV0 Heq0]]]]].
    destruct (Htpkg _ _ HWfull) as [A'' [HTA'' HeqA'']].
    exists A'', (oExpSubst (oExt D1 j A1') D1 (oWkn D1 j A1') i A0 x0).
    repeat split;
      [ exact HTA''
      | exact HeqA''
      | apply vart_wkn;
        [ exact HV0 | exact HA1' | exact HTA'' |
          apply lift_step_T4
            with (G := G) (w1 := w1) (B := B) (A := A) (A' := A'); wfx ]
      | apply lift_step_tm; wfx ].
Qed.

(* ================================================================== *)
(* PHASE A: the type-level block ([EnvOk]/[TyOk]/[NfCode]/[VarT]) is    *)
(* closed under weakening, structurally.                               *)
(* ================================================================== *)

Theorem Nf_wk_str :
  (forall G, EnvOk G -> True)
  /\ (forall G i A, TyOk G i A ->
        forall D w, Wk D G w ->
          exists A', TyOk D i A'
                  /\ eqt (sTy D i) (oTySubst D G w i A) A')
  /\ (forall G r l c, NfCode G r l c ->
        forall D w, Wk D G w ->
          exists c', NfCode D r l c'
                  /\ eqt (sCode D r l)
                       (oExpSubst D G w (iCode l) (oU G r l) c) c')
  /\ (forall G i A x, VarT G i A x ->
        forall D w, Wk D G w ->
          exists A' x', TyOk D i A'
                     /\ eqt (sTy D i) (oTySubst D G w i A) A'
                     /\ VarT D i A' x'
                     /\ eqt (sExp D i A') (oExpSubst D G w i A x) x')
  /\ (forall G i A e, NeET G i A e -> True)
  /\ (forall G i A e, NfET G i A e -> True).
Proof.
  apply Nf_mutind.
  (* ---- EnvOk ---- *)
  - exact I.
  - intros; exact I.
  (* ---- TyOk ---- *)
  - intros G r l HG _ Hr Hl D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    exists (oU D r l); split;
      [ apply tyok_U; assumption | apply eq_U_subst; wfx ].
  - intros G r l c Hc IHc D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    destruct (IHc D w HW) as [c' [Hc' Heqc]].
    exists (oEl D r l c'); split;
      [ apply tyok_El; exact Hc' | apply eq_El_wk; assumption ].
  (* ---- NfCode ---- *)
  - intros G HG _ D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    exists (oNat D); split;
      [ apply nfcode_nat; exact HD | apply eq_Nat_subst'; wfx ].
  - intros G HG _ D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    exists (oEmpty D); split;
      [ apply nfcode_empty; exact HD | apply eq_Empty_subst; wfx ].
  - intros G rF lF lG F B HrF HlF HlG HF IHF HB IHB D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    destruct (IHF D w HW) as [F' [HF' HeqF]].
    destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 HeqEl]].
    destruct (IHB _ _ HW2) as [B' [HB' HeqB]].
    exists (oPiRel D rF lF lG F' B'); split;
      [ apply nfcode_pi_rel; assumption | apply eq_pi_rel_wk; assumption ].
  - intros G rF lF F B HrF HlF HF IHF HB IHB D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    destruct (IHF D w HW) as [F' [HF' HeqF]].
    destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 HeqEl]].
    destruct (IHB _ _ HW2) as [B' [HB' HeqB]].
    exists (oPiIrr D rF lF F' B'); split;
      [ apply nfcode_pi_irr; assumption | apply eq_pi_irr_wk; assumption ].
  - intros G r l c Hx IHx D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    destruct (TyOk_U_inv (VarT_TyOk Hx)) as [Hr Hl].
    destruct (IHx D w HW) as [A' [x' [HTA [HeqA [HV Heq]]]]].
    assert (A' = oU D r l) as HA'
        by (eapply TyOk_wk_U; eassumption).
    subst A'.
    exists x'; split; [ apply nfcode_var; exact HV | exact Heq ].
  (* ---- VarT ---- *)
  - intros G i A A' HG _ HA IHA HA' IHA' Heq D w HW.
    eapply vart_hd_wk_gen;
      [ exact HW | reflexivity | exact HG | exact HA | exact HA' | exact Heq
      | exact IHA' ].
  - intros G i A x j B A' Hx IHx HB IHB HA' IHA' Heq D w HW.
    eapply vart_wkn_wk_gen;
      [ exact HW | reflexivity | exact Hx | exact HB | exact HA' | exact Heq
      | exact IHx | exact IHA' ].
  (* ---- NeET (not part of this phase) ---- *)
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  (* ---- NfET (not part of this phase) ---- *)
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.

(* ================================================================== *)
(* The projections, as consumed downstream                             *)
(* ================================================================== *)

Theorem TyOk_wk G i A
  : TyOk G i A -> forall D w, Wk D G w -> EnvOk D ->
    exists A', TyOk D i A'
            /\ eqt (sTy D i) (oTySubst D G w i A) A'.
Proof. intros HA D w HW HD; exact (proj1 (proj2 Nf_wk_str) _ _ _ HA D w HW). Qed.

Theorem NfCode_wk G r l c
  : NfCode G r l c -> forall D w, Wk D G w -> EnvOk D ->
    exists c', NfCode D r l c'
            /\ eqt (sCode D r l)
                 (oExpSubst D G w (iCode l) (oU G r l) c) c'.
Proof.
  intros Hc D w HW HD;
    exact (proj1 (proj2 (proj2 Nf_wk_str)) _ _ _ _ Hc D w HW).
Qed.

Theorem VarT_wk G i A x
  : VarT G i A x -> forall D w, Wk D G w -> EnvOk D ->
    exists A' x', TyOk D i A'
               /\ eqt (sTy D i) (oTySubst D G w i A) A'
               /\ VarT D i A' x'
               /\ eqt (sExp D i A') (oExpSubst D G w i A x) x'.
Proof.
  intros Hx D w HW HD;
    exact (proj1 (proj2 (proj2 (proj2 Nf_wk_str))) _ _ _ _ Hx D w HW).
Qed.

(* ================================================================== *)
(* PART 2: NORMAL SUBSTITUTIONS                                        *)
(* ================================================================== *)

(* ================================================================== *)
(* (a) THE FOUR NEW SUBSTITUTION COMMUTATIONS                          *)
(*                                                                     *)
(* [ott_subst_commute] (Lang/OTT/SubstCommute.v) supplies the rules     *)
(* that were missing when the first half of this file was written:      *)
(* "app_rel subst", "app_irr subst", "lam_irr subst", "Emptyrec subst". *)
(* They are repackaged here in the vocabulary of src/Pyrosome/Gluing/Dtt/Syntax.v,       *)
(* exactly as src/Pyrosome/Gluing/Dtt/Eqns.v does for the other 28.                      *)
(*                                                                     *)
(* Two spelling facts, both deliberate on the language side:            *)
(*   - the two [app] rules and [lam_irr subst] lift [g] with            *)
(*     [Syntax.oLift], i.e. over [ext G [rF,iota lF] (El G rF lF     *)
(*     g[F])], the same shape "Pi_rel subst"/"lam_rel subst" use;       *)
(*   - their codomain code [B] sits at [iCode _] ([info rel (next _)]), *)
(*     matching [lam_irr]/[app_irr]/[app_rel] -- NOT at [Pi_irr]'s      *)
(*     [info rel (iota L1)].  So NO "next0" bridge is needed for any of *)
(*     the four.                                                        *)
(* ================================================================== *)

Lemma eq_lam_irr_subst G G' g rF lF F B t
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft rF sRelevance -> wft lF sLvl ->
    wft F (sCode G' rF lF) ->
    wft B (sCode (oExtC G' rF lF F) oIrr oL0) ->
    wft t (sElt (oExtC G' rF lF F) oIrr oL0 B) ->
    eqt (sExp G (iEl oIrr oL0)
           (oTySubst G G' g (iEl oIrr oL0)
              (oEl G' oIrr oL0 (oPiIrr G' rF lF F B))))
      (oExpSubst G G' g (iEl oIrr oL0)
         (oEl G' oIrr oL0 (oPiIrr G' rF lF F B))
         (oLamIrr G' rF lF F B t))
      (oLamIrr G rF lF (oCodeSubst G G' g rF lF F)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iCode oL0) (oU (oExtC G' rF lF F) oIrr oL0) B)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iEl oIrr oL0) (oEl (oExtC G' rF lF F) oIrr oL0 B) t)).
Proof. intros; estep "lam_irr subst". Qed.

Lemma eq_app_irr_subst G G' g rF lF F B f a
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft rF sRelevance -> wft lF sLvl ->
    wft F (sCode G' rF lF) ->
    wft B (sCode (oExtC G' rF lF F) oIrr oL0) ->
    wft f (sElt G' oIrr oL0 (oPiIrr G' rF lF F B)) ->
    wft a (sElt G' rF lF F) ->
    eqt (sExp G (iEl oIrr oL0)
           (oTySubst G G' g (iEl oIrr oL0)
              (oTySubst G' (oExtC G' rF lF F) (oInst G' rF lF F a)
                 (iEl oIrr oL0) (oEl (oExtC G' rF lF F) oIrr oL0 B))))
      (oExpSubst G G' g (iEl oIrr oL0)
         (oTySubst G' (oExtC G' rF lF F) (oInst G' rF lF F a)
            (iEl oIrr oL0) (oEl (oExtC G' rF lF F) oIrr oL0 B))
         (oAppIrr G' rF lF F B f a))
      (oAppIrr G rF lF (oCodeSubst G G' g rF lF F)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iCode oL0) (oU (oExtC G' rF lF F) oIrr oL0) B)
         (oExpSubst G G' g (iEl oIrr oL0)
            (oEl G' oIrr oL0 (oPiIrr G' rF lF F B)) f)
         (oExpSubst G G' g (iEl rF lF) (oEl G' rF lF F) a)).
Proof. intros; estep "app_irr subst". Qed.

Lemma eq_app_rel_subst G G' g rF lF lG F B f a
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft rF sRelevance -> wft lF sLvl -> wft lG sLvl ->
    wft F (sCode G' rF lF) ->
    wft B (sCode (oExtC G' rF lF F) oRel lG) ->
    wft f (sElt G' oRel lG (oPiRel G' rF lF lG F B)) ->
    wft a (sElt G' rF lF F) ->
    eqt (sExp G (iEl oRel lG)
           (oTySubst G G' g (iEl oRel lG)
              (oTySubst G' (oExtC G' rF lF F) (oInst G' rF lF F a)
                 (iEl oRel lG) (oEl (oExtC G' rF lF F) oRel lG B))))
      (oExpSubst G G' g (iEl oRel lG)
         (oTySubst G' (oExtC G' rF lF F) (oInst G' rF lF F a)
            (iEl oRel lG) (oEl (oExtC G' rF lF F) oRel lG B))
         (oAppRel G' rF lF lG F B f a))
      (oAppRel G rF lF lG (oCodeSubst G G' g rF lF F)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iCode lG) (oU (oExtC G' rF lF F) oRel lG) B)
         (oExpSubst G G' g (iEl oRel lG)
            (oEl G' oRel lG (oPiRel G' rF lF lG F B)) f)
         (oExpSubst G G' g (iEl rF lF) (oEl G' rF lF F) a)).
Proof. intros; estep "app_rel subst". Qed.

Lemma eq_Emptyrec_subst G G' g rA lA A e
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    wft rA sRelevance -> wft lA sLvl ->
    wft A (sCode G' rA lA) ->
    wft e (sElt G' oIrr oL0 (oEmpty G')) ->
    eqt (sExp G (iEl rA lA)
           (oTySubst G G' g (iEl rA lA) (oEl G' rA lA A)))
      (oExpSubst G G' g (iEl rA lA) (oEl G' rA lA A)
         (oEmptyrec G' rA lA A e))
      (oEmptyrec G rA lA (oCodeSubst G G' g rA lA A)
         (oExpSubst G G' g (iEl oIrr oL0)
            (oEl G' oIrr oL0 (oEmpty G')) e)).
Proof. intros; estep "Emptyrec subst". Qed.

(* ================================================================== *)
(* (b) MACHINERY FOR [NeET_wk] / [NfET_wk]                             *)
(* ================================================================== *)

(* The sigma-identity behind [neet_app_rel]:
     <id_D, a'> ; lift(w)  =  w ; <id_G, a>       (both are <w, a'>). *)
Lemma eq_inst_lift D G w i A A' a a'
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    wft a (sExp G i A) -> wft a' (sExp D i A') ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sExp D i A') (oExpSubst D G w i A a) a' ->
    eqt (sSub D (oExt G i A))
      (oCmp D (oExt D i A') (oExt G i A)
         (oSnoc D D i A' (oId D) a') (oLiftW D G w i A A'))
      (oCmp D G (oExt G i A) w (oSnoc G G i A (oId G) a)).
Proof.
  intros HD HG Hi HA HA' Hw Ha Ha' HeqT Heqa.
  assert (wft (oExt D i A') sEnv) as HED by (apply wf_Ext; assumption).
  assert (wft (oExt G i A) sEnv) as HEG by (apply wf_Ext; assumption).
  assert (wft (oWkn D i A') (sSub (oExt D i A') D)) as HWD
      by (apply wf_Wkn; assumption).
  assert (wft (oId D) (sSub D D)) as HidD by (apply wf_Id; assumption).
  assert (wft (oId G) (sSub G G)) as HidG by (apply wf_Id; assumption).
  assert (wft (oLiftW D G w i A A') (sSub (oExt D i A') (oExt G i A))) as HL
      by (apply wf_liftW; assumption).
  assert (wft a' (sExp D i (oTySubst D D (oId D) i A'))) as Ha'id.
  { eapply wf_term_conv; [ exact Ha' | ].
    apply eq_sort_exp_ty.
    apply eq_term_sym; apply eq_ty_subst_id; assumption. }
  assert (wft a (sExp G i (oTySubst G G (oId G) i A))) as Haid.
  { eapply wf_term_conv; [ exact Ha | ].
    apply eq_sort_exp_ty.
    apply eq_term_sym; apply eq_ty_subst_id; assumption. }
  assert (wft (oSnoc D D i A' (oId D) a') (sSub D (oExt D i A'))) as HinstD
      by (apply wf_Snoc; assumption).
  assert (wft (oSnoc G G i A (oId G) a) (sSub G (oExt G i A))) as HinstG
      by (apply wf_Snoc; assumption).
  assert (wft (oCmp (oExt D i A') D G (oWkn D i A') w)
            (sSub (oExt D i A') G)) as Hcw by (apply wf_Cmp; assumption).
  assert (wft (oHd D i A')
            (sExp (oExt D i A') i
               (oTySubst (oExt D i A') G
                  (oCmp (oExt D i A') D G (oWkn D i A') w) i A))) as Hhd
      by (apply wf_liftW_hd; assumption).
  (* the common value: [oSnoc D G i A w a'] *)
  eapply eq_term_trans with (e12 := oSnoc D G i A w a').
  - (* left-hand side *)
    unfold oLiftW.
    eapply eq_term_trans; [ apply eq_cmp_snoc; assumption | ].
    apply Snoc_cong;
      [ er | er | er | er
      | (* substitution component *)
        eapply eq_term_trans; [ apply eq_cmp_assoc; assumption | ]
      | ].
    + eapply eq_term_trans.
      * apply Cmp_cong
          with (f1 := oCmp D (oExt D i A') D
                        (oSnoc D D i A' (oId D) a') (oWkn D i A'))
               (f2 := oId D) (g1 := w) (g2 := w);
          [ er | er | er | apply eq_wkn_snoc; assumption | er ].
      * apply eq_id_left; assumption.
    + (* value component *)
      eapply eq_term_conv;
        [ | apply eq_sort_exp_ty; apply eq_term_sym; exact HeqT ].
      eapply eq_term_trans.
      * eapply eq_term_conv.
        -- apply ExpSubst_cong
             with (G1 := D) (G2 := D)
                  (G1' := oExt D i A') (G2' := oExt D i A')
                  (g1 := oSnoc D D i A' (oId D) a')
                  (g2 := oSnoc D D i A' (oId D) a')
                  (i1 := i) (i2 := i)
                  (A1 := oTySubst (oExt D i A') G
                           (oCmp (oExt D i A') D G (oWkn D i A') w) i A)
                  (A2 := oTySubst (oExt D i A') D (oWkn D i A') i A')
                  (v1 := oHd D i A') (v2 := oHd D i A');
             [ er | er | er | er
             | apply eq_term_sym; apply eq_wk_lift_ty; assumption
             | apply eq_term_refl; apply wf_Hd; assumption ].
        -- apply eq_sort_exp_ty.
           eapply eq_term_trans;
             [ apply eq_ty_subst_cmp; assumption | ].
           eapply eq_term_trans;
             [ apply TySubst_cong
                 with (G1 := D) (G2 := D) (G1' := D) (G2' := D)
                      (g1 := oCmp D (oExt D i A')  D
                               (oSnoc D D i A' (oId D) a') (oWkn D i A'))
                      (g2 := oId D) (i1 := i) (i2 := i) (A1 := A') (A2 := A');
               [ er | er | apply eq_wkn_snoc; assumption | er | er ]
             | apply eq_ty_subst_id; assumption ].
      * eapply eq_term_conv;
          [ apply eq_snoc_hd; assumption
          | apply eq_sort_exp_ty; apply eq_ty_subst_id; assumption ].
  - (* right-hand side, reversed *)
    apply eq_term_sym.
    eapply eq_term_trans; [ apply eq_cmp_snoc; assumption | ].
    apply Snoc_cong;
      [ er | er | er | er
      | apply eq_id_right; assumption
      | ].
    eapply eq_term_trans.
    + apply ExpSubst_cong
        with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
             (i1 := i) (i2 := i)
             (A1 := oTySubst G G (oId G) i A) (A2 := A) (v1 := a) (v2 := a);
        [ er | er | er | er | apply eq_ty_subst_id; assumption | er ].
    + eapply eq_term_conv;
        [ exact Heqa
        | apply eq_sort_exp_ty; apply eq_term_sym; exact HeqT ].
Qed.

(* The instantiating substitution [<id, a>] is well typed.  ([snoc] wants
   its value at [A[id]], so this needs a conversion and [wfa] cannot find
   it on its own.) *)
Lemma wf_oInst G rF lF F a
  : wft G sEnv -> wft rF sRelevance -> wft lF sLvl ->
    wft F (sCode G rF lF) -> wft a (sElt G rF lF F) ->
    wft (oInst G rF lF F a) (sSub G (oExtC G rF lF F)).
Proof.
  intros HG HrF HlF HF Ha.
  assert (wft (oEl G rF lF F) (sTy G (iEl rF lF))) as HEl by wfa.
  unfold oInst; apply wf_Snoc;
    [ exact HG | exact HG | wfa | exact HEl | apply wf_Id; exact HG | ].
  eapply wf_term_conv; [ exact Ha | ].
  apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id; [ exact HG | wfa | exact HEl ].
Qed.

#[local] Hint Resolve wf_oInst : dtt_wf.

(* ---- reading the SHAPE of a weakened type off its source ---- *)
(*                                                                     *)
(* Each of these builds the canonical representative from [NfCode_wk]  *)
(* on the components and then pins the one the induction hypothesis    *)
(* supplied to it.  This is what the old [CodeSub]/[TySub] shape        *)
(* relations and their determinism proofs were for.                    *)

Lemma TyOk_wk_El D G w r l c A'
  : Wk D G w -> EnvOk D -> NfCode G r l c ->
    TyOk D (iEl r l) A' ->
    eqt (sTy D (iEl r l)) (oTySubst D G w (iEl r l) (oEl G r l c)) A' ->
    exists c', A' = oEl D r l c'
            /\ NfCode D r l c'
            /\ eqt (sCode D r l) (oExpSubst D G w (iCode l) (oU G r l) c) c'.
Proof.
  intros HW HD Hc HA' Heq.
  destruct (NfCode_wk Hc HW HD) as [c' [Hc' Heqc]].
  exists c'; repeat split; [ | exact Hc' | exact Heqc ].
  eapply TyOk_pin;
    [ exact HA' | apply tyok_El; exact Hc' | exact Heq
    | apply eq_El_wk; assumption ].
Qed.

Lemma TyOk_wk_nat D G w A'
  : Wk D G w -> EnvOk D -> EnvOk G ->
    TyOk D (iEl oRel oL0) A' ->
    eqt (sTy D (iEl oRel oL0))
      (oTySubst D G w (iEl oRel oL0) (oEl G oRel oL0 (oNat G))) A' ->
    A' = oEl D oRel oL0 (oNat D).
Proof.
  intros HW HD HG HA' Heq.
  destruct (TyOk_wk_El HW HD (nfcode_nat HG) HA' Heq) as [c' [HA [Hc' Heqc]]].
  assert (c' = oNat D) as Hcn
      by (eapply NfCode_pin;
          [ exact Hc' | apply nfcode_nat; exact HD | exact Heqc
          | apply eq_Nat_subst'; wfx ]).
  subst c'; exact HA.
Qed.

Lemma TyOk_wk_empty D G w A'
  : Wk D G w -> EnvOk D -> EnvOk G ->
    TyOk D (iEl oIrr oL0) A' ->
    eqt (sTy D (iEl oIrr oL0))
      (oTySubst D G w (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G))) A' ->
    A' = oEl D oIrr oL0 (oEmpty D).
Proof.
  intros HW HD HG HA' Heq.
  destruct (TyOk_wk_El HW HD (nfcode_empty HG) HA' Heq) as [c' [HA [Hc' Heqc]]].
  assert (c' = oEmpty D) as Hcn
      by (eapply NfCode_pin;
          [ exact Hc' | apply nfcode_empty; exact HD | exact Heqc
          | apply eq_Empty_subst; wfx ]).
  subst c'; exact HA.
Qed.

(* The weakening of a code VARIABLE is a code variable. *)
Lemma TyOk_wk_El_var D G w r l c A'
  : Wk D G w -> EnvOk D -> VarT G (iCode l) (oU G r l) c ->
    TyOk D (iEl r l) A' ->
    eqt (sTy D (iEl r l)) (oTySubst D G w (iEl r l) (oEl G r l c)) A' ->
    exists c', A' = oEl D r l c'
            /\ VarT D (iCode l) (oU D r l) c'
            /\ eqt (sCode D r l) (oExpSubst D G w (iCode l) (oU G r l) c) c'.
Proof.
  intros HW HD Hc HA' Heq.
  destruct (TyOk_U_inv (VarT_TyOk Hc)) as [Hr Hl].
  destruct (VarT_wk Hc HW HD) as [A0 [x' [HTA0 [HeqA0 [HV Heqx]]]]].
  assert (A0 = oU D r l) as HA0 by (eapply TyOk_wk_U; eassumption).
  subst A0.
  destruct (TyOk_wk_El HW HD (nfcode_var Hc) HA' Heq) as [c0 [HA [Hc0 Heqc]]].
  assert (c0 = x') as Hcx
      by (eapply NfCode_pin;
          [ exact Hc0 | apply nfcode_var; exact HV | exact Heqc | exact Heqx ]).
  subst c0; exists x'; repeat split; assumption.
Qed.

(* The weakening of an [El] of a [Pi] is an [El] of a [Pi] -- the fact
   [neet_app_rel] needs, and the reason Layer 0.5 is a prerequisite. *)
Lemma TyOk_wk_pi_rel D G w rF lF lG F B A'
  : Wk D G w -> EnvOk D ->
    NfCode G oRel lG (oPiRel G rF lF lG F B) ->
    TyOk D (iEl oRel lG) A' ->
    eqt (sTy D (iEl oRel lG))
      (oTySubst D G w (iEl oRel lG)
         (oEl G oRel lG (oPiRel G rF lF lG F B))) A' ->
    exists F' B',
      A' = oEl D oRel lG (oPiRel D rF lF lG F' B')
      /\ NfCode G rF lF F /\ NfCode (oExtC G rF lF F) oRel lG B
      /\ NfCode D rF lF F'
      /\ eqt (sCode D rF lF) (oExpSubst D G w (iCode lF) (oU G rF lF) F) F'
      /\ NfCode (oExtC D rF lF F') oRel lG B'
      /\ eqt (sCode (oExtC D rF lF F') oRel lG)
           (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
              (iCode lG) (oU (oExtC G rF lF F) oRel lG) B) B'.
Proof.
  intros HW HD HPi HA' Heq.
  destruct (NfCode_pi_rel_inv HPi) as [HrF [HlF [HlG [HF HB]]]].
  destruct (NfCode_wk HF HW HD) as [F' [HF' HeqF]].
  destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 HeqEl]].
  destruct (NfCode_wk HB HW2 HD2) as [B' [HB' HeqB]].
  destruct (TyOk_wk_El HW HD HPi HA' Heq) as [c0 [HA [Hc0 Heqc]]].
  assert (c0 = oPiRel D rF lF lG F' B') as Hc
      by (eapply NfCode_pin;
          [ exact Hc0 | apply nfcode_pi_rel; assumption | exact Heqc
          | apply eq_pi_rel_wk; assumption ]).
  subst c0; exists F', B'; repeat split; assumption.
Qed.

Lemma TyOk_wk_pi_irr D G w rF lF F B A'
  : Wk D G w -> EnvOk D ->
    NfCode G oIrr oL0 (oPiIrr G rF lF F B) ->
    TyOk D (iEl oIrr oL0) A' ->
    eqt (sTy D (iEl oIrr oL0))
      (oTySubst D G w (iEl oIrr oL0)
         (oEl G oIrr oL0 (oPiIrr G rF lF F B))) A' ->
    exists F' B',
      A' = oEl D oIrr oL0 (oPiIrr D rF lF F' B')
      /\ NfCode G rF lF F /\ NfCode (oExtC G rF lF F) oIrr oL0 B
      /\ NfCode D rF lF F'
      /\ eqt (sCode D rF lF) (oExpSubst D G w (iCode lF) (oU G rF lF) F) F'
      /\ NfCode (oExtC D rF lF F') oIrr oL0 B'
      /\ eqt (sCode (oExtC D rF lF F') oIrr oL0)
           (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
              (iCode oL0) (oU (oExtC G rF lF F) oIrr oL0) B) B'.
Proof.
  intros HW HD HPi HA' Heq.
  destruct (NfCode_pi_irr_inv HPi) as [HrF [HlF [HF HB]]].
  destruct (NfCode_wk HF HW HD) as [F' [HF' HeqF]].
  destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 HeqEl]].
  destruct (NfCode_wk HB HW2 HD2) as [B' [HB' HeqB]].
  destruct (TyOk_wk_El HW HD HPi HA' Heq) as [c0 [HA [Hc0 Heqc]]].
  assert (c0 = oPiIrr D rF lF F' B') as Hc
      by (eapply NfCode_pin;
          [ exact Hc0 | apply nfcode_pi_irr; assumption | exact Heqc
          | apply eq_pi_irr_wk; assumption ]).
  subst c0; exists F', B'; repeat split; assumption.
Qed.

(* ================================================================== *)
(* PHASE B: neutrals and normals are stable under weakening            *)
(* ================================================================== *)

Theorem Nf_wk_ne :
  (forall G, EnvOk G -> True)
  /\ (forall G i A, TyOk G i A -> True)
  /\ (forall G r l c, NfCode G r l c -> True)
  /\ (forall G i A x, VarT G i A x -> True)
  /\ (forall G i A e, NeET G i A e ->
        forall D w, Wk D G w ->
          exists A' e', TyOk D i A'
                     /\ eqt (sTy D i) (oTySubst D G w i A) A'
                     /\ NeET D i A' e'
                     /\ eqt (sExp D i A') (oExpSubst D G w i A e) e')
  /\ (forall G i A e, NfET G i A e ->
        forall D w, Wk D G w ->
          exists A' e', TyOk D i A'
                     /\ eqt (sTy D i) (oTySubst D G w i A) A'
                     /\ NfET D i A' e'
                     /\ eqt (sExp D i A') (oExpSubst D G w i A e) e').
Proof.
  apply Nf_mutind.
  (* ---- the type-level block: handled by Phase A ---- *)
  - exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.

  (* ---- NeET ---- *)
  - (* neet_var *)
    intros G i A x Hx IHx D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    destruct (VarT_wk Hx HW HD) as [A' [x' [HTA [HeqA [HV Heq]]]]].
    exists A', x'; repeat split;
      [ exact HTA | exact HeqA | apply neet_var; exact HV | exact Heq ].

  - (* neet_app_rel *)
    intros G rF lF lG F B f a C Hf IHf Ha IHa HC IHC Heq D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (NfCode G oRel lG (oPiRel G rF lF lG F B)) as HPi
        by (apply TyOk_El_inv; exact (NeET_TyOk Hf)).
    destruct (IHf D w HW) as [Af [f' [HTf [HeqTf [HNf Heqf]]]]].
    destruct (TyOk_wk_pi_rel HW HD HPi HTf HeqTf)
      as [F' [B' [HAf [HFn [HBn [HF' [HeqF [HB' HeqB]]]]]]]].
    subst Af.
    destruct (Wk_liftC HW HD HFn HF' HeqF) as [HW2 [HD2 HeqEl]].
    destruct (Wk_liftC HW2 HD2 HBn HB' HeqB) as [_ [_ HeqElB]].
    destruct (IHa D w HW) as [Aa [a' [HTa [HeqTa [HNa Heqa]]]]].
    assert (Aa = oEl D rF lF F') as HAa
        by (eapply TyOk_pin;
            [ exact HTa | apply tyok_El; exact HF' | exact HeqTa
            | exact HeqEl ]).
    subst Aa.
    destruct (TyOk_wk HC HW HD) as [C' [HTC' HeqC]].
    (* the key sigma computation *)
    assert (eqt (sTy D (iEl oRel lG))
              (oTySubst D (oExtC D rF lF F') (oInst D rF lF F' a')
                 (iEl oRel lG) (oEl (oExtC D rF lF F') oRel lG B')) C')
      as HKEY.
    { eapply eq_term_trans; [ | exact HeqC ].
      eapply eq_term_trans.
      - apply TySubst_cong
          with (G1 := D) (G2 := D)
               (G1' := oExtC D rF lF F') (G2' := oExtC D rF lF F')
               (g1 := oInst D rF lF F' a') (g2 := oInst D rF lF F' a')
               (i1 := iEl oRel lG) (i2 := iEl oRel lG)
               (A1 := oEl (oExtC D rF lF F') oRel lG B')
               (A2 := oTySubst (oExtC D rF lF F') (oExtC G rF lF F)
                        (oLiftW D G w (iEl rF lF) (oEl G rF lF F)
                           (oEl D rF lF F'))
                        (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B));
          [ er | er | er | er | apply eq_term_sym; exact HeqElB ].
      - eapply eq_term_trans; [ apply eq_ty_subst_cmp; wfx | ].
        eapply eq_term_trans.
        + apply TySubst_cong
            with (G1 := D) (G2 := D)
                 (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
                 (g1 := oCmp D (oExtC D rF lF F') (oExtC G rF lF F)
                          (oInst D rF lF F' a')
                          (oLiftW D G w (iEl rF lF) (oEl G rF lF F)
                             (oEl D rF lF F')))
                 (g2 := oCmp D G (oExtC G rF lF F) w (oInst G rF lF F a))
                 (i1 := iEl oRel lG) (i2 := iEl oRel lG)
                 (A1 := oEl (oExtC G rF lF F) oRel lG B)
                 (A2 := oEl (oExtC G rF lF F) oRel lG B);
            [ er | er
            | apply eq_inst_lift; wfx
            | er | er ].
        + eapply eq_term_trans;
            [ apply eq_term_sym; apply eq_ty_subst_cmp; wfx | ].
          apply TySubst_cong
            with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
                 (i1 := iEl oRel lG) (i2 := iEl oRel lG)
                 (A1 := oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                          (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B))
                 (A2 := C);
            [ er | er | er | er | exact Heq ]. }
    assert (eqt (sTy D (iEl oRel lG))
              (oTySubst D G w (iEl oRel lG)
                 (oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                    (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B))) C')
      as HTC1.
    { eapply eq_term_trans; [ | exact HeqC ].
      apply TySubst_cong
        with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
             (i1 := iEl oRel lG) (i2 := iEl oRel lG)
             (A1 := oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                      (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B))
             (A2 := C);
        [ er | er | er | er | exact Heq ]. }
    exists C', (oAppRel D rF lF lG F' B' f' a').
    repeat split;
      [ exact HTC'
      | exact HeqC
      | eapply neet_app_rel;
        [ exact HNf | exact HNa | exact HTC' | exact HKEY ]
      | ].
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := D) (G2 := D) (G1' := G) (G2' := G)
                 (g1 := w) (g2 := w)
                 (i1 := iEl oRel lG) (i2 := iEl oRel lG)
                 (A1 := C)
                 (A2 := oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                          (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B))
                 (v1 := oAppRel G rF lF lG F B f a)
                 (v2 := oAppRel G rF lF lG F B f a);
          [ er | er | er | er
          | apply eq_term_sym; exact Heq
          | apply eq_term_refl; apply wf_AppRel; wfx ]
        | apply eq_sort_exp_ty; exact HTC1 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_app_rel_subst; wfx
        | apply eq_sort_exp_ty; exact HTC1 ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HKEY ].
    apply AppRel_cong;
      [ er | er | er | er | exact HeqF | | exact Heqf | exact Heqa ].
    eapply eq_term_trans; [ | exact HeqB ].
    eapply eqt_Usub_c
      with (G' := oExtC G rF lF F)
           (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'));
      [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
    apply eq_lift_shift; wfx.

  - (* neet_app_irr *)
    intros G rF lF F B f a C Hf IHf Ha IHa HC IHC Heq D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (NfCode G oIrr oL0 (oPiIrr G rF lF F B)) as HPi
        by (apply TyOk_El_inv; exact (NeET_TyOk Hf)).
    destruct (IHf D w HW) as [Af [f' [HTf [HeqTf [HNf Heqf]]]]].
    destruct (TyOk_wk_pi_irr HW HD HPi HTf HeqTf)
      as [F' [B' [HAf [HFn [HBn [HF' [HeqF [HB' HeqB]]]]]]]].
    subst Af.
    destruct (Wk_liftC HW HD HFn HF' HeqF) as [HW2 [HD2 HeqEl]].
    destruct (Wk_liftC HW2 HD2 HBn HB' HeqB) as [_ [_ HeqElB]].
    destruct (IHa D w HW) as [Aa [a' [HTa [HeqTa [HNa Heqa]]]]].
    assert (Aa = oEl D rF lF F') as HAa
        by (eapply TyOk_pin;
            [ exact HTa | apply tyok_El; exact HF' | exact HeqTa
            | exact HeqEl ]).
    subst Aa.
    destruct (TyOk_wk HC HW HD) as [C' [HTC' HeqC]].
    assert (eqt (sTy D (iEl oIrr oL0))
              (oTySubst D (oExtC D rF lF F') (oInst D rF lF F' a')
                 (iEl oIrr oL0) (oEl (oExtC D rF lF F') oIrr oL0 B')) C')
      as HKEY.
    { eapply eq_term_trans; [ | exact HeqC ].
      eapply eq_term_trans.
      - apply TySubst_cong
          with (G1 := D) (G2 := D)
               (G1' := oExtC D rF lF F') (G2' := oExtC D rF lF F')
               (g1 := oInst D rF lF F' a') (g2 := oInst D rF lF F' a')
               (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
               (A1 := oEl (oExtC D rF lF F') oIrr oL0 B')
               (A2 := oTySubst (oExtC D rF lF F') (oExtC G rF lF F)
                        (oLiftW D G w (iEl rF lF) (oEl G rF lF F)
                           (oEl D rF lF F'))
                        (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B));
          [ er | er | er | er | apply eq_term_sym; exact HeqElB ].
      - eapply eq_term_trans; [ apply eq_ty_subst_cmp; wfx | ].
        eapply eq_term_trans.
        + apply TySubst_cong
            with (G1 := D) (G2 := D)
                 (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
                 (g1 := oCmp D (oExtC D rF lF F') (oExtC G rF lF F)
                          (oInst D rF lF F' a')
                          (oLiftW D G w (iEl rF lF) (oEl G rF lF F)
                             (oEl D rF lF F')))
                 (g2 := oCmp D G (oExtC G rF lF F) w (oInst G rF lF F a))
                 (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
                 (A1 := oEl (oExtC G rF lF F) oIrr oL0 B)
                 (A2 := oEl (oExtC G rF lF F) oIrr oL0 B);
            [ er | er
            | apply eq_inst_lift; wfx
            | er | er ].
        + eapply eq_term_trans;
            [ apply eq_term_sym; apply eq_ty_subst_cmp; wfx | ].
          apply TySubst_cong
            with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
                 (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
                 (A1 := oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                          (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B))
                 (A2 := C);
            [ er | er | er | er | exact Heq ]. }
    assert (eqt (sTy D (iEl oIrr oL0))
              (oTySubst D G w (iEl oIrr oL0)
                 (oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                    (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B))) C')
      as HTC1.
    { eapply eq_term_trans; [ | exact HeqC ].
      apply TySubst_cong
        with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
             (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
             (A1 := oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                      (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B))
             (A2 := C);
        [ er | er | er | er | exact Heq ]. }
    exists C', (oAppIrr D rF lF F' B' f' a').
    repeat split;
      [ exact HTC'
      | exact HeqC
      | eapply neet_app_irr;
        [ exact HNf | exact HNa | exact HTC' | exact HKEY ]
      | ].
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := D) (G2 := D) (G1' := G) (G2' := G)
                 (g1 := w) (g2 := w)
                 (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
                 (A1 := C)
                 (A2 := oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
                          (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B))
                 (v1 := oAppIrr G rF lF F B f a)
                 (v2 := oAppIrr G rF lF F B f a);
          [ er | er | er | er
          | apply eq_term_sym; exact Heq
          | apply eq_term_refl; apply wf_AppIrr; wfx ]
        | apply eq_sort_exp_ty; exact HTC1 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_app_irr_subst; wfx
        | apply eq_sort_exp_ty; exact HTC1 ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HKEY ].
    apply AppIrr_cong;
      [ er | er | er | exact HeqF | | exact Heqf | exact Heqa ].
    eapply eq_term_trans; [ | exact HeqB ].
    eapply eqt_Usub_c
      with (G' := oExtC G rF lF F)
           (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'));
      [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
    apply eq_lift_shift; wfx.

  - (* neet_emptyrec *)
    intros G rA lA A e HA IHA He IHe D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (EnvOk G) as HG by (eapply NeET_EnvOk; exact He).
    destruct (NfCode_wk HA HW HD) as [A2 [HA2 HeqA]].
    destruct (IHe D w HW) as [Ae [e' [HTe [HeqTe [HNe Heqe]]]]].
    assert (Ae = oEl D oIrr oL0 (oEmpty D)) as HAe
        by (eapply TyOk_wk_empty; eassumption).
    subst Ae.
    assert (eqt (sTy D (iEl rA lA))
              (oTySubst D G w (iEl rA lA) (oEl G rA lA A)) (oEl D rA lA A2))
      as HeqEl by (apply eq_El_wk; assumption).
    exists (oEl D rA lA A2), (oEmptyrec D rA lA A2 e').
    repeat split;
      [ apply tyok_El; exact HA2
      | exact HeqEl
      | apply neet_emptyrec; [ exact HA2 | exact HNe ]
      | ].
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_Emptyrec_subst; wfx
        | apply eq_sort_exp_ty; exact HeqEl ]. }
    apply Emptyrec_cong; [ er | er | er | exact HeqA | exact Heqe ].

  (* ---- NfET ---- *)
  - (* nfet_code *)
    intros G r l c Hc IHc D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    destruct (NfCode_idx Hc) as [Hr Hl].
    destruct (NfCode_wk Hc HW HD) as [c' [Hc' Heqc]].
    exists (oU D r l), c'; repeat split;
      [ apply tyok_U; assumption | apply eq_U_subst; wfx
      | apply nfet_code; exact Hc' | exact Heqc ].

  - (* nfet_zero *)
    intros G HG IHG D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    exists (oEl D oRel oL0 (oNat D)), (oZero D); repeat split;
      [ apply tyok_El; apply nfcode_nat; exact HD
      | apply eq_El_nat_wk; assumption
      | apply nfet_zero; exact HD
      | apply eq_zero_subst; wfx ].

  - (* nfet_suc *)
    intros G n Hn IHn D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (EnvOk G) as HG by (eapply NfET_EnvOk; exact Hn).
    destruct (IHn D w HW) as [An [n' [HTn [HeqTn [HNn Heqn]]]]].
    assert (An = oEl D oRel oL0 (oNat D)) as HAn
        by (eapply TyOk_wk_nat; eassumption).
    subst An.
    exists (oEl D oRel oL0 (oNat D)), (oSuc D n'); repeat split;
      [ apply tyok_El; apply nfcode_nat; exact HD
      | apply eq_El_nat_wk; assumption
      | apply nfet_suc; exact HNn
      | ].
    eapply eq_term_trans; [ apply eq_suc_subst; wfx | ].
    apply Suc_cong; [ er | exact Heqn ].

  - (* nfet_ne_nat *)
    intros G e He IHe D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (EnvOk G) as HG by (eapply NeET_EnvOk; exact He).
    destruct (IHe D w HW) as [Ae [e' [HTe [HeqTe [HNe Heqe]]]]].
    assert (Ae = oEl D oRel oL0 (oNat D)) as HAe
        by (eapply TyOk_wk_nat; eassumption).
    subst Ae.
    exists (oEl D oRel oL0 (oNat D)), e'; repeat split;
      [ apply tyok_El; apply nfcode_nat; exact HD
      | apply eq_El_nat_wk; assumption
      | apply nfet_ne_nat; exact HNe
      | exact Heqe ].

  - (* nfet_ne_empty *)
    intros G e He IHe D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (EnvOk G) as HG by (eapply NeET_EnvOk; exact He).
    destruct (IHe D w HW) as [Ae [e' [HTe [HeqTe [HNe Heqe]]]]].
    assert (Ae = oEl D oIrr oL0 (oEmpty D)) as HAe
        by (eapply TyOk_wk_empty; eassumption).
    subst Ae.
    exists (oEl D oIrr oL0 (oEmpty D)), e'; repeat split;
      [ apply tyok_El; apply nfcode_empty; exact HD
      | apply eq_El_empty_wk; assumption
      | apply nfet_ne_empty; exact HNe
      | exact Heqe ].

  - (* nfet_ne_var *)
    intros G r l c e Hc IHc He IHe D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    destruct (IHe D w HW) as [Ae [e' [HTe [HeqTe [HNe Heqe]]]]].
    destruct (TyOk_wk_El_var HW HD Hc HTe HeqTe) as [c' [HAe [Hc' Heqc]]].
    subst Ae.
    exists (oEl D r l c'), e'; repeat split;
      [ apply tyok_El; apply nfcode_var; exact Hc'
      | apply eq_El_wk;
        [ exact HW | exact HD | apply nfcode_var; exact Hc
        | apply nfcode_var; exact Hc' | exact Heqc ]
      | eapply nfet_ne_var; [ exact Hc' | exact HNe ]
      | exact Heqe ].

  - (* nfet_lam_rel *)
    intros G rF lF lG F B t HrF HlF HlG HF IHF HB IHB Ht IHt D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (NfCode G oRel lG (oPiRel G rF lF lG F B)) as HPi
        by (apply nfcode_pi_rel; assumption).
    destruct (NfCode_wk HF HW HD) as [F' [HF' HeqF]].
    destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 HeqEl]].
    destruct (NfCode_wk HB HW2 HD2) as [B' [HB' HeqB]].
    destruct (Wk_liftC HW2 HD2 HB HB' HeqB) as [_ [_ HeqElB]].
    destruct (IHt _ _ HW2) as [At [t' [HTt [HeqTt [HNt Heqt]]]]].
    assert (At = oEl (oExtC D rF lF F') oRel lG B') as HAt
        by (eapply TyOk_pin;
            [ exact HTt | apply tyok_El; exact HB' | exact HeqTt
            | exact HeqElB ]).
    subst At.
    assert (NfCode D oRel lG (oPiRel D rF lF lG F' B')) as HPi'
        by (apply nfcode_pi_rel; assumption).
    assert (eqt (sTy D (iEl oRel lG))
              (oTySubst D G w (iEl oRel lG)
                 (oEl G oRel lG (oPiRel G rF lF lG F B)))
              (oEl D oRel lG (oPiRel D rF lF lG F' B'))) as HeqElPi
        by (apply eq_El_wk;
            [ exact HW | exact HD | exact HPi | exact HPi'
            | apply eq_pi_rel_wk; assumption ]).
    exists (oEl D oRel lG (oPiRel D rF lF lG F' B')),
           (oLamRel D rF lF lG F' B' t').
    repeat split;
      [ apply tyok_El; exact HPi'
      | exact HeqElPi
      | apply nfet_lam_rel; assumption
      | ].
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_lam_rel_subst; wfx
        | apply eq_sort_exp_ty; exact HeqElPi ]. }
    apply LamRel_cong; [ er | er | er | er | exact HeqF | | ].
    + eapply eq_term_trans; [ | exact HeqB ].
      eapply eqt_Usub_c
      with (G' := oExtC G rF lF F)
           (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'));
        [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
      apply eq_lift_shift; wfx.
    + eapply eq_term_trans; [ | exact Heqt ].
      eapply eq_term_conv;
        [ apply eq_lift_shift; wfx
        | apply eq_sort_exp_ty; exact HeqElB ].

  - (* nfet_lam_irr *)
    intros G rF lF F B t HrF HlF HF IHF HB IHB Ht IHt D w HW.
    assert (EnvOk D) as HD by (eapply Wk_dom; exact HW).
    assert (NfCode G oIrr oL0 (oPiIrr G rF lF F B)) as HPi
        by (apply nfcode_pi_irr; assumption).
    destruct (NfCode_wk HF HW HD) as [F' [HF' HeqF]].
    destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 HeqEl]].
    destruct (NfCode_wk HB HW2 HD2) as [B' [HB' HeqB]].
    destruct (Wk_liftC HW2 HD2 HB HB' HeqB) as [_ [_ HeqElB]].
    destruct (IHt _ _ HW2) as [At [t' [HTt [HeqTt [HNt Heqt]]]]].
    assert (At = oEl (oExtC D rF lF F') oIrr oL0 B') as HAt
        by (eapply TyOk_pin;
            [ exact HTt | apply tyok_El; exact HB' | exact HeqTt
            | exact HeqElB ]).
    subst At.
    assert (NfCode D oIrr oL0 (oPiIrr D rF lF F' B')) as HPi'
        by (apply nfcode_pi_irr; assumption).
    assert (eqt (sTy D (iEl oIrr oL0))
              (oTySubst D G w (iEl oIrr oL0)
                 (oEl G oIrr oL0 (oPiIrr G rF lF F B)))
              (oEl D oIrr oL0 (oPiIrr D rF lF F' B'))) as HeqElPi
        by (apply eq_El_wk;
            [ exact HW | exact HD | exact HPi | exact HPi'
            | apply eq_pi_irr_wk; assumption ]).
    exists (oEl D oIrr oL0 (oPiIrr D rF lF F' B')),
           (oLamIrr D rF lF F' B' t').
    repeat split;
      [ apply tyok_El; exact HPi'
      | exact HeqElPi
      | apply nfet_lam_irr; assumption
      | ].
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_lam_irr_subst; wfx
        | apply eq_sort_exp_ty; exact HeqElPi ]. }
    apply LamIrr_cong; [ er | er | er | exact HeqF | | ].
    + eapply eq_term_trans; [ | exact HeqB ].
      eapply eqt_Usub_c
      with (G' := oExtC G rF lF F)
           (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'));
        [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
      apply eq_lift_shift; wfx.
    + eapply eq_term_trans; [ | exact Heqt ].
      eapply eq_term_conv;
        [ apply eq_lift_shift; wfx
        | apply eq_sort_exp_ty; exact HeqElB ].
Qed.

Theorem NeET_wk G i A e
  : NeET G i A e -> forall D w, Wk D G w -> EnvOk D ->
    exists A' e', TyOk D i A'
               /\ eqt (sTy D i) (oTySubst D G w i A) A'
               /\ NeET D i A' e'
               /\ eqt (sExp D i A') (oExpSubst D G w i A e) e'.
Proof.
  intros He D w HW HD;
    exact (proj1 (proj2 (proj2 (proj2 (proj2 Nf_wk_ne)))) _ _ _ _ He D w HW).
Qed.

Theorem NfET_wk G i A e
  : NfET G i A e -> forall D w, Wk D G w -> EnvOk D ->
    exists A' e', TyOk D i A'
               /\ eqt (sTy D i) (oTySubst D G w i A) A'
               /\ NfET D i A' e'
               /\ eqt (sExp D i A') (oExpSubst D G w i A e) e'.
Proof.
  intros He D w HW HD;
    exact (proj2 (proj2 (proj2 (proj2 (proj2 Nf_wk_ne)))) _ _ _ _ He D w HW).
Qed.

(* ================================================================== *)
(* (c) CLOSURE OF NORMAL CODES UNDER SUBSTITUTION                      *)
(*                                                                     *)
(* The obvious class of normal substitutions -- every entry an [NfET] at *)
(* the entry's normal type -- is NOT closed under lifting: the lift      *)
(* snocs the head variable, and [hd] at a [Pi_rel] type is not an        *)
(* [NfET] (eta-long normality forbids it).  But the code fragment only   *)
(* ever inspects the UNIVERSE-typed entries, and there [hd] IS normal    *)
(* -- it is a normal code, by [nfcode_var].  [CSub] is weakened exactly  *)
(* that far, and is closed under lifting; it is the only class any       *)
(* consumer, here or downstream, ever needs.                             *)
(* ================================================================== *)

(* one-step weakening of a normal type / normal code.  [wk_wkn] IS the
   bare one-step weakening, so these are [TyOk_wk]/[NfCode_wk] read off
   at it, with nothing to bridge. *)
Lemma TyOk_wkn D i A' j C
  : EnvOk D -> TyOk D i A' -> TyOk D j C ->
    exists C', TyOk (oExt D i A') j C'
            /\ eqt (sTy (oExt D i A') j)
                 (oTySubst (oExt D i A') D (oWkn D i A') j C) C'.
Proof.
  intros HD HA' HC.
  assert (EnvOk (oExt D i A')) as HE by (apply envok_ext; assumption).
  exact (TyOk_wk HC (wk_wkn HD HA') HE).
Qed.

Lemma NfCode_wkn D i A' r l c
  : EnvOk D -> TyOk D i A' -> NfCode D r l c ->
    exists c', NfCode (oExt D i A') r l c'
            /\ eqt (sCode (oExt D i A') r l)
                 (oExpSubst (oExt D i A') D (oWkn D i A') (iCode l)
                    (oU D r l) c) c'.
Proof.
  intros HD HA' Hc.
  assert (EnvOk (oExt D i A')) as HE by (apply envok_ext; assumption).
  exact (NfCode_wk Hc (wk_wkn HD HA') HE).
Qed.

(* ---- the class ---- *)

Inductive CSub : term -> term -> term -> Prop :=
| csub_wk : forall D G w, Wk D G w -> CSub D G w
| csub_forget : forall D, EnvOk D -> CSub D oEmp (oForget D)
| csub_conv : forall D G g g',
    CSub D G g -> wft g' (sSub D G) -> eqt (sSub D G) g' g -> CSub D G g'
| csub_snoc : forall D G i A g v A',
    CSub D G g -> EnvOk D -> TyOk G i A -> TyOk D i A' ->
    eqt (sTy D i) (oTySubst D G g i A) A' ->
    wft v (sExp D i A') ->
    (forall r l, A' = oU D r l -> HasNfCode D r l v) ->
    CSub D (oExt G i A) (oSnoc D G i A g v).

Lemma CSub_dom D G g : CSub D G g -> EnvOk D.
Proof.
  induction 1;
    [ eapply Wk_dom; eassumption | assumption | assumption | assumption ].
Qed.

Lemma CSub_cod D G g : CSub D G g -> EnvOk G.
Proof.
  induction 1;
    [ eapply Wk_cod; eassumption | apply envok_emp | assumption
    | apply envok_ext; [ eapply TyOk_EnvOk | ]; eassumption ].
Qed.

Lemma CSub_wf D G g : CSub D G g -> wft g (sSub D G).
Proof.
  induction 1 as
    [ D G w HW | D HD | D G g g' Hg IHg Hwf Heq
    | D G i A g v A' Hg IHg HD HA HA' Heq Hv Hcode ].
  - apply Wk_wf; assumption.
  - apply wf_Forget; apply EnvOk_wf; assumption.
  - exact Hwf.
  - assert (EnvOk G) as HG by (eapply TyOk_EnvOk; exact HA).
    apply wf_Snoc; try wfx.
    eapply wf_term_conv; [ exact Hv | ].
    apply eq_sort_exp_ty; apply eq_term_sym; exact Heq.
Qed.

(* [CSub] is closed under composing with a one-step weakening ... *)
Lemma CSub_cmp_wkn D G g j C
  : CSub D G g -> EnvOk D -> TyOk D j C ->
    CSub (oExt D j C) G (oCmp (oExt D j C) D G (oWkn D j C) g).
Proof.
  intros HC HD HTC.
  assert (EnvOk (oExt D j C)) as HE by (apply envok_ext; assumption).
  induction HC as
    [ D G w HW | D HD0 | D G g g' Hg IHg Hwf Heq
    | D G i A g v A' Hg IHg HD0 HA HA' Heq Hv Hcode ].
  - apply csub_wk; apply wk_ext; assumption.
  - eapply csub_conv; [ apply csub_forget; exact HE | wfx | ].
    apply eq_cmp_forget; wfx.
  - eapply csub_conv; [ exact (IHg HD HTC HE) | | ].
    + apply wf_Cmp; try wfx; apply CSub_wf; assumption.
    + apply Cmp_cong;
        [ er | er | er
        | apply eq_term_refl; apply wf_Wkn; wfx
        | exact Heq ].
  - assert (EnvOk G) as HG by (eapply TyOk_EnvOk; exact HA).
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; assumption).
    destruct (TyOk_wkn HD HTC HA') as [A'' [HA'' HeqA'']].
    assert (eqt (sTy (oExt D j C) i)
              (oTySubst (oExt D j C) G
                 (oCmp (oExt D j C) D G (oWkn D j C) g) i A) A'') as HeqA.
    { eapply eq_term_trans; [ apply eq_term_sym; apply eq_ty_subst_cmp; wfx | ].
      eapply eq_term_trans; [ | exact HeqA'' ].
      apply TySubst_cong
        with (G1 := oExt D j C) (G2 := oExt D j C) (G1' := D) (G2' := D)
             (g1 := oWkn D j C) (g2 := oWkn D j C) (i1 := i) (i2 := i)
             (A1 := oTySubst D G g i A) (A2 := A');
        [ er | er | er | er | exact Heq ]. }
    assert (wft (oExpSubst (oExt D j C) D (oWkn D j C) i A' v)
              (sExp (oExt D j C) i A'')) as Hv'.
    { eapply wf_term_conv;
        [ apply wf_ExpSubst; try wfx; apply wf_Wkn; wfx | ].
      apply eq_sort_exp_ty; exact HeqA''. }
    eapply csub_conv.
    + apply csub_snoc with (A' := A'');
        [ exact (IHg HD HTC HE) | exact HE | exact HA | exact HA'' | exact HeqA
        | exact Hv' | ].
      intros r l HA''eq.
      assert (i = iCode l) as Hi
          by (eapply TyOk_U_info; [ exact HA'' | exact HA''eq ]).
      subst i.
      destruct (TyOk_iCode_shape HA') as [r2 HA'shape].
      assert (TyOk D (iCode l) (oU D r2 l)) as HA'U
          by (rewrite <- HA'shape; exact HA').
      destruct (TyOk_U_inv HA'U) as [Hr2n Hln].
      assert (r2 = r) as Hr2.
      { assert (eqt (sTy (oExt D j C) (iCode l))
                  (oU (oExt D j C) r2 l) (oU (oExt D j C) r l)) as Heqrr.
        { eapply eq_term_trans;
            [ apply eq_term_sym;
              apply eq_U_subst with (G := oExt D j C) (G' := D)
                                    (g := oWkn D j C) (r := r2) (l := l);
              solve [ wfx | apply wf_Wkn; wfx ]
            | ].
          rewrite <- HA''eq.
          eapply eq_term_trans; [ | exact HeqA'' ].
          apply TySubst_cong
            with (G1 := oExt D j C) (G2 := oExt D j C) (G1' := D) (G2' := D)
                 (g1 := oWkn D j C) (g2 := oWkn D j C)
                 (i1 := iCode l) (i2 := iCode l)
                 (A1 := oU D r2 l) (A2 := A');
            [ er | er | er | er
            | apply eq_term_sym; rewrite HA'shape; er ]. }
        assert (oU (oExt D j C) r2 l = oU (oExt D j C) r l) as Hcon
            by (eapply TyOk_inj;
                [ apply tyok_U; [ exact HE | exact Hr2n | exact Hln ]
                | rewrite <- HA''eq; exact HA''
                | exact Heqrr ]).
        cbv [oU] in Hcon; safe_invert Hcon; reflexivity. }
      subst r2.
      destruct (Hcode r l HA'shape) as [c0 [Hc0 Heqc0]].
      destruct (NfCode_wkn HD HTC Hc0) as [c0' [Hc0' Heqc0']].
      exists c0'; split; [ exact Hc0' | ].
      eapply eq_term_trans; [ | exact Heqc0' ].
      eapply eqt_Usub_c with (G' := D) (g := oWkn D j C) (r := r) (l := l);
        [ wfx | wfx | apply wf_Wkn; wfx | wfx | wfx | ].
      apply ExpSubst_cong
        with (G1 := oExt D j C) (G2 := oExt D j C) (G1' := D) (G2' := D)
             (g1 := oWkn D j C) (g2 := oWkn D j C)
             (i1 := iCode l) (i2 := iCode l)
             (A1 := A') (A2 := oU D r l) (v1 := v) (v2 := c0);
        [ er | er | er | er
        | rewrite HA'shape; er
        | exact Heqc0 ].
    + assert (wft v (sExp D i (oTySubst D G g i A))) as Hvs.
      { eapply wf_term_conv; [ exact Hv | ].
        apply eq_sort_exp_ty; apply eq_term_sym; exact Heq. }
      apply wf_Cmp;
        [ wfx | wfx | wfx | apply wf_Wkn; wfx | ].
      apply wf_Snoc; [ wfx | wfx | wfx | wfx | wfx | exact Hvs ].
    + assert (wft v (sExp D i (oTySubst D G g i A))) as Hvs.
      { eapply wf_term_conv; [ exact Hv | ].
        apply eq_sort_exp_ty; apply eq_term_sym; exact Heq. }
      eapply eq_term_trans.
      * apply eq_cmp_snoc;
          [ wfx | wfx | wfx | apply wf_Wkn; wfx | wfx | wfx | wfx | exact Hvs ].
      * apply Snoc_cong; [ er | er | er | er | er | ].
        eapply eq_term_conv;
          [ apply ExpSubst_cong
              with (G1 := oExt D j C) (G2 := oExt D j C) (G1' := D) (G2' := D)
                   (g1 := oWkn D j C) (g2 := oWkn D j C) (i1 := i) (i2 := i)
                   (A1 := oTySubst D G g i A) (A2 := A') (v1 := v) (v2 := v);
            [ er | er | er | er | exact Heq
            | apply eq_term_refl; exact Hv ]
          | apply eq_sort_exp_ty; eapply eq_term_trans; [ exact HeqA'' | apply eq_term_sym; exact HeqA ] ].
Qed.

(* ... and therefore under lifting over a binder. *)
Lemma CSub_lift D G g i A A'
  : CSub D G g -> EnvOk D -> TyOk G i A -> TyOk D i A' ->
    eqt (sTy D i) (oTySubst D G g i A) A' ->
    CSub (oExt D i A') (oExt G i A) (oLiftW D G g i A A').
Proof.
  intros Hg HD HA HA' Heq.
  assert (EnvOk G) as HG by (eapply TyOk_EnvOk; exact HA).
  assert (EnvOk (oExt D i A')) as HE by (apply envok_ext; assumption).
  assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; assumption).
  destruct (TyOk_wkn HD HA' HA') as [A'' [HA'' HeqA'']].
  assert (eqt (sTy (oExt D i A') i)
            (oTySubst (oExt D i A') G
               (oCmp (oExt D i A') D G (oWkn D i A') g) i A) A'') as HeqA.
  { eapply eq_term_trans; [ apply eq_term_sym; apply eq_ty_subst_cmp; wfx | ].
    eapply eq_term_trans; [ | exact HeqA'' ].
    apply TySubst_cong
      with (G1 := oExt D i A') (G2 := oExt D i A') (G1' := D) (G2' := D)
           (g1 := oWkn D i A') (g2 := oWkn D i A') (i1 := i) (i2 := i)
           (A1 := oTySubst D G g i A) (A2 := A');
      [ er | er | er | er | exact Heq ]. }
  assert (VarT (oExt D i A') i A'' (oHd D i A')) as HVhd
      by (apply vart_hd; assumption).
  unfold oLiftW; apply csub_snoc with (A' := A'');
    [ apply CSub_cmp_wkn; assumption
    | exact HE | exact HA | exact HA'' | exact HeqA
    | apply VarT_wf; exact HVhd
    | ].
  intros r l HA''eq.
  assert (i = iCode l) as Hi
      by (eapply TyOk_U_info; [ exact HA'' | exact HA''eq ]).
  subst i.
  exists (oHd D (iCode l) A'); split;
    [ apply nfcode_var; rewrite <- HA''eq; exact HVhd
    | apply eq_term_refl; unfold sCode; rewrite <- HA''eq;
      apply VarT_wf; exact HVhd ].
Qed.

(* ---- moving a universe shape across a substitution (this is where
       Layer 0.5's [TyOk_inj] is cashed in: the HEAD and the LEVEL of a
       normal type at info [iCode l] are syntactic, but the RELEVANCE is
       only determined up to provable equality) ---- *)

Lemma U_pull G D f A A' r l
  : EnvOk D -> wft D sEnv -> wft G sEnv -> wft f (sSub D G) ->
    TyOk G (iCode l) A -> TyOk D (iCode l) A' -> A' = oU D r l ->
    eqt (sTy D (iCode l)) (oTySubst D G f (iCode l) A) A' ->
    A = oU G r l.
Proof.
  intros HDok HD HG Hf HA HA' HA'eq Heq.
  destruct (TyOk_iCode_shape HA) as [r2 HAeq].
  assert (TyOk G (iCode l) (oU G r2 l)) as HAU by (rewrite <- HAeq; exact HA).
  destruct (TyOk_U_inv HAU) as [Hr2 Hl].
  assert (oU D r2 l = oU D r l) as Hcon.
  { eapply TyOk_inj;
      [ apply tyok_U; assumption
      | rewrite <- HA'eq; exact HA'
      | ].
    eapply eq_term_trans; [ apply eq_term_sym; apply eq_U_subst; wfx | ].
    rewrite <- HA'eq; rewrite <- HAeq; exact Heq. }
  assert (r2 = r) as Hrr by (cbv [oU] in Hcon; safe_invert Hcon; reflexivity).
  rewrite <- Hrr; exact HAeq.
Qed.

Lemma U_push G D f A A' r l
  : EnvOk D -> wft D sEnv -> wft G sEnv -> wft f (sSub D G) ->
    RelNf r -> LvlNf l -> TyOk D (iCode l) A' -> A = oU G r l ->
    eqt (sTy D (iCode l)) (oTySubst D G f (iCode l) A) A' ->
    A' = oU D r l.
Proof.
  intros HDok HD HG Hf Hr Hl HA' HAeq Heq.
  symmetry; eapply TyOk_inj;
    [ apply tyok_U; assumption | exact HA' | ].
  eapply eq_term_trans; [ apply eq_term_sym; apply eq_U_subst; wfx | ].
  rewrite <- HAeq; exact Heq.
Qed.

(* ---- substituting a code variable ---- *)

Lemma csub_hd_subst D GG g
  : CSub D GG g ->
    EnvOk D ->
    forall G i A A' r l, GG = oExt G i A ->
      EnvOk G -> TyOk G i A -> TyOk (oExt G i A) i A' ->
      eqt (sTy (oExt G i A) i)
          (oTySubst (oExt G i A) G (oWkn G i A) i A) A' ->
      A' = oU (oExt G i A) r l ->
      HasNfCode D r l (oExpSubst D (oExt G i A) g i A' (oHd G i A)).
Proof.
  induction 1 as
    [ D0 GG0 w HW | D0 HD0 | D0 GG0 s s' Hs IHs Hwf Heqs
    | D0 GG0 i0 A0 s v A0' Hs IHs HD0 HA0 HA0' Heq0 Hv Hcode ];
    intros HD G i A A' r l HGG HG HA HA2 Heq HA'eq.
  - (* the substitution is a weakening *)
    subst GG0.
    assert (i = iCode l) as Hi
        by (eapply TyOk_U_info; [ exact HA2 | exact HA'eq ]).
    subst i; subst A'.
    assert (VarT (oExt G (iCode l) A) (iCode l)
              (oU (oExt G (iCode l) A) r l) (oHd G (iCode l) A)) as HV
        by (apply vart_hd; assumption).
    destruct (NfCode_wk (nfcode_var HV) HW HD) as [c' [Hc' Heqc]].
    exists c'; split; assumption.
  - (* forget: the codomain is empty *)
    cbv [oEmp oExt] in HGG; discriminate.
  - (* conversion *)
    subst GG0.
    assert (i = iCode l) as Hi
        by (eapply TyOk_U_info; [ exact HA2 | exact HA'eq ]).
    subst i; subst A'.
    assert (VarT (oExt G (iCode l) A) (iCode l)
              (oU (oExt G (iCode l) A) r l) (oHd G (iCode l) A)) as HV
        by (apply vart_hd; assumption).
    destruct (IHs HD G (iCode l) A (oU (oExt G (iCode l) A) r l) r l
                eq_refl HG HA HA2 Heq eq_refl) as [c0 [Hc0 Heqc0]].
    exists c0; split; [ exact Hc0 | ].
    eapply eq_term_trans; [ | exact Heqc0 ].
    eapply eqt_Usub_c
      with (G' := oExt G (iCode l) A) (g := s) (r := r) (l := l);
      [ wfx | wfx | apply CSub_wf; exact Hs | wfx | wfx | ].
    apply ExpSubst_cong
      with (G1 := D0) (G2 := D0)
           (G1' := oExt G (iCode l) A) (G2' := oExt G (iCode l) A)
           (g1 := s') (g2 := s) (i1 := iCode l) (i2 := iCode l)
           (A1 := oU (oExt G (iCode l) A) r l)
           (A2 := oU (oExt G (iCode l) A) r l)
           (v1 := oHd G (iCode l) A) (v2 := oHd G (iCode l) A);
      [ er | er | exact Heqs | er | er | er ].
  - (* snoc: read the entry off *)
    cbv [oExt] in HGG; safe_invert HGG.
    assert (i = iCode l) as Hi
        by (eapply TyOk_U_info; [ exact HA2 | reflexivity ]).
    subst i.
    assert (wft s (sSub D0 G)) as Hsw by (apply CSub_wf; exact Hs).
    assert (A = oU G r l) as HAeq0.
    { eapply U_pull
        with (G := G) (D := oExt G (iCode l) A) (f := oWkn G (iCode l) A)
             (A := A) (A' := oU (oExt G (iCode l) A) r l);
        [ apply envok_ext; assumption | wfx | wfx | apply wf_Wkn; wfx
        | exact HA | exact HA2 | reflexivity | exact Heq ]. }
    assert (TyOk G (iCode l) (oU G r l)) as HAU
        by (rewrite <- HAeq0; exact HA).
    destruct (TyOk_U_inv HAU) as [Hr Hl].
    assert (A0' = oU D0 r l) as HA0'eq.
    { eapply U_push with (G := G) (D := D0) (f := s) (A := A) (A' := A0');
        [ exact HD | wfx | wfx | exact Hsw | exact Hr | exact Hl
        | exact HA0' | exact HAeq0 | exact Heq0 ]. }
    destruct (Hcode r l HA0'eq) as [c0 [Hc0 Heqc0]].
    exists c0; split; [ exact Hc0 | ].
    assert (wft v (sExp D0 (iCode l) (oTySubst D0 G s (iCode l) A))) as Hvs.
    { eapply wf_term_conv; [ exact Hv | ].
      apply eq_sort_exp_ty; apply eq_term_sym; exact Heq0. }
    assert (eqt (sTy D0 (iCode l))
              (oTySubst D0 G s (iCode l) A) (oU D0 r l)) as HeqTy
        by (rewrite <- HA0'eq; exact Heq0).
    eapply eq_term_trans; [ | exact Heqc0 ].
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HeqTy ].
    assert (eqt (sTy D0 (iCode l))
              (oTySubst D0 (oExt G (iCode l) A) (oSnoc D0 G (iCode l) A s v)
                 (iCode l)
                 (oTySubst (oExt G (iCode l) A) G (oWkn G (iCode l) A)
                    (iCode l) A))
              (oTySubst D0 G s (iCode l) A)) as HeqTy2.
    { eapply eq_term_trans;
        [ apply eq_ty_subst_cmp;
          [ wfx | wfx | wfx
          | apply wf_Snoc; [ wfx | wfx | wfx | wfx | exact Hsw | exact Hvs ]
          | apply wf_Wkn; wfx | wfx | wfx ]
        | ].
      apply TySubst_cong
        with (G1 := D0) (G2 := D0) (G1' := G) (G2' := G)
             (g1 := oCmp D0 (oExt G (iCode l) A) G
                      (oSnoc D0 G (iCode l) A s v) (oWkn G (iCode l) A))
             (g2 := s) (i1 := iCode l) (i2 := iCode l) (A1 := A) (A2 := A);
        [ er | er
        | apply eq_wkn_snoc; [ wfx | wfx | exact Hsw | wfx | wfx | exact Hvs ]
        | er | er ]. }
    eapply eq_term_trans.
    + eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := D0) (G2 := D0)
                 (G1' := oExt G (iCode l) A) (G2' := oExt G (iCode l) A)
                 (g1 := oSnoc D0 G (iCode l) A s v)
                 (g2 := oSnoc D0 G (iCode l) A s v)
                 (i1 := iCode l) (i2 := iCode l)
                 (A1 := oU (oExt G (iCode l) A) r l)
                 (A2 := oTySubst (oExt G (iCode l) A) G
                          (oWkn G (iCode l) A) (iCode l) A)
                 (v1 := oHd G (iCode l) A) (v2 := oHd G (iCode l) A);
          [ er | er
          | apply eq_term_refl; apply wf_Snoc;
            [ wfx | wfx | wfx | wfx | exact Hsw | exact Hvs ]
          | er
          | apply eq_term_sym; exact Heq
          | apply eq_term_refl; apply wf_Hd; wfx ]
        | apply eq_sort_exp_ty; exact HeqTy2 ].
    + apply eq_snoc_hd; [ wfx | wfx | exact Hsw | wfx | wfx | exact Hvs ].
Qed.

Lemma csub_wkn_subst D GG g
  : CSub D GG g ->
    EnvOk D ->
    forall G i A x j B A' r l, GG = oExt G j B ->
      VarT G i A x -> TyOk G j B -> TyOk (oExt G j B) i A' ->
      eqt (sTy (oExt G j B) i)
          (oTySubst (oExt G j B) G (oWkn G j B) i A) A' ->
      A' = oU (oExt G j B) r l ->
      (forall D0 s0, CSub D0 G s0 -> EnvOk D0 ->
         forall r0 l0, A = oU G r0 l0 ->
           HasNfCode D0 r0 l0 (oExpSubst D0 G s0 i A x)) ->
      HasNfCode D r l
        (oExpSubst D (oExt G j B) g i A'
           (oExpSubst (oExt G j B) G (oWkn G j B) i A x)).
Proof.
  induction 1 as
    [ D0 GG0 w HW | D0 HD0 | D0 GG0 s s' Hs IHs Hwf Heqs
    | D0 GG0 j0 B0 s v B0' Hs IHs HD0 HB0 HB0' Heq0 Hv Hcode ];
    intros HD G i A x j B A' r l HGG Hx HB HA2 Heq HA'eq Hpkg.
  - (* weakening *)
    subst GG0.
    assert (i = iCode l) as Hi
        by (eapply TyOk_U_info; [ exact HA2 | exact HA'eq ]).
    subst i; subst A'.
    assert (VarT (oExt G j B) (iCode l) (oU (oExt G j B) r l)
              (oExpSubst (oExt G j B) G (oWkn G j B) (iCode l) A x)) as HV
        by (apply vart_wkn; assumption).
    destruct (NfCode_wk (nfcode_var HV) HW HD) as [c' [Hc' Heqc]].
    exists c'; split; assumption.
  - cbv [oEmp oExt] in HGG; discriminate.
  - (* conversion *)
    subst GG0.
    assert (i = iCode l) as Hi
        by (eapply TyOk_U_info; [ exact HA2 | exact HA'eq ]).
    subst i; subst A'.
    assert (VarT (oExt G j B) (iCode l) (oU (oExt G j B) r l)
              (oExpSubst (oExt G j B) G (oWkn G j B) (iCode l) A x)) as HV
        by (apply vart_wkn; assumption).
    destruct (IHs HD G (iCode l) A x j B (oU (oExt G j B) r l) r l
                eq_refl Hx HB HA2 Heq eq_refl Hpkg) as [c0 [Hc0 Heqc0]].
    exists c0; split; [ exact Hc0 | ].
    eapply eq_term_trans; [ | exact Heqc0 ].
    eapply eqt_Usub_c
      with (G' := oExt G j B) (g := s) (r := r) (l := l);
      [ wfx | wfx | apply CSub_wf; exact Hs | wfx | wfx | ].
    apply ExpSubst_cong
      with (G1 := D0) (G2 := D0)
           (G1' := oExt G j B) (G2' := oExt G j B)
           (g1 := s') (g2 := s) (i1 := iCode l) (i2 := iCode l)
           (A1 := oU (oExt G j B) r l) (A2 := oU (oExt G j B) r l)
           (v1 := oExpSubst (oExt G j B) G (oWkn G j B) (iCode l) A x)
           (v2 := oExpSubst (oExt G j B) G (oWkn G j B) (iCode l) A x);
      [ er | er | exact Heqs | er | er | er ].
  - (* snoc: skip the entry, recurse down the chain *)
    cbv [oExt] in HGG; safe_invert HGG.
    assert (i = iCode l) as Hi
        by (eapply TyOk_U_info; [ exact HA2 | reflexivity ]).
    subst i.
    assert (wft s (sSub D0 G)) as Hsw by (apply CSub_wf; exact Hs).
    assert (TyOk G (iCode l) A) as HAt by (eapply VarT_TyOk; exact Hx).
    assert (A = oU G r l) as HAeq0.
    { eapply U_pull
        with (G := G) (D := oExt G j B) (f := oWkn G j B)
             (A := A) (A' := oU (oExt G j B) r l);
        [ apply envok_ext; [ eapply TyOk_EnvOk; exact HB | exact HB ]
        | wfx | wfx | apply wf_Wkn; wfx
        | exact HAt | exact HA2 | reflexivity | exact Heq ]. }
    assert (eqt (sTy D0 (iCode l))
              (oTySubst D0 G s (iCode l) A) (oU D0 r l)) as HeqTy.
    { rewrite HAeq0.
      apply eq_U_subst;
        [ wfx | wfx | exact Hsw
        | eapply RelNf_wf; eapply NfCode_RelNf; apply nfcode_var;
          rewrite <- HAeq0; exact Hx
        | eapply LvlNf_wf; eapply NfCode_LvlNf; apply nfcode_var;
          rewrite <- HAeq0; exact Hx ]. }
    destruct (Hpkg D0 s Hs HD r l HAeq0) as [c0 [Hc0 Heqc0]].
    exists c0; split; [ exact Hc0 | ].
    assert (wft v (sExp D0 j (oTySubst D0 G s j B))) as Hvs.
    { eapply wf_term_conv; [ exact Hv | ].
      apply eq_sort_exp_ty; apply eq_term_sym; exact Heq0. }
    assert (wft (oExpSubst (oExt G j B) G (oWkn G j B) (iCode l) A x)
              (sExp (oExt G j B) (iCode l)
                 (oTySubst (oExt G j B) G (oWkn G j B) (iCode l) A))) as Hxw
        by (apply wf_ExpSubst;
            [ wfx | wfx | apply wf_Wkn; wfx | wfx | wfx
            | eapply VarT_wf; exact Hx ]).
    assert (eqt (sTy D0 (iCode l))
              (oTySubst D0 (oExt G j B) (oSnoc D0 G j B s v) (iCode l)
                 (oTySubst (oExt G j B) G (oWkn G j B) (iCode l) A))
              (oTySubst D0 G s (iCode l) A)) as HeqTy2.
    { eapply eq_term_trans;
        [ apply eq_ty_subst_cmp;
          [ wfx | wfx | wfx
          | apply wf_Snoc; [ wfx | wfx | wfx | wfx | exact Hsw | exact Hvs ]
          | apply wf_Wkn; wfx | wfx | wfx ]
        | ].
      apply TySubst_cong
        with (G1 := D0) (G2 := D0) (G1' := G) (G2' := G)
             (g1 := oCmp D0 (oExt G j B) G (oSnoc D0 G j B s v)
                      (oWkn G j B))
             (g2 := s) (i1 := iCode l) (i2 := iCode l) (A1 := A) (A2 := A);
        [ er | er
        | apply eq_wkn_snoc; [ wfx | wfx | exact Hsw | wfx | wfx | exact Hvs ]
        | er | er ]. }
    eapply eq_term_trans; [ | exact Heqc0 ].
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HeqTy ].
    eapply eq_term_trans.
    + eapply eq_term_conv.
      * eapply eq_term_trans.
        -- apply ExpSubst_cong
             with (G1 := D0) (G2 := D0)
                  (G1' := oExt G j B) (G2' := oExt G j B)
                  (g1 := oSnoc D0 G j B s v) (g2 := oSnoc D0 G j B s v)
                  (i1 := iCode l) (i2 := iCode l)
                  (A1 := oU (oExt G j B) r l)
                  (A2 := oTySubst (oExt G j B) G (oWkn G j B) (iCode l) A)
                  (v1 := oExpSubst (oExt G j B) G (oWkn G j B) (iCode l) A x)
                  (v2 := oExpSubst (oExt G j B) G (oWkn G j B) (iCode l) A x);
             [ er | er
             | apply eq_term_refl; apply wf_Snoc;
               [ wfx | wfx | wfx | wfx | exact Hsw | exact Hvs ]
             | er
             | apply eq_term_sym; exact Heq
             | apply eq_term_refl; exact Hxw ].
        -- apply eq_exp_subst_cmp;
             [ wfx | wfx | wfx
             | apply wf_Snoc; [ wfx | wfx | wfx | wfx | exact Hsw | exact Hvs ]
             | apply wf_Wkn; wfx | wfx | wfx | eapply VarT_wf; exact Hx ].
      * apply eq_sort_exp_ty; exact HeqTy2.
    + apply ExpSubst_cong
        with (G1 := D0) (G2 := D0) (G1' := G) (G2' := G)
             (g1 := oCmp D0 (oExt G j B) G (oSnoc D0 G j B s v)
                      (oWkn G j B))
             (g2 := s) (i1 := iCode l) (i2 := iCode l)
             (A1 := A) (A2 := A) (v1 := x) (v2 := x);
        [ er | er
        | apply eq_wkn_snoc; [ wfx | wfx | exact Hsw | wfx | wfx | exact Hvs ]
        | er | er | apply eq_term_refl; eapply VarT_wf; exact Hx ].
Qed.

Lemma CSub_liftC D G g rF lF F F'
  : CSub D G g -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (oCodeSubst D G g rF lF F) F' ->
    CSub (oExtC D rF lF F') (oExtC G rF lF F)
      (oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
    /\ EnvOk (oExtC D rF lF F')
    /\ eqt (sTy D (iEl rF lF))
         (oTySubst D G g (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F').
Proof.
  intros HC HD HF HF' HeqF.
  assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact HC).
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G g (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
    as HeqEl.
  { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
    apply El_cong; [ er | er | er | exact HeqF ]. }
  repeat split;
    [ apply CSub_lift;
      [ exact HC | exact HD | apply tyok_El; exact HF
      | apply tyok_El; exact HF' | exact HeqEl ]
    | apply envok_ext; [ exact HD | apply tyok_El; exact HF' ]
    | exact HeqEl ].
Qed.

(* ================================================================== *)
(* Normal codes are closed under normal substitution                   *)
(* ================================================================== *)

Theorem Nf_subst_str :
  (forall G, EnvOk G -> True)
  /\ (forall G i A, TyOk G i A ->
        forall D g, CSub D G g -> EnvOk D ->
          exists A', TyOk D i A'
                  /\ eqt (sTy D i) (oTySubst D G g i A) A')
  /\ (forall G r l c, NfCode G r l c ->
        forall D g, CSub D G g -> EnvOk D ->
          HasNfCode D r l (oExpSubst D G g (iCode l) (oU G r l) c))
  /\ (forall G i A x, VarT G i A x ->
        forall D g, CSub D G g -> EnvOk D ->
          forall r l, A = oU G r l ->
            HasNfCode D r l (oExpSubst D G g i A x))
  /\ (forall G i A e, NeET G i A e -> True)
  /\ (forall G i A e, NfET G i A e -> True).
Proof.
  apply Nf_mutind.
  - exact I.
  - intros; exact I.
  (* ---- TyOk ---- *)
  - intros G r l HG _ Hr Hl D g HC HD.
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact HC).
    exists (oU D r l); split;
      [ apply tyok_U; assumption | apply eq_U_subst; wfx ].
  - intros G r l c Hc IHc D g HC HD.
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact HC).
    destruct (IHc D g HC HD) as [c' [Hc' Heqc]].
    exists (oEl D r l c'); split; [ apply tyok_El; exact Hc' | ].
    eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
    apply El_cong; [ er | er | er | exact Heqc ].
  (* ---- NfCode ---- *)
  - intros G HG _ D g HC HD.
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact HC).
    exists (oNat D); split;
      [ apply nfcode_nat; exact HD | apply eq_Nat_subst'; wfx ].
  - intros G HG _ D g HC HD.
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact HC).
    exists (oEmpty D); split;
      [ apply nfcode_empty; exact HD | apply eq_Empty_subst; wfx ].
  - intros G rF lF lG F B HrF HlF HlG HF IHF HB IHB D g HC HD.
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact HC).
    destruct (IHF D g HC HD) as [F' [HF' HeqF]].
    destruct (CSub_liftC HC HD HF HF' HeqF) as [HC2 [HD2 HeqEl]].
    destruct (IHB _ _ HC2 HD2) as [B' [HB' HeqB]].
    exists (oPiRel D rF lF lG F' B'); split;
      [ apply nfcode_pi_rel; assumption | ].
    eapply eq_term_trans; [ apply eq_Pi_rel_subst; wfx | ].
    apply PiRel_cong; [ er | er | er | er | exact HeqF | ].
    eapply eq_term_trans; [ | exact HeqB ].
    eapply eqt_Usub_c
      with (G' := oExtC G rF lF F)
           (g := oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
           (r := oRel) (l := lG);
      [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
    apply eq_lift_shift'; wfx.
  - intros G rF lF F B HrF HlF HF IHF HB IHB D g HC HD.
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact HC).
    destruct (IHF D g HC HD) as [F' [HF' HeqF]].
    destruct (CSub_liftC HC HD HF HF' HeqF) as [HC2 [HD2 HeqEl]].
    destruct (IHB _ _ HC2 HD2) as [B' [HB' HeqB]].
    exists (oPiIrr D rF lF F' B'); split;
      [ apply nfcode_pi_irr; assumption | ].
    eapply eq_term_trans; [ apply eq_Pi_irr_subst'; wfx | ].
    apply eqt_i2c; [ wfx | apply wf_Irr | ].
    apply PiIrr_cong; [ er | er | er | exact HeqF | ].
    apply eqt_c2i; [ wfx | apply wf_Irr | ].
    eapply eq_term_trans; [ | exact HeqB ].
    eapply eqt_Usub_c
      with (G' := oExtC G rF lF F)
           (g := oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
           (r := oIrr) (l := oL0);
      [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
    apply eq_lift_shift'; wfx.
  - intros G r l c Hx IHx D g HC HD.
    exact (IHx D g HC HD r l eq_refl).
  (* ---- VarT ---- *)
  - intros G i A A' HG _ HA IHA HA'' IHA' Heq D g HC HD r l HA'eq.
    eapply csub_hd_subst;
      [ exact HC | exact HD | reflexivity | exact HG | exact HA | exact HA''
      | exact Heq | exact HA'eq ].
  - intros G i A x j B A' Hx IHx HB IHB HA' IHA' Heq D g HC HD r l HA'eq.
    eapply csub_wkn_subst;
      [ exact HC | exact HD | reflexivity | exact Hx | exact HB | exact HA'
      | exact Heq | exact HA'eq | ].
    intros D0 s0 HC0 HD0 r0 l0 HAeq.
    exact (IHx D0 s0 HC0 HD0 r0 l0 HAeq).
  (* ---- NeET / NfET ---- *)
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.

Definition TyOk_subst := proj1 (proj2 Nf_subst_str).

(* The theorem, for the class that survived: [CSub]. *)
Theorem NfCode_csubst G r l c
  : NfCode G r l c -> forall D g, CSub D G g -> EnvOk D ->
    exists c', NfCode D r l c'
            /\ eqt (sCode D r l)
                 (oExpSubst D G g (iCode l) (oU G r l) c) c'.
Proof. exact (proj1 (proj2 (proj2 Nf_subst_str)) G r l c). Qed.
