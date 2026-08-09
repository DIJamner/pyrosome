Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttSyntax WIP.DttWf WIP.DttEqns WIP.DttNf WIP.DttNfWf.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 1: STABILITY UNDER WEAKENING.

   WHAT IS PROVED HERE (all axiom-free):

     * [Wk_cmp]      -- weakenings compose, up to provable equality;
     * [TyOk_wk], [NfCode_wk], [VarT_wk]
                     -- normal TYPES, normal CODES and VARIABLES are
                        stable under weakening;
     * [NSub], [NSub_wf]
                     -- normal substitutions and their typing;
     * the supporting machinery: [CodeSub]/[TySub] (the STRUCTURAL
       substitution of a normal code/type along a weakening),
       [CodeSub_ok]/[TySub_ok], [CodeSub_det]/[TySub_det] (they are
       partial functions), [CVar]/[CVar_det].

   WHAT IS *NOT* PROVED HERE, AND WHY -- read this before consuming the
   file.

   (1) [NeET_wk] / [NfET_wk] (stability of NEUTRALS and NORMALS) are NOT
       provable in [ott_dtt] as it stands, because THE LANGUAGE IS MISSING
       FOUR SUBSTITUTION-COMMUTATION RULES.  Computing the [term_eq_rule]
       names of [ott_dtt] gives exactly 28 rules, and among them there is
       no

           "app_rel subst"   "app_irr subst"
           "lam_irr subst"   "Emptyrec subst"

       (only "Pi_rel subst", "Pi_irr subst", "lam_rel subst", "Nat subst",
       "zero subst", "suc subst", "Empty subst", "U subst", "El subst").
       So [(app_rel G .. f a)[w]] cannot be pushed inwards at all.

       "app_rel subst" *is* derivable, via eta + beta + "lam_rel subst"
       (write [f = lam (app f[wkn] hd)], beta both sides, and use the
       sigma-identity [<id,a'> ; lift w = w ; <id,a>], which is proved
       below in the [LiftStep] section's idiom).  The other three are NOT:
       [Pi_irr] has no eta ("Pi_irr eta" is not a rule of [ott_pi]) and
       [Emptyrec] has no eta either, so [lam_irr], [app_irr] and
       [Emptyrec] are simply stuck under an explicit substitution.

       => THIS IS A LANGUAGE BUG, NOT A PROOF-ENGINEERING PROBLEM.  Layer 1
       cannot be finished until Lang/OTT/Pi.v and Lang/OTT/Nat.v gain the
       three missing commutations (and, for uniformity, "app_rel subst").

   (2) [NfCode_subst] (closure of normal codes under a NORMAL SUBSTITUTION)
       needs TWO things the design did not anticipate:

       (a) [NSub] as specified is NOT CLOSED UNDER LIFTING, so the
           induction cannot go under a binder.  The lift of [g] snocs the
           head variable [hd], and [hd] at a [Pi_rel] type is NOT an
           [NfET] -- eta-long normality forbids it.  The fix is to weaken
           [NSub] to a class that only constrains the UNIVERSE-typed
           entries (codes) and lets the others be arbitrary well-typed
           terms; that class is closed under lifting, and it is all the
           code fragment ever looks at.

       (b) Even then, the variable case needs [TyOk_inj] -- i.e. LAYER 0.5.
           Concretely: [DttNf.vart_hd] lets the normal type [A'] of [hd] be
           ANY normal type provably equal to [A[wkn]].  Reading a code
           variable off a [snoc] gives a normal term at the entry's normal
           type [A0'], and to turn that into an [NfCode D r l] one must
           know [A0' = oU D r l] SYNTACTICALLY.  The head and the level are
           free ([TyOk] at the info [iCode l] can only be a [U _ _ l]), but
           THE RELEVANCE IS NOT: one needs
              [eq_term ott_dtt [] (sTy D (iCode l)) (oU D r l) (oU D r' l)
                 -> r = r'],
           which is exactly the rigidity Layer 0.5 exports.  So the design
           doc's claim (section 2, "R2 dissolves ... provable in Layer 1
           with no reducibility at all") is TRUE for WEAKENING (that is
           [NfCode_wk], proved here) but FALSE for general normal
           substitutions: [NfCode_subst] depends on Layer 0.5.

   (3) The [exists A', TyOk D i A' /\ A[w] = A']-shaped statement is not
       strong enough to drive its own induction -- see the comment above
       [CodeSub].  Everything below therefore runs the induction on
       [CodeSub]/[TySub], which record the SHAPE of the substituted type,
       and recovers the [exists] form at the end.  [CodeSub_det] /
       [TySub_det] (proved here) are what a future [NeET_wk] will need to
       make the head's and the argument's weakenings agree at
       [neet_app_rel].
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

(* [DttSyntax.oLift] is [oLiftW] at the shapes the binder rules use. *)
Lemma oLift_oLiftW G G' g rF lF F
  : oLift G G' g rF lF F
    = oLiftW G G' g (iEl rF lF) (oEl G' rF lF F)
        (oEl G rF lF (oCodeSubst G G' g rF lF F)).
Proof. reflexivity. Qed.

(* The [wf_term] of a lifted weakening's head variable, at the sort
   [snoc] demands.  (This is [DttNfWf.eq_wk_lift_ty] packaged.) *)
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
  apply eq_sort_exp_ty; [ apply wf_Ext; assumption | assumption | ].
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
  apply eq_sort_exp_ty; [ assumption | assumption | ].
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
    \/ (exists w2, Wk G0 Gt w2 /\ TyOk G0 i0 A0
                   /\ wt = oCmp (oExt G0 i0 A0) G0 Gt (oWkn G0 i0 A0) w2)
    \/ (exists G1 A1 w2,
           Gt = oExt G1 i0 A1 /\ Wk G0 G1 w2
           /\ TyOk G1 i0 A1 /\ TyOk G0 i0 A0
           /\ eqt (sTy G0 i0) (oTySubst G0 G1 w2 i0 A1) A0
           /\ wt = oLiftW G0 G1 w2 i0 A1 A0).
Proof.
  destruct 1 as [ G HG | D G i A w HW HA | D G i A A' w HW HA HA' Heq ];
    intros G0 i0 A0 HE.
  - left; split; [ exact HE | rewrite HE; reflexivity ].
  - unfold oExt in HE; safe_invert HE.
    right; left; exists w; repeat split; assumption.
  - unfold oExt in HE; safe_invert HE.
    right; right; exists G, A, w; unfold oLiftW; repeat split; assumption.
Qed.

Lemma Wk_ext_inv G0 i0 A0 Gt wt
  : Wk (oExt G0 i0 A0) Gt wt ->
    (Gt = oExt G0 i0 A0 /\ wt = oId (oExt G0 i0 A0))
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
    | Di Gi ii Ai wi HWi IH HAi
    | Di Gi ii Ai Ai' wi HWi IH HAi HAi' Heqi ];
    intros Gt wt Hwt HD'.
  - (* wk_id *)
    exists wt; split; [ assumption | ].
    apply eq_id_left; wfx.
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
    destruct Hwt as [ [HGt Hwt] | [ [w2 [HW2 [HA2 Hwt]]]
                                  | [G1 [A1 [w2 [HGt [HW2 [HA1 [HA2 [Heq2 Hwt]]]]]]]] ] ];
      subst.
    + (* inner wk_id *)
      exists (oLiftW Di Gi wi ii Ai Ai'); split;
        [ apply wk_lift'; assumption | ].
      apply eq_id_right; wfx.
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
                | apply eq_sort_exp_ty;
                  [ wfx | wfx | apply eq_ty_liftW_canon; wfx ] ]
              | apply eq_liftW_hd'; wfx ]
            | apply eq_sort_exp_ty;
              [ wfx | wfx | apply eq_wk_lift_ty; wfx ] ] ].
Qed.

(* ================================================================== *)
(* THE "next0" BRIDGE, PAID FOR ONCE                                   *)
(*                                                                     *)
(* [iCode L0 = info rel (next L0)] and [info rel (iota L1)] are the two *)
(* spellings the elaborator left behind.  [DttNf.v] pins every          *)
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
  apply eq_sort_ty_cong; [ er | apply eq_info_next0 ].
Qed.

Lemma eq_sort_code0 G r
  : wft G sEnv -> wft r sRelevance ->
    eq_sort ott_dtt [] (sCode G r oL0)
      (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)).
Proof.
  intros; apply eq_sort_exp_cong;
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
  intros; apply eq_sort_exp_ty;
    [ assumption | wfa | apply eq_U_subst; assumption ].
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
    + apply eq_sort_ty_cong; [ er | apply eq_info_next0 ].
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
  - apply eq_sort_exp_ty;
      [ assumption | wfa | apply eq_U_subst0i; auto using wf_Rel ].
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
    + apply eq_sort_exp_ty;
        [ assumption | wfa | apply eq_U_subst0i; auto using wf_Irr ].
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
(* STRUCTURAL SUBSTITUTION OF A NORMAL CODE / TYPE ALONG A WEAKENING   *)
(*                                                                     *)
(* The [exists A', TyOk D i A' /\ A[w] = A'] form of the weakening      *)
(* theorem is NOT strong enough to drive its own induction: at          *)
(* [neet_app_rel] one must know that the weakening of [El (Pi F B)] is  *)
(* an [El (Pi F' B')] -- SYNTACTICALLY, since [NfET]'s clauses dispatch *)
(* on the head of the type -- and provable equality does not give that  *)
(* without Layer 0.5's rigidity.  So the induction is run with a        *)
(* relation recording the structural shape of the substituted type,     *)
(* and the [exists] form is recovered at the end.                      *)
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

Lemma TyOk_El_inv G r l c : TyOk G (iEl r l) (oEl G r l c) -> NfCode G r l c.
Proof.
  intro H; apply TyOk_inv in H;
    destruct H as [ [r0 [l0 [HA _]]] | [r0 [l0 [c0 [HA [Hi Hc]]]]] ].
  - cbv [oU oEl] in HA; discriminate.
  - cbv [oEl] in HA; safe_invert HA; assumption.
Qed.

(* ================================================================== *)
(* WHY [CodeSub] MUST BE DETERMINISTIC, AND HOW IT IS MADE SO          *)
(*                                                                     *)
(* At [neet_app_rel] the head's type contributes the domain code [F']  *)
(* of the weakened Pi, while the ARGUMENT's weakening must be typed at *)
(* that same [F'].  Two independent applications of the theorem to the *)
(* same [F] must therefore agree -- i.e. [CodeSub] must be a partial   *)
(* function.  Its only non-structural clause is [codesub_var], so the  *)
(* fix is to pin the weakening of a code VARIABLE to a structural      *)
(* relation, [CVar], read off the shape of the weakening.  [CVar] is   *)
(* about SHAPES only: it carries no typing or equational content.      *)
(* ================================================================== *)

Inductive CVar : term -> term -> term -> term -> term -> term -> term -> Prop :=
| cvar_id : forall G r l c, CVar G G (oId G) r l c c
| cvar_ext : forall D0 G j C w0 r l c c0,
    CVar D0 G w0 r l c c0 ->
    CVar (oExt D0 j C) G (oCmp (oExt D0 j C) D0 G (oWkn D0 j C) w0) r l c
      (oExpSubst (oExt D0 j C) D0 (oWkn D0 j C) (iCode l) (oU D0 r l) c0)
| cvar_lift_hd : forall D1 G1 i A A1' w1 r l,
    CVar (oExt D1 i A1') (oExt G1 i A) (oLiftW D1 G1 w1 i A A1') r l
      (oHd G1 i A) (oHd D1 i A1')
| cvar_lift_wkn : forall D1 G1 i A A1' w1 r l r0 c0 c0',
    CVar D1 G1 w1 r0 l c0 c0' ->
    CVar (oExt D1 i A1') (oExt G1 i A) (oLiftW D1 G1 w1 i A A1') r l
      (oExpSubst (oExt G1 i A) G1 (oWkn G1 i A) (iCode l) (oU G1 r0 l) c0)
      (oExpSubst (oExt D1 i A1') D1 (oWkn D1 i A1') (iCode l) (oU D1 r0 l) c0').

Lemma CVar_inv D G w r l c c'
  : CVar D G w r l c c' ->
    (D = G /\ w = oId G /\ c' = c)
    \/ (exists D0 j C w0 c0,
           D = oExt D0 j C
           /\ w = oCmp (oExt D0 j C) D0 G (oWkn D0 j C) w0
           /\ CVar D0 G w0 r l c c0
           /\ c' = oExpSubst (oExt D0 j C) D0 (oWkn D0 j C) (iCode l)
                     (oU D0 r l) c0)
    \/ (exists D1 G1 i A A1' w1,
           D = oExt D1 i A1' /\ G = oExt G1 i A
           /\ w = oLiftW D1 G1 w1 i A A1'
           /\ c = oHd G1 i A /\ c' = oHd D1 i A1')
    \/ (exists D1 G1 i A A1' w1 r0 c0 c0',
           D = oExt D1 i A1' /\ G = oExt G1 i A
           /\ w = oLiftW D1 G1 w1 i A A1'
           /\ c = oExpSubst (oExt G1 i A) G1 (oWkn G1 i A) (iCode l)
                    (oU G1 r0 l) c0
           /\ CVar D1 G1 w1 r0 l c0 c0'
           /\ c' = oExpSubst (oExt D1 i A1') D1 (oWkn D1 i A1') (iCode l)
                     (oU D1 r0 l) c0').
Proof.
  destruct 1 as
    [ G r l c | D0 G j C w0 r l c c0 H | D1 G1 i A A1' w1 r l
    | D1 G1 i A A1' w1 r l r0 c0 c0' H ].
  - left; repeat split.
  - right; left; exists D0, j, C, w0, c0; repeat split; assumption.
  - right; right; left; exists D1, G1, i, A, A1', w1; repeat split.
  - right; right; right;
      exists D1, G1, i, A, A1', w1, r0, c0, c0'; repeat split; assumption.
Qed.

Lemma CVar_det D G w r l c c1 c2
  : CVar D G w r l c c1 -> CVar D G w r l c c2 -> c1 = c2.
Proof.
  intro H1; revert c2.
  induction H1 as
    [ G r l c | D0 G j C w0 r l c c0 H IH | D1 G1 i A A1' w1 r l
    | D1 G1 i A A1' w1 r l r0 c0 c0' H IH ];
    intros c2 H2; apply CVar_inv in H2;
    destruct H2 as
      [ [HD [Hw Hc]]
      | [ [Da [ja [Ca [wa [ea [HD [Hw [HC Hc]]]]]]]]
        | [ [Db [Gb [ib [Ab [Ab' [wb [HD [HG [Hw [Hc Hc']]]]]]]]]]
          | [Dc [Gc [ic [Ac [Ac' [wc [rc [ec [ec' [HD [HG [Hw [Hc [HC Hc']]]]]]]]]]]]]] ] ] ].
  - congruence.
  - cbv [oId oCmp] in Hw; discriminate.
  - cbv [oId oSnoc oLiftW] in Hw; discriminate.
  - cbv [oId oSnoc oLiftW] in Hw; discriminate.
  - cbv [oId oCmp] in Hw; discriminate.
  - rewrite Hc; cbv [oCmp oWkn] in Hw; safe_invert Hw;
      f_equal; apply IH; assumption.
  - cbv [oCmp oSnoc oLiftW] in Hw; discriminate.
  - cbv [oCmp oSnoc oLiftW] in Hw; discriminate.
  - cbv [oId oSnoc oLiftW] in Hw; discriminate.
  - cbv [oCmp oSnoc oLiftW] in Hw; discriminate.
  - rewrite Hc'; cbv [oExt] in HD; safe_invert HD; reflexivity.
  - cbv [oHd oExpSubst] in Hc; discriminate.
  - cbv [oId oSnoc oLiftW] in Hw; discriminate.
  - cbv [oCmp oSnoc oLiftW] in Hw; discriminate.
  - cbv [oHd oExpSubst] in Hc; discriminate.
  - rewrite Hc';
    cbv [oLiftW oSnoc oCmp oWkn oHd oExt] in Hw; safe_invert Hw;
    cbv [oExpSubst oU] in Hc; safe_invert Hc;
    f_equal; apply IH; assumption.
Qed.

Lemma TyOk_iCode_shape G l A : TyOk G (iCode l) A -> exists r, A = oU G r l.
Proof.
  intro H; apply TyOk_inv in H;
    destruct H as [ [r [l0 [HA [Hi _]]]] | [r [l0 [c [HA [Hi _]]]]] ].
  - exists r; cbv [iCode oInfo oNext] in Hi; safe_invert Hi; congruence.
  - cbv [iEl iCode oInfo oIota oNext] in Hi; discriminate.
Qed.

Lemma VarT_inv GG i AA x
  : VarT GG i AA x ->
    (exists G A, GG = oExt G i A /\ x = oHd G i A
                 /\ TyOk G i A /\ TyOk (oExt G i A) i AA)
    \/ (exists G j B A x0,
           GG = oExt G j B
           /\ x = oExpSubst (oExt G j B) G (oWkn G j B) i A x0
           /\ VarT G i A x0 /\ TyOk G j B /\ TyOk (oExt G j B) i AA).
Proof.
  destruct 1 as [ G i A A' HG HA HA' Heq | G i A x j B A' Hx HB HA' Heq ].
  - left; exists G, A; repeat split; assumption.
  - right; exists G, j, B, A, x; repeat split; assumption.
Qed.

(* Substitutions that are provably the identity, in the shape the
   [CodeSub_id] recursion produces them. *)
Inductive IdLike : term -> term -> Prop :=
| idlike_id : forall G, IdLike G (oId G)
| idlike_lift : forall G w i A,
    IdLike G w -> IdLike (oExt G i A) (oLiftW G G w i A A).

Lemma CVar_idlike G w
  : IdLike G w ->
    forall r l c, VarT G (iCode l) (oU G r l) c -> CVar G G w r l c c.
Proof.
  induction 1 as [ G | G w i A HI IH ]; intros r l c Hc.
  - apply cvar_id.
  - apply VarT_inv in Hc;
      destruct Hc as [ [G0 [A0 [HG [Hx [HA0 HAA]]]]]
                     | [G0 [j [B [A0 [x0 [HG [Hx [Hx0 [HB HAA]]]]]]]]] ].
    + cbv [oExt] in HG; safe_invert HG; try subst c; apply cvar_lift_hd.
    + cbv [oExt] in HG; safe_invert HG.
      destruct (TyOk_iCode_shape (VarT_TyOk Hx0)) as [r0 HA0eq];
        try subst A0; try subst c.
      apply cvar_lift_wkn; apply IH; assumption.
Qed.

Inductive CodeSub : term -> term -> term -> term -> term -> term -> term -> Prop :=
| codesub_nat : forall D G w, EnvOk G -> CodeSub D G w oRel oL0 (oNat G) (oNat D)
| codesub_empty : forall D G w,
    EnvOk G -> CodeSub D G w oIrr oL0 (oEmpty G) (oEmpty D)
| codesub_pi_rel : forall D G w rF lF lG F B F' B',
    RelNf rF -> LvlNf lF -> LvlNf lG ->
    NfCode G rF lF F -> NfCode (oExtC G rF lF F) oRel lG B ->
    CodeSub D G w rF lF F F' ->
    CodeSub (oExtC D rF lF F') (oExtC G rF lF F)
      (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
      oRel lG B B' ->
    CodeSub D G w oRel lG (oPiRel G rF lF lG F B) (oPiRel D rF lF lG F' B')
| codesub_pi_irr : forall D G w rF lF F B F' B',
    RelNf rF -> LvlNf lF ->
    NfCode G rF lF F -> NfCode (oExtC G rF lF F) oIrr oL0 B ->
    CodeSub D G w rF lF F F' ->
    CodeSub (oExtC D rF lF F') (oExtC G rF lF F)
      (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
      oIrr oL0 B B' ->
    CodeSub D G w oIrr oL0 (oPiIrr G rF lF F B) (oPiIrr D rF lF F' B')
| codesub_var : forall D G w r l c c',
    VarT G (iCode l) (oU G r l) c ->
    VarT D (iCode l) (oU D r l) c' ->
    eqt (sCode D r l) (oExpSubst D G w (iCode l) (oU G r l) c) c' ->
    CVar D G w r l c c' ->
    CodeSub D G w r l c c'.

Inductive TySub (D G w : term) : term -> term -> term -> Prop :=
| tysub_U : forall r l, TySub D G w (iCode l) (oU G r l) (oU D r l)
| tysub_El : forall r l c c',
    CodeSub D G w r l c c' ->
    TySub D G w (iEl r l) (oEl G r l c) (oEl D r l c').

(* A [TySub] whose source is a universe lands on the same universe. *)
Lemma TySub_U_inv D G w r l A' : TySub D G w (iCode l) (oU G r l) A' -> A' = oU D r l.
Proof.
  intro H.
  remember (iCode l) as i0 eqn:Hi0; remember (oU G r l) as A0 eqn:HA0.
  destruct H as [ r1 l1 | r1 l1 c c' Hc ].
  - cbv [oU] in HA0; safe_invert HA0; reflexivity.
  - cbv [oU oEl] in HA0; discriminate.
Qed.

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
  - apply eq_sort_exp_ty;
      [ apply wf_Ext; assumption | assumption
      | apply eq_wk_lift_ty; assumption ].
Qed.

(* [CodeSub] / [TySub] do what they say: the target is normal, and it is
   provably the substitution of the source. *)
Lemma CodeSub_ok D G w r l c c'
  : CodeSub D G w r l c c' -> Wk D G w -> EnvOk D ->
    NfCode D r l c'
    /\ eqt (sCode D r l) (oExpSubst D G w (iCode l) (oU G r l) c) c'.
Proof.
  induction 1 as
    [ D G w HG | D G w HG
    | D G w rF lF lG F B F' B' HrF HlF HlG HF HB HCF IHF HCB IHB
    | D G w rF lF F B F' B' HrF HlF HF HB HCF IHF HCB IHB
    | D G w r l c c' Hx Hx' Heq Hcv ];
    intros HWk HD.
  - (* nat *)
    split; [ apply nfcode_nat; assumption | apply eq_Nat_subst'; wfx ].
  - (* empty *)
    split; [ apply nfcode_empty; assumption | apply eq_Empty_subst; wfx ].
  - (* Pi_rel *)
    destruct (IHF HWk HD) as [HF' HeqF].
    assert (TyOk G (iEl rF lF) (oEl G rF lF F)) as HTA
        by (apply tyok_El; assumption).
    assert (TyOk D (iEl rF lF) (oEl D rF lF F')) as HTA'
        by (apply tyok_El; assumption).
    assert (eqt (sTy D (iEl rF lF))
              (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
      as HeqEl.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF ]. }
    assert (Wk (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')))
      as HWk2 by (apply wk_lift'; assumption).
    assert (EnvOk (oExtC D rF lF F')) as HD2 by (apply envok_ext; assumption).
    destruct (IHB HWk2 HD2) as [HB' HeqB].
    split; [ apply nfcode_pi_rel; assumption | ].
    eapply eq_term_trans; [ apply eq_Pi_rel_subst; wfx | ].
    apply PiRel_cong; [ er | er | er | er | exact HeqF | ].
    eapply eq_term_trans; [ | exact HeqB ].
    eapply eqt_Usub_c;
      [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
    apply ExpSubst_cong
      with (G1 := oExtC D rF lF (oCodeSubst D G w rF lF F))
           (G2 := oExtC D rF lF F')
           (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
           (g1 := oLift D G w rF lF F)
           (g2 := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
           (i1 := iCode lG) (i2 := iCode lG)
           (A1 := oU (oExtC G rF lF F) oRel lG)
           (A2 := oU (oExtC G rF lF F) oRel lG)
           (v1 := B) (v2 := B);
      [ apply Ext_cong; [ er | er | apply El_cong; [ er | er | er | exact HeqF ] ]
      | er
      | rewrite oLift_oLiftW;
        apply eq_liftW_cong
          with (A1 := oEl D rF lF (oCodeSubst D G w rF lF F))
               (A2 := oEl D rF lF F');
        [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
        | apply eq_El_subst; wfx | exact HeqEl ]
      | er | er | er ].
  - (* Pi_irr *)
    destruct (IHF HWk HD) as [HF' HeqF].
    assert (TyOk G (iEl rF lF) (oEl G rF lF F)) as HTA
        by (apply tyok_El; assumption).
    assert (TyOk D (iEl rF lF) (oEl D rF lF F')) as HTA'
        by (apply tyok_El; assumption).
    assert (eqt (sTy D (iEl rF lF))
              (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
      as HeqEl.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF ]. }
    assert (Wk (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')))
      as HWk2 by (apply wk_lift'; assumption).
    assert (EnvOk (oExtC D rF lF F')) as HD2 by (apply envok_ext; assumption).
    destruct (IHB HWk2 HD2) as [HB' HeqB].
    split; [ apply nfcode_pi_irr; assumption | ].
    eapply eq_term_trans; [ apply eq_Pi_irr_subst'; wfx | ].
    apply eqt_i2c; [ wfx | apply wf_Irr | ].
    apply PiIrr_cong; [ er | er | er | exact HeqF | ].
    apply eqt_c2i; [ wfx | apply wf_Irr | ].
    eapply eq_term_trans; [ | exact HeqB ].
    eapply eqt_Usub_c;
      [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
    apply ExpSubst_cong
      with (G1 := oExtC D rF lF (oCodeSubst D G w rF lF F))
           (G2 := oExtC D rF lF F')
           (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
           (g1 := oLift D G w rF lF F)
           (g2 := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
           (i1 := iCode oL0) (i2 := iCode oL0)
           (A1 := oU (oExtC G rF lF F) oIrr oL0)
           (A2 := oU (oExtC G rF lF F) oIrr oL0)
           (v1 := B) (v2 := B);
      [ apply Ext_cong; [ er | er | apply El_cong; [ er | er | er | exact HeqF ] ]
      | er
      | rewrite oLift_oLiftW;
        apply eq_liftW_cong
          with (A1 := oEl D rF lF (oCodeSubst D G w rF lF F))
               (A2 := oEl D rF lF F');
        [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
        | apply eq_El_subst; wfx | exact HeqEl ]
      | er | er | er ].
  - (* var *)
    split; [ apply nfcode_var; assumption | assumption ].
Qed.

Lemma TySub_ok D G w i A A'
  : TySub D G w i A A' -> Wk D G w -> EnvOk D -> TyOk G i A ->
    TyOk D i A' /\ eqt (sTy D i) (oTySubst D G w i A) A'.
Proof.
  intros HT HWk HD HA.
  destruct HT as [ r l | r l c c' HC ].
  - apply TyOk_U_inv in HA; destruct HA as [Hr Hl].
    split; [ apply tyok_U; assumption | apply eq_U_subst; wfx ].
  - apply TyOk_El_inv in HA.
    destruct (CodeSub_ok HC HWk HD) as [Hc' Heqc].
    split; [ apply tyok_El; assumption | ].
    eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
    apply El_cong; [ er | er | er | exact Heqc ].
Qed.

(* ---- the identity case ---- *)

Lemma eq_ty_subst_id' G i A w
  : wft G sEnv -> wft i sInfo -> wft A (sTy G i) -> wft w (sSub G G) ->
    eqt (sSub G G) w (oId G) -> eqt (sTy G i) (oTySubst G G w i A) A.
Proof.
  intros HG Hi HA Hw Hid.
  eapply eq_term_trans;
    [ apply TySubst_cong with (g1 := w) (g2 := oId G) (A1 := A) (A2 := A);
      [ er | er | exact Hid | er | er ]
    | apply eq_ty_subst_id; assumption ].
Qed.

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

Lemma wf_liftW_id G i A w
  : wft G sEnv -> wft i sInfo -> wft A (sTy G i) -> wft w (sSub G G) ->
    eqt (sSub G G) w (oId G) ->
    wft (oLiftW G G w i A A) (sSub (oExt G i A) (oExt G i A)).
Proof.
  intros; apply wf_liftW; try assumption.
  apply eq_ty_subst_id'; assumption.
Qed.

Lemma CodeSub_id G r l c
  : NfCode G r l c ->
    forall w, wft w (sSub G G) -> eqt (sSub G G) w (oId G) -> IdLike G w ->
              CodeSub G G w r l c c.
Proof.
  induction 1 as
    [ G HG | G HG
    | G rF lF lG F B HrF HlF HlG HF IHF HB IHB
    | G rF lF F B HrF HlF HF IHF HB IHB
    | G r l c Hx ];
    intros w Hw Hid HI.
  - apply codesub_nat; assumption.
  - apply codesub_empty; assumption.
  - apply codesub_pi_rel; try assumption.
    + apply IHF; assumption.
    + apply IHB;
        [ apply wf_liftW_id; wfx | apply eq_liftW_id; wfx
        | apply idlike_lift; assumption ].
  - apply codesub_pi_irr; try assumption.
    + apply IHF; assumption.
    + apply IHB;
        [ apply wf_liftW_id; wfx | apply eq_liftW_id; wfx
        | apply idlike_lift; assumption ].
  - eapply codesub_var;
      [ exact Hx | exact Hx | | apply CVar_idlike; assumption ].
    eapply eq_term_trans; [ | apply eq_exp_subst_id; wfx ].
    eapply eqt_Usub_c with (G' := G) (g := oId G) (r := r) (l := l);
      [ wfx | wfx | wfx | wfx | wfx | ].
    apply ExpSubst_cong
      with (G1 := G) (G2 := G) (G1' := G) (G2' := G)
           (g1 := w) (g2 := oId G) (i1 := iCode l) (i2 := iCode l)
           (A1 := oU G r l) (A2 := oU G r l) (v1 := c) (v2 := c);
      [ er | er | exact Hid | er | er | er ].
Qed.

Lemma TySub_id G i A
  : TyOk G i A ->
    forall w, wft w (sSub G G) -> eqt (sSub G G) w (oId G) -> IdLike G w ->
              TySub G G w i A A.
Proof.
  destruct 1; intros w Hw Hid HI;
    [ apply tysub_U | apply tysub_El; apply CodeSub_id; assumption ].
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
    [ | apply eq_sort_exp_ty;
        [ exact HE | exact Hi
        | eapply eq_wkn_step_ty with (GG := GG) (w0 := w0) (A := A);
          eassumption ] ].
  eapply eq_term_trans.
  - eapply eq_term_conv.
    + apply eq_term_sym; apply eq_exp_subst_cmp; assumption.
    + apply eq_sort_exp_ty;
        [ exact HE | exact Hi
        | apply TySubst_cong
            with (G1 := oExt D0 j C) (G2 := oExt D0 j C) (G1' := D0) (G2' := D0)
                 (g1 := oWkn D0 j C) (g2 := oWkn D0 j C) (i1 := i) (i2 := i)
                 (A1 := oTySubst D0 GG w0 i A) (A2 := A0);
          [ er | er | er | er | exact H1 ] ].
  - apply ExpSubst_cong
      with (G1 := oExt D0 j C) (G2 := oExt D0 j C) (G1' := D0) (G2' := D0)
           (g1 := oWkn D0 j C) (g2 := oWkn D0 j C) (i1 := i) (i2 := i)
           (A1 := oTySubst D0 GG w0 i A) (A2 := A0)
           (v1 := oExpSubst D0 GG w0 i A x) (v2 := x0);
      [ er | er | er | er | exact H1 | exact H2 ].
Qed.

Lemma TyOk_U_info G i G' r l A : TyOk G i A -> A = oU G' r l -> i = iCode l.
Proof.
  intros H HA; apply TyOk_inv in H;
    destruct H as [ [r0 [l0 [HA0 [Hi _]]]] | [r0 [l0 [c [HA0 [Hi _]]]]] ].
  - cbv [oU] in HA0, HA; congruence.
  - cbv [oU oEl] in HA0, HA; congruence.
Qed.

(* ---- weakening a head variable ---- *)

Lemma vart_hd_wk_gen D GG w
  : Wk D GG w ->
    forall G i A A', GG = oExt G i A ->
      EnvOk G -> TyOk G i A -> TyOk (oExt G i A) i A' ->
      eqt (sTy (oExt G i A) i)
          (oTySubst (oExt G i A) G (oWkn G i A) i A) A' ->
      (forall D0 w0, Wk D0 (oExt G i A) w0 ->
          exists A'', TySub D0 (oExt G i A) w0 i A' A'') ->
      exists A'' x', TySub D GG w i A' A'' /\ VarT D i A'' x'
                  /\ eqt (sExp D i A'') (oExpSubst D GG w i A' (oHd G i A)) x'
                  /\ (forall r l, A' = oU GG r l ->
                        CVar D GG w r l (oHd G i A) x').
Proof.
  induction 1 as
    [ G0 HG0
    | D0 GG0 j C w0 HW0 IH HC
    | D1 G1 i1 A1 A1' w1 HW1 IH1 HA1 HA1' Heq1 ];
    intros G i A A' HGG HG HA HA' Heq Hpkg;
    assert (VarT (oExt G i A) i A' (oHd G i A)) as HVhd
        by (apply vart_hd; assumption).
  - (* wk_id *)
    subst G0.
    exists A', (oHd G i A).
    repeat split;
      [ apply TySub_id; [ assumption | wfx | er | apply idlike_id ]
      | exact HVhd
      | apply eq_exp_subst_id; wfx
      | intros r l Hr; apply cvar_id ].
  - (* wk_ext *)
    subst GG0.
    assert (Wk (oExt D0 j C) (oExt G i A)
              (oCmp (oExt D0 j C) D0 (oExt G i A) (oWkn D0 j C) w0)) as HWfull
        by (apply wk_ext; assumption).
    destruct (IH G i A A' eq_refl HG HA HA' Heq Hpkg)
      as [A0 [x0 [HT0 [HV0 [Heq0 Hcv0]]]]].
    destruct (Hpkg _ _ HWfull) as [A'' HT''].
    destruct (TySub_ok HT0 HW0 (Wk_dom HW0) HA') as [HTA0 HeqA0].
    destruct (TySub_ok HT'' HWfull (Wk_dom HWfull) HA') as [HTA'' HeqA''].
    exists A'', (oExpSubst (oExt D0 j C) D0 (oWkn D0 j C) i A0 x0).
    repeat split;
      [ exact HT''
      | apply vart_wkn;
        [ exact HV0 | exact HC | exact HTA'' |
          eapply eq_wkn_step_ty with (GG := oExt G i A) (w0 := w0) (A := A');
          wfx ]
      | eapply eq_wkn_step with (A := A') (x := oHd G i A); wfx
      | ].
    intros r l Hr.
    assert (i = iCode l) as Hi0 by (eapply TyOk_U_info; [ exact HA' | exact Hr ]).
    subst i.
    rewrite Hr in HT0; apply TySub_U_inv in HT0; subst A0.
    apply cvar_ext; apply Hcv0; exact Hr.
  - (* wk_lift *)
    unfold oExt in HGG; safe_invert HGG.
    assert (Wk (oExt D1 i A1') (oExt G i A) (oLiftW D1 G w1 i A A1')) as HWfull
        by (apply wk_lift'; assumption).
    destruct (Hpkg _ _ HWfull) as [A'' HT''].
    destruct (TySub_ok HT'' HWfull (Wk_dom HWfull) HA') as [HTA'' HeqA''].
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
      [ exact HT''
      | apply vart_hd;
        [ eapply Wk_dom; exact HW1 | exact HA1' | exact HTA'' | exact Hhd ]
      | | intros r l Hr; apply cvar_lift_hd ].
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; [ wfx | wfx | exact Hhd ] ].
    eapply eq_term_trans;
      [ | apply eq_liftW_hd' with (G := G) (w := w1) (A := A); wfx ].
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty;
          [ wfx | wfx
          | apply eq_ty_liftW_canon with (G := G) (w := w1) (A := A); wfx ] ].
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
        | apply eq_sort_exp_ty; [ exact HE | exact Hi | exact lift_step_T1 ] ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_exp_subst_cmp; assumption
        | apply eq_sort_exp_ty; [ exact HE | exact Hi | exact lift_step_T1 ] ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := E) (G2 := E) (G1' := G) (G2' := G)
                 (g1 := oCmp E GG G L wG) (g2 := oCmp E D1 G wD w1)
                 (i1 := i) (i2 := i) (A1 := A) (A2 := A) (v1 := x) (v2 := x);
          [ er | er | apply eq_liftW_wkn; assumption | er | er | er ]
        | apply eq_sort_exp_ty; [ exact HE | exact Hi | exact lift_step_T2 ] ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_term_sym; apply eq_exp_subst_cmp; assumption
        | apply eq_sort_exp_ty; [ exact HE | exact Hi | exact lift_step_T3 ] ]. }
    eapply eq_term_conv;
      [ apply ExpSubst_cong
          with (G1 := E) (G2 := E) (G1' := D1) (G2' := D1)
               (g1 := wD) (g2 := wD) (i1 := i) (i2 := i)
               (A1 := oTySubst D1 G w1 i A) (A2 := A0)
               (v1 := oExpSubst D1 G w1 i A x) (v2 := x0)
        ; [ er | er | er | er | exact E3 | exact E4 ]
      | apply eq_sort_exp_ty; [ exact HE | exact Hi | exact lift_step_T4 ] ].
  Qed.

End LiftStep.

Lemma vart_wkn_wk_gen D GG w
  : Wk D GG w ->
    forall G i A x j B A', GG = oExt G j B ->
      VarT G i A x -> TyOk G j B -> TyOk (oExt G j B) i A' ->
      eqt (sTy (oExt G j B) i)
          (oTySubst (oExt G j B) G (oWkn G j B) i A) A' ->
      (forall D0 w0, Wk D0 G w0 ->
          exists A0 x0, TySub D0 G w0 i A A0 /\ VarT D0 i A0 x0
                     /\ eqt (sExp D0 i A0) (oExpSubst D0 G w0 i A x) x0
                     /\ (forall r l, A = oU G r l -> CVar D0 G w0 r l x x0)) ->
      (forall D0 w0, Wk D0 (oExt G j B) w0 ->
          exists A'', TySub D0 (oExt G j B) w0 i A' A'') ->
      exists A'' x', TySub D GG w i A' A'' /\ VarT D i A'' x'
        /\ eqt (sExp D i A'')
             (oExpSubst D GG w i A'
                (oExpSubst (oExt G j B) G (oWkn G j B) i A x)) x'
        /\ (forall r l, A' = oU GG r l ->
              CVar D GG w r l
                (oExpSubst (oExt G j B) G (oWkn G j B) i A x) x').
Proof.
  induction 1 as
    [ G0 HG0
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
      [ apply TySub_id; [ assumption | wfx | er | apply idlike_id ]
      | exact HVw
      | apply eq_exp_subst_id; wfx
      | intros r l Hr; apply cvar_id ].
  - (* wk_ext *)
    subst GG0.
    assert (Wk (oExt D0 k C) (oExt G j B)
              (oCmp (oExt D0 k C) D0 (oExt G j B) (oWkn D0 k C) w0)) as HWfull
        by (apply wk_ext; assumption).
    destruct (IH G i A x j B A' eq_refl Hx HB HA' Heq Hvpkg Htpkg)
      as [A0 [x0 [HT0 [HV0 [Heq0 Hcv0]]]]].
    destruct (Htpkg _ _ HWfull) as [A'' HT''].
    destruct (TySub_ok HT0 HW0 (Wk_dom HW0) HA') as [HTA0 HeqA0].
    destruct (TySub_ok HT'' HWfull (Wk_dom HWfull) HA') as [HTA'' HeqA''].
    exists A'', (oExpSubst (oExt D0 k C) D0 (oWkn D0 k C) i A0 x0).
    repeat split;
      [ exact HT''
      | apply vart_wkn;
        [ exact HV0 | exact HC | exact HTA'' |
          eapply eq_wkn_step_ty with (GG := oExt G j B) (w0 := w0) (A := A');
          wfx ]
      | eapply eq_wkn_step
          with (A := A')
               (x := oExpSubst (oExt G j B) G (oWkn G j B) i A x); wfx
      | ].
    intros r l Hr.
    assert (i = iCode l) as Hi0 by (eapply TyOk_U_info; [ exact HA' | exact Hr ]).
    subst i.
    rewrite Hr in HT0; apply TySub_U_inv in HT0; subst A0.
    apply cvar_ext; apply Hcv0; exact Hr.
  - (* wk_lift *)
    unfold oExt in HGG; safe_invert HGG.
    assert (Wk (oExt D1 j A1') (oExt G j B) (oLiftW D1 G w1 j B A1')) as HWfull
        by (apply wk_lift'; assumption).
    destruct (Hvpkg _ _ HW1) as [A0 [x0 [HT0 [HV0 [Heq0 Hcv0]]]]].
    destruct (Htpkg _ _ HWfull) as [A'' HT''].
    destruct (TySub_ok HT'' HWfull (Wk_dom HWfull) HA') as [HTA'' HeqA''].
    destruct (TySub_ok HT0 HW1 (Wk_dom HW1) (VarT_TyOk Hx)) as [HTA0 HeqA0].
    exists A'', (oExpSubst (oExt D1 j A1') D1 (oWkn D1 j A1') i A0 x0).
    repeat split;
      [ exact HT''
      | apply vart_wkn;
        [ exact HV0 | exact HA1' | exact HTA'' |
          apply lift_step_T4
            with (G := G) (w1 := w1) (B := B) (A := A) (A' := A'); wfx ]
      | apply lift_step_tm; wfx
      | ].
    intros r l Hr.
    assert (i = iCode l) as Hi0 by (eapply TyOk_U_info; [ exact HA' | exact Hr ]).
    subst i.
    destruct (TyOk_iCode_shape (VarT_TyOk Hx)) as [r0 HAeq].
    rewrite HAeq in HT0; apply TySub_U_inv in HT0; subst A0.
    rewrite HAeq; apply cvar_lift_wkn; apply Hcv0; exact HAeq.
Qed.

(* ================================================================== *)
(* PHASE A: the type-level block ([EnvOk]/[TyOk]/[NfCode]/[VarT]) is    *)
(* closed under weakening, structurally.                               *)
(* ================================================================== *)

Theorem Nf_wk_str :
  (forall G, EnvOk G -> True)
  /\ (forall G i A, TyOk G i A ->
        forall D w, Wk D G w -> exists A', TySub D G w i A A')
  /\ (forall G r l c, NfCode G r l c ->
        forall D w, Wk D G w -> exists c', CodeSub D G w r l c c')
  /\ (forall G i A x, VarT G i A x ->
        forall D w, Wk D G w ->
          exists A' x', TySub D G w i A A' /\ VarT D i A' x'
                     /\ eqt (sExp D i A') (oExpSubst D G w i A x) x'
                     /\ (forall r l, A = oU G r l -> CVar D G w r l x x'))
  /\ (forall G i A e, NeET G i A e -> True)
  /\ (forall G i A e, NfET G i A e -> True).
Proof.
  apply Nf_mutind.
  (* ---- EnvOk ---- *)
  - exact I.
  - intros; exact I.
  (* ---- TyOk ---- *)
  - intros G r l HG _ Hr Hl D w HW.
    exists (oU D r l); apply tysub_U.
  - intros G r l c Hc IHc D w HW.
    destruct (IHc D w HW) as [c' Hc'].
    exists (oEl D r l c'); apply tysub_El; assumption.
  (* ---- NfCode ---- *)
  - intros G HG _ D w HW; exists (oNat D); apply codesub_nat; assumption.
  - intros G HG _ D w HW; exists (oEmpty D); apply codesub_empty; assumption.
  - intros G rF lF lG F B HrF HlF HlG HF IHF HB IHB D w HW.
    destruct (IHF D w HW) as [F' HCF].
    destruct (CodeSub_ok HCF HW (Wk_dom HW)) as [HF' HeqF].
    assert (eqt (sTy D (iEl rF lF))
              (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
      as HeqEl.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF ]. }
    assert (Wk (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')))
      as HW2
      by (apply wk_lift';
          [ assumption | apply tyok_El; assumption
          | apply tyok_El; assumption | exact HeqEl ]).
    destruct (IHB _ _ HW2) as [B' HCB].
    exists (oPiRel D rF lF lG F' B'); apply codesub_pi_rel; assumption.
  - intros G rF lF F B HrF HlF HF IHF HB IHB D w HW.
    destruct (IHF D w HW) as [F' HCF].
    destruct (CodeSub_ok HCF HW (Wk_dom HW)) as [HF' HeqF].
    assert (eqt (sTy D (iEl rF lF))
              (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
      as HeqEl.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF ]. }
    assert (Wk (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')))
      as HW2
      by (apply wk_lift';
          [ assumption | apply tyok_El; assumption
          | apply tyok_El; assumption | exact HeqEl ]).
    destruct (IHB _ _ HW2) as [B' HCB].
    exists (oPiIrr D rF lF F' B'); apply codesub_pi_irr; assumption.
  - intros G r l c Hx IHx D w HW.
    destruct (IHx D w HW) as [A' [x' [HT [HV [Heq Hcv]]]]].
    apply TySub_U_inv in HT; subst A'.
    exists x'; eapply codesub_var;
      [ exact Hx | exact HV | exact Heq | apply Hcv; reflexivity ].
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
  - intros; exact I.
Qed.

Definition TyOk_wk_str := proj1 (proj2 Nf_wk_str).
Definition NfCode_wk_str := proj1 (proj2 (proj2 Nf_wk_str)).
Definition VarT_wk_str := proj1 (proj2 (proj2 (proj2 Nf_wk_str))).

(* ================================================================== *)
(* The [exists]-form projections, as consumed downstream               *)
(* ================================================================== *)

Theorem TyOk_wk G i A
  : TyOk G i A -> forall D w, Wk D G w -> EnvOk D ->
    exists A', TyOk D i A'
            /\ eqt (sTy D i) (oTySubst D G w i A) A'.
Proof.
  intros HA D w HW HD.
  destruct (TyOk_wk_str HA HW) as [A' HT].
  exists A'; apply (TySub_ok HT HW HD HA).
Qed.

Theorem NfCode_wk G r l c
  : NfCode G r l c -> forall D w, Wk D G w -> EnvOk D ->
    exists c', NfCode D r l c'
            /\ eqt (sCode D r l)
                 (oExpSubst D G w (iCode l) (oU G r l) c) c'.
Proof.
  intros Hc D w HW HD.
  destruct (NfCode_wk_str Hc HW) as [c' HC].
  exists c'; apply (CodeSub_ok HC HW HD).
Qed.

Theorem VarT_wk G i A x
  : VarT G i A x -> forall D w, Wk D G w -> EnvOk D ->
    exists A' x', TyOk D i A'
               /\ eqt (sTy D i) (oTySubst D G w i A) A'
               /\ VarT D i A' x'
               /\ eqt (sExp D i A') (oExpSubst D G w i A x) x'.
Proof.
  intros Hx D w HW HD.
  destruct (VarT_wk_str Hx HW) as [A' [x' [HT [HV [Heq _]]]]].
  destruct (TySub_ok HT HW HD (VarT_TyOk Hx)) as [HTA HeqA].
  exists A', x'; repeat split; assumption.
Qed.

(* ================================================================== *)
(* PART 2: NORMAL SUBSTITUTIONS                                        *)
(* ================================================================== *)

Inductive NSub : term -> term -> term -> Prop :=
| nsub_wk : forall D G w, Wk D G w -> NSub D G w
| nsub_forget : forall D, EnvOk D -> NSub D oEmp (oForget D)
| nsub_snoc : forall D G i A g a A',
    NSub D G g -> TyOk G i A -> TyOk D i A' ->
    eqt (sTy D i) (oTySubst D G g i A) A' ->
    NfET D i A' a ->
    NSub D (oExt G i A) (oSnoc D G i A g a).

Lemma NSub_dom D G g : NSub D G g -> EnvOk D.
Proof.
  induction 1; [ eapply Wk_dom; eassumption | assumption | assumption ].
Qed.

Lemma NSub_cod D G g : NSub D G g -> EnvOk G.
Proof.
  induction 1;
    [ eapply Wk_cod; eassumption | apply envok_emp
    | apply envok_ext; [ | assumption ];
      eapply TyOk_EnvOk; eassumption ].
Qed.

Lemma NSub_wf D G g : NSub D G g -> wf_term ott_dtt [] g (sSub D G).
Proof.
  induction 1 as [ D G w HW | D HD | D G i A g a A' Hg IHg HA HA' Heq Ha ].
  - apply Wk_wf; assumption.
  - apply wf_Forget; apply EnvOk_wf; assumption.
  - assert (EnvOk D) as HDok by (eapply NSub_dom; eassumption).
    assert (EnvOk G) as HGok by (eapply NSub_cod; eassumption).
    apply wf_Snoc; try wfx.
    eapply wf_term_conv; [ apply (NfET_wf Ha) | ].
    apply eq_sort_exp_ty; [ wfx | wfx | apply eq_term_sym; exact Heq ].
Qed.


(* ---- [CodeSub] and [TySub] are partial functions ---- *)

Lemma CodeSub_inv D G w r l c c'
  : CodeSub D G w r l c c' ->
    (c = oNat G /\ c' = oNat D)
    \/ (c = oEmpty G /\ c' = oEmpty D)
    \/ (exists rF lF F B F' B',
           c = oPiRel G rF lF l F B /\ c' = oPiRel D rF lF l F' B'
           /\ CodeSub D G w rF lF F F'
           /\ CodeSub (oExtC D rF lF F') (oExtC G rF lF F)
                (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
                oRel l B B')
    \/ (exists rF lF F B F' B',
           c = oPiIrr G rF lF F B /\ c' = oPiIrr D rF lF F' B'
           /\ CodeSub D G w rF lF F F'
           /\ CodeSub (oExtC D rF lF F') (oExtC G rF lF F)
                (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
                oIrr oL0 B B')
    \/ (VarT G (iCode l) (oU G r l) c /\ CVar D G w r l c c').
Proof.
  destruct 1 as
    [ D G w HG | D G w HG
    | D G w rF lF lG F B F' B' HrF HlF HlG HF HB HCF HCB
    | D G w rF lF F B F' B' HrF HlF HF HB HCF HCB
    | D G w r l c c' Hx Hx' Heq Hcv ].
  - left; split; reflexivity.
  - right; left; split; reflexivity.
  - right; right; left; exists rF, lF, F, B, F', B'; repeat split; assumption.
  - right; right; right; left;
      exists rF, lF, F, B, F', B'; repeat split; assumption.
  - right; right; right; right; split; assumption.
Qed.

Lemma CodeSub_det D G w r l c c1 c2
  : CodeSub D G w r l c c1 -> CodeSub D G w r l c c2 -> c1 = c2.
Proof.
  intro H1; revert c2.
  induction H1 as
    [ D G w HG | D G w HG
    | D G w rF lF lG F B F' B' HrF HlF HlG HF HB HCF IHF HCB IHB
    | D G w rF lF F B F' B' HrF HlF HF HB HCF IHF HCB IHB
    | D G w r l c c' Hx Hx' Heq Hcv ];
    intros c2 H2; apply CodeSub_inv in H2;
    destruct H2 as
      [ [Hc Hc2]
      | [ [Hc Hc2]
        | [ [rF2 [lF2 [F2 [B2 [F2' [B2' [Hc [Hc2 [HCF2 HCB2]]]]]]]]]
          | [ [rF2 [lF2 [F2 [B2 [F2' [B2' [Hc [Hc2 [HCF2 HCB2]]]]]]]]]
            | [Hv Hcv2] ] ] ] ];
    try (cbv [oNat oEmpty oPiRel oPiIrr] in Hc; discriminate);
    try (no_var Hv);
    try (rewrite Hc in Hx; no_var Hx).
  - congruence.
  - congruence.
  - cbv [oPiRel] in Hc; safe_invert Hc.
    assert (F' = F2') as HF2 by (apply IHF; assumption).
    subst F2'.
    assert (B' = B2') as HB2 by (apply IHB; assumption).
    congruence.
  - cbv [oPiIrr] in Hc; safe_invert Hc.
    assert (F' = F2') as HF2 by (apply IHF; assumption).
    subst F2'.
    assert (B' = B2') as HB2 by (apply IHB; assumption).
    congruence.
  - eapply CVar_det; [ exact Hcv | exact Hcv2 ].
Qed.

Lemma TySub_inv D G w i A A'
  : TySub D G w i A A' ->
    (exists r l, i = iCode l /\ A = oU G r l /\ A' = oU D r l)
    \/ (exists r l c c', i = iEl r l /\ A = oEl G r l c /\ A' = oEl D r l c'
                         /\ CodeSub D G w r l c c').
Proof.
  destruct 1 as [ r l | r l c c' HC ].
  - left; exists r, l; repeat split.
  - right; exists r, l, c, c'; repeat split; assumption.
Qed.

Lemma TySub_El_inv D G w r l c A'
  : TySub D G w (iEl r l) (oEl G r l c) A' ->
    exists c', A' = oEl D r l c' /\ CodeSub D G w r l c c'.
Proof.
  intro H; apply TySub_inv in H;
    destruct H as [ [r0 [l0 [Hi [HA _]]]]
                  | [r0 [l0 [c0 [c' [Hi [HA [HA' HC]]]]]]] ].
  - cbv [oU oEl] in HA; discriminate.
  - cbv [oEl] in HA; safe_invert HA; exists c'; split;
      [ congruence | assumption ].
Qed.

Lemma TySub_det D G w i A A1 A2
  : TySub D G w i A A1 -> TySub D G w i A A2 -> A1 = A2.
Proof.
  intros H1 H2; destruct H1 as [ r l | r l c c1 HC1 ].
  - apply TySub_U_inv in H2; congruence.
  - apply TySub_El_inv in H2; destruct H2 as [c2 [HA2 HC2]].
    assert (c1 = c2) by (eapply CodeSub_det; eassumption); congruence.
Qed.

(* ================================================================== *)
(* (a) THE FOUR NEW SUBSTITUTION COMMUTATIONS                          *)
(*                                                                     *)
(* [ott_subst_commute] (Lang/OTT/SubstCommute.v) supplies the rules     *)
(* that were missing when the first half of this file was written:      *)
(* "app_rel subst", "app_irr subst", "lam_irr subst", "Emptyrec subst". *)
(* They are repackaged here in the vocabulary of WIP/DttSyntax.v,       *)
(* exactly as WIP/DttEqns.v does for the other 28.                      *)
(*                                                                     *)
(* Two spelling facts, both deliberate on the language side:            *)
(*   - the two [app] rules and [lam_irr subst] lift [g] with            *)
(*     [DttSyntax.oLift], i.e. over [ext G [rF,iota lF] (El G rF lF     *)
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
