Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.NfWk Pyrosome.Gluing.Dtt.Inj Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelCand Pyrosome.Gluing.Dtt.LogRelFun.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 2c: ESCAPE AND REFLECT.
   ===================================================================== *)

Notation term := (@Term.term string).
Notation sort := (@Term.sort string).

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* ================================================================== *)
(* 0. Small inversions                                                 *)
(* ================================================================== *)

(* At a universe the only neutrals are variables: no eliminator of
   [ott_dtt] has a universe as its result type, so every other [NeET]
   clause concludes at an [iEl] info. *)
Lemma NeET_iCode G i A n
  : NeET G i A n -> forall l, i = iCode l -> VarT G i A n.
Proof.
  destruct 1; intros l0 Hi;
    try (exfalso; unfold iCode, iEl, oInfo, oNext, oIota in Hi; congruence).
  assumption.
Qed.

(* ================================================================== *)
(* 1. The codomain instance at a NAMED domain/codomain/argument         *)
(*                                                                     *)
(* [neet_app_rel] insists on the SYNTACTIC normal forms [F'], [B'] and  *)
(* [a'] in the slots where [appAtRel] carries the raw substitution      *)
(* instances.  This transports [LogRelCand.ac_appConcl] across that      *)
(* renaming; it is stated generically in the outer relevance/level, so  *)
(* the one lemma serves both Pi clauses.                                *)
(* ================================================================== *)

Section AppNamed.

  Context (D G rF lF rG lG F B w a F' B' a' : term).

  Context
    (HD : wft D sEnv)
    (HG : wft G sEnv)
    (HrF : wft rF sRelevance)
    (HlF : wft lF sLvl)
    (HrG : wft rG sRelevance)
    (HlG : wft lG sLvl)
    (Hw : wft w (sSub D G))
    (HF : wft F (sCode G rF lF))
    (HB : wft B (sCode (oExtC G rF lF F) rG lG))
    (Ha : wft a (sElt D rF lF (wkCode D G w rF lF F)))
    (HF' : wft F' (sCode D rF lF))
    (HeqF : eqt (sCode D rF lF) (wkCode D G w rF lF F) F')
    (HB' : wft B' (sCode (oExtC D rF lF F') rG lG))
    (HeqB : eqt (sCode (oExtC D rF lF F') rG lG)
              (oExpSubst (oExtC D rF lF (wkCode D G w rF lF F))
                 (oExtC G rF lF F) (oLift D G w rF lF F) (iCode lG)
                 (oU (oExtC G rF lF F) rG lG) B) B')
    (Ha' : wft a' (sElt D rF lF F'))
    (Heqa : eqt (sElt D rF lF F') a a').

  Local Notation Fw := (wkCode D G w rF lF F).
  Local Notation Bw :=
    (oExpSubst (oExtC D rF lF (wkCode D G w rF lF F)) (oExtC G rF lF F)
       (oLift D G w rF lF F) (iCode lG) (oU (oExtC G rF lF F) rG lG) B).

  Lemma an_iF : wft (iEl rF lF) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]. Qed.

  Lemma an_iG : wft (iEl rG lG) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrG | apply wf_Iota; exact HlG ]. Qed.

  Lemma an_cG : wft (iCode lG) sInfo.
  Proof.
    unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlG ].
  Qed.

  Lemma an_Fw : wft Fw (sCode D rF lF).
  Proof.
    apply ac_Fw;
      [ exact HD | exact HG | exact HrF | exact HlF | exact Hw | exact HF ].
  Qed.

  Lemma an_ElFw : wft (oEl D rF lF Fw) (sTy D (iEl rF lF)).
  Proof. apply wf_El; [ exact HD | exact HrF | exact HlF | apply an_Fw ]. Qed.

  Lemma an_ElF' : wft (oEl D rF lF F') (sTy D (iEl rF lF)).
  Proof. apply wf_El; [ exact HD | exact HrF | exact HlF | exact HF' ]. Qed.

  Lemma an_DFw : wft (oExtC D rF lF Fw) sEnv.
  Proof. apply wf_ExtC; [ exact HD | exact HrF | exact HlF | apply an_Fw ]. Qed.

  Lemma an_DF' : wft (oExtC D rF lF F') sEnv.
  Proof. apply wf_ExtC; [ exact HD | exact HrF | exact HlF | exact HF' ]. Qed.

  Lemma an_Elqe
    : eqt (sTy D (iEl rF lF)) (oEl D rF lF F') (oEl D rF lF Fw).
  Proof.
    apply El_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply eq_term_sym; exact HeqF ].
  Qed.

  Lemma an_env
    : eqt sEnv (oExtC D rF lF F') (oExtC D rF lF Fw).
  Proof.
    unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; apply an_iF
      | apply an_Elqe ].
  Qed.

  (* [B'] and [Bw] agree, at the [Fw]-flavoured spelling of the sort. *)
  Lemma an_Bqe
    : eqt (sCode (oExtC D rF lF Fw) rG lG) B' Bw.
  Proof.
    eapply eq_term_conv; [ apply eq_term_sym; exact HeqB | ].
    unfold sCode; apply sExp_cong;
      [ apply an_env
      | apply eq_term_refl; apply an_cG
      | apply U_cong;
        [ apply an_env | apply eq_term_refl; exact HrG
        | apply eq_term_refl; exact HlG ] ].
  Qed.

  Lemma an_inst
    : eqt (sSub D (oExtC D rF lF Fw))
        (oInst D rF lF F' a') (oInst D rF lF Fw a).
  Proof.
    unfold oInst, oExtC.
    apply Snoc_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HD
      | apply eq_term_refl; apply an_iF
      | apply an_Elqe
      | apply eq_term_refl; apply wf_Id; exact HD
      | ].
    eapply eq_term_conv; [ apply eq_term_sym; exact Heqa | ].
    unfold sElt; apply eq_sort_exp_ty.
    eapply eq_term_trans; [ apply an_Elqe | ].
    apply eq_term_sym; apply eq_ty_subst_id;
      [ exact HD | apply an_iF | apply an_ElFw ].
  Qed.

  Theorem an_appConcl
    : eqt (sTy D (iEl rG lG))
        (oTySubst D (oExtC D rF lF F') (oInst D rF lF F' a') (iEl rG lG)
           (oEl (oExtC D rF lF F') rG lG B'))
        (oTySubst D (oExtC G rF lF F) (instAt D G rF lF F w a) (iEl rG lG)
           (oEl (oExtC G rF lF F) rG lG B)).
  Proof.
    eapply eq_term_trans; [ | apply ac_appConcl;
      [ exact HD | exact HG | exact HrF | exact HlF | exact HrG | exact HlG
      | exact Hw | exact HF | exact HB | exact Ha ] ].
    apply TySubst_cong
      with (G1 := D) (G2 := D)
           (G1' := oExtC D rF lF F') (G2' := oExtC D rF lF Fw)
           (g1 := oInst D rF lF F' a') (g2 := oInst D rF lF Fw a)
           (i1 := iEl rG lG) (i2 := iEl rG lG)
           (A1 := oEl (oExtC D rF lF F') rG lG B')
           (A2 := oEl (oExtC D rF lF Fw) rG lG Bw);
      [ apply eq_term_refl; exact HD
      | apply an_env
      | apply an_inst
      | apply eq_term_refl; apply an_iG
      | apply El_cong;
        [ apply an_env | apply eq_term_refl; exact HrG
        | apply eq_term_refl; exact HlG | apply an_Bqe ] ].
  Qed.

End AppNamed.

(* ================================================================== *)
(* 2. Naming the weakened Pi type                                      *)
(* ================================================================== *)

Lemma eq_ElPiRel_wk D G rF lF lG F B w F' B'
  : wft D sEnv -> wft G sEnv -> wft rF sRelevance -> wft lF sLvl ->
    wft lG sLvl -> wft w (sSub D G) -> wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) oRel lG) ->
    eqt (sCode D rF lF) (wkCode D G w rF lF F) F' ->
    eqt (sCode (oExtC D rF lF F') oRel lG)
        (wkCodCodeRel D G w rF lF lG F B) B' ->
    eqt (sTy D (iEl oRel lG))
      (oTySubst D G w (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)))
      (oEl D oRel lG (oPiRel D rF lF lG F' B')).
Proof.
  intros HD HG HrF HlF HlG Hw HF HB HeqF HeqB.
  eapply eq_term_trans.
  { apply pr_Pi_subst;
      [ exact HD | exact HG | exact HrF | exact HlF | exact HlG | exact Hw
      | exact HF | exact HB ]. }
  apply El_cong;
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; apply wf_Rel
    | apply eq_term_refl; exact HlG
    | ].
  apply PiRel_cong;
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; exact HrF
    | apply eq_term_refl; exact HlF
    | apply eq_term_refl; exact HlG
    | exact HeqF | exact HeqB ].
Qed.

Lemma eq_ElPiIrr_wk D G rF lF F B w F' B'
  : wft D sEnv -> wft G sEnv -> wft rF sRelevance -> wft lF sLvl ->
    wft w (sSub D G) -> wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) oIrr oL0) ->
    eqt (sCode D rF lF) (wkCode D G w rF lF F) F' ->
    eqt (sCode (oExtC D rF lF F') oIrr oL0)
        (wkCodCodeIrr D G w rF lF F B) B' ->
    eqt (sTy D (iEl oIrr oL0))
      (oTySubst D G w (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)))
      (oEl D oIrr oL0 (oPiIrr D rF lF F' B')).
Proof.
  intros HD HG HrF HlF Hw HF HB HeqF HeqB.
  assert (wft F' (sCode D rF lF)) as HF'
      by (eapply eqt_wf_r; exact HeqF).
  assert (wft (oExtC D rF lF F') sEnv) as HDF'
      by (apply wf_ExtC; [ exact HD | exact HrF | exact HlF | exact HF' ]).
  eapply eq_term_trans.
  { apply pi_Pi_subst;
      [ exact HD | exact HG | exact HrF | exact HlF | exact Hw
      | exact HF | exact HB ]. }
  apply El_cong;
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; apply wf_Irr
    | apply eq_term_refl; apply wf_L0
    | ].
  apply eqt_i2c; [ exact HD | apply wf_Irr | ].
  apply PiIrr_cong;
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; exact HrF
    | apply eq_term_refl; exact HlF
    | exact HeqF
    | apply eqt_c2i; [ exact HDF' | apply wf_Irr | exact HeqB ] ].
Qed.

(* ================================================================== *)
(* 3. Weakening the codomain code, at the clause's chosen [F']          *)
(* ================================================================== *)

Lemma wk_codcode D G w rF lF rG lG F B F'
  : Wk D G w -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (wkCode D G w rF lF F) F' ->
    NfCode (oExtC G rF lF F) rG lG B ->
    exists B', NfCode (oExtC D rF lF F') rG lG B'
            /\ eqt (sCode (oExtC D rF lF F') rG lG)
                 (oExpSubst (oExtC D rF lF (wkCode D G w rF lF F))
                    (oExtC G rF lF F) (oLift D G w rF lF F) (iCode lG)
                    (oU (oExtC G rF lF F) rG lG) B) B'.
Proof.
  intros HW HD HF HF' HeqF HB.
  destruct (CSub_liftC (csub_wk HW) HD HF HF' HeqF) as [HC2 [HD2 HeqEl]].
  destruct (NfCode_csubst HB HC2 HD2) as [B' [HB' HeqB']].
  exists B'; split; [ exact HB' | ].
  eapply eq_term_trans; [ | exact HeqB' ].
  assert (EnvOk G) as HGok by (eapply Wk_cod; exact HW).
  eapply eqt_Usub_c
    with (G' := oExtC G rF lF F)
         (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (r := rG) (l := lG);
    [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
  apply eq_lift_shift;
    [ exact HW | exact HD | exact HF | exact HF' | exact HeqF
    | wfx | wfx | wfx ].
Qed.

(* ================================================================== *)
(* 4. REFLECT at the two Pi clauses: a neutral function applied to a    *)
(*    normalizable argument is neutral, at the clause's named codomain. *)
(* ================================================================== *)

Lemma pi_rel_reflect_app D G rF lF lG F B w e a F' C
  : Wk D G w -> EnvOk D ->
    NfCode G rF lF F -> NfCode (oExtC G rF lF F) oRel lG B ->
    HasNe G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) e ->
    NfCode D rF lF F' ->
    eqt (sCode D rF lF) (wkCode D G w rF lF F) F' ->
    HasNf D (iEl rF lF) (oEl D rF lF F') a ->
    wft a (sElt D rF lF (wkCode D G w rF lF F)) ->
    TyOk D (iEl oRel lG) C ->
    eqt (sTy D (iEl oRel lG)) (codAtRel D G rF lF lG F B w a) C ->
    HasNe D (iEl oRel lG) C (appAtRel D G rF lF lG F B w e a).
Proof.
  intros HW HD HF HB HNe HF' HeqF HNfa Haw HTC HeqC.
  assert (EnvOk G) as HG by (eapply Wk_cod; exact HW).
  assert (RelNf rF) as HrF by (eapply NfCode_RelNf; exact HF).
  assert (LvlNf lF) as HlF by (eapply NfCode_LvlNf; exact HF).
  assert (LvlNf lG) as HlG by (eapply NfCode_LvlNf; exact HB).
  destruct (wk_codcode HW HD HF HF' HeqF HB) as [B' [HB' HeqB]].
  destruct HNe as [n [Hn Heqn]].
  destruct HNfa as [a1 [Ha1 Heqa1]].
  destruct (NeET_wk Hn HW HD) as [A2 [n' [HTA2 [HeqA2 [Hn' Heqn']]]]].
  (* the weakened Pi type IS [El (Pi F' B')] *)
  assert (A2 = oEl D oRel lG (oPiRel D rF lF lG F' B')) as HA2.
  { eapply TyOk_inj;
      [ exact HTA2
      | apply tyok_El; apply nfcode_pi_rel;
        [ exact HrF | exact HlF | exact HlG | exact HF' | exact HB' ]
      | eapply eq_term_trans;
        [ apply eq_term_sym; exact HeqA2
        | apply eq_ElPiRel_wk;
          [ wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx
          | exact HeqF | exact HeqB ] ] ]. }
  subst A2.
  (* the codomain instance, at the named data *)
  assert (eqt (sTy D (iEl oRel lG))
            (oTySubst D (oExtC D rF lF F') (oInst D rF lF F' a1)
               (iEl oRel lG) (oEl (oExtC D rF lF F') oRel lG B')) C)
    as HeqCn.
  { eapply eq_term_trans; [ | exact HeqC ].
    apply an_appConcl with (rG := oRel);
      [ wfx | wfx | wfx | wfx | apply wf_Rel | wfx | wfx | wfx | wfx
      | exact Haw | exact HeqF | exact HeqB | exact Heqa1 ]. }
  exists (oAppRel D rF lF lG F' B' n' a1); split.
  - eapply neet_app_rel;
      [ exact Hn' | exact Ha1 | exact HTC | exact HeqCn ].
  - eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HeqCn ].
    apply AppRel_cong;
      [ apply eq_term_refl; wfx
      | apply eq_term_refl; wfx
      | apply eq_term_refl; wfx
      | apply eq_term_refl; wfx
      | exact HeqF
      | exact HeqB
      | (* the function *)
        eapply eq_term_trans; [ | exact Heqn' ];
        eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := D) (G2 := D) (G1' := G) (G2' := G)
                 (g1 := w) (g2 := w)
                 (i1 := iEl oRel lG) (i2 := iEl oRel lG)
                 (A1 := oEl G oRel lG (oPiRel G rF lF lG F B))
                 (A2 := oEl G oRel lG (oPiRel G rF lF lG F B))
                 (v1 := e) (v2 := n);
          [ apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | exact Heqn ]
        | apply eq_sort_exp_ty; exact HeqA2 ]
      | exact Heqa1 ].
Qed.

Lemma pi_irr_reflect_app D G rF lF F B w e a F' C
  : Wk D G w -> EnvOk D ->
    NfCode G rF lF F -> NfCode (oExtC G rF lF F) oIrr oL0 B ->
    HasNe G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e ->
    NfCode D rF lF F' ->
    eqt (sCode D rF lF) (wkCode D G w rF lF F) F' ->
    HasNf D (iEl rF lF) (oEl D rF lF F') a ->
    wft a (sElt D rF lF (wkCode D G w rF lF F)) ->
    TyOk D (iEl oIrr oL0) C ->
    eqt (sTy D (iEl oIrr oL0)) (codAtIrr D G rF lF F B w a) C ->
    HasNe D (iEl oIrr oL0) C (appAtIrr D G rF lF F B w e a).
Proof.
  intros HW HD HF HB HNe HF' HeqF HNfa Haw HTC HeqC.
  assert (EnvOk G) as HG by (eapply Wk_cod; exact HW).
  assert (RelNf rF) as HrF by (eapply NfCode_RelNf; exact HF).
  assert (LvlNf lF) as HlF by (eapply NfCode_LvlNf; exact HF).
  destruct (wk_codcode HW HD HF HF' HeqF HB) as [B' [HB' HeqB]].
  destruct HNe as [n [Hn Heqn]].
  destruct HNfa as [a1 [Ha1 Heqa1]].
  destruct (NeET_wk Hn HW HD) as [A2 [n' [HTA2 [HeqA2 [Hn' Heqn']]]]].
  assert (A2 = oEl D oIrr oL0 (oPiIrr D rF lF F' B')) as HA2.
  { eapply TyOk_inj;
      [ exact HTA2
      | apply tyok_El; apply nfcode_pi_irr;
        [ exact HrF | exact HlF | exact HF' | exact HB' ]
      | eapply eq_term_trans;
        [ apply eq_term_sym; exact HeqA2
        | apply eq_ElPiIrr_wk;
          [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
          | exact HeqF | exact HeqB ] ] ]. }
  subst A2.
  assert (eqt (sTy D (iEl oIrr oL0))
            (oTySubst D (oExtC D rF lF F') (oInst D rF lF F' a1)
               (iEl oIrr oL0) (oEl (oExtC D rF lF F') oIrr oL0 B')) C)
    as HeqCn.
  { eapply eq_term_trans; [ | exact HeqC ].
    apply an_appConcl with (rG := oIrr);
      [ wfx | wfx | wfx | wfx | apply wf_Irr | apply wf_L0 | wfx | wfx | wfx
      | exact Haw | exact HeqF | exact HeqB | exact Heqa1 ]. }
  exists (oAppIrr D rF lF F' B' n' a1); split.
  - eapply neet_app_irr;
      [ exact Hn' | exact Ha1 | exact HTC | exact HeqCn ].
  - eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HeqCn ].
    apply AppIrr_cong;
      [ apply eq_term_refl; wfx
      | apply eq_term_refl; wfx
      | apply eq_term_refl; wfx
      | exact HeqF
      | exact HeqB
      | eapply eq_term_trans; [ | exact Heqn' ];
        eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := D) (G2 := D) (G1' := G) (G2' := G)
                 (g1 := w) (g2 := w)
                 (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
                 (A1 := oEl G oIrr oL0 (oPiIrr G rF lF F B))
                 (A2 := oEl G oIrr oL0 (oPiIrr G rF lF F B))
                 (v1 := e) (v2 := n);
          [ apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | apply eq_term_refl; wfx
          | exact Heqn ]
        | apply eq_sort_exp_ty; exact HeqA2 ]
      | exact Heqa1 ].
Qed.

(* ================================================================== *)
(* 5. ESCAPE at [rty_pi_rel]: this is where ETA is cashed in.          *)
(*                                                                     *)
(* [Wk]'s one-step weakening is the BARE [wkn] ([wk_wkn]), which is    *)
(* exactly how "Pi_rel eta" is stated, so the eta step below is the     *)
(* rule read off directly.                                             *)
(* ================================================================== *)

(* At the one-step weakening and the head variable, the raw codomain
   instance IS the codomain type: [<wkn,hd> = id]. *)
Lemma eq_codAt_wkn G rF lF lG F B
  : wft G sEnv -> wft rF sRelevance -> wft lF sLvl -> wft lG sLvl ->
    wft F (sCode G rF lF) -> wft B (sCode (oExtC G rF lF F) oRel lG) ->
    eqt (sTy (oExtC G rF lF F) (iEl oRel lG))
      (codAtRel (oExtC G rF lF F) G rF lF lG F B
         (oWkn G (iEl rF lF) (oEl G rF lF F))
         (oHd G (iEl rF lF) (oEl G rF lF F)))
      (oEl (oExtC G rF lF F) oRel lG B).
Proof.
  intros HG HrF HlF HlG HF HB.
  assert (wft (iEl rF lF) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]).
  assert (wft (iEl oRel lG) sInfo) as HiG
      by (unfold iEl; apply wf_Info;
          [ apply wf_Rel | apply wf_Iota; exact HlG ]).
  assert (wft (oEl G rF lF F) (sTy G (iEl rF lF))) as HA
      by (apply wf_El; [ exact HG | exact HrF | exact HlF | exact HF ]).
  assert (wft (oExtC G rF lF F) sEnv) as HD
      by (apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]).
  assert (wft (oEl (oExtC G rF lF F) oRel lG B)
            (sTy (oExtC G rF lF F) (iEl oRel lG))) as HElB
      by (apply wf_El; [ exact HD | apply wf_Rel | exact HlG | exact HB ]).
  assert (eqt (sSub (oExtC G rF lF F) (oExtC G rF lF F))
            (instAt (oExtC G rF lF F) G rF lF F
               (oWkn G (iEl rF lF) (oEl G rF lF F))
               (oHd G (iEl rF lF) (oEl G rF lF F)))
            (oId (oExtC G rF lF F))) as Hsnoc
      by (unfold instAt, oExtC;
          apply eq_snoc_wkn_hd; [ exact HG | exact HiF | exact HA ]).
  unfold codAtRel.
  eapply eq_term_trans;
    [ | apply eq_ty_subst_id; [ exact HD | exact HiG | exact HElB ] ].
  apply TySubst_cong
    with (G1 := oExtC G rF lF F) (G2 := oExtC G rF lF F)
         (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
         (g2 := oId (oExtC G rF lF F))
         (i1 := iEl oRel lG) (i2 := iEl oRel lG)
         (A1 := oEl (oExtC G rF lF F) oRel lG B)
         (A2 := oEl (oExtC G rF lF F) oRel lG B);
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; exact HD
    | exact Hsnoc
    | apply eq_term_refl; exact HiG
    | apply eq_term_refl; exact HElB ].
Qed.

(* The [Pi_irr] analogue of [eq_codAt_wkn] above -- same statement with
   [lG] pinned to [oL0] and the relevance of the binder pinned to [oIrr].
   Used by the ESCAPE half of [rty_pi_irr] below, to identify the
   codomain candidate's own type [C] with [oEl (oExtC G rF lF F) oIrr oL0 B]
   at the one-step weakening, exactly as the [Pi_rel] ESCAPE half does for
   [codAtRel]. *)
Lemma eq_codAtIrr_wkn G rF lF F B
  : wft G sEnv -> wft rF sRelevance -> wft lF sLvl ->
    wft F (sCode G rF lF) -> wft B (sCode (oExtC G rF lF F) oIrr oL0) ->
    eqt (sTy (oExtC G rF lF F) (iEl oIrr oL0))
      (codAtIrr (oExtC G rF lF F) G rF lF F B
         (oWkn G (iEl rF lF) (oEl G rF lF F))
         (oHd G (iEl rF lF) (oEl G rF lF F)))
      (oEl (oExtC G rF lF F) oIrr oL0 B).
Proof.
  intros HG HrF HlF HF HB.
  assert (wft (iEl rF lF) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]).
  assert (wft (iEl oIrr oL0) sInfo) as HiG
      by (unfold iEl; apply wf_Info;
          [ apply wf_Irr | apply wf_Iota; apply wf_L0 ]).
  assert (wft (oEl G rF lF F) (sTy G (iEl rF lF))) as HA
      by (apply wf_El; [ exact HG | exact HrF | exact HlF | exact HF ]).
  assert (wft (oExtC G rF lF F) sEnv) as HD
      by (apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]).
  assert (wft (oEl (oExtC G rF lF F) oIrr oL0 B)
            (sTy (oExtC G rF lF F) (iEl oIrr oL0))) as HElB
      by (apply wf_El; [ exact HD | apply wf_Irr | apply wf_L0 | exact HB ]).
  assert (eqt (sSub (oExtC G rF lF F) (oExtC G rF lF F))
            (instAt (oExtC G rF lF F) G rF lF F
               (oWkn G (iEl rF lF) (oEl G rF lF F))
               (oHd G (iEl rF lF) (oEl G rF lF F)))
            (oId (oExtC G rF lF F))) as Hsnoc
      by (unfold instAt, oExtC;
          apply eq_snoc_wkn_hd; [ exact HG | exact HiF | exact HA ]).
  unfold codAtIrr.
  eapply eq_term_trans;
    [ | apply eq_ty_subst_id; [ exact HD | exact HiG | exact HElB ] ].
  apply TySubst_cong
    with (G1 := oExtC G rF lF F) (G2 := oExtC G rF lF F)
         (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
         (g2 := oId (oExtC G rF lF F))
         (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
         (A1 := oEl (oExtC G rF lF F) oIrr oL0 B)
         (A2 := oEl (oExtC G rF lF F) oIrr oL0 B);
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; exact HD
    | exact Hsnoc
    | apply eq_term_refl; exact HiG
    | apply eq_term_refl; exact HElB ].
Qed.

(* THE eta STEP.  [t] is a normal form of [e] applied to the fresh
   variable; [lam t] is then a normal form of [e] ITSELF, and nothing but
   "Pi_rel eta" can supply that. *)
Lemma eq_eta_wkn G rF lF lG F B e t
  : wft G sEnv -> wft rF sRelevance -> wft lF sLvl -> wft lG sLvl ->
    wft F (sCode G rF lF) -> wft B (sCode (oExtC G rF lF F) oRel lG) ->
    wft e (sElt G oRel lG (oPiRel G rF lF lG F B)) ->
    eqt (sExp (oExtC G rF lF F) (iEl oRel lG)
           (oEl (oExtC G rF lF F) oRel lG B))
      (appAtRel (oExtC G rF lF F) G rF lF lG F B
         (oWkn G (iEl rF lF) (oEl G rF lF F)) e
         (oHd G (iEl rF lF) (oEl G rF lF F))) t ->
    eqt (sElt G oRel lG (oPiRel G rF lF lG F B)) e (oLamRel G rF lF lG F B t).
Proof.
  intros HG HrF HlF HlG HF HB He Ht.
  (* [appAtRel] at the bare [wkn] and the head variable IS the body of
     "Pi_rel eta"'s left-hand side, so there is nothing to bridge. *)
  eapply eq_term_trans;
    [ apply eq_term_sym; apply eq_Pi_rel_eta;
      [ exact HG | exact HrF | exact HlF | exact HlG | exact HF | exact HB
      | exact He ]
    | ].
  apply LamRel_cong;
    [ apply eq_term_refl; exact HG
    | apply eq_term_refl; exact HrF
    | apply eq_term_refl; exact HlF
    | apply eq_term_refl; exact HlG
    | apply eq_term_refl; exact HF
    | apply eq_term_refl; exact HB
    | exact Ht ].
Qed.

(* ================================================================== *)
(* 6. Reading typing off an application / a substitution               *)
(*                                                                     *)
(* [rty_pi_rel] imposes no typing on the members of [P]; the escape     *)
(* half needs [e] to be well typed, and recovers it from the codomain   *)
(* premise's own equation, exactly as [LogRelCand.codAt_wf_a] recovers   *)
(* the Kripke argument's.                                              *)
(* ================================================================== *)

Lemma wft_ExpSubst_args G G' g i A v t
  : wft (oExpSubst G G' g i A v) t ->
    wft G sEnv /\ wft G' sEnv /\ wft g (sSub G G')
    /\ wft i sInfo /\ wft A (sTy G' i) /\ wft v (sExp G' i A).
Proof.
  unfold oExpSubst; intro H; con_args_inv H; repeat split; assumption.
Qed.

Lemma wft_AppRel_args G rF lF lG F B f a t
  : wft (oAppRel G rF lF lG F B f a) t ->
    wft G sEnv /\ wft rF sRelevance /\ wft lF sLvl /\ wft lG sLvl
    /\ wft F (sCode G rF lF)
    /\ wft B (sCode (oExtC G rF lF F) oRel lG)
    /\ wft f (sElt G oRel lG (oPiRel G rF lF lG F B))
    /\ wft a (sElt G rF lF F).
Proof.
  unfold oAppRel; intro H; con_args_inv H; repeat split; assumption.
Qed.

(* [e] is well typed as soon as [appAtRel ... e ...] is. *)
Lemma appAtRel_wf_e D G rF lF lG F B w e a t
  : wft (appAtRel D G rF lF lG F B w e a) t ->
    wft e (sElt G oRel lG (oPiRel G rF lF lG F B)).
Proof.
  unfold appAtRel; intro H.
  apply wft_AppRel_args in H.
  destruct H as [_ [_ [_ [_ [_ [_ [Hf _]]]]]]].
  unfold wkFunRel in Hf; apply wft_ExpSubst_args in Hf.
  destruct Hf as [_ [_ [_ [_ [_ Hv]]]]]; exact Hv.
Qed.

Lemma wft_AppIrr_args G rF lF F B f a t
  : wft (oAppIrr G rF lF F B f a) t ->
    wft G sEnv /\ wft rF sRelevance /\ wft lF sLvl
    /\ wft F (sCode G rF lF)
    /\ wft B (sCode (oExtC G rF lF F) oIrr oL0)
    /\ wft f (sElt G oIrr oL0 (oPiIrr G rF lF F B))
    /\ wft a (sElt G rF lF F).
Proof.
  unfold oAppIrr; intro H; con_args_inv H; repeat split; assumption.
Qed.

(* [e] is well typed as soon as [appAtIrr ... e ...] is -- the [Pi_irr]
   analogue of [appAtRel_wf_e], used by [Pi_irr]'s ESCAPE half. *)
Lemma appAtIrr_wf_e D G rF lF F B w e a t
  : wft (appAtIrr D G rF lF F B w e a) t ->
    wft e (sElt G oIrr oL0 (oPiIrr G rF lF F B)).
Proof.
  unfold appAtIrr; intro H.
  apply wft_AppIrr_args in H.
  destruct H as [_ [_ [_ [_ [_ [Hf _]]]]]].
  unfold wkFunIrr in Hf; apply wft_ExpSubst_args in Hf.
  destruct Hf as [_ [_ [_ [_ [_ Hv]]]]]; exact Hv.
Qed.

(* ================================================================== *)
(* 7. The head variable of the one-step weakening is reducible         *)
(* ================================================================== *)

Lemma esc_hd_var G rF lF F F1
  : EnvOk G -> NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) rF lF F1 ->
    eqt (sCode (oExtC G rF lF F) rF lF)
      (wkCode (oExtC G rF lF F) G (oWkn G (iEl rF lF) (oEl G rF lF F))
         rF lF F) F1 ->
    VarT (oExtC G rF lF F) (iEl rF lF) (oEl (oExtC G rF lF F) rF lF F1)
         (oHd G (iEl rF lF) (oEl G rF lF F)).
Proof.
  intros HG HF HF1 HeqF1.
  assert (RelNf rF) as HrF by (eapply NfCode_RelNf; exact HF).
  assert (LvlNf lF) as HlF by (eapply NfCode_LvlNf; exact HF).
  assert (TyOk G (iEl rF lF) (oEl G rF lF F)) as HTA by (apply tyok_El; exact HF).
  assert (EnvOk (oExtC G rF lF F)) as HD
      by (unfold oExtC; apply envok_ext; assumption).
  unfold oExtC; apply vart_hd;
    [ exact HG | exact HTA | apply tyok_El; exact HF1 | ].
  eapply eq_term_trans.
  - apply eq_El_subst;
      [ wfx | wfx | apply Wk_wf; apply wk_wkn; [ exact HG | exact HTA ]
      | wfx | wfx | wfx ].
  - apply El_cong; [ er | er | er | exact HeqF1 ].
Qed.

(* ================================================================== *)
(* A. ESCAPE AND REFLECT                                               *)
(*                                                                     *)
(* One induction, on LogRelBasics.v's hand-written [RTy_strong_ind]      *)
(* (Rocq's generated [RTy_ind] gives no induction hypothesis in either  *)
(* Pi case).  The two halves have to run together: reflect at a Pi      *)
(* needs escape at the DOMAIN (to normalize the argument of the         *)
(* neutral application), and escape at a Pi needs reflect at the        *)
(* domain (to know the fresh variable is reducible) and escape at the   *)
(* codomain.                                                           *)
(* ================================================================== *)

Theorem RTy_escape_reflect : forall G i A P, RTy G i A P ->
  (forall e, P e -> HasNf G i A e) /\ (forall e, HasNe G i A e -> P e).
Proof.
  apply (@RTy_strong_ind
           (fun G i A P => (forall e, P e -> HasNf G i A e)
                        /\ (forall e, HasNe G i A e -> P e))).

  (* ---- U : normal codes ---- *)
  - intros G r l P HG Hr Hl Hiff; split.
    + intros e He; destruct (proj1 (Hiff e) He) as [c0 [Hc0 Heq]].
      exists c0; split; [ apply nfet_code; exact Hc0 | exact Heq ].
    + intros e [n [Hn Heq]]; apply Hiff.
      exists n; split; [ | exact Heq ].
      apply nfcode_var; eapply NeET_iCode; [ exact Hn | reflexivity ].

  (* ---- Nat ---- *)
  - intros G P HG Hiff; split.
    + intros e He; apply Hiff; exact He.
    + intros e He; apply Hiff; apply HasNe_HasNf_nat; exact He.

  (* ---- Empty ---- *)
  - intros G P HG Hiff; split.
    + intros e He; apply HasNe_HasNf_empty; apply Hiff; exact He.
    + intros e He; apply Hiff; exact He.

  (* ---- a type named by a variable ---- *)
  - intros G r l c P Hx Hiff; split.
    + intros e He; eapply HasNe_HasNf_var; [ exact Hx | apply Hiff; exact He ].
    + intros e He; apply Hiff; exact He.

  (* ---- Pi_rel ---- *)
  - intros G rF lF lG F B P Pd Pc HrF HlF HlG HF HB Hd Hc Hiff.
    assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
    assert (TyOk G (iEl rF lF) (oEl G rF lF F)) as HTA
        by (apply tyok_El; exact HF).
    assert (EnvOk (oExtC G rF lF F)) as HDok
        by (unfold oExtC; apply envok_ext; [ exact HGok | exact HTA ]).
    assert (Wk (oExtC G rF lF F) G (oWkn G (iEl rF lF) (oEl G rF lF F))) as HW1
        by (unfold oExtC; apply wk_wkn; [ exact HGok | exact HTA ]).
    split.

    + (* ESCAPE.  The fresh variable is reducible by the induction
         hypothesis's REFLECT at the domain; the body then has a normal
         form by its ESCAPE at the codomain; and "Pi_rel eta" turns that
         into a normal form of [e] itself. *)
      intros e He.
      destruct (Hd _ _ HW1 HDok) as [F1 (HF1 & HeqF1 & HR1 & Hesc1 & Href1)].
      assert (VarT (oExtC G rF lF F) (iEl rF lF)
                (oEl (oExtC G rF lF F) rF lF F1)
                (oHd G (iEl rF lF) (oEl G rF lF F))) as Hvar
          by (apply esc_hd_var; assumption).
      assert (Pd (oExtC G rF lF F) (oWkn G (iEl rF lF) (oEl G rF lF F))
                (oHd G (iEl rF lF) (oEl G rF lF F))) as Hhd.
      { apply Href1.
        exists (oHd G (iEl rF lF) (oEl G rF lF F)); split;
          [ apply neet_var; exact Hvar
          | apply eq_term_refl; apply VarT_wf; exact Hvar ]. }
      destruct (Hc _ _ _ HW1 HDok Hhd)
        as [C (HTC & HeqC & HRC & HescC & HrefC)].
      assert (C = oEl (oExtC G rF lF F) oRel lG B) as HCeq.
      { eapply TyOk_inj;
          [ exact HTC | apply tyok_El; exact HB
          | eapply eq_term_trans;
            [ apply eq_term_sym; exact HeqC
            | apply eq_codAt_wkn; wfx ] ]. }
      subst C.
      destruct (HescC _ ((proj1 (Hiff e) He) _ _ _ HW1 HDok Hhd))
        as [t (Ht1 & Ht2)].
      exists (oLamRel G rF lF lG F B t); split.
      * apply nfet_lam_rel; assumption.
      * apply eq_eta_wkn;
          [ wfx | wfx | wfx | wfx | wfx | wfx
          | eapply appAtRel_wf_e; eapply eqt_wf_l; exact Ht2
          | exact Ht2 ].

    + (* REFLECT *)
      intros e HNe.
      apply Hiff; intros D w a HW HD Ha.
      destruct (Hd D w HW HD) as [F1 (HF1 & HeqF1 & HR1 & Hesc1 & Href1)].
      destruct (Hc D w a HW HD Ha) as [C (HTC & HeqC & HRC & HescC & HrefC)].
      apply HrefC.
      assert (wft a (sElt D rF lF (wkCode D G w rF lF F))) as Haw.
      { eapply codAt_wf_a with (rG := oRel) (lG := lG) (B := B);
          [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HW | wfx
          | apply (eqt_wf_l HeqC) ]. }
      eapply pi_rel_reflect_app;
        [ exact HW | exact HD | exact HF | exact HB | exact HNe
        | exact HF1 | exact HeqF1 | apply Hesc1; exact Ha | exact Haw
        | exact HTC | exact HeqC ].

  (* ---- Pi_irr ---- *)
  - intros G rF lF F B P Pd Pc HrF HlF HF HB Hd Hc Hiff.
    split.

    + (* ESCAPE.  Same shape as the [Pi_rel] ESCAPE half above, with
         [eq_proof_irr] standing in for [eq_eta_wkn]: the fresh variable
         is reducible by REFLECT at the domain; the body then has a
         normal form by ESCAPE at the codomain, read off [He : P e] at
         the one-step weakening (now the plain Kripke property, via
         [proj1 (Hiff e) He]); and "proof irrelevance" identifies the
         resulting lambda with [e] itself -- this is the ONLY use of
         that rule in the development, and it replaces the missing
         "Pi_irr eta". *)
      intros e He.
      assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
      assert (TyOk G (iEl rF lF) (oEl G rF lF F)) as HTA
          by (apply tyok_El; exact HF).
      assert (EnvOk (oExtC G rF lF F)) as HDok
          by (unfold oExtC; apply envok_ext; [ exact HGok | exact HTA ]).
      assert (Wk (oExtC G rF lF F) G (oWkn G (iEl rF lF) (oEl G rF lF F)))
        as HW1 by (unfold oExtC; apply wk_wkn; [ exact HGok | exact HTA ]).
      destruct (Hd _ _ HW1 HDok) as [F1 (HF1 & HeqF1 & HR1 & Hesc1 & Href1)].
      assert (VarT (oExtC G rF lF F) (iEl rF lF)
                (oEl (oExtC G rF lF F) rF lF F1)
                (oHd G (iEl rF lF) (oEl G rF lF F))) as Hvar
          by (apply esc_hd_var; assumption).
      assert (Pd (oExtC G rF lF F) (oWkn G (iEl rF lF) (oEl G rF lF F))
                (oHd G (iEl rF lF) (oEl G rF lF F))) as Hhd.
      { apply Href1.
        exists (oHd G (iEl rF lF) (oEl G rF lF F)); split;
          [ apply neet_var; exact Hvar
          | apply eq_term_refl; apply VarT_wf; exact Hvar ]. }
      destruct (Hc _ _ _ HW1 HDok Hhd)
        as [C (HTC & HeqC & HRC & HescC & HrefC)].
      assert (C = oEl (oExtC G rF lF F) oIrr oL0 B) as HCeq.
      { eapply TyOk_inj;
          [ exact HTC | apply tyok_El; exact HB
          | eapply eq_term_trans;
            [ apply eq_term_sym; exact HeqC
            | apply eq_codAtIrr_wkn; wfx ] ]. }
      subst C.
      destruct (HescC _ ((proj1 (Hiff e) He) _ _ _ HW1 HDok Hhd))
        as [t (Ht1 & Ht2)].
      assert (NfET G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B))
                (oLamIrr G rF lF F B t)) as Hn
          by (apply nfet_lam_irr; assumption).
      assert (NfCode G oIrr oL0 (oPiIrr G rF lF F B)) as HPiC
          by (apply nfcode_pi_irr; assumption).
      assert (wft e (sElt G oIrr oL0 (oPiIrr G rF lF F B))) as He_wf
          by (eapply appAtIrr_wf_e; eapply eqt_wf_l; exact Ht2).
      assert (wft (oLamIrr G rF lF F B t)
                (sElt G oIrr oL0 (oPiIrr G rF lF F B))) as Hlam_wf
          by (eapply NfET_wf; exact Hn).
      exists (oLamIrr G rF lF F B t); split; [ exact Hn | ].
      apply eq_proof_irr; wfx.

    + (* REFLECT.  Plain Kripke body, mirroring the [Pi_rel] REFLECT
         half: no [HasNf] to construct any more, so this is exactly
         [Hiff] applied to the standard reflect-at-codomain argument. *)
      intros e HNe.
      apply Hiff; intros D w a HW HD Ha.
      destruct (Hd D w HW HD) as [F1 (HF1 & HeqF1 & HR1 & Hesc1 & Href1)].
      destruct (Hc D w a HW HD Ha) as [C (HTC & HeqC & HRC & HescC & HrefC)].
      apply HrefC.
      assert (wft a (sElt D rF lF (wkCode D G w rF lF F))) as Haw.
      { eapply codAt_wf_a with (rG := oIrr) (lG := oL0) (B := B);
          [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HW | wfx
          | apply (eqt_wf_l HeqC) ]. }
      eapply pi_irr_reflect_app;
        [ exact HW | exact HD | exact HF | exact HB | exact HNe
        | exact HF1 | exact HeqF1 | apply Hesc1; exact Ha | exact Haw
        | exact HTC | exact HeqC ].
Qed.

Theorem RTy_escape G i A P : RTy G i A P -> forall e, P e -> HasNf G i A e.
Proof. intro H; exact (proj1 (RTy_escape_reflect H)). Qed.

Theorem RTy_reflect G i A P : RTy G i A P -> forall e, HasNe G i A e -> P e.
Proof. intro H; exact (proj2 (RTy_escape_reflect H)). Qed.

(* ================================================================== *)
(* B0. Two sigma-identities about composing weakenings under a binder   *)
(* ================================================================== *)

(* [<w2,a> ; lift(w)  =  <w2;w, a>].  ([NfWk.eq_inst_lift] is the
   special case [w2 = id].) *)
Lemma eq_snoc_liftW D2 D G w2 w i A A' a
  : wft D2 sEnv -> wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) ->
    wft w (sSub D G) -> wft w2 (sSub D2 D) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    wft a (sExp D2 i (oTySubst D2 D w2 i A')) ->
    eqt (sSub D2 (oExt G i A))
      (oCmp D2 (oExt D i A') (oExt G i A) (oSnoc D2 D i A' w2 a)
         (oLiftW D G w i A A'))
      (oSnoc D2 G i A (oCmp D2 D G w2 w) a).
Proof.
  intros HD2 HD HG Hi HA HA' Hw Hw2 HeqT Ha.
  assert (wft (oExt D i A') sEnv) as HED by (apply wf_Ext; assumption).
  assert (wft (oExt G i A) sEnv) as HEG by (apply wf_Ext; assumption).
  assert (wft (oWkn D i A') (sSub (oExt D i A') D)) as HWD
      by (apply wf_Wkn; assumption).
  assert (wft (oCmp (oExt D i A') D G (oWkn D i A') w)
            (sSub (oExt D i A') G)) as Hcw by (apply wf_Cmp; assumption).
  assert (wft (oHd D i A')
            (sExp (oExt D i A') i
               (oTySubst (oExt D i A') G
                  (oCmp (oExt D i A') D G (oWkn D i A') w) i A))) as Hhd
      by (apply wf_liftW_hd; assumption).
  assert (wft (oSnoc D2 D i A' w2 a) (sSub D2 (oExt D i A'))) as Hsn
      by (apply wf_Snoc; assumption).
  assert (wft (oCmp D2 D G w2 w) (sSub D2 G)) as Hcw2
      by (apply wf_Cmp; assumption).
  (* the substitution component *)
  assert (eqt (sSub D2 G)
            (oCmp D2 (oExt D i A') G (oSnoc D2 D i A' w2 a)
               (oCmp (oExt D i A') D G (oWkn D i A') w))
            (oCmp D2 D G w2 w)) as Hsub.
  { eapply eq_term_trans;
      [ apply eq_cmp_assoc with (G2 := oExt D i A') (G3 := D);
        [ exact HD2 | exact HED | exact HD | exact HG | exact Hsn
        | exact HWD | exact Hw ] | ].
    apply Cmp_cong
      with (X1 := D2) (Y1 := D2) (X2 := D) (Y2 := D) (X3 := G) (Y3 := G)
           (f1 := oCmp D2 (oExt D i A') D (oSnoc D2 D i A' w2 a)
                    (oWkn D i A')) (f2 := w2) (g1 := w) (g2 := w);
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HG
      | apply eq_wkn_snoc;
        [ exact HD2 | exact HD | exact Hw2 | exact Hi | exact HA' | exact Ha ]
      | apply eq_term_refl; exact Hw ]. }
  (* the type of the value component *)
  assert (eqt (sTy D2 i) (oTySubst D2 D w2 i A')
            (oTySubst D2 G (oCmp D2 D G w2 w) i A)) as Hty.
  { eapply eq_term_trans;
      [ apply TySubst_cong
          with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D)
               (g1 := w2) (g2 := w2) (i1 := i) (i2 := i)
               (A1 := A') (A2 := oTySubst D G w i A);
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; exact HD
        | apply eq_term_refl; exact Hw2
        | apply eq_term_refl; exact Hi
        | apply eq_term_sym; exact HeqT ]
      | apply eq_ty_subst_cmp;
        [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw | exact Hi
        | exact HA ] ]. }
  unfold oLiftW.
  eapply eq_term_trans.
  { apply eq_cmp_snoc with (G1 := D2) (G2 := oExt D i A') (G3 := G)
      (f := oSnoc D2 D i A' w2 a)
      (g := oCmp (oExt D i A') D G (oWkn D i A') w) (i := i) (A := A)
      (v := oHd D i A');
      [ exact HD2 | exact HED | exact HG | exact Hsn | exact Hcw | exact Hi
      | exact HA | exact Hhd ]. }
  apply Snoc_cong;
    [ apply eq_term_refl; exact HD2
    | apply eq_term_refl; exact HG
    | apply eq_term_refl; exact Hi
    | apply eq_term_refl; exact HA
    | exact Hsub
    | ].
  eapply eq_term_conv;
    [ | apply eq_sort_exp_ty; exact Hty ].
  eapply eq_term_trans;
    [ | apply eq_snoc_hd;
        [ exact HD2 | exact HD | exact Hw2 | exact Hi | exact HA'
        | exact Ha ] ].
  eapply eq_term_conv.
  - apply ExpSubst_cong
      with (G1 := D2) (G2 := D2)
           (G1' := oExt D i A') (G2' := oExt D i A')
           (g1 := oSnoc D2 D i A' w2 a) (g2 := oSnoc D2 D i A' w2 a)
           (i1 := i) (i2 := i)
           (A1 := oTySubst (oExt D i A') G
                    (oCmp (oExt D i A') D G (oWkn D i A') w) i A)
           (A2 := oTySubst (oExt D i A') D (oWkn D i A') i A')
           (v1 := oHd D i A') (v2 := oHd D i A');
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HED
      | apply eq_term_refl; exact Hsn
      | apply eq_term_refl; exact Hi
      | apply eq_term_sym; apply eq_wk_lift_ty;
        [ exact HD | exact HG | exact Hi | exact HA | exact HA' | exact Hw
        | exact HeqT ]
      | apply eq_term_refl; apply wf_Hd; assumption ].
  - apply eq_sort_exp_ty.
    eapply eq_term_trans;
      [ apply eq_ty_subst_cmp with (G2 := oExt D i A');
        [ exact HD2 | exact HED | exact HD | exact Hsn | exact HWD | exact Hi
        | exact HA' ] | ].
    apply TySubst_cong
      with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D)
           (g1 := oCmp D2 (oExt D i A') D (oSnoc D2 D i A' w2 a)
                    (oWkn D i A'))
           (g2 := w2) (i1 := i) (i2 := i) (A1 := A') (A2 := A');
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HD
      | apply eq_wkn_snoc;
        [ exact HD2 | exact HD | exact Hw2 | exact Hi | exact HA' | exact Ha ]
      | apply eq_term_refl; exact Hi
      | apply eq_term_refl; exact HA' ].
Qed.

(* [lift(w2) ; lift(w) = lift(w2;w)] -- the special case of the above with
   the lifted weakening in the value slot. *)
Lemma eq_liftW_cmp D2 D G w2 w w'' i A A' A2
  : wft D2 sEnv -> wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft A2 (sTy D2 i) ->
    wft w (sSub D G) -> wft w2 (sSub D2 D) -> wft w'' (sSub D2 G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sTy D2 i) (oTySubst D2 D w2 i A') A2 ->
    eqt (sSub D2 G) (oCmp D2 D G w2 w) w'' ->
    eqt (sSub (oExt D2 i A2) (oExt G i A))
      (oCmp (oExt D2 i A2) (oExt D i A') (oExt G i A)
         (oLiftW D2 D w2 i A' A2) (oLiftW D G w i A A'))
      (oLiftW D2 G w'' i A A2).
Proof.
  intros HD2 HD HG Hi HA HA' HA2 Hw Hw2 Hw'' HeqT HeqT2 Hcmp.
  assert (wft (oExt D2 i A2) sEnv) as HE2 by (apply wf_Ext; assumption).
  assert (wft (oWkn D2 i A2) (sSub (oExt D2 i A2) D2)) as HW2
      by (apply wf_Wkn; assumption).
  assert (wft (oCmp (oExt D2 i A2) D2 D (oWkn D2 i A2) w2)
            (sSub (oExt D2 i A2) D)) as Hc2 by (apply wf_Cmp; assumption).
  assert (eqt (sTy D2 i) (oTySubst D2 G w'' i A) A2) as HeqT''.
  { eapply eq_term_trans; [ | exact HeqT2 ].
    eapply eq_term_trans.
    - apply TySubst_cong
        with (G1 := D2) (G2 := D2) (G1' := G) (G2' := G)
             (g1 := w'') (g2 := oCmp D2 D G w2 w) (i1 := i) (i2 := i)
             (A1 := A) (A2 := A);
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; exact HG
        | apply eq_term_sym; exact Hcmp
        | apply eq_term_refl; exact Hi
        | apply eq_term_refl; exact HA ].
    - eapply eq_term_trans;
        [ apply eq_term_sym; apply eq_ty_subst_cmp;
          [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw | exact Hi
          | exact HA ] | ].
      apply TySubst_cong
        with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D)
             (g1 := w2) (g2 := w2) (i1 := i) (i2 := i)
             (A1 := oTySubst D G w i A) (A2 := A');
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; exact HD
        | apply eq_term_refl; exact Hw2
        | apply eq_term_refl; exact Hi
        | exact HeqT ]. }
  eapply eq_term_trans.
  { unfold oLiftW at 1.
    apply eq_snoc_liftW
      with (D2 := oExt D2 i A2) (D := D) (G := G)
           (w2 := oCmp (oExt D2 i A2) D2 D (oWkn D2 i A2) w2)
           (w := w) (i := i) (A := A) (A' := A') (a := oHd D2 i A2);
      [ exact HE2 | exact HD | exact HG | exact Hi | exact HA | exact HA'
      | exact Hw | exact Hc2 | exact HeqT
      | apply wf_liftW_hd; assumption ]. }
  unfold oLiftW.
  apply Snoc_cong;
    [ apply eq_term_refl; exact HE2
    | apply eq_term_refl; exact HG
    | apply eq_term_refl; exact Hi
    | apply eq_term_refl; exact HA
    | | ].
  - eapply eq_term_trans;
      [ apply eq_term_sym;
        apply eq_cmp_assoc with (G2 := D2) (G3 := D);
        [ exact HE2 | exact HD2 | exact HD | exact HG | exact HW2 | exact Hw2
        | exact Hw ] | ].
    apply Cmp_cong
      with (X1 := oExt D2 i A2) (Y1 := oExt D2 i A2) (X2 := D2) (Y2 := D2)
           (X3 := G) (Y3 := G) (f1 := oWkn D2 i A2) (f2 := oWkn D2 i A2)
           (g1 := oCmp D2 D G w2 w) (g2 := w'');
      [ apply eq_term_refl; exact HE2
      | apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; exact HW2
      | exact Hcmp ].
  - apply eq_term_refl; apply wf_liftW_hd; assumption.
Qed.

(* A [sub] sort congruence (the [ty]/[exp] analogues are in
   src/Pyrosome/Gluing/Dtt/NfTyping.v). *)
Lemma eq_sort_sub_cong G1 G2 G1' G2'
  : eqt sEnv G1 G2 -> eqt sEnv G1' G2' ->
    eq_sort ott_dtt [] (sSub G1 G1') (sSub G2 G2').
Proof. intros; scong_step "sub" [G1'; G1] [G2'; G2]. Qed.

(* [wk_codcode] again, keeping BOTH spellings of the lifted weakening. *)
Lemma wk_codcodeW D G w rF lF rG lG F B F'
  : Wk D G w -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (wkCode D G w rF lF F) F' ->
    NfCode (oExtC G rF lF F) rG lG B ->
    exists B', NfCode (oExtC D rF lF F') rG lG B'
            /\ eqt (sCode (oExtC D rF lF F') rG lG)
                 (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
                    (oLiftW D G w (iEl rF lF) (oEl G rF lF F)
                       (oEl D rF lF F')) (iCode lG)
                    (oU (oExtC G rF lF F) rG lG) B) B'
            /\ eqt (sCode (oExtC D rF lF F') rG lG)
                 (oExpSubst (oExtC D rF lF (wkCode D G w rF lF F))
                    (oExtC G rF lF F) (oLift D G w rF lF F) (iCode lG)
                    (oU (oExtC G rF lF F) rG lG) B) B'.
Proof.
  intros HW HD HF HF' HeqF HB.
  destruct (CSub_liftC (csub_wk HW) HD HF HF' HeqF) as [HC2 [HD2 HeqEl]].
  destruct (NfCode_csubst HB HC2 HD2) as [B' [HB' HeqB']].
  assert (EnvOk G) as HGok by (eapply Wk_cod; exact HW).
  exists B'; split; [ exact HB' | split; [ exact HeqB' | ] ].
  eapply eq_term_trans; [ | exact HeqB' ].
  eapply eqt_Usub_c
    with (G' := oExtC G rF lF F)
         (g := oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (r := rG) (l := lG);
    [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
  apply eq_lift_shift;
    [ exact HW | exact HD | exact HF | exact HF' | exact HeqF
    | wfx | wfx | wfx ].
Qed.

(* ================================================================== *)
(* B1. Two-step weakening of the Pi data                               *)
(*                                                                     *)
(* [w : D -> G] and [w2 : D2 -> D] compose to [w'' : D2 -> G]; [F']/[B'] *)
(* are the normal domain/codomain codes of the [w]-weakened Pi.  This   *)
(* section shows that the Kripke data of the Pi clause at [(D2,w2)]     *)
(* over [D] agrees with the data at [(D2,w'')] over [G].                *)
(* ================================================================== *)

Section WkStepC.

  Context (D2 D G rF lF rG lG F B w w2 w'' F' B' : term).

  Context
    (HG : wft G sEnv) (HD : wft D sEnv) (HD2 : wft D2 sEnv)
    (HrF : wft rF sRelevance) (HlF : wft lF sLvl)
    (HrG : wft rG sRelevance) (HlG : wft lG sLvl)
    (HF : wft F (sCode G rF lF))
    (HB : wft B (sCode (oExtC G rF lF F) rG lG))
    (Hw : wft w (sSub D G)) (Hw2 : wft w2 (sSub D2 D))
    (Hw'' : wft w'' (sSub D2 G))
    (Hcmp : eqt (sSub D2 G) (oCmp D2 D G w2 w) w'')
    (HF'w : wft F' (sCode D rF lF))
    (HeqF : eqt (sCode D rF lF) (wkCode D G w rF lF F) F')
    (HB'w : wft B' (sCode (oExtC D rF lF F') rG lG))
    (HeqB' : eqt (sCode (oExtC D rF lF F') rG lG)
               (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
                  (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
                  (iCode lG) (oU (oExtC G rF lF F) rG lG) B) B').

  Local Notation i := (iEl rF lF).
  Local Notation A := (oEl G rF lF F).
  Local Notation A' := (oEl D rF lF F').
  Local Notation GF := (oExtC G rF lF F).
  Local Notation DF := (oExtC D rF lF F').
  Local Notation lw :=
    (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')).

  (* ---- routine well-formedness ---- *)

  Lemma wsc_iF : wft (iEl rF lF) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]. Qed.

  Lemma wsc_iG : wft (iEl rG lG) sInfo.
  Proof.
    unfold iEl; apply wf_Info; [ exact HrG | apply wf_Iota; exact HlG ].
  Qed.

  Lemma wsc_cF : wft (iCode lF) sInfo.
  Proof.
    unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlF ].
  Qed.

  Lemma wsc_cG : wft (iCode lG) sInfo.
  Proof.
    unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlG ].
  Qed.

  Lemma wsc_A : wft A (sTy G (iEl rF lF)).
  Proof. apply wf_El; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  Lemma wsc_A' : wft A' (sTy D (iEl rF lF)).
  Proof. apply wf_El; [ exact HD | exact HrF | exact HlF | exact HF'w ]. Qed.

  Lemma wsc_GF : wft GF sEnv.
  Proof. apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  Lemma wsc_DF : wft DF sEnv.
  Proof. apply wf_ExtC; [ exact HD | exact HrF | exact HlF | exact HF'w ]. Qed.

  Lemma wsc_ElW : eqt (sTy D (iEl rF lF)) (oTySubst D G w (iEl rF lF) A) A'.
  Proof.
    eapply eq_term_trans;
      [ apply eq_El_subst;
        [ exact HD | exact HG | exact Hw | exact HrF | exact HlF | exact HF ]
      | apply El_cong;
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HrF
        | apply eq_term_refl; exact HlF
        | exact HeqF ] ].
  Qed.

  Lemma wsc_lw : wft lw (sSub DF GF).
  Proof.
    unfold oExtC; apply wf_liftW;
      [ exact HD | exact HG | apply wsc_iF | apply wsc_A | apply wsc_A'
      | exact Hw | apply wsc_ElW ].
  Qed.

  Lemma wsc_UG : wft (oU G rF lF) (sTy G (iCode lF)).
  Proof. apply wf_U; [ exact HG | exact HrF | exact HlF ]. Qed.

  Lemma wsc_UD : wft (oU D rF lF) (sTy D (iCode lF)).
  Proof. apply wf_U; [ exact HD | exact HrF | exact HlF ]. Qed.

  (* ---- the domain code, composed ---- *)

  Lemma wsc_S1F
    : eqt (sTy D2 (iCode lF))
        (oTySubst D2 D w2 (iCode lF)
           (oTySubst D G w (iCode lF) (oU G rF lF)))
        (oU D2 rF lF).
  Proof.
    eapply eq_term_trans.
    { apply TySubst_cong
        with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D) (g1 := w2) (g2 := w2)
             (i1 := iCode lF) (i2 := iCode lF)
             (A1 := oTySubst D G w (iCode lF) (oU G rF lF))
             (A2 := oU D rF lF);
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; exact HD
        | apply eq_term_refl; exact Hw2
        | apply eq_term_refl; apply wsc_cF
        | apply eq_U_subst;
          [ exact HD | exact HG | exact Hw | exact HrF | exact HlF ] ]. }
    apply eq_U_subst;
      [ exact HD2 | exact HD | exact Hw2 | exact HrF | exact HlF ].
  Qed.

  Theorem wsc_F1
    : eqt (sCode D2 rF lF)
        (wkCode D2 D w2 rF lF F') (wkCode D2 G w'' rF lF F).
  Proof.
    unfold wkCode.
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ | apply eq_sort_exp_ty; apply wsc_S1F ].
      eapply eq_term_trans.
      - apply ExpSubst_cong
          with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D)
               (g1 := w2) (g2 := w2) (i1 := iCode lF) (i2 := iCode lF)
               (A1 := oU D rF lF)
               (A2 := oTySubst D G w (iCode lF) (oU G rF lF))
               (v1 := F')
               (v2 := oExpSubst D G w (iCode lF) (oU G rF lF) F);
          [ apply eq_term_refl; exact HD2
          | apply eq_term_refl; exact HD
          | apply eq_term_refl; exact Hw2
          | apply eq_term_refl; apply wsc_cF
          | apply eq_term_sym; apply eq_U_subst;
            [ exact HD | exact HG | exact Hw | exact HrF | exact HlF ]
          | eapply eq_term_conv;
            [ apply eq_term_sym; exact HeqF
            | apply eq_sort_sym; apply eq_sort_Usub;
              [ exact HD | exact HG | exact Hw | exact HrF | exact HlF ] ] ].
      - apply eq_exp_subst_cmp with (G2 := D);
          [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw
          | apply wsc_cF | apply wsc_UG | exact HF ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply eq_U_subst;
            [ exact HD2 | exact HG | exact Hw'' | exact HrF | exact HlF ] ].
    apply ExpSubst_cong
      with (G1 := D2) (G2 := D2) (G1' := G) (G2' := G)
           (g1 := oCmp D2 D G w2 w) (g2 := w'')
           (i1 := iCode lF) (i2 := iCode lF)
           (A1 := oU G rF lF) (A2 := oU G rF lF) (v1 := F) (v2 := F);
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HG
      | exact Hcmp
      | apply eq_term_refl; apply wsc_cF
      | apply eq_term_refl; apply wsc_UG
      | apply eq_term_refl; exact HF ].
  Qed.

  Lemma wsc_Fw2 : wft (wkCode D2 D w2 rF lF F') (sCode D2 rF lF).
  Proof.
    apply ac_Fw;
      [ exact HD2 | exact HD | exact HrF | exact HlF | exact Hw2 | exact HF'w ].
  Qed.

  Lemma wsc_Fw'' : wft (wkCode D2 G w'' rF lF F) (sCode D2 rF lF).
  Proof.
    apply ac_Fw;
      [ exact HD2 | exact HG | exact HrF | exact HlF | exact Hw'' | exact HF ].
  Qed.

  Lemma wsc_El1
    : eqt (sTy D2 (iEl rF lF))
        (oEl D2 rF lF (wkCode D2 D w2 rF lF F'))
        (oEl D2 rF lF (wkCode D2 G w'' rF lF F)).
  Proof.
    apply El_cong;
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply wsc_F1 ].
  Qed.

  Lemma wsc_E1 : wft (oExtC D2 rF lF (wkCode D2 D w2 rF lF F')) sEnv.
  Proof.
    apply wf_ExtC; [ exact HD2 | exact HrF | exact HlF | apply wsc_Fw2 ].
  Qed.

  Lemma wsc_E2 : wft (oExtC D2 rF lF (wkCode D2 G w'' rF lF F)) sEnv.
  Proof.
    apply wf_ExtC; [ exact HD2 | exact HrF | exact HlF | apply wsc_Fw'' ].
  Qed.

  Lemma wsc_Eeq
    : eqt sEnv (oExtC D2 rF lF (wkCode D2 D w2 rF lF F'))
               (oExtC D2 rF lF (wkCode D2 G w'' rF lF F)).
  Proof.
    unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; apply wsc_iF
      | apply wsc_El1 ].
  Qed.

  (* the type of the fresh variable of the composed weakening *)
  Lemma wsc_Aty
    : eqt (sTy D2 (iEl rF lF)) (oTySubst D2 D w2 (iEl rF lF) A')
        (oTySubst D2 G w'' (iEl rF lF) A).
  Proof.
    eapply eq_term_trans.
    { apply TySubst_cong
        with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D) (g1 := w2) (g2 := w2)
             (i1 := iEl rF lF) (i2 := iEl rF lF)
             (A1 := A') (A2 := oTySubst D G w (iEl rF lF) A);
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; exact HD
        | apply eq_term_refl; exact Hw2
        | apply eq_term_refl; apply wsc_iF
        | apply eq_term_sym; apply wsc_ElW ]. }
    eapply eq_term_trans.
    { apply eq_ty_subst_cmp;
        [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw
        | apply wsc_iF | apply wsc_A ]. }
    apply TySubst_cong
      with (G1 := D2) (G2 := D2) (G1' := G) (G2' := G)
           (g1 := oCmp D2 D G w2 w) (g2 := w'')
           (i1 := iEl rF lF) (i2 := iEl rF lF) (A1 := A) (A2 := A);
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HG
      | exact Hcmp
      | apply eq_term_refl; apply wsc_iF
      | apply eq_term_refl; apply wsc_A ].
  Qed.

  (* ---- the codomain instance ---- *)

  Lemma wsc_ElB
    : eqt (sTy DF (iEl rG lG))
        (oTySubst DF GF lw (iEl rG lG) (oEl GF rG lG B))
        (oEl DF rG lG B').
  Proof.
    eapply eq_term_trans.
    { apply eq_El_subst;
        [ apply wsc_DF | apply wsc_GF | apply wsc_lw | exact HrG | exact HlG
        | exact HB ]. }
    apply El_cong;
      [ apply eq_term_refl; apply wsc_DF
      | apply eq_term_refl; exact HrG
      | apply eq_term_refl; exact HlG
      | exact HeqB' ].
  Qed.

  Lemma wsc_cod a
    : wft a (sExp D2 (iEl rF lF) (oTySubst D2 D w2 (iEl rF lF) A')) ->
      eqt (sTy D2 (iEl rG lG))
        (oTySubst D2 (oExtC D rF lF F') (instAt D2 D rF lF F' w2 a)
           (iEl rG lG) (oEl (oExtC D rF lF F') rG lG B'))
        (oTySubst D2 (oExtC G rF lF F) (instAt D2 G rF lF F w'' a)
           (iEl rG lG) (oEl (oExtC G rF lF F) rG lG B)).
  Proof.
    intro Ha.
    assert (wft a (sExp D2 (iEl rF lF) (oTySubst D2 G w'' (iEl rF lF) A)))
      as Ha''.
    { eapply wf_term_conv; [ exact Ha | ].
      apply eq_sort_exp_ty; apply wsc_Aty. }
    assert (wft (instAt D2 D rF lF F' w2 a) (sSub D2 DF)) as Hs.
    { unfold instAt, oExtC; apply wf_Snoc;
        [ exact HD2 | exact HD | apply wsc_iF | apply wsc_A' | exact Hw2
        | exact Ha ]. }
    eapply eq_term_trans.
    { apply TySubst_cong
        with (G1 := D2) (G2 := D2) (G1' := DF) (G2' := DF)
             (g1 := instAt D2 D rF lF F' w2 a)
             (g2 := instAt D2 D rF lF F' w2 a)
             (i1 := iEl rG lG) (i2 := iEl rG lG)
             (A1 := oEl DF rG lG B')
             (A2 := oTySubst DF GF lw (iEl rG lG) (oEl GF rG lG B));
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; apply wsc_DF
        | apply eq_term_refl; exact Hs
        | apply eq_term_refl; apply wsc_iG
        | apply eq_term_sym; apply wsc_ElB ]. }
    eapply eq_term_trans.
    { apply eq_ty_subst_cmp with (G2 := DF);
        [ exact HD2 | apply wsc_DF | apply wsc_GF | exact Hs | apply wsc_lw
        | apply wsc_iG
        | apply wf_El;
          [ apply wsc_GF | exact HrG | exact HlG | exact HB ] ]. }
    apply TySubst_cong
      with (G1 := D2) (G2 := D2) (G1' := GF) (G2' := GF)
           (g1 := oCmp D2 DF GF (instAt D2 D rF lF F' w2 a) lw)
           (g2 := instAt D2 G rF lF F w'' a)
           (i1 := iEl rG lG) (i2 := iEl rG lG)
           (A1 := oEl GF rG lG B) (A2 := oEl GF rG lG B);
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; apply wsc_GF
      | | apply eq_term_refl; apply wsc_iG
      | apply eq_term_refl; apply wf_El;
        [ apply wsc_GF | exact HrG | exact HlG | exact HB ] ].
    unfold instAt, oExtC.
    eapply eq_term_trans.
    { apply eq_snoc_liftW with (i := iEl rF lF) (A := A) (A' := A');
        [ exact HD2 | exact HD | exact HG | apply wsc_iF | apply wsc_A
        | apply wsc_A' | exact Hw | exact Hw2 | apply wsc_ElW | exact Ha ]. }
    apply Snoc_cong;
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; apply wsc_iF
      | apply eq_term_refl; apply wsc_A
      | exact Hcmp
      | apply eq_term_refl; exact Ha'' ].
  Qed.

  (* ---- the codomain code ---- *)

  Local Notation E1 := (oExtC D2 rF lF (wkCode D2 D w2 rF lF F')).
  Local Notation E2 := (oExtC D2 rF lF (wkCode D2 G w'' rF lF F)).

  Lemma wsc_lw2 : wft (oLift D2 D w2 rF lF F') (sSub E1 DF).
  Proof.
    apply wf_oLift;
      [ exact HD2 | exact HD | exact Hw2 | exact HrF | exact HlF | exact HF'w ].
  Qed.

  Lemma wsc_lw'' : wft (oLift D2 G w'' rF lF F) (sSub E2 GF).
  Proof.
    apply wf_oLift;
      [ exact HD2 | exact HG | exact Hw'' | exact HrF | exact HlF | exact HF ].
  Qed.

  Lemma wsc_sortE : eq_sort ott_dtt [] (sCode E1 rG lG) (sCode E2 rG lG).
  Proof.
    unfold sCode; apply sExp_cong;
      [ apply wsc_Eeq
      | apply eq_term_refl; apply wsc_cG
      | apply U_cong;
        [ apply wsc_Eeq | apply eq_term_refl; exact HrG
        | apply eq_term_refl; exact HlG ] ].
  Qed.

  Lemma wsc_liftcmp
    : eqt (sSub E2 GF)
        (oCmp E1 DF GF (oLift D2 D w2 rF lF F') lw)
        (oLift D2 G w'' rF lF F).
  Proof.
    assert (eqt (sTy D2 (iEl rF lF)) (oTySubst D2 D w2 (iEl rF lF) A')
              (oEl D2 rF lF (wkCode D2 D w2 rF lF F'))) as He2
        by (apply eq_El_subst;
            [ exact HD2 | exact HD | exact Hw2 | exact HrF | exact HlF
            | exact HF'w ]).
    assert (eqt (sTy D2 (iEl rF lF)) (oTySubst D2 G w'' (iEl rF lF) A)
              (oEl D2 rF lF (wkCode D2 G w'' rF lF F))) as He''
        by (apply eq_El_subst;
            [ exact HD2 | exact HG | exact Hw'' | exact HrF | exact HlF
            | exact HF ]).
    assert (eqt (sTy D2 (iEl rF lF)) (oTySubst D2 G w'' (iEl rF lF) A)
              (oEl D2 rF lF (wkCode D2 D w2 rF lF F'))) as He2'
        by (eapply eq_term_trans;
            [ apply eq_term_sym; apply wsc_Aty | exact He2 ]).
    eapply eq_term_trans.
    { eapply eq_term_conv.
      - unfold oExtC at 1 2 3.
        apply eq_liftW_cmp
          with (D2 := D2) (D := D) (G := G) (w2 := w2) (w := w) (w'' := w'')
               (i := iEl rF lF) (A := A) (A' := A')
               (A2 := oEl D2 rF lF (wkCode D2 D w2 rF lF F'));
          [ exact HD2 | exact HD | exact HG | apply wsc_iF | apply wsc_A
          | apply wsc_A'
          | apply wf_El;
            [ exact HD2 | exact HrF | exact HlF | apply wsc_Fw2 ]
          | exact Hw | exact Hw2 | exact Hw'' | apply wsc_ElW | exact He2
          | exact Hcmp ].
      - apply eq_sort_sub_cong;
          [ apply wsc_Eeq | apply eq_term_refl; apply wsc_GF ]. }
    unfold oExtC.
    apply eq_liftW_cong
      with (D := D2) (G := G) (w := w'') (i := iEl rF lF) (A := A)
           (A1 := oEl D2 rF lF (wkCode D2 D w2 rF lF F'))
           (A2 := oEl D2 rF lF (wkCode D2 G w'' rF lF F));
      [ exact HD2 | exact HG | apply wsc_iF | apply wsc_A
      | apply wf_El; [ exact HD2 | exact HrF | exact HlF | apply wsc_Fw2 ]
      | apply wf_El; [ exact HD2 | exact HrF | exact HlF | apply wsc_Fw'' ]
      | exact Hw'' | exact He2' | exact He'' ].
  Qed.

  Lemma wsc_S1B
    : eqt (sTy E1 (iCode lG))
        (oTySubst E1 DF (oLift D2 D w2 rF lF F') (iCode lG)
           (oTySubst DF GF lw (iCode lG) (oU GF rG lG)))
        (oU E1 rG lG).
  Proof.
    eapply eq_term_trans.
    { apply TySubst_cong
        with (G1 := E1) (G2 := E1) (G1' := DF) (G2' := DF)
             (g1 := oLift D2 D w2 rF lF F') (g2 := oLift D2 D w2 rF lF F')
             (i1 := iCode lG) (i2 := iCode lG)
             (A1 := oTySubst DF GF lw (iCode lG) (oU GF rG lG))
             (A2 := oU DF rG lG);
        [ apply eq_term_refl; apply wsc_E1
        | apply eq_term_refl; apply wsc_DF
        | apply eq_term_refl; apply wsc_lw2
        | apply eq_term_refl; apply wsc_cG
        | apply eq_U_subst;
          [ apply wsc_DF | apply wsc_GF | apply wsc_lw | exact HrG
          | exact HlG ] ]. }
    apply eq_U_subst;
      [ apply wsc_E1 | apply wsc_DF | apply wsc_lw2 | exact HrG | exact HlG ].
  Qed.

  Theorem wsc_codcode
    : eqt (sCode E2 rG lG)
        (oExpSubst (oExtC D2 rF lF (wkCode D2 D w2 rF lF F'))
           (oExtC D rF lF F') (oLift D2 D w2 rF lF F') (iCode lG)
           (oU (oExtC D rF lF F') rG lG) B')
        (oExpSubst (oExtC D2 rF lF (wkCode D2 G w'' rF lF F))
           (oExtC G rF lF F) (oLift D2 G w'' rF lF F) (iCode lG)
           (oU (oExtC G rF lF F) rG lG) B).
  Proof.
    eapply eq_term_trans
      with (e12 := oExpSubst E1 GF (oCmp E1 DF GF (oLift D2 D w2 rF lF F') lw)
                     (iCode lG) (oU GF rG lG) B).
    - eapply eq_term_conv; [ | apply wsc_sortE ].
      eapply eq_term_conv;
        [ | apply eq_sort_exp_ty; apply wsc_S1B ].
      eapply eq_term_trans.
      + apply ExpSubst_cong
          with (G1 := E1) (G2 := E1) (G1' := DF) (G2' := DF)
               (g1 := oLift D2 D w2 rF lF F') (g2 := oLift D2 D w2 rF lF F')
               (i1 := iCode lG) (i2 := iCode lG)
               (A1 := oU DF rG lG)
               (A2 := oTySubst DF GF lw (iCode lG) (oU GF rG lG))
               (v1 := B')
               (v2 := oExpSubst DF GF lw (iCode lG) (oU GF rG lG) B);
          [ apply eq_term_refl; apply wsc_E1
          | apply eq_term_refl; apply wsc_DF
          | apply eq_term_refl; apply wsc_lw2
          | apply eq_term_refl; apply wsc_cG
          | apply eq_term_sym; apply eq_U_subst;
            [ apply wsc_DF | apply wsc_GF | apply wsc_lw | exact HrG
            | exact HlG ]
          | eapply eq_term_conv;
            [ apply eq_term_sym; exact HeqB'
            | apply eq_sort_sym; apply eq_sort_Usub;
              [ apply wsc_DF | apply wsc_GF | apply wsc_lw | exact HrG
              | exact HlG ] ] ].
      + apply eq_exp_subst_cmp with (G2 := DF);
          [ apply wsc_E1 | apply wsc_DF | apply wsc_GF | apply wsc_lw2
          | apply wsc_lw | apply wsc_cG
          | apply wf_U; [ apply wsc_GF | exact HrG | exact HlG ]
          | exact HB ].
    -       eapply eqt_Usub_c
        with (G' := GF) (g := oLift D2 G w'' rF lF F) (r := rG) (l := lG);
        [ apply wsc_E2 | apply wsc_GF | apply wsc_lw'' | exact HrG
        | exact HlG | ].
      apply ExpSubst_cong
        with (G1 := E1) (G2 := E2) (G1' := GF) (G2' := GF)
             (g1 := oCmp E1 DF GF (oLift D2 D w2 rF lF F') lw)
             (g2 := oLift D2 G w'' rF lF F)
             (i1 := iCode lG) (i2 := iCode lG)
             (A1 := oU GF rG lG) (A2 := oU GF rG lG) (v1 := B) (v2 := B);
        [ apply wsc_Eeq
        | apply eq_term_refl; apply wsc_GF
        | apply wsc_liftcmp
        | apply eq_term_refl; apply wsc_cG
        | apply eq_term_refl; apply wf_U;
          [ apply wsc_GF | exact HrG | exact HlG ]
        | apply eq_term_refl; exact HB ].
  Qed.

End WkStepC.

(* ---- the relevant Pi: the weakened function and the application ---- *)

Section WkPiRel.

  Context (D2 D G rF lF lG F B w w2 w'' F' B' : term).

  Context
    (HG : wft G sEnv) (HD : wft D sEnv) (HD2 : wft D2 sEnv)
    (HrF : wft rF sRelevance) (HlF : wft lF sLvl) (HlG : wft lG sLvl)
    (HF : wft F (sCode G rF lF))
    (HB : wft B (sCode (oExtC G rF lF F) oRel lG))
    (Hw : wft w (sSub D G)) (Hw2 : wft w2 (sSub D2 D))
    (Hw'' : wft w'' (sSub D2 G))
    (Hcmp : eqt (sSub D2 G) (oCmp D2 D G w2 w) w'')
    (HF'w : wft F' (sCode D rF lF))
    (HeqF : eqt (sCode D rF lF) (wkCode D G w rF lF F) F')
    (HB'w : wft B' (sCode (oExtC D rF lF F') oRel lG))
    (HeqB' : eqt (sCode (oExtC D rF lF F') oRel lG)
               (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
                  (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
                  (iCode lG) (oU (oExtC G rF lF F) oRel lG) B) B')
    (HeqBL : eqt (sCode (oExtC D rF lF F') oRel lG)
               (wkCodCodeRel D G w rF lF lG F B) B').

  Lemma wpr_iF : wft (iEl rF lF) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]. Qed.

  Lemma wpr_iG : wft (iEl oRel lG) sInfo.
  Proof.
    unfold iEl; apply wf_Info; [ apply wf_Rel | apply wf_Iota; exact HlG ].
  Qed.

  Lemma wpr_ElPiG
    : wft (oEl G oRel lG (oPiRel G rF lF lG F B)) (sTy G (iEl oRel lG)).
  Proof.
    apply wf_El;
      [ exact HG | apply wf_Rel | exact HlG
      | apply wf_PiRel;
        [ exact HG | exact HrF | exact HlF | exact HlG | exact HF
        | exact HB ] ].
  Qed.

  Lemma wpr_PiW
    : eqt (sTy D (iEl oRel lG))
        (oTySubst D G w (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)))
        (oEl D oRel lG (oPiRel D rF lF lG F' B')).
  Proof.
    apply eq_ElPiRel_wk;
      [ exact HD | exact HG | exact HrF | exact HlF | exact HlG | exact Hw
      | exact HF | exact HB | exact HeqF | exact HeqBL ].
  Qed.

  Lemma wpr_Pity
    : eqt (sTy D2 (iEl oRel lG))
        (oTySubst D2 D w2 (iEl oRel lG)
           (oTySubst D G w (iEl oRel lG)
              (oEl G oRel lG (oPiRel G rF lF lG F B))))
        (oTySubst D2 G w'' (iEl oRel lG)
           (oEl G oRel lG (oPiRel G rF lF lG F B))).
  Proof.
    eapply eq_term_trans.
    { apply eq_ty_subst_cmp;
        [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw
        | apply wpr_iG | apply wpr_ElPiG ]. }
    apply TySubst_cong
      with (G1 := D2) (G2 := D2) (G1' := G) (G2' := G)
           (g1 := oCmp D2 D G w2 w) (g2 := w'')
           (i1 := iEl oRel lG) (i2 := iEl oRel lG)
           (A1 := oEl G oRel lG (oPiRel G rF lF lG F B))
           (A2 := oEl G oRel lG (oPiRel G rF lF lG F B));
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HG
      | exact Hcmp
      | apply eq_term_refl; apply wpr_iG
      | apply eq_term_refl; apply wpr_ElPiG ].
  Qed.

  Lemma wpr_fun e
    : wft e (sElt G oRel lG (oPiRel G rF lF lG F B)) ->
      eqt (sElt D2 oRel lG
             (oPiRel D2 rF lF lG (wkCode D2 G w'' rF lF F)
                (wkCodCodeRel D2 G w'' rF lF lG F B)))
        (wkFunRel D2 D w2 rF lF lG F' B' (wkFunRel D G w rF lF lG F B e))
        (wkFunRel D2 G w'' rF lF lG F B e).
  Proof.
    intro He.
    assert (wft (wkFunRel D G w rF lF lG F B e)
              (sExp D (iEl oRel lG)
                 (oTySubst D G w (iEl oRel lG)
                    (oEl G oRel lG (oPiRel G rF lF lG F B))))) as Hew.
    { unfold wkFunRel; apply wf_ExpSubst;
        [ exact HD | exact HG | exact Hw | apply wpr_iG | apply wpr_ElPiG
        | exact He ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply pr_Pi_subst;
            [ exact HD2 | exact HG | exact HrF | exact HlF | exact HlG
            | exact Hw'' | exact HF | exact HB ] ].
    eapply eq_term_trans
      with (e12 := oExpSubst D2 G (oCmp D2 D G w2 w) (iEl oRel lG)
                     (oEl G oRel lG (oPiRel G rF lF lG F B)) e).
    - eapply eq_term_conv;
        [ | apply eq_sort_exp_ty; apply wpr_Pity ].
      eapply eq_term_trans.
      + unfold wkFunRel at 1.
        apply ExpSubst_cong
          with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D)
               (g1 := w2) (g2 := w2)
               (i1 := iEl oRel lG) (i2 := iEl oRel lG)
               (A1 := oEl D oRel lG (oPiRel D rF lF lG F' B'))
               (A2 := oTySubst D G w (iEl oRel lG)
                        (oEl G oRel lG (oPiRel G rF lF lG F B)))
               (v1 := wkFunRel D G w rF lF lG F B e)
               (v2 := wkFunRel D G w rF lF lG F B e);
          [ apply eq_term_refl; exact HD2
          | apply eq_term_refl; exact HD
          | apply eq_term_refl; exact Hw2
          | apply eq_term_refl; apply wpr_iG
          | apply eq_term_sym; apply wpr_PiW
          | apply eq_term_refl; exact Hew ].
      + unfold wkFunRel.
        apply eq_exp_subst_cmp with (G2 := D);
          [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw
          | apply wpr_iG | apply wpr_ElPiG | exact He ].
    - unfold wkFunRel.
      apply ExpSubst_cong
        with (G1 := D2) (G2 := D2) (G1' := G) (G2' := G)
             (g1 := oCmp D2 D G w2 w) (g2 := w'')
             (i1 := iEl oRel lG) (i2 := iEl oRel lG)
             (A1 := oEl G oRel lG (oPiRel G rF lF lG F B))
             (A2 := oEl G oRel lG (oPiRel G rF lF lG F B))
             (v1 := e) (v2 := e);
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; exact HG
        | exact Hcmp
        | apply eq_term_refl; apply wpr_iG
        | apply eq_term_refl; apply wpr_ElPiG
        | apply eq_term_refl; exact He ].
  Qed.

  Lemma wpr_a'' a
    : wft a (sExp D2 (iEl rF lF)
               (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F'))) ->
      wft a (sElt D2 rF lF (wkCode D2 G w'' rF lF F)).
  Proof.
    intro Ha.
    eapply wf_term_conv; [ exact Ha | ].
    unfold sElt; apply eq_sort_exp_ty.
    eapply eq_term_trans.
    - apply wsc_Aty with (w := w);
        [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF | exact HF
        | exact Hw | exact Hw2 | exact Hcmp | exact HeqF ].
    - apply eq_El_subst;
        [ exact HD2 | exact HG | exact Hw'' | exact HrF | exact HlF
        | exact HF ].
  Qed.

  Theorem wpr_cod a
    : wft a (sExp D2 (iEl rF lF)
               (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F'))) ->
      eqt (sTy D2 (iEl oRel lG))
        (codAtRel D2 D rF lF lG F' B' w2 a)
        (codAtRel D2 G rF lF lG F B w'' a).
  Proof.
    apply wsc_cod with (w := w);
      [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF | apply wf_Rel
      | exact HlG | exact HF | exact HB | exact Hw | exact Hw2 | exact Hcmp
      | exact HF'w | exact HeqF | exact HeqB' ].
  Qed.

  Theorem wpr_app e a
    : wft e (sElt G oRel lG (oPiRel G rF lF lG F B)) ->
      wft a (sExp D2 (iEl rF lF)
               (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F'))) ->
      eqt (sExp D2 (iEl oRel lG) (codAtRel D2 G rF lF lG F B w'' a))
        (appAtRel D2 D rF lF lG F' B' w2 (wkFunRel D G w rF lF lG F B e) a)
        (appAtRel D2 G rF lF lG F B w'' e a).
  Proof.
    intros He Ha.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply ac_appConcl;
            [ exact HD2 | exact HG | exact HrF | exact HlF | apply wf_Rel
            | exact HlG | exact Hw'' | exact HF | exact HB
            | apply wpr_a''; exact Ha ] ].
    unfold appAtRel; apply AppRel_cong;
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply eq_term_refl; exact HlG
      | apply wsc_F1 with (w := w);
        [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF | exact HF
        | exact Hw | exact Hw2 | exact Hw'' | exact Hcmp | exact HeqF ]
      | apply wsc_codcode with (rG := oRel) (w := w);
        [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF
        | apply wf_Rel | exact HlG | exact HF | exact HB | exact Hw
        | exact Hw2 | exact Hw'' | exact Hcmp | exact HF'w | exact HeqF
        | exact HeqB' ]
      | apply wpr_fun; exact He
      | apply eq_term_refl; apply wpr_a''; exact Ha ].
  Qed.

End WkPiRel.

(* ---- the irrelevant Pi: the same, with [AppIrr] ---- *)

Section WkPiIrr.

  Context (D2 D G rF lF F B w w2 w'' F' B' : term).

  Context
    (HG : wft G sEnv) (HD : wft D sEnv) (HD2 : wft D2 sEnv)
    (HrF : wft rF sRelevance) (HlF : wft lF sLvl)
    (HF : wft F (sCode G rF lF))
    (HB : wft B (sCode (oExtC G rF lF F) oIrr oL0))
    (Hw : wft w (sSub D G)) (Hw2 : wft w2 (sSub D2 D))
    (Hw'' : wft w'' (sSub D2 G))
    (Hcmp : eqt (sSub D2 G) (oCmp D2 D G w2 w) w'')
    (HF'w : wft F' (sCode D rF lF))
    (HeqF : eqt (sCode D rF lF) (wkCode D G w rF lF F) F')
    (HB'w : wft B' (sCode (oExtC D rF lF F') oIrr oL0))
    (HeqB' : eqt (sCode (oExtC D rF lF F') oIrr oL0)
               (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
                  (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
                  (iCode oL0) (oU (oExtC G rF lF F) oIrr oL0) B) B')
    (HeqBL : eqt (sCode (oExtC D rF lF F') oIrr oL0)
               (wkCodCodeIrr D G w rF lF F B) B').

  Lemma wpi_iF : wft (iEl rF lF) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]. Qed.

  Lemma wpi_iG : wft (iEl oIrr oL0) sInfo.
  Proof.
    unfold iEl; apply wf_Info; [ apply wf_Irr | apply wf_Iota; apply wf_L0 ].
  Qed.

  Lemma wpi_GF : wft (oExtC G rF lF F) sEnv.
  Proof. apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  Lemma wpi_Pi : wft (oPiIrr G rF lF F B) (sCode G oIrr oL0).
  Proof.
    apply wft_U0irr_iota; [ exact HG | ].
    apply wf_PiIrr;
      [ exact HG | exact HrF | exact HlF | exact HF
      | apply wft_U0irr_next; [ apply wpi_GF | exact HB ] ].
  Qed.

  Lemma wpi_ElPiG
    : wft (oEl G oIrr oL0 (oPiIrr G rF lF F B)) (sTy G (iEl oIrr oL0)).
  Proof.
    apply wf_El; [ exact HG | apply wf_Irr | apply wf_L0 | apply wpi_Pi ].
  Qed.

  Lemma wpi_PiW
    : eqt (sTy D (iEl oIrr oL0))
        (oTySubst D G w (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)))
        (oEl D oIrr oL0 (oPiIrr D rF lF F' B')).
  Proof.
    apply eq_ElPiIrr_wk;
      [ exact HD | exact HG | exact HrF | exact HlF | exact Hw
      | exact HF | exact HB | exact HeqF | exact HeqBL ].
  Qed.

  Lemma wpi_Pity
    : eqt (sTy D2 (iEl oIrr oL0))
        (oTySubst D2 D w2 (iEl oIrr oL0)
           (oTySubst D G w (iEl oIrr oL0)
              (oEl G oIrr oL0 (oPiIrr G rF lF F B))))
        (oTySubst D2 G w'' (iEl oIrr oL0)
           (oEl G oIrr oL0 (oPiIrr G rF lF F B))).
  Proof.
    eapply eq_term_trans.
    { apply eq_ty_subst_cmp;
        [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw
        | apply wpi_iG | apply wpi_ElPiG ]. }
    apply TySubst_cong
      with (G1 := D2) (G2 := D2) (G1' := G) (G2' := G)
           (g1 := oCmp D2 D G w2 w) (g2 := w'')
           (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
           (A1 := oEl G oIrr oL0 (oPiIrr G rF lF F B))
           (A2 := oEl G oIrr oL0 (oPiIrr G rF lF F B));
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HG
      | exact Hcmp
      | apply eq_term_refl; apply wpi_iG
      | apply eq_term_refl; apply wpi_ElPiG ].
  Qed.

  Lemma wpi_fun e
    : wft e (sElt G oIrr oL0 (oPiIrr G rF lF F B)) ->
      eqt (sElt D2 oIrr oL0
             (oPiIrr D2 rF lF (wkCode D2 G w'' rF lF F)
                (wkCodCodeIrr D2 G w'' rF lF F B)))
        (wkFunIrr D2 D w2 rF lF F' B' (wkFunIrr D G w rF lF F B e))
        (wkFunIrr D2 G w'' rF lF F B e).
  Proof.
    intro He.
    assert (wft (wkFunIrr D G w rF lF F B e)
              (sExp D (iEl oIrr oL0)
                 (oTySubst D G w (iEl oIrr oL0)
                    (oEl G oIrr oL0 (oPiIrr G rF lF F B))))) as Hew.
    { unfold wkFunIrr; apply wf_ExpSubst;
        [ exact HD | exact HG | exact Hw | apply wpi_iG | apply wpi_ElPiG
        | exact He ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply pi_Pi_subst;
            [ exact HD2 | exact HG | exact HrF | exact HlF
            | exact Hw'' | exact HF | exact HB ] ].
    eapply eq_term_trans
      with (e12 := oExpSubst D2 G (oCmp D2 D G w2 w) (iEl oIrr oL0)
                     (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e).
    - eapply eq_term_conv;
        [ | apply eq_sort_exp_ty; apply wpi_Pity ].
      eapply eq_term_trans.
      + unfold wkFunIrr at 1.
        apply ExpSubst_cong
          with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D)
               (g1 := w2) (g2 := w2)
               (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
               (A1 := oEl D oIrr oL0 (oPiIrr D rF lF F' B'))
               (A2 := oTySubst D G w (iEl oIrr oL0)
                        (oEl G oIrr oL0 (oPiIrr G rF lF F B)))
               (v1 := wkFunIrr D G w rF lF F B e)
               (v2 := wkFunIrr D G w rF lF F B e);
          [ apply eq_term_refl; exact HD2
          | apply eq_term_refl; exact HD
          | apply eq_term_refl; exact Hw2
          | apply eq_term_refl; apply wpi_iG
          | apply eq_term_sym; apply wpi_PiW
          | apply eq_term_refl; exact Hew ].
      + unfold wkFunIrr.
        apply eq_exp_subst_cmp with (G2 := D);
          [ exact HD2 | exact HD | exact HG | exact Hw2 | exact Hw
          | apply wpi_iG | apply wpi_ElPiG | exact He ].
    - unfold wkFunIrr.
      apply ExpSubst_cong
        with (G1 := D2) (G2 := D2) (G1' := G) (G2' := G)
             (g1 := oCmp D2 D G w2 w) (g2 := w'')
             (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
             (A1 := oEl G oIrr oL0 (oPiIrr G rF lF F B))
             (A2 := oEl G oIrr oL0 (oPiIrr G rF lF F B))
             (v1 := e) (v2 := e);
        [ apply eq_term_refl; exact HD2
        | apply eq_term_refl; exact HG
        | exact Hcmp
        | apply eq_term_refl; apply wpi_iG
        | apply eq_term_refl; apply wpi_ElPiG
        | apply eq_term_refl; exact He ].
  Qed.

  Lemma wpi_a'' a
    : wft a (sExp D2 (iEl rF lF)
               (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F'))) ->
      wft a (sElt D2 rF lF (wkCode D2 G w'' rF lF F)).
  Proof.
    intro Ha.
    eapply wf_term_conv; [ exact Ha | ].
    unfold sElt; apply eq_sort_exp_ty.
    eapply eq_term_trans.
    - apply wsc_Aty with (w := w);
        [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF | exact HF
        | exact Hw | exact Hw2 | exact Hcmp | exact HeqF ].
    - apply eq_El_subst;
        [ exact HD2 | exact HG | exact Hw'' | exact HrF | exact HlF
        | exact HF ].
  Qed.

  Theorem wpi_cod a
    : wft a (sExp D2 (iEl rF lF)
               (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F'))) ->
      eqt (sTy D2 (iEl oIrr oL0))
        (codAtIrr D2 D rF lF F' B' w2 a)
        (codAtIrr D2 G rF lF F B w'' a).
  Proof.
    apply wsc_cod with (w := w);
      [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF | apply wf_Irr
      | apply wf_L0 | exact HF | exact HB | exact Hw | exact Hw2 | exact Hcmp
      | exact HF'w | exact HeqF | exact HeqB' ].
  Qed.

  Theorem wpi_app e a
    : wft e (sElt G oIrr oL0 (oPiIrr G rF lF F B)) ->
      wft a (sExp D2 (iEl rF lF)
               (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F'))) ->
      eqt (sExp D2 (iEl oIrr oL0) (codAtIrr D2 G rF lF F B w'' a))
        (appAtIrr D2 D rF lF F' B' w2 (wkFunIrr D G w rF lF F B e) a)
        (appAtIrr D2 G rF lF F B w'' e a).
  Proof.
    intros He Ha.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply ac_appConcl;
            [ exact HD2 | exact HG | exact HrF | exact HlF | apply wf_Irr
            | apply wf_L0 | exact Hw'' | exact HF | exact HB
            | apply wpi_a''; exact Ha ] ].
    unfold appAtIrr; apply AppIrr_cong;
      [ apply eq_term_refl; exact HD2
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply wsc_F1 with (w := w);
        [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF | exact HF
        | exact Hw | exact Hw2 | exact Hw'' | exact Hcmp | exact HeqF ]
      | apply wsc_codcode with (rG := oIrr) (w := w);
        [ exact HG | exact HD | exact HD2 | exact HrF | exact HlF
        | apply wf_Irr | apply wf_L0 | exact HF | exact HB | exact Hw
        | exact Hw2 | exact Hw'' | exact Hcmp | exact HF'w | exact HeqF
        | exact HeqB' ]
      | apply wpi_fun; exact He
      | apply eq_term_refl; apply wpi_a''; exact Ha ].
  Qed.

End WkPiIrr.

(* ================================================================== *)
(* B2. Independence of the Kripke data in the CHOICE of composite      *)
(*                                                                     *)
(* [Wk_cmp] produces the composite of two weakenings only up to         *)
(* provable equality, so the Kripke families of the weakened Pi clause  *)
(* have to be defined by quantifying over every such composite.  These  *)
(* two congruences are what makes that quantification harmless.         *)
(* ================================================================== *)

Lemma eq_wkCode_cong D G w1 w2 rF lF F
  : wft D sEnv -> wft G sEnv -> wft w2 (sSub D G) ->
    wft rF sRelevance -> wft lF sLvl -> wft F (sCode G rF lF) ->
    eqt (sSub D G) w1 w2 ->
    eqt (sCode D rF lF) (wkCode D G w1 rF lF F) (wkCode D G w2 rF lF F).
Proof.
  intros HD HG Hw2 HrF HlF HF Hw.
  unfold wkCode.
  eapply eqt_Usub_c with (G' := G) (g := w2) (r := rF) (l := lF);
    [ exact HD | exact HG | exact Hw2 | exact HrF | exact HlF | ].
  apply ExpSubst_cong
    with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w1) (g2 := w2)
         (i1 := iCode lF) (i2 := iCode lF)
         (A1 := oU G rF lF) (A2 := oU G rF lF) (v1 := F) (v2 := F);
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; exact HG
    | exact Hw
    | apply eq_term_refl; unfold iCode; apply wf_Info;
      [ apply wf_Rel | apply wf_Next; exact HlF ]
    | apply eq_term_refl; apply wf_U; [ exact HG | exact HrF | exact HlF ]
    | apply eq_term_refl; exact HF ].
Qed.

Lemma eq_codAt_cong_w D G rF lF rG lG F B w1 w2 a
  : wft D sEnv -> wft G sEnv -> wft rF sRelevance -> wft lF sLvl ->
    wft rG sRelevance -> wft lG sLvl -> wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) rG lG) ->
    wft w2 (sSub D G) -> eqt (sSub D G) w1 w2 ->
    wft a (sExp D (iEl rF lF)
             (oTySubst D G w2 (iEl rF lF) (oEl G rF lF F))) ->
    eqt (sTy D (iEl rG lG))
      (oTySubst D (oExtC G rF lF F) (instAt D G rF lF F w1 a) (iEl rG lG)
         (oEl (oExtC G rF lF F) rG lG B))
      (oTySubst D (oExtC G rF lF F) (instAt D G rF lF F w2 a) (iEl rG lG)
         (oEl (oExtC G rF lF F) rG lG B)).
Proof.
  intros HD HG HrF HlF HrG HlG HF HB Hw2 Hw Ha.
  assert (wft (iEl rF lF) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]).
  assert (wft (iEl rG lG) sInfo) as HiG
      by (unfold iEl; apply wf_Info; [ exact HrG | apply wf_Iota; exact HlG ]).
  assert (wft (oEl G rF lF F) (sTy G (iEl rF lF))) as HA
      by (apply wf_El; [ exact HG | exact HrF | exact HlF | exact HF ]).
  assert (wft (oExtC G rF lF F) sEnv) as HGF
      by (apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]).
  apply TySubst_cong
    with (G1 := D) (G2 := D) (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
         (g1 := instAt D G rF lF F w1 a) (g2 := instAt D G rF lF F w2 a)
         (i1 := iEl rG lG) (i2 := iEl rG lG)
         (A1 := oEl (oExtC G rF lF F) rG lG B)
         (A2 := oEl (oExtC G rF lF F) rG lG B);
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; exact HGF
    | | apply eq_term_refl; exact HiG
    | apply eq_term_refl; apply wf_El;
      [ exact HGF | exact HrG | exact HlG | exact HB ] ].
  unfold instAt, oExtC.
  apply Snoc_cong;
    [ apply eq_term_refl; exact HD
    | apply eq_term_refl; exact HG
    | apply eq_term_refl; exact HiF
    | apply eq_term_refl; exact HA
    | exact Hw
    | apply eq_term_refl; exact Ha ].
Qed.

(* [RTy] only ever constrains its candidate through an [iff], so it is
   stable under replacing the candidate by an equivalent one. *)
Lemma RTy_iff G i A P Q : RTy G i A P -> (forall e, Q e <-> P e) -> RTy G i A Q.
Proof.
  destruct 1 as
    [ G r l P HG Hr Hl Hiff
    | G P HG Hiff
    | G P HG Hiff
    | G r l c P Hx Hiff
    | G rF lF lG F B P Pd Pc HrF HlF HlG HF HB Hd Hc Hiff
    | G rF lF F B P Pd Pc HrF HlF HF HB Hd Hc Hiff ];
    intro Hq.
  - apply rty_U; try assumption;
      intro e; eapply iff_trans_r; [ apply Hq | apply iff_sym, Hiff ].
  - apply rty_nat; try assumption;
      intro e; eapply iff_trans_r; [ apply Hq | apply iff_sym, Hiff ].
  - apply rty_empty; try assumption;
      intro e; eapply iff_trans_r; [ apply Hq | apply iff_sym, Hiff ].
  - eapply rty_var; try eassumption;
      intro e; eapply iff_trans_r; [ apply Hq | apply iff_sym, Hiff ].
  - eapply rty_pi_rel with (Pd := Pd) (Pc := Pc); try eassumption;
      intro e; eapply iff_trans_r; [ apply Hq | apply iff_sym, Hiff ].
  - eapply rty_pi_irr with (Pd := Pd) (Pc := Pc); try eassumption;
      intro e; eapply iff_trans_r; [ apply Hq | apply iff_sym, Hiff ].
Qed.

(* ================================================================== *)
(* B. WEAKENING OF REDUCIBILITY                                        *)
(* ================================================================== *)

Theorem RTy_wk : forall G i A P, RTy G i A P ->
  forall D w, Wk D G w -> EnvOk D ->
  exists A' Q, TyOk D i A'
            /\ eqt (sTy D i) (oTySubst D G w i A) A'
            /\ RTy D i A' Q
            /\ (forall e, P e -> Q (oExpSubst D G w i A e)).
Proof.
  apply (@RTy_strong_ind
    (fun G i A P => forall D w, Wk D G w -> EnvOk D ->
       exists A' Q, TyOk D i A'
                 /\ eqt (sTy D i) (oTySubst D G w i A) A'
                 /\ RTy D i A' Q
                 /\ (forall e, P e -> Q (oExpSubst D G w i A e)))).

  (* ---- U ---- *)
  - intros G r l P HG Hr Hl Hiff D w HW HD.
    exists (oU D r l), (HasNfCode D r l).
    split; [ apply tyok_U; assumption | ].
    split; [ apply eq_U_subst; wfx | ].
    split; [ apply RTy_U_i; assumption | ].
    intros e He; destruct (proj1 (Hiff e) He) as [c0 [Hc0 Heq]].
    destruct (NfCode_wk Hc0 HW HD) as [c1 [Hc1 Heq1]].
    exists c1; split; [ exact Hc1 | ].
    eapply eq_term_trans; [ | exact Heq1 ].
    eapply eqt_Usub_c with (G' := G) (g := w) (r := r) (l := l);
      [ wfx | wfx | wfx | wfx | wfx | ].
    apply ExpSubst_cong
      with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
           (i1 := iCode l) (i2 := iCode l)
           (A1 := oU G r l) (A2 := oU G r l) (v1 := e) (v2 := c0);
      [ er | er | er | er | er | exact Heq ].

  (* ---- Nat ---- *)
  - intros G P HG Hiff D w HW HD.
    assert (eqt (sTy D (iEl oRel oL0))
              (oTySubst D G w (iEl oRel oL0) (oEl G oRel oL0 (oNat G)))
              (oEl D oRel oL0 (oNat D))) as HeqA.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | apply eq_Nat_subst'; wfx ]. }
    exists (oEl D oRel oL0 (oNat D)),
      (HasNf D (iEl oRel oL0) (oEl D oRel oL0 (oNat D))).
    split; [ apply tyok_El; apply nfcode_nat; exact HD | ].
    split; [ exact HeqA | ].
    split; [ apply RTy_nat_i; exact HD | ].
    intros e He; destruct (proj1 (Hiff e) He) as [n [Hn Heq]].
    destruct (NfET_wk Hn HW HD) as [A2 [e' [HT2 [HeqA2 [Hn' Heq']]]]].
    assert (A2 = oEl D oRel oL0 (oNat D)) as ->.
    { eapply TyOk_inj;
        [ exact HT2 | apply tyok_El; apply nfcode_nat; exact HD
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact HeqA2 | exact HeqA ] ]. }
    exists e'; split; [ exact Hn' | ].
    eapply eq_term_trans; [ | exact Heq' ].
    eapply eq_term_conv;
      [ apply ExpSubst_cong
          with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
               (i1 := iEl oRel oL0) (i2 := iEl oRel oL0)
               (A1 := oEl G oRel oL0 (oNat G)) (A2 := oEl G oRel oL0 (oNat G))
               (v1 := e) (v2 := n);
        [ er | er | er | er | er | exact Heq ]
      | apply eq_sort_exp_ty; exact HeqA2 ].

  (* ---- Empty ---- *)
  - intros G P HG Hiff D w HW HD.
    assert (wft (oEmpty G) (sCode G oIrr oL0)) as HEc
        by (apply wft_i2c; [ wfx | apply wf_Irr | apply wf_Empty; wfx ]).
    assert (eqt (sTy D (iEl oIrr oL0))
              (oTySubst D G w (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)))
              (oEl D oIrr oL0 (oEmpty D))) as HeqA.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | apply eq_Empty_subst; wfx ]. }
    exists (oEl D oIrr oL0 (oEmpty D)),
      (HasNe D (iEl oIrr oL0) (oEl D oIrr oL0 (oEmpty D))).
    split; [ apply tyok_El; apply nfcode_empty; exact HD | ].
    split; [ exact HeqA | ].
    split; [ apply RTy_empty_i; exact HD | ].
    intros e He; destruct (proj1 (Hiff e) He) as [n [Hn Heq]].
    destruct (NeET_wk Hn HW HD) as [A2 [e' [HT2 [HeqA2 [Hn' Heq']]]]].
    assert (A2 = oEl D oIrr oL0 (oEmpty D)) as ->.
    { eapply TyOk_inj;
        [ exact HT2 | apply tyok_El; apply nfcode_empty; exact HD
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact HeqA2 | exact HeqA ] ]. }
    exists e'; split; [ exact Hn' | ].
    eapply eq_term_trans; [ | exact Heq' ].
    eapply eq_term_conv;
      [ apply ExpSubst_cong
          with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
               (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
               (A1 := oEl G oIrr oL0 (oEmpty G))
               (A2 := oEl G oIrr oL0 (oEmpty G)) (v1 := e) (v2 := n);
        [ er | er | er | er | er | exact Heq ]
      | apply eq_sort_exp_ty; exact HeqA2 ].

  (* ---- a type named by a variable ---- *)
  - intros G r l c P Hx Hiff D w HW HD.
    assert (TyOk G (iCode l) (oU G r l)) as HTU by (eapply VarT_TyOk; exact Hx).
    assert (RelNf r) as Hr by (apply (proj1 (TyOk_U_inv HTU))).
    assert (LvlNf l) as Hl by (apply (proj2 (TyOk_U_inv HTU))).
    destruct (VarT_wk Hx HW HD) as [A2 [x' [HT2 [HeqA2 [Hx' Heqx']]]]].
    assert (A2 = oU D r l) as ->.
    { eapply TyOk_inj;
        [ exact HT2 | apply tyok_U; assumption
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact HeqA2 | apply eq_U_subst; wfx ] ]. }
    assert (eqt (sTy D (iEl r l))
              (oTySubst D G w (iEl r l) (oEl G r l c)) (oEl D r l x')) as HeqA.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact Heqx' ]. }
    exists (oEl D r l x'), (HasNe D (iEl r l) (oEl D r l x')).
    split; [ apply tyok_El; apply nfcode_var; exact Hx' | ].
    split; [ exact HeqA | ].
    split; [ apply RTy_var_i; exact Hx' | ].
    intros e He; destruct (proj1 (Hiff e) He) as [n [Hn Heq]].
    destruct (NeET_wk Hn HW HD) as [A3 [e' [HT3 [HeqA3 [Hn' Heq']]]]].
    assert (A3 = oEl D r l x') as ->.
    { eapply TyOk_inj;
        [ exact HT3 | apply tyok_El; apply nfcode_var; exact Hx'
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact HeqA3 | exact HeqA ] ]. }
    exists e'; split; [ exact Hn' | ].
    eapply eq_term_trans; [ | exact Heq' ].
    eapply eq_term_conv;
      [ apply ExpSubst_cong
          with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w)
               (i1 := iEl r l) (i2 := iEl r l)
               (A1 := oEl G r l c) (A2 := oEl G r l c) (v1 := e) (v2 := n);
        [ er | er | er | er | er | exact Heq ]
      | apply eq_sort_exp_ty; exact HeqA3 ].

  (* ---- Pi_rel ---- *)
  - intros G rF lF lG F B P Pd Pc HrF HlF HlG HF HB Hd Hc Hiff D w HW HD.
    assert (EnvOk G) as HGok by (eapply Wk_cod; exact HW).
    destruct (Hd D w HW HD) as [F1 (HF1 & HeqF1 & HR1 & _)].
    destruct (wk_codcodeW HW HD HF HF1 HeqF1 HB)
      as [B1 (HB1 & HeqB1W & HeqB1L)].
    (* the Kripke families do not depend on the choice of composite *)
    assert (forall D2 u1 u2 a, Wk D2 G u1 -> Wk D2 G u2 -> EnvOk D2 ->
              eqt (sSub D2 G) u1 u2 -> Pd D2 u1 a -> Pd D2 u2 a) as Hdind.
    { intros D2 u1 u2 a HU1 HU2 HD2 Hu Ha.
      destruct (Hd D2 u1 HU1 HD2) as [Fa (HFa & HeqFa & HRa & _)].
      destruct (Hd D2 u2 HU2 HD2) as [Fb (HFb & HeqFb & HRb & _)].
      refine (proj1 (RTy_fun_eq HRa HRb _ a) Ha).
      apply El_cong; [ er | er | er | ].
      eapply eq_term_trans; [ apply eq_term_sym; exact HeqFa | ].
      eapply eq_term_trans; [ | exact HeqFb ].
      apply eq_wkCode_cong;
        [ wfx | wfx | apply Wk_wf; exact HU2 | wfx | wfx | wfx | exact Hu ]. }
    assert (forall D2 u1 u2 a x, Wk D2 G u1 -> Wk D2 G u2 -> EnvOk D2 ->
              eqt (sSub D2 G) u1 u2 -> Pd D2 u1 a -> Pd D2 u2 a ->
              Pc D2 u1 a x -> Pc D2 u2 a x) as Hcind.
    { intros D2 u1 u2 a x HU1 HU2 HD2 Hu Ha1 Ha2 Hx.
      destruct (Hc D2 u1 a HU1 HD2 Ha1) as [C1 (HT1 & Heq1 & HRc1 & _)].
      destruct (Hc D2 u2 a HU2 HD2 Ha2) as [C2 (HT2 & Heq2 & HRc2 & _)].
      refine (proj1 (RTy_fun_eq HRc1 HRc2 _ x) Hx).
      assert (wft a (sElt D2 rF lF (wkCode D2 G u2 rF lF F))) as Haw2.
      { eapply codAt_wf_a with (rG := oRel) (lG := lG) (B := B);
          [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HU2 | wfx
          | apply (eqt_wf_l Heq2) ]. }
      eapply eq_term_trans; [ apply eq_term_sym; exact Heq1 | ].
      eapply eq_term_trans; [ | exact Heq2 ].
      apply eq_codAt_cong_w with (rG := oRel);
        [ wfx | wfx | wfx | wfx | apply wf_Rel | wfx | wfx | wfx
        | apply Wk_wf; exact HU2 | exact Hu | ].
      eapply wf_term_conv; [ exact Haw2 | ].
      unfold sElt; apply eq_sort_exp_ty.
      apply eq_term_sym; apply eq_El_subst;
        [ wfx | wfx | apply Wk_wf; exact HU2 | wfx | wfx | wfx ]. }
    exists (oEl D oRel lG (oPiRel D rF lF lG F1 B1)),
      (fun e => forall D2 w2 a, Wk D2 D w2 -> EnvOk D2 ->
         (forall u, Wk D2 G u ->
            eqt (sSub D2 G) (oCmp D2 D G w2 w) u -> Pd D2 u a) ->
         forall u, Wk D2 G u -> eqt (sSub D2 G) (oCmp D2 D G w2 w) u ->
           Pc D2 u a (appAtRel D2 D rF lF lG F1 B1 w2 e a)).
    split; [ apply tyok_El; apply nfcode_pi_rel; assumption | ].
    split;
      [ apply eq_ElPiRel_wk;
        [ wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx
        | exact HeqF1 | exact HeqB1L ] | ].
    split.
    { apply rty_pi_rel
        with (Pd := fun D2 w2 a => forall u, Wk D2 G u ->
                      eqt (sSub D2 G) (oCmp D2 D G w2 w) u -> Pd D2 u a)
             (Pc := fun D2 w2 a x => forall u, Wk D2 G u ->
                      eqt (sSub D2 G) (oCmp D2 D G w2 w) u -> Pc D2 u a x);
        try assumption.
      (* the domain, at every further weakening *)
      { intros D2 w2 HW2 HD2.
        destruct (Wk_cmp HW2 HW HD2) as [u [HU Hu]].
        destruct (Hd D2 u HU HD2) as [F2 (HF2 & HeqF2 & HR2 & _)].
        exists F2; split; [ exact HF2 | split ].
        { eapply eq_term_trans; [ | exact HeqF2 ].
          apply wsc_F1 with (w := w);
            [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
            | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
            | exact HeqF1 ]. }
        { eapply RTy_iff; [ exact HR2 | ].
          intro a; split.
          { intro Hh; exact (Hh u HU Hu). }
          { intros Ha u2 HU2 Hu2.
            eapply Hdind;
              [ exact HU | exact HU2 | exact HD2
              | eapply eq_term_trans;
                [ apply eq_term_sym; exact Hu | exact Hu2 ]
              | exact Ha ]. } } }
      (* the codomain, at every further weakening and reducible argument *)
      { intros D2 w2 a HW2 HD2 Hpd.
        destruct (Wk_cmp HW2 HW HD2) as [u [HU Hu]].
        assert (Pd D2 u a) as Hpda by (apply Hpd; assumption).
        destruct (Hc D2 u a HU HD2 Hpda) as [C (HTC & HeqC & HRC & _)].
        assert (wft a (sElt D2 rF lF (wkCode D2 G u rF lF F))) as Haw.
        { eapply codAt_wf_a with (rG := oRel) (lG := lG) (B := B);
            [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HU | wfx
            | apply (eqt_wf_l HeqC) ]. }
        assert (wft a (sExp D2 (iEl rF lF)
                  (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F1)))) as Haw2.
        { eapply wf_term_conv; [ exact Haw | ].
          unfold sElt; apply eq_sort_exp_ty.
          apply eq_term_sym.
          eapply eq_term_trans;
            [ apply eq_El_subst;
              [ wfx | wfx | apply Wk_wf; exact HW2 | wfx | wfx | wfx ] | ].
          apply El_cong; [ er | er | er | ].
          apply wsc_F1 with (w := w);
            [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
            | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
            | exact HeqF1 ]. }
        exists C; split; [ exact HTC | split ].
        { eapply eq_term_trans; [ | exact HeqC ].
          apply wpr_cod with (w := w);
            [ wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx
            | apply Wk_wf; exact HW2 | exact Hu | wfx
            | exact HeqF1 | exact HeqB1W | exact Haw2 ]. }
        { eapply RTy_iff; [ exact HRC | ].
          intro x; split.
          { intro Hh; exact (Hh u HU Hu). }
          { intros Hx u2 HU2 Hu2.
            assert (eqt (sSub D2 G) u u2) as Huu2
                by (eapply eq_term_trans;
                    [ apply eq_term_sym; exact Hu | exact Hu2 ]).
            eapply Hcind;
              [ exact HU | exact HU2 | exact HD2 | exact Huu2 | exact Hpda
              | eapply Hdind;
                [ exact HU | exact HU2 | exact HD2 | exact Huu2 | exact Hpda ]
              | exact Hx ]. } } }
      { intros e; split; intro H; exact H. } }
    (* the transfer *)
    { intros e He D2 w2 a HW2 HD2 Hpd u HU Hu.
      assert (Pd D2 u a) as Hpda by (apply Hpd; assumption).
      destruct (Hc D2 u a HU HD2 Hpda) as [C (HTC & HeqC & HRC & _)].
      assert (Hpc := (proj1 (Hiff e) He) D2 u a HU HD2 Hpda).
      destruct (RTy_escape HRC _ Hpc) as [t [Ht1 Ht2]].
      assert (wft e (sElt G oRel lG (oPiRel G rF lF lG F B))) as Hew
          by (eapply appAtRel_wf_e; eapply eqt_wf_l; exact Ht2).
      assert (wft a (sElt D2 rF lF (wkCode D2 G u rF lF F))) as Haw.
      { eapply codAt_wf_a with (rG := oRel) (lG := lG) (B := B);
          [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HU | wfx
          | apply (eqt_wf_l HeqC) ]. }
      assert (wft a (sExp D2 (iEl rF lF)
                (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F1)))) as Haw2.
      { eapply wf_term_conv; [ exact Haw | ].
        unfold sElt; apply eq_sort_exp_ty.
        apply eq_term_sym.
        eapply eq_term_trans;
          [ apply eq_El_subst;
            [ wfx | wfx | apply Wk_wf; exact HW2 | wfx | wfx | wfx ] | ].
        apply El_cong; [ er | er | er | ].
        apply wsc_F1 with (w := w);
          [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
          | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
          | exact HeqF1 ]. }
      eapply (RTy_cand_eq HRC); [ exact Hpc | ].
      eapply eq_term_conv;
        [ apply eq_term_sym;
          apply wpr_app with (w := w);
          [ wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx
          | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
          | wfx | exact HeqF1 | exact HeqB1W | exact HeqB1L
          | exact Hew | exact Haw2 ]
        | apply eq_sort_exp_ty; exact HeqC ]. }

  (* ---- Pi_irr ---- *)
  - intros G rF lF F B P Pd Pc HrF HlF HF HB Hd Hc Hiff D w HW HD.
    assert (EnvOk G) as HGok by (eapply Wk_cod; exact HW).
    destruct (Hd D w HW HD) as [F1 (HF1 & HeqF1 & HR1 & _)].
    destruct (wk_codcodeW HW HD HF HF1 HeqF1 HB)
      as [B1 (HB1 & HeqB1W & HeqB1L)].
    assert (eqt (sTy D (iEl oIrr oL0))
              (oTySubst D G w (iEl oIrr oL0)
                 (oEl G oIrr oL0 (oPiIrr G rF lF F B)))
              (oEl D oIrr oL0 (oPiIrr D rF lF F1 B1))) as HeqPi
        by (apply eq_ElPiIrr_wk;
            [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
            | exact HeqF1 | exact HeqB1L ]).
    assert (forall D2 u1 u2 a, Wk D2 G u1 -> Wk D2 G u2 -> EnvOk D2 ->
              eqt (sSub D2 G) u1 u2 -> Pd D2 u1 a -> Pd D2 u2 a) as Hdind.
    { intros D2 u1 u2 a HU1 HU2 HD2 Hu Ha.
      destruct (Hd D2 u1 HU1 HD2) as [Fa (HFa & HeqFa & HRa & _)].
      destruct (Hd D2 u2 HU2 HD2) as [Fb (HFb & HeqFb & HRb & _)].
      refine (proj1 (RTy_fun_eq HRa HRb _ a) Ha).
      apply El_cong; [ er | er | er | ].
      eapply eq_term_trans; [ apply eq_term_sym; exact HeqFa | ].
      eapply eq_term_trans; [ | exact HeqFb ].
      apply eq_wkCode_cong;
        [ wfx | wfx | apply Wk_wf; exact HU2 | wfx | wfx | wfx | exact Hu ]. }
    assert (forall D2 u1 u2 a x, Wk D2 G u1 -> Wk D2 G u2 -> EnvOk D2 ->
              eqt (sSub D2 G) u1 u2 -> Pd D2 u1 a -> Pd D2 u2 a ->
              Pc D2 u1 a x -> Pc D2 u2 a x) as Hcind.
    { intros D2 u1 u2 a x HU1 HU2 HD2 Hu Ha1 Ha2 Hx.
      destruct (Hc D2 u1 a HU1 HD2 Ha1) as [C1 (HT1 & Heq1 & HRc1 & _)].
      destruct (Hc D2 u2 a HU2 HD2 Ha2) as [C2 (HT2 & Heq2 & HRc2 & _)].
      refine (proj1 (RTy_fun_eq HRc1 HRc2 _ x) Hx).
      assert (wft a (sElt D2 rF lF (wkCode D2 G u2 rF lF F))) as Haw2.
      { eapply codAt_wf_a with (rG := oIrr) (lG := oL0) (B := B);
          [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HU2 | wfx
          | apply (eqt_wf_l Heq2) ]. }
      eapply eq_term_trans; [ apply eq_term_sym; exact Heq1 | ].
      eapply eq_term_trans; [ | exact Heq2 ].
      apply eq_codAt_cong_w with (rG := oIrr);
        [ wfx | wfx | wfx | wfx | apply wf_Irr | apply wf_L0 | wfx | wfx
        | apply Wk_wf; exact HU2 | exact Hu | ].
      eapply wf_term_conv; [ exact Haw2 | ].
      unfold sElt; apply eq_sort_exp_ty.
      apply eq_term_sym; apply eq_El_subst;
        [ wfx | wfx | apply Wk_wf; exact HU2 | wfx | wfx | wfx ]. }
    exists (oEl D oIrr oL0 (oPiIrr D rF lF F1 B1)),
      (fun e => forall D2 w2 a, Wk D2 D w2 -> EnvOk D2 ->
         (forall u, Wk D2 G u ->
            eqt (sSub D2 G) (oCmp D2 D G w2 w) u -> Pd D2 u a) ->
         forall u, Wk D2 G u -> eqt (sSub D2 G) (oCmp D2 D G w2 w) u ->
           Pc D2 u a (appAtIrr D2 D rF lF F1 B1 w2 e a)).
    split; [ apply tyok_El; apply nfcode_pi_irr; assumption | ].
    split; [ exact HeqPi | ].
    split.
    { apply rty_pi_irr
        with (Pd := fun D2 w2 a => forall u, Wk D2 G u ->
                      eqt (sSub D2 G) (oCmp D2 D G w2 w) u -> Pd D2 u a)
             (Pc := fun D2 w2 a x => forall u, Wk D2 G u ->
                      eqt (sSub D2 G) (oCmp D2 D G w2 w) u -> Pc D2 u a x);
        try assumption.
      { intros D2 w2 HW2 HD2.
        destruct (Wk_cmp HW2 HW HD2) as [u [HU Hu]].
        destruct (Hd D2 u HU HD2) as [F2 (HF2 & HeqF2 & HR2 & _)].
        exists F2; split; [ exact HF2 | split ].
        { eapply eq_term_trans; [ | exact HeqF2 ].
          apply wsc_F1 with (w := w);
            [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
            | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
            | exact HeqF1 ]. }
        { eapply RTy_iff; [ exact HR2 | ].
          intro a; split.
          { intro Hh; exact (Hh u HU Hu). }
          { intros Ha u2 HU2 Hu2.
            eapply Hdind;
              [ exact HU | exact HU2 | exact HD2
              | eapply eq_term_trans;
                [ apply eq_term_sym; exact Hu | exact Hu2 ]
              | exact Ha ]. } } }
      { intros D2 w2 a HW2 HD2 Hpd.
        destruct (Wk_cmp HW2 HW HD2) as [u [HU Hu]].
        assert (Pd D2 u a) as Hpda by (apply Hpd; assumption).
        destruct (Hc D2 u a HU HD2 Hpda) as [C (HTC & HeqC & HRC & _)].
        assert (wft a (sElt D2 rF lF (wkCode D2 G u rF lF F))) as Haw.
        { eapply codAt_wf_a with (rG := oIrr) (lG := oL0) (B := B);
            [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HU | wfx
            | apply (eqt_wf_l HeqC) ]. }
        assert (wft a (sExp D2 (iEl rF lF)
                  (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F1)))) as Haw2.
        { eapply wf_term_conv; [ exact Haw | ].
          unfold sElt; apply eq_sort_exp_ty.
          apply eq_term_sym.
          eapply eq_term_trans;
            [ apply eq_El_subst;
              [ wfx | wfx | apply Wk_wf; exact HW2 | wfx | wfx | wfx ] | ].
          apply El_cong; [ er | er | er | ].
          apply wsc_F1 with (w := w);
            [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
            | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
            | exact HeqF1 ]. }
        exists C; split; [ exact HTC | split ].
        { eapply eq_term_trans; [ | exact HeqC ].
          apply wpi_cod with (w := w);
            [ wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx
            | apply Wk_wf; exact HW2 | exact Hu | wfx
            | exact HeqF1 | exact HeqB1W | exact Haw2 ]. }
        { eapply RTy_iff; [ exact HRC | ].
          intro x; split.
          { intro Hh; exact (Hh u HU Hu). }
          { intros Hx u2 HU2 Hu2.
            assert (eqt (sSub D2 G) u u2) as Huu2
                by (eapply eq_term_trans;
                    [ apply eq_term_sym; exact Hu | exact Hu2 ]).
            eapply Hcind;
              [ exact HU | exact HU2 | exact HD2 | exact Huu2 | exact Hpda
              | eapply Hdind;
                [ exact HU | exact HU2 | exact HD2 | exact Huu2 | exact Hpda ]
              | exact Hx ]. } } }
      { intros e; split; intro H; exact H. } }
    (* the transfer *)
    { intros e He D2 w2 a HW2 HD2 Hpd u HU Hu.
      assert (Pd D2 u a) as Hpda by (apply Hpd; assumption).
      destruct (Hc D2 u a HU HD2 Hpda) as [C (HTC & HeqC & HRC & _)].
      assert (Hpc := (proj1 (Hiff e) He) D2 u a HU HD2 Hpda).
      destruct (RTy_escape HRC _ Hpc) as [t [Ht1 Ht2]].
      assert (wft e (sElt G oIrr oL0 (oPiIrr G rF lF F B))) as Hew
          by (eapply appAtIrr_wf_e; eapply eqt_wf_l; exact Ht2).
      assert (wft a (sElt D2 rF lF (wkCode D2 G u rF lF F))) as Haw.
      { eapply codAt_wf_a with (rG := oIrr) (lG := oL0) (B := B);
          [ wfx | wfx | wfx | wfx | apply Wk_wf; exact HU | wfx
          | apply (eqt_wf_l HeqC) ]. }
      assert (wft a (sExp D2 (iEl rF lF)
                (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F1)))) as Haw2.
      { eapply wf_term_conv; [ exact Haw | ].
        unfold sElt; apply eq_sort_exp_ty.
        apply eq_term_sym.
        eapply eq_term_trans;
          [ apply eq_El_subst;
            [ wfx | wfx | apply Wk_wf; exact HW2 | wfx | wfx | wfx ] | ].
        apply El_cong; [ er | er | er | ].
        apply wsc_F1 with (w := w);
          [ wfx | wfx | wfx | wfx | wfx | wfx | wfx
          | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
          | exact HeqF1 ]. }
      eapply (RTy_cand_eq HRC); [ exact Hpc | ].
      eapply eq_term_conv;
        [ apply eq_term_sym;
          apply wpi_app with (w := w);
          [ wfx | wfx | wfx | wfx | wfx | wfx | wfx | wfx
          | apply Wk_wf; exact HW2 | apply Wk_wf; exact HU | exact Hu
          | wfx | exact HeqF1 | exact HeqB1W | exact HeqB1L
          | exact Hew | exact Haw2 ]
        | apply eq_sort_exp_ty; exact HeqC ]. }
Qed.

(* ================================================================== *)
(* C0. Weakening-and-instantiation substitutions                       *)
(*                                                                     *)
(* The code fragment's fundamental lemma cannot be stated for an        *)
(* arbitrary substitution: [rty_var] is a clause about a type named by  *)
(* a code VARIABLE, and a general substitution replaces that variable   *)
(* by an arbitrary code.  What the Pi clause actually needs is much     *)
(* smaller -- a weakening, extended by instantiations at the binders of *)
(* the code grammar -- and every such binder extends the environment by *)
(* an [El] type, never by a universe.  So a code variable's slot is     *)
(* only ever weakened, and code variables travel to code variables      *)
(* ([WIS_var] below).                                                   *)
(* ================================================================== *)

Inductive WIS : term -> term -> term -> Prop :=
| wis_wk : forall D G w, Wk D G w -> WIS D G w
| wis_conv : forall D G g g',
    WIS D G g -> wft g' (sSub D G) -> eqt (sSub D G) g' g -> WIS D G g'
| wis_snoc : forall D G rF lF F F' g v,
    WIS D G g -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (wkCode D G g rF lF F) F' ->
    wft v (sElt D rF lF F') ->
    WIS D (oExtC G rF lF F)
        (oSnoc D G (iEl rF lF) (oEl G rF lF F) g v).

Lemma WIS_dom D G g : WIS D G g -> EnvOk D.
Proof. induction 1; [ eapply Wk_dom; eassumption | assumption | assumption ]. Qed.

Lemma WIS_cod D G g : WIS D G g -> EnvOk G.
Proof.
  induction 1;
    [ eapply Wk_cod; eassumption | assumption
    | unfold oExtC; apply envok_ext;
      [ eapply NfCode_EnvOk; eassumption | apply tyok_El; assumption ] ].
Qed.

Lemma WIS_CSub D G g : WIS D G g -> CSub D G g.
Proof.
  induction 1 as
    [ D G w HW | D G g g' Hg IH Hwf Heq
    | D G rF lF F F' g v Hg IH HDok HF HF' HeqF Hv ].
  - apply csub_wk; assumption.
  - eapply csub_conv; eassumption.
  - assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
    assert (wft g (sSub D G)) as Hgw by (apply CSub_wf; exact IH).
    unfold oExtC; apply csub_snoc with (A' := oEl D rF lF F');
      [ exact IH | exact HDok | apply tyok_El; exact HF
      | apply tyok_El; exact HF' | | exact Hv | ].
    + eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF ].
    + intros r l Habs; unfold oEl, oU in Habs; discriminate.
Qed.

Lemma WIS_wf D G g : WIS D G g -> wft g (sSub D G).
Proof. intro H; apply CSub_wf; apply WIS_CSub; exact H. Qed.

(* [WIS] is closed under precomposition with a weakening -- which is what
   the Kripke quantifier of the Pi clause consumes. *)
Lemma WIS_cmp_Wk D2 D G w2 g
  : Wk D2 D w2 -> WIS D G g -> EnvOk D2 ->
    exists g', WIS D2 G g' /\ eqt (sSub D2 G) (oCmp D2 D G w2 g) g'.
Proof.
  intros HW2 HWIS; revert D2 w2 HW2.
  induction HWIS as
    [ D G w HW | D G g g' Hg IH Hwf Heq
    | D G rF lF F F' g v Hg IH HDok HF HF' HeqF Hv ];
    intros D2 w2 HW2 HD2.
  - destruct (Wk_cmp HW2 HW HD2) as [w'' [HW'' Hcmp]].
    exists w''; split; [ apply wis_wk; exact HW'' | exact Hcmp ].
  - destruct (IH D2 w2 HW2 HD2) as [g'' [Hg'' Hcmp]].
    exists g''; split; [ exact Hg'' | ].
    eapply eq_term_trans; [ | exact Hcmp ].
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    apply Cmp_cong
      with (X1 := D2) (Y1 := D2) (X2 := D) (Y2 := D) (X3 := G) (Y3 := G)
           (f1 := w2) (f2 := w2) (g1 := g') (g2 := g);
      [ er | er | er | er | exact Heq ].
  - assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    assert (wft w2 (sSub D2 D)) as Hw2w by (apply Wk_wf; exact HW2).
    destruct (IH D2 w2 HW2 HD2) as [g' [Hg' Hcmp]].
    assert (wft g' (sSub D2 G)) as Hg'w by (apply WIS_wf; exact Hg').
    destruct (NfCode_wk HF' HW2 HD2) as [F'' [HF'' HeqF'']].
    assert (eqt (sCode D2 rF lF) (wkCode D2 G g' rF lF F) F'') as HeqFn.
    { eapply eq_term_trans; [ apply eq_term_sym | exact HeqF'' ].
      apply wsc_F1 with (w := g);
        [ wfx | wfx | wfx | wfx | wfx | wfx | exact Hgw | exact Hw2w
        | exact Hg'w | exact Hcmp | exact HeqF ]. }
    assert (eqt (sTy D (iEl rF lF))
              (oTySubst D G g (iEl rF lF) (oEl G rF lF F))
              (oEl D rF lF F')) as HeqEl.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF ]. }
    assert (wft (oExpSubst D2 D w2 (iEl rF lF) (oEl D rF lF F') v)
              (sElt D2 rF lF F'')) as Hvw2.
    { eapply wf_term_conv;
        [ apply wf_ExpSubst;
          [ wfx | wfx | exact Hw2w | wfx | wfx | exact Hv ] | ].
      unfold sElt; apply eq_sort_exp_ty.
      eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF'' ]. }
    exists (oSnoc D2 G (iEl rF lF) (oEl G rF lF F) g'
              (oExpSubst D2 D w2 (iEl rF lF) (oEl D rF lF F') v)).
    split.
    { apply wis_snoc with (F' := F'');
        [ exact Hg' | exact HD2 | exact HF | exact HF'' | exact HeqFn
        | exact Hvw2 ]. }
    { eapply eq_term_trans.
      { apply eq_cmp_snoc with (G1 := D2) (G2 := D) (G3 := G)
          (f := w2) (g := g) (i := iEl rF lF) (A := oEl G rF lF F) (v := v);
          [ wfx | wfx | wfx | exact Hw2w | exact Hgw | wfx | wfx | ].
        eapply wf_term_conv; [ exact Hv | ].
        unfold sElt; apply eq_sort_exp_ty; apply eq_term_sym; exact HeqEl. }
      unfold oExtC; apply Snoc_cong;
        [ er | er | er | er | exact Hcmp | ].
      eapply eq_term_conv;
        [ | apply eq_sort_exp_ty; apply wsc_Aty with (w := g);
              [ wfx | wfx | wfx | wfx | wfx | wfx | exact Hgw | exact Hw2w
              | exact Hcmp | exact HeqF ] ].
      apply ExpSubst_cong
        with (G1 := D2) (G2 := D2) (G1' := D) (G2' := D)
             (g1 := w2) (g2 := w2)
             (i1 := iEl rF lF) (i2 := iEl rF lF)
             (A1 := oTySubst D G g (iEl rF lF) (oEl G rF lF F))
             (A2 := oEl D rF lF F') (v1 := v) (v2 := v);
        [ er | er | er | er | exact HeqEl | apply eq_term_refl; exact Hv ]. }
Qed.

(* [WIS] is closed under going under a binder of the code grammar. *)
Lemma WIS_liftC D G g rF lF F F'
  : WIS D G g -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (wkCode D G g rF lF F) F' ->
    WIS (oExtC D rF lF F') (oExtC G rF lF F)
        (oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')).
Proof.
  intros HWIS HDok HF HF' HeqF.
  assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
  assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact HWIS).
  assert (TyOk D (iEl rF lF) (oEl D rF lF F')) as HTA'
      by (apply tyok_El; exact HF').
  assert (EnvOk (oExt D (iEl rF lF) (oEl D rF lF F'))) as HEok
      by (apply envok_ext; assumption).
  destruct (NfCode_wkn HDok HTA' HF') as [F'' [HF'' HeqF'']].
  destruct (WIS_cmp_Wk (wk_wkn HDok HTA') HWIS HEok) as [g'' [Hg'' Hcmp'']].
  assert (wft (oWkn D (iEl rF lF) (oEl D rF lF F'))
            (sSub (oExt D (iEl rF lF) (oEl D rF lF F')) D)) as Hwkn by wfx.
  assert (WIS (oExt D (iEl rF lF) (oEl D rF lF F')) G
            (oCmp (oExt D (iEl rF lF) (oEl D rF lF F')) D G
               (oWkn D (iEl rF lF) (oEl D rF lF F')) g)) as Hcw
      by (eapply wis_conv; [ exact Hg'' | wfx | exact Hcmp'' ]).
  unfold oLiftW, oExtC.
  apply wis_snoc with (F' := F'');
    [ exact Hcw | exact HEok | exact HF | exact HF'' | | ].
  - eapply eq_term_trans; [ apply eq_term_sym | exact HeqF'' ].
    apply wsc_F1 with (w := g);
      [ wfx | wfx | wfx | wfx | wfx | wfx | exact Hgw | exact Hwkn
      | wfx | apply eq_term_refl; wfx | exact HeqF ].
  - eapply wf_term_conv; [ apply wf_Hd; wfx | ].
    unfold sElt; apply eq_sort_exp_ty.
    eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
    apply El_cong; [ er | er | er | exact HeqF'' ].
Qed.

(* [VarT_inv] keeping the clause's own type equation. *)
Lemma VarT_inv' GG i AA x
  : VarT GG i AA x ->
    (exists G A, GG = oExt G i A /\ x = oHd G i A
                 /\ TyOk G i A /\ TyOk (oExt G i A) i AA
                 /\ eqt (sTy (oExt G i A) i)
                        (oTySubst (oExt G i A) G (oWkn G i A) i A) AA)
    \/ (exists G j B A x0,
           GG = oExt G j B
           /\ x = oExpSubst (oExt G j B) G (oWkn G j B) i A x0
           /\ VarT G i A x0 /\ TyOk G j B /\ TyOk (oExt G j B) i AA
           /\ eqt (sTy (oExt G j B) i)
                  (oTySubst (oExt G j B) G (oWkn G j B) i A) AA).
Proof.
  destruct 1 as [ G i A A' HG HA HA' Heq | G i A x j B A' Hx HB HA' Heq ].
  - left; exists G, A; repeat split; assumption.
  - right; exists G, j, B, A, x; repeat split; assumption.
Qed.

(* THE point of [WIS]: a code variable travels to a code variable. *)
Lemma WIS_var D G g : WIS D G g ->
  forall r l c, VarT G (iCode l) (oU G r l) c ->
    exists x', VarT D (iCode l) (oU D r l) x'
            /\ eqt (sCode D r l)
                 (oExpSubst D G g (iCode l) (oU G r l) c) x'.
Proof.
  induction 1 as
    [ D G w HW | D G g g' Hg IH Hwf Heq
    | D G rF lF F F' g v Hg IH HDok HF HF' HeqF Hv ];
    intros r l c Hc.
  - (* a weakening *)
    assert (EnvOk D) as HDok by (eapply Wk_dom; exact HW).
    assert (TyOk G (iCode l) (oU G r l)) as HTU by (eapply VarT_TyOk; exact Hc).
    assert (RelNf r) as Hr by (apply (proj1 (TyOk_U_inv HTU))).
    assert (LvlNf l) as Hl by (apply (proj2 (TyOk_U_inv HTU))).
    destruct (VarT_wk Hc HW HDok) as [A2 [x' [HT2 [HeqA2 [Hx' Heqx']]]]].
    assert (A2 = oU D r l) as ->.
    { eapply TyOk_inj;
        [ exact HT2 | apply tyok_U; assumption
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact HeqA2 | apply eq_U_subst; wfx ] ]. }
    exists x'; split; [ exact Hx' | exact Heqx' ].
  - (* a conversion *)
    destruct (IH r l c Hc) as [x' [Hx' Heqx']].
    exists x'; split; [ exact Hx' | ].
    eapply eq_term_trans; [ | exact Heqx' ].
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    assert (EnvOk G) as HGok by (eapply VarT_EnvOk; exact Hc).
    eapply eqt_Usub_c with (G' := G) (g := g) (r := r) (l := l);
      [ wfx | wfx | exact Hgw | wfx | wfx | ].
    apply ExpSubst_cong
      with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := g') (g2 := g)
           (i1 := iCode l) (i2 := iCode l)
           (A1 := oU G r l) (A2 := oU G r l) (v1 := c) (v2 := c);
      [ er | er | exact Heq | er | er | er ].
  - (* an instantiation at an El-typed slot *)
    assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    assert (eqt (sTy D (iEl rF lF))
              (oTySubst D G g (iEl rF lF) (oEl G rF lF F))
              (oEl D rF lF F')) as HeqEl.
    { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact HeqF ]. }
    assert (wft v (sExp D (iEl rF lF)
              (oTySubst D G g (iEl rF lF) (oEl G rF lF F)))) as Hvg.
    { eapply wf_term_conv; [ exact Hv | ].
      unfold sElt; apply eq_sort_exp_ty; apply eq_term_sym; exact HeqEl. }
    assert (wft (oSnoc D G (iEl rF lF) (oEl G rF lF F) g v)
              (sSub D (oExt G (iEl rF lF) (oEl G rF lF F)))) as Hsg
        by (apply wf_Snoc; [ wfx | wfx | wfx | wfx | exact Hgw | exact Hvg ]).
    apply VarT_inv' in Hc.
    destruct Hc as
      [ [G1 [A1 [HGG [Hx [HT1 [HT2 Hq]]]]]]
      | [G1 [j [B1 [A0 [y [HGG [Hx [Hy [HTB [HTA Hq]]]]]]]]]] ].
    + exfalso; unfold oExtC, oExt in HGG; safe_invert HGG;
        unfold iEl, iCode, oInfo, oIota, oNext in *; congruence.
    + unfold oExtC, oExt in HGG; safe_invert HGG.
      assert (A0 = oU G1 r l) as -> by (eapply WknU_shape; [ eapply VarT_TyOk; exact Hy | exact Hq ]).
      destruct (IH r l y Hy) as [x' [Hx' Heqx']].
      exists x'; split; [ exact Hx' | ].
      try subst c.
      eapply eq_term_trans; [ | exact Heqx' ].
      assert (eqt (sTy D (iCode l))
                (oTySubst D (oExt G1 (iEl rF lF) (oEl G1 rF lF F))
                   (oSnoc D G1 (iEl rF lF) (oEl G1 rF lF F) g v) (iCode l)
                   (oTySubst (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) G1
                      (oWkn G1 (iEl rF lF) (oEl G1 rF lF F)) (iCode l)
                      (oU G1 r l)))
                (oU D r l)) as HS1.
      { eapply eq_term_trans.
        - apply TySubst_cong
            with (G1 := D) (G2 := D)
                 (G1' := oExt G1 (iEl rF lF) (oEl G1 rF lF F))
                 (G2' := oExt G1 (iEl rF lF) (oEl G1 rF lF F))
                 (g1 := oSnoc D G1 (iEl rF lF) (oEl G1 rF lF F) g v)
                 (g2 := oSnoc D G1 (iEl rF lF) (oEl G1 rF lF F) g v)
                 (i1 := iCode l) (i2 := iCode l)
                 (A1 := oTySubst (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) G1
                          (oWkn G1 (iEl rF lF) (oEl G1 rF lF F)) (iCode l)
                          (oU G1 r l))
                 (A2 := oU (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) r l);
            [ er | er | apply eq_term_refl; exact Hsg | er
            | apply eq_U_subst; wfx ].
        - apply eq_U_subst; [ wfx | wfx | exact Hsg | wfx | wfx ]. }
      eapply eq_term_trans.
      { eapply eq_term_conv;
          [ | apply eq_sort_exp_ty; exact HS1 ].
        eapply eq_term_trans.
        - apply ExpSubst_cong
            with (G1 := D) (G2 := D)
                 (G1' := oExt G1 (iEl rF lF) (oEl G1 rF lF F))
                 (G2' := oExt G1 (iEl rF lF) (oEl G1 rF lF F))
                 (g1 := oSnoc D G1 (iEl rF lF) (oEl G1 rF lF F) g v)
                 (g2 := oSnoc D G1 (iEl rF lF) (oEl G1 rF lF F) g v)
                 (i1 := iCode l) (i2 := iCode l)
                 (A1 := oU (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) r l)
                 (A2 := oTySubst (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) G1
                          (oWkn G1 (iEl rF lF) (oEl G1 rF lF F))
                          (iCode l) (oU G1 r l))
                 (v1 := oExpSubst (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) G1
                          (oWkn G1 (iEl rF lF) (oEl G1 rF lF F))
                          (iCode l) (oU G1 r l) y)
                 (v2 := oExpSubst (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) G1
                          (oWkn G1 (iEl rF lF) (oEl G1 rF lF F))
                          (iCode l) (oU G1 r l) y);
            [ er | er | er | er
            | apply eq_term_sym; apply eq_U_subst; wfx
            | apply eq_term_refl; apply wf_ExpSubst; wfx ].
        - apply eq_exp_subst_cmp
            with (G1 := D) (G2 := oExt G1 (iEl rF lF) (oEl G1 rF lF F))
                 (G3 := G1)
                 (f := oSnoc D G1 (iEl rF lF) (oEl G1 rF lF F) g v)
                 (g := oWkn G1 (iEl rF lF) (oEl G1 rF lF F))
                 (i := iCode l) (A := oU G1 r l) (v := y);
            [ wfx | wfx | wfx | exact Hsg | wfx | wfx | wfx
            | apply VarT_wf; exact Hy ]. }
      eapply eqt_Usub_c with (G' := G1) (g := g) (r := r) (l := l);
        [ wfx | wfx | exact Hgw | wfx | wfx | ].
      apply ExpSubst_cong
        with (G1 := D) (G2 := D) (G1' := G1) (G2' := G1)
             (g1 := oCmp D (oExt G1 (iEl rF lF) (oEl G1 rF lF F)) G1
                      (oSnoc D G1 (iEl rF lF) (oEl G1 rF lF F) g v)
                      (oWkn G1 (iEl rF lF) (oEl G1 rF lF F)))
             (g2 := g) (i1 := iCode l) (i2 := iCode l)
             (A1 := oU G1 r l) (A2 := oU G1 r l) (v1 := y) (v2 := y);
        [ er | er
        | apply eq_wkn_snoc;
          [ wfx | wfx | exact Hgw | wfx | wfx | exact Hvg ]
        | er | er | apply eq_term_refl; apply VarT_wf; exact Hy ].
Qed.

(* The codomain code under a [WIS], in both spellings of the lift. *)
Lemma wis_codcode D G g rF lF rG lG F B F'
  : WIS D G g -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (wkCode D G g rF lF F) F' ->
    NfCode (oExtC G rF lF F) rG lG B ->
    exists B', NfCode (oExtC D rF lF F') rG lG B'
            /\ eqt (sCode (oExtC D rF lF F') rG lG)
                 (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
                    (oLiftW D G g (iEl rF lF) (oEl G rF lF F)
                       (oEl D rF lF F')) (iCode lG)
                    (oU (oExtC G rF lF F) rG lG) B) B'
            /\ eqt (sCode (oExtC D rF lF F') rG lG)
                 (oExpSubst (oExtC D rF lF (wkCode D G g rF lF F))
                    (oExtC G rF lF F) (oLift D G g rF lF F) (iCode lG)
                    (oU (oExtC G rF lF F) rG lG) B) B'.
Proof.
  intros HWIS HD HF HF' HeqF HB.
  assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
  assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact HWIS).
  assert (EnvOk (oExtC D rF lF F')) as HD2
      by (unfold oExtC; apply envok_ext; [ exact HD | apply tyok_El; exact HF' ]).
  destruct (NfCode_csubst HB (WIS_CSub (WIS_liftC HWIS HD HF HF' HeqF)) HD2)
    as [B' [HB' HeqB']].
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G g (iEl rF lF) (oEl G rF lF F))
            (oEl D rF lF F')) as HeqEl.
  { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
    apply El_cong; [ er | er | er | exact HeqF ]. }
  exists B'; split; [ exact HB' | split; [ exact HeqB' | ] ].
  eapply eq_term_trans; [ | exact HeqB' ].
  eapply eqt_Usub_c
    with (G' := oExtC G rF lF F)
         (g := oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         (r := rG) (l := lG);
    [ wfx | wfx | apply wf_liftW; wfx | wfx | wfx | ].
  apply eq_lift_shift';
    [ wfx | wfx | exact Hgw | exact HF | exact HF' | exact HeqF
    | wfx | wfx | wfx ].
Qed.

(* The domain datum at a further weakening: the normal code, the composed
   substitution, and the reducibility the induction hypothesis supplies. *)
Lemma wis_dom_step G rF lF F
  (IHF : forall D0 g0, WIS D0 G g0 -> EnvOk D0 ->
           forall F0, NfCode D0 rF lF F0 ->
             eqt (sCode D0 rF lF) (wkCode D0 G g0 rF lF F) F0 ->
             exists P, RTy D0 (iEl rF lF) (oEl D0 rF lF F0) P)
  D g F1 D2 w2
  : WIS D G g -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F1 ->
    eqt (sCode D rF lF) (wkCode D G g rF lF F) F1 ->
    Wk D2 D w2 -> EnvOk D2 ->
    exists F2 g2 P0,
      NfCode D2 rF lF F2
      /\ eqt (sCode D2 rF lF) (wkCode D2 D w2 rF lF F1) F2
      /\ WIS D2 G g2
      /\ eqt (sSub D2 G) (oCmp D2 D G w2 g) g2
      /\ eqt (sCode D2 rF lF) (wkCode D2 G g2 rF lF F) F2
      /\ RTy D2 (iEl rF lF) (oEl D2 rF lF F2) P0.
Proof.
  intros HWIS HD HF HF1 HeqF1 HW2 HD2.
  assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
  assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact HWIS).
  destruct (NfCode_wk HF1 HW2 HD2) as [F2 [HF2 HeqF2]].
  destruct (WIS_cmp_Wk HW2 HWIS HD2) as [g2 [Hg2 Hcmp]].
  assert (wft g2 (sSub D2 G)) as Hg2w by (apply WIS_wf; exact Hg2).
  assert (eqt (sCode D2 rF lF) (wkCode D2 G g2 rF lF F) F2) as HeqFn.
  { eapply eq_term_trans; [ apply eq_term_sym | exact HeqF2 ].
    apply wsc_F1 with (w := g);
      [ wfx | wfx | wfx | wfx | wfx | wfx | exact Hgw | apply Wk_wf; exact HW2
      | exact Hg2w | exact Hcmp | exact HeqF1 ]. }
  destruct (IHF D2 g2 Hg2 HD2 F2 HF2 HeqFn) as [P0 HR0].
  exists F2, g2, P0; repeat split; assumption.
Qed.

(* ================================================================== *)
(* C. EVERY NORMAL CODE NAMES A REDUCIBLE TYPE                         *)
(*                                                                     *)
(* Generalised over [WIS] substitutions, because the Pi clause's        *)
(* codomain has to be reducible not merely weakened but INSTANTIATED at *)
(* every reducible argument.  This is where the termination content     *)
(* sits: the Pi case consumes [NfCode_csubst] at the substitution built *)
(* from the weakening and the argument, and the argument's normal form  *)
(* comes from part A's escape.                                          *)
(* ================================================================== *)

Theorem RTyEx_str :
  (forall G, EnvOk G -> True)
  /\ (forall G i A, TyOk G i A ->
        forall D g, WIS D G g -> EnvOk D ->
          forall A', TyOk D i A' ->
            eqt (sTy D i) (oTySubst D G g i A) A' ->
            exists P, RTy D i A' P)
  /\ (forall G r l c, NfCode G r l c ->
        forall D g, WIS D G g -> EnvOk D ->
          forall c', NfCode D r l c' ->
            eqt (sCode D r l) (oExpSubst D G g (iCode l) (oU G r l) c) c' ->
            exists P, RTy D (iEl r l) (oEl D r l c') P)
  /\ (forall G i A x, VarT G i A x -> True)
  /\ (forall G i A e, NeET G i A e -> True)
  /\ (forall G i A e, NfET G i A e -> True).
Proof.
  apply Nf_mutind.
  - exact I.
  - intros; exact I.

  (* ---- TyOk: a universe ---- *)
  - intros G r l HG _ Hr Hl D g Hg HD A' HTA' HeqA'.
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    assert (A' = oU D r l) as ->.
    { eapply TyOk_inj;
        [ exact HTA' | apply tyok_U; assumption
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact HeqA' | apply eq_U_subst; wfx ] ]. }
    exists (HasNfCode D r l); apply RTy_U_i; assumption.

  (* ---- TyOk: an El ---- *)
  - intros G r l c Hc IHc D g Hg HD A' HTA' HeqA'.
    assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact Hc).
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    destruct (NfCode_csubst Hc (WIS_CSub Hg) HD) as [c1 [Hc1 Heqc1]].
    assert (A' = oEl D r l c1) as ->.
    { eapply TyOk_inj;
        [ exact HTA' | apply tyok_El; exact Hc1
        | eapply eq_term_trans; [ apply eq_term_sym; exact HeqA' | ] ].
      eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
      apply El_cong; [ er | er | er | exact Heqc1 ]. }
    exact (IHc D g Hg HD c1 Hc1 Heqc1).

  (* ---- Nat ---- *)
  - intros G HG _ D g Hg HD c' Hc' Heqc'.
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    assert (c' = oNat D) as ->.
    { eapply NfCode_inj;
        [ exact Hc' | apply nfcode_nat; exact HD
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact Heqc' | apply eq_Nat_subst'; wfx ] ]. }
    exists (HasNf D (iEl oRel oL0) (oEl D oRel oL0 (oNat D)));
      apply RTy_nat_i; exact HD.

  (* ---- Empty ---- *)
  - intros G HG _ D g Hg HD c' Hc' Heqc'.
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    assert (c' = oEmpty D) as ->.
    { eapply NfCode_inj;
        [ exact Hc' | apply nfcode_empty; exact HD
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact Heqc' | apply eq_Empty_subst; wfx ] ]. }
    exists (HasNe D (iEl oIrr oL0) (oEl D oIrr oL0 (oEmpty D)));
      apply RTy_empty_i; exact HD.

  (* ---- Pi_rel ---- *)
  - intros G rF lF lG F B HrF HlF HlG HF IHF HB IHB D g Hg HD c' Hc' Heqc'.
    assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    destruct (NfCode_csubst HF (WIS_CSub Hg) HD) as [F1 [HF1 HeqF1]].
    destruct (wis_codcode Hg HD HF HF1 HeqF1 HB)
      as [B1 (HB1 & HeqB1W & HeqB1L)].
    assert (c' = oPiRel D rF lF lG F1 B1) as ->.
    { eapply NfCode_inj;
        [ exact Hc' | apply nfcode_pi_rel; assumption
        | eapply eq_term_trans; [ apply eq_term_sym; exact Heqc' | ] ].
      eapply eq_term_trans; [ apply eq_Pi_rel_subst; wfx | ].
      apply PiRel_cong; [ er | er | er | er | exact HeqF1 | exact HeqB1L ]. }
    exists (fun e => forall D2 w2 a, Wk D2 D w2 -> EnvOk D2 ->
              (forall F2, NfCode D2 rF lF F2 ->
                 eqt (sCode D2 rF lF) (wkCode D2 D w2 rF lF F1) F2 ->
                 RTm D2 (iEl rF lF) (oEl D2 rF lF F2) a) ->
              forall C, TyOk D2 (iEl oRel lG) C ->
                eqt (sTy D2 (iEl oRel lG))
                    (codAtRel D2 D rF lF lG F1 B1 w2 a) C ->
                RTm D2 (iEl oRel lG) C
                    (appAtRel D2 D rF lF lG F1 B1 w2 e a)).
    apply rty_pi_rel
      with (Pd := fun D2 w2 a => forall F2, NfCode D2 rF lF F2 ->
                    eqt (sCode D2 rF lF) (wkCode D2 D w2 rF lF F1) F2 ->
                    RTm D2 (iEl rF lF) (oEl D2 rF lF F2) a)
           (Pc := fun D2 w2 a x => forall C, TyOk D2 (iEl oRel lG) C ->
                    eqt (sTy D2 (iEl oRel lG))
                        (codAtRel D2 D rF lF lG F1 B1 w2 a) C ->
                    RTm D2 (iEl oRel lG) C x);
      [ exact HrF | exact HlF | exact HlG | exact HF1 | exact HB1 | | | ].
    (* the domain *)
    { intros D2 w2 HW2 HD2.
      destruct (wis_dom_step IHF Hg HD HF HF1 HeqF1 HW2 HD2)
        as [F2 [g2 [P0 (HF2 & HeqF2 & Hg2 & Hcmp & HeqFn & HR0)]]].
      exists F2; split; [ exact HF2 | split; [ exact HeqF2 | ] ].
      eapply RTy_iff; [ exact HR0 | ].
      intro a; split.
      { intro Hh; eapply RTm_elim; [ exact HR0 | exact (Hh F2 HF2 HeqF2) ]. }
      { intros Ha F2' HF2' HeqF2'.
        assert (F2' = F2) as ->.
        { eapply NfCode_inj;
            [ exact HF2' | exact HF2
            | eapply eq_term_trans;
              [ apply eq_term_sym; exact HeqF2' | exact HeqF2 ] ]. }
        eapply RTm_intro; [ exact HR0 | exact Ha ]. } }
    (* the codomain *)
    { intros D2 w2 a HW2 HD2 Hpd.
      destruct (wis_dom_step IHF Hg HD HF HF1 HeqF1 HW2 HD2)
        as [F2 [g2 [P0 (HF2 & HeqF2 & Hg2 & Hcmp & HeqFn & HR0)]]].
      assert (wft a (sElt D2 rF lF F2)) as Haw.
      { destruct (RTy_escape HR0 _ (RTm_elim HR0 (Hpd F2 HF2 HeqF2)))
          as [n [_ Hn]].
        eapply eqt_wf_l; exact Hn. }
      assert (wft g2 (sSub D2 G)) as Hg2w by (apply WIS_wf; exact Hg2).
      assert (WIS D2 (oExtC G rF lF F)
                (oSnoc D2 G (iEl rF lF) (oEl G rF lF F) g2 a)) as Hsig
          by (apply wis_snoc with (F' := F2);
              [ exact Hg2 | exact HD2 | exact HF | exact HF2 | exact HeqFn
              | exact Haw ]).
      assert (wft (oSnoc D2 G (iEl rF lF) (oEl G rF lF F) g2 a)
                (sSub D2 (oExtC G rF lF F))) as Hsigw
          by (apply WIS_wf; exact Hsig).
      destruct (NfCode_csubst HB (WIS_CSub Hsig) HD2) as [B0 [HB0 HeqB0]].
      assert (wft a (sExp D2 (iEl rF lF)
                (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F1)))) as Haw2.
      { eapply wf_term_conv; [ exact Haw | ].
        unfold sElt; apply eq_sort_exp_ty.
        apply eq_term_sym.
        eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
        apply El_cong; [ er | er | er | exact HeqF2 ]. }
      assert (eqt (sTy D2 (iEl oRel lG))
                (codAtRel D2 D rF lF lG F1 B1 w2 a)
                (oEl D2 oRel lG B0)) as HeqCod.
      { eapply eq_term_trans.
        { apply wsc_cod with (w := g) (rG := oRel) (G := G) (F := F) (B := B)
            (w'' := g2);
            [ wfx | wfx | wfx | wfx | wfx | apply wf_Rel | wfx | wfx | wfx
            | exact Hgw | apply Wk_wf; exact HW2 | exact Hcmp | wfx
            | exact HeqF1 | exact HeqB1W | exact Haw2 ]. }
        eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
        apply El_cong; [ er | er | er | exact HeqB0 ]. }
      exists (oEl D2 oRel lG B0).
      split; [ apply tyok_El; exact HB0 | split; [ exact HeqCod | ] ].
      destruct (IHB D2 _ Hsig HD2 B0 HB0 HeqB0) as [P0' HR0'].
      eapply RTy_iff; [ exact HR0' | ].
      intro x; split.
      { intro Hh; eapply RTm_elim;
          [ exact HR0'
          | exact (Hh (oEl D2 oRel lG B0) (tyok_El HB0) HeqCod) ]. }
      { intros Hx C HTC HeqC.
        assert (C = oEl D2 oRel lG B0) as ->.
        { eapply TyOk_inj;
            [ exact HTC | apply tyok_El; exact HB0
            | eapply eq_term_trans;
              [ apply eq_term_sym; exact HeqC | exact HeqCod ] ]. }
        eapply RTm_intro; [ exact HR0' | exact Hx ]. } }
    { intros e; split; intro H; exact H. }

  (* ---- Pi_irr ---- *)
  - intros G rF lF F B HrF HlF HF IHF HB IHB D g Hg HD c' Hc' Heqc'.
    assert (EnvOk G) as HGok by (eapply NfCode_EnvOk; exact HF).
    assert (wft g (sSub D G)) as Hgw by (apply WIS_wf; exact Hg).
    destruct (NfCode_csubst HF (WIS_CSub Hg) HD) as [F1 [HF1 HeqF1]].
    destruct (wis_codcode Hg HD HF HF1 HeqF1 HB)
      as [B1 (HB1 & HeqB1W & HeqB1L)].
    assert (EnvOk (oExtC D rF lF F1)) as HDF1
        by (unfold oExtC; apply envok_ext;
            [ exact HD | apply tyok_El; exact HF1 ]).
    assert (c' = oPiIrr D rF lF F1 B1) as ->.
    { eapply NfCode_inj;
        [ exact Hc' | apply nfcode_pi_irr; assumption
        | eapply eq_term_trans; [ apply eq_term_sym; exact Heqc' | ] ].
      eapply eq_term_trans; [ apply eq_Pi_irr_subst'; wfx | ].
      apply eqt_i2c; [ wfx | apply wf_Irr | ].
      apply PiIrr_cong;
        [ er | er | er | exact HeqF1
        | apply eqt_c2i; [ wfx | apply wf_Irr | exact HeqB1L ] ]. }
    exists (fun e => forall D2 w2 a, Wk D2 D w2 -> EnvOk D2 ->
              (forall F2, NfCode D2 rF lF F2 ->
                 eqt (sCode D2 rF lF) (wkCode D2 D w2 rF lF F1) F2 ->
                 RTm D2 (iEl rF lF) (oEl D2 rF lF F2) a) ->
              forall C, TyOk D2 (iEl oIrr oL0) C ->
                eqt (sTy D2 (iEl oIrr oL0))
                    (codAtIrr D2 D rF lF F1 B1 w2 a) C ->
                RTm D2 (iEl oIrr oL0) C
                    (appAtIrr D2 D rF lF F1 B1 w2 e a)).
    apply rty_pi_irr
      with (Pd := fun D2 w2 a => forall F2, NfCode D2 rF lF F2 ->
                    eqt (sCode D2 rF lF) (wkCode D2 D w2 rF lF F1) F2 ->
                    RTm D2 (iEl rF lF) (oEl D2 rF lF F2) a)
           (Pc := fun D2 w2 a x => forall C, TyOk D2 (iEl oIrr oL0) C ->
                    eqt (sTy D2 (iEl oIrr oL0))
                        (codAtIrr D2 D rF lF F1 B1 w2 a) C ->
                    RTm D2 (iEl oIrr oL0) C x);
      [ exact HrF | exact HlF | exact HF1 | exact HB1 | | | ].
    { intros D2 w2 HW2 HD2.
      destruct (wis_dom_step IHF Hg HD HF HF1 HeqF1 HW2 HD2)
        as [F2 [g2 [P0 (HF2 & HeqF2 & Hg2 & Hcmp & HeqFn & HR0)]]].
      exists F2; split; [ exact HF2 | split; [ exact HeqF2 | ] ].
      eapply RTy_iff; [ exact HR0 | ].
      intro a; split.
      { intro Hh; eapply RTm_elim; [ exact HR0 | exact (Hh F2 HF2 HeqF2) ]. }
      { intros Ha F2' HF2' HeqF2'.
        assert (F2' = F2) as ->.
        { eapply NfCode_inj;
            [ exact HF2' | exact HF2
            | eapply eq_term_trans;
              [ apply eq_term_sym; exact HeqF2' | exact HeqF2 ] ]. }
        eapply RTm_intro; [ exact HR0 | exact Ha ]. } }
    { intros D2 w2 a HW2 HD2 Hpd.
      destruct (wis_dom_step IHF Hg HD HF HF1 HeqF1 HW2 HD2)
        as [F2 [g2 [P0 (HF2 & HeqF2 & Hg2 & Hcmp & HeqFn & HR0)]]].
      assert (wft a (sElt D2 rF lF F2)) as Haw.
      { destruct (RTy_escape HR0 _ (RTm_elim HR0 (Hpd F2 HF2 HeqF2)))
          as [n [_ Hn]].
        eapply eqt_wf_l; exact Hn. }
      assert (wft g2 (sSub D2 G)) as Hg2w by (apply WIS_wf; exact Hg2).
      assert (WIS D2 (oExtC G rF lF F)
                (oSnoc D2 G (iEl rF lF) (oEl G rF lF F) g2 a)) as Hsig
          by (apply wis_snoc with (F' := F2);
              [ exact Hg2 | exact HD2 | exact HF | exact HF2 | exact HeqFn
              | exact Haw ]).
      assert (wft (oSnoc D2 G (iEl rF lF) (oEl G rF lF F) g2 a)
                (sSub D2 (oExtC G rF lF F))) as Hsigw
          by (apply WIS_wf; exact Hsig).
      destruct (NfCode_csubst HB (WIS_CSub Hsig) HD2) as [B0 [HB0 HeqB0]].
      assert (wft a (sExp D2 (iEl rF lF)
                (oTySubst D2 D w2 (iEl rF lF) (oEl D rF lF F1)))) as Haw2.
      { eapply wf_term_conv; [ exact Haw | ].
        unfold sElt; apply eq_sort_exp_ty.
        apply eq_term_sym.
        eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
        apply El_cong; [ er | er | er | exact HeqF2 ]. }
      assert (eqt (sTy D2 (iEl oIrr oL0))
                (codAtIrr D2 D rF lF F1 B1 w2 a)
                (oEl D2 oIrr oL0 B0)) as HeqCod.
      { eapply eq_term_trans.
        { apply wsc_cod with (w := g) (rG := oIrr) (G := G) (F := F) (B := B)
            (w'' := g2);
            [ wfx | wfx | wfx | wfx | wfx | apply wf_Irr | apply wf_L0
            | wfx | wfx | exact Hgw | apply Wk_wf; exact HW2 | exact Hcmp
            | wfx | exact HeqF1 | exact HeqB1W | exact Haw2 ]. }
        eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
        apply El_cong; [ er | er | er | exact HeqB0 ]. }
      exists (oEl D2 oIrr oL0 B0).
      split; [ apply tyok_El; exact HB0 | split; [ exact HeqCod | ] ].
      destruct (IHB D2 _ Hsig HD2 B0 HB0 HeqB0) as [P0' HR0'].
      eapply RTy_iff; [ exact HR0' | ].
      intro x; split.
      { intro Hh; eapply RTm_elim;
          [ exact HR0'
          | exact (Hh (oEl D2 oIrr oL0 B0) (tyok_El HB0) HeqCod) ]. }
      { intros Hx C HTC HeqC.
        assert (C = oEl D2 oIrr oL0 B0) as ->.
        { eapply TyOk_inj;
            [ exact HTC | apply tyok_El; exact HB0
            | eapply eq_term_trans;
              [ apply eq_term_sym; exact HeqC | exact HeqCod ] ]. }
        eapply RTm_intro; [ exact HR0' | exact Hx ]. } }
    { intros e; split; intro H; exact H. }

  (* ---- a code variable ---- *)
  - intros G r l c Hx _ D g Hg HD c' Hc' Heqc'.
    destruct (WIS_var Hg Hx) as [x' [Hx' Heqx']].
    assert (c' = x') as ->.
    { eapply NfCode_inj;
        [ exact Hc' | apply nfcode_var; exact Hx'
        | eapply eq_term_trans;
          [ apply eq_term_sym; exact Heqc' | exact Heqx' ] ]. }
    exists (HasNe D (iEl r l) (oEl D r l x')); apply RTy_var_i; exact Hx'.

  (* ---- VarT / NeET / NfET: nothing to prove ---- *)
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
  - intros; exact I.
  - intros; exact I.
Qed.

Theorem RTyEx_of_NfCode G r l c
  : NfCode G r l c -> exists P, RTy G (iEl r l) (oEl G r l c) P.
Proof.
  intro Hc.
  assert (EnvOk G) as HG by (eapply NfCode_EnvOk; exact Hc).
  apply (proj1 (proj2 (proj2 RTyEx_str)) G r l c Hc G (oId G)
           (wis_wk (wk_id HG)) HG c Hc).
  eapply eq_term_conv;
    [ apply eq_exp_subst_id;
      [ apply EnvOk_wf; exact HG | wfx | wfx | apply NfCode_wf; exact Hc ]
    | apply eq_sort_exp_ty; apply eq_term_refl; wfx ].
Qed.

Theorem RTyEx_of_TyOk G i A : TyOk G i A -> exists P, RTy G i A P.
Proof.
  intro HA.
  assert (EnvOk G) as HG by (eapply TyOk_EnvOk; exact HA).
  apply (proj1 (proj2 RTyEx_str) G i A HA G (oId G)
           (wis_wk (wk_id HG)) HG A HA).
  apply eq_ty_subst_id;
    [ apply EnvOk_wf; exact HG | wfx | apply TyOk_wf; exact HA ].
Qed.
