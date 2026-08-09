Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttSyntax WIP.DttWf WIP.DttEqns WIP.DttNf WIP.DttNfWf
  WIP.DttNfWk WIP.DttInj WIP.DttLR WIP.DttLRBasics WIP.DttLRCand WIP.DttLRFun.
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
(* 1. Congruence of the Kripke application in the WEAKENING            *)
(*                                                                     *)
(* [Wk] never derives a bare [wkn]: the one-step weakening of [Wk] is  *)
(* [oWk1 = wkn ; id].  "Pi_rel eta", on the other hand, is stated with *)
(* the bare [wkn].  Bridging the two -- which is what the escape half   *)
(* of the Pi_rel case needs -- is exactly congruence of [appAtRel] in   *)
(* its substitution argument, and that is what this section supplies.   *)
(* ================================================================== *)

Section AppW.

  Context (D G rF lF lG F B w w' e a : term).

  Context
    (HD : wft D sEnv)
    (HG : wft G sEnv)
    (HrF : wft rF sRelevance)
    (HlF : wft lF sLvl)
    (HlG : wft lG sLvl)
    (Hw : wft w (sSub D G))
    (Hw' : wft w' (sSub D G))
    (Hww' : eqt (sSub D G) w w')
    (HF : wft F (sCode G rF lF))
    (HB : wft B (sCode (oExtC G rF lF F) oRel lG)).

  Lemma aw_iF : wft (iEl rF lF) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]. Qed.

  Lemma aw_iG : wft (iEl oRel lG) sInfo.
  Proof.
    unfold iEl; apply wf_Info; [ apply wf_Rel | apply wf_Iota; exact HlG ].
  Qed.

  Lemma aw_cF : wft (iCode lF) sInfo.
  Proof.
    unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlF ].
  Qed.

  Lemma aw_cG : wft (iCode lG) sInfo.
  Proof.
    unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlG ].
  Qed.

  Lemma aw_ElG : wft (oEl G rF lF F) (sTy G (iEl rF lF)).
  Proof. apply wf_El; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  Lemma aw_GF : wft (oExtC G rF lF F) sEnv.
  Proof. apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  (* ---- the domain code ---- *)

  Lemma aw_code
    : eqt (sCode D rF lF)
        (wkCode D G w rF lF F) (wkCode D G w' rF lF F).
  Proof.
    unfold wkCode.
    eapply eqt_Usub_c with (G' := G) (g := w') (r := rF) (l := lF);
      [ exact HD | exact HG | exact Hw' | exact HrF | exact HlF | ].
    apply ExpSubst_cong
      with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w')
           (i1 := iCode lF) (i2 := iCode lF)
           (A1 := oU G rF lF) (A2 := oU G rF lF) (v1 := F) (v2 := F);
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HG
      | exact Hww'
      | apply eq_term_refl; apply aw_cF
      | apply eq_term_refl; apply wf_U; [ exact HG | exact HrF | exact HlF ]
      | apply eq_term_refl; exact HF ].
  Qed.

  Lemma aw_Fw : wft (wkCode D G w rF lF F) (sCode D rF lF).
  Proof.
    apply ac_Fw;
      [ exact HD | exact HG | exact HrF | exact HlF | exact Hw | exact HF ].
  Qed.

  Lemma aw_Fw' : wft (wkCode D G w' rF lF F) (sCode D rF lF).
  Proof.
    apply ac_Fw;
      [ exact HD | exact HG | exact HrF | exact HlF | exact Hw' | exact HF ].
  Qed.

  Lemma aw_ElD : wft (oEl D rF lF (wkCode D G w rF lF F)) (sTy D (iEl rF lF)).
  Proof. apply wf_El; [ exact HD | exact HrF | exact HlF | apply aw_Fw ]. Qed.

  Lemma aw_ElD' : wft (oEl D rF lF (wkCode D G w' rF lF F)) (sTy D (iEl rF lF)).
  Proof. apply wf_El; [ exact HD | exact HrF | exact HlF | apply aw_Fw' ]. Qed.

  Lemma aw_ElDeq
    : eqt (sTy D (iEl rF lF))
        (oEl D rF lF (wkCode D G w rF lF F))
        (oEl D rF lF (wkCode D G w' rF lF F)).
  Proof.
    apply El_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply aw_code ].
  Qed.

  Lemma aw_DF : wft (oExtC D rF lF (wkCode D G w rF lF F)) sEnv.
  Proof. apply wf_ExtC; [ exact HD | exact HrF | exact HlF | apply aw_Fw ]. Qed.

  Lemma aw_DF' : wft (oExtC D rF lF (wkCode D G w' rF lF F)) sEnv.
  Proof. apply wf_ExtC; [ exact HD | exact HrF | exact HlF | apply aw_Fw' ]. Qed.

  Lemma aw_DFeq
    : eqt sEnv (oExtC D rF lF (wkCode D G w rF lF F))
               (oExtC D rF lF (wkCode D G w' rF lF F)).
  Proof.
    unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; apply aw_iF
      | apply aw_ElDeq ].
  Qed.

  (* ---- the lifted weakening ---- *)

  Lemma aw_ElsubW
    : eqt (sTy D (iEl rF lF))
        (oTySubst D G w (iEl rF lF) (oEl G rF lF F))
        (oEl D rF lF (wkCode D G w rF lF F)).
  Proof.
    apply eq_El_subst;
      [ exact HD | exact HG | exact Hw | exact HrF | exact HlF | exact HF ].
  Qed.

  Lemma aw_ElsubW'
    : eqt (sTy D (iEl rF lF))
        (oTySubst D G w' (iEl rF lF) (oEl G rF lF F))
        (oEl D rF lF (wkCode D G w' rF lF F)).
  Proof.
    apply eq_El_subst;
      [ exact HD | exact HG | exact Hw' | exact HrF | exact HlF | exact HF ].
  Qed.

  Lemma aw_lift
    : eqt (sSub (oExtC D rF lF (wkCode D G w' rF lF F)) (oExtC G rF lF F))
        (oLift D G w rF lF F) (oLift D G w' rF lF F).
  Proof.
    rewrite !oLift_oLiftW.
    unfold oLiftW, oExtC.
    apply Snoc_cong;
      [ apply Ext_cong;
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; apply aw_iF
        | apply aw_ElDeq ]
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; apply aw_iF
      | apply eq_term_refl; apply aw_ElG
      | apply Cmp_cong;
        [ apply Ext_cong;
          [ apply eq_term_refl; exact HD
          | apply eq_term_refl; apply aw_iF
          | apply aw_ElDeq ]
        | apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HG
        | apply Wkn_cong;
          [ apply eq_term_refl; exact HD
          | apply eq_term_refl; apply aw_iF
          | apply aw_ElDeq ]
        | exact Hww' ]
      | ].
    eapply eq_term_conv.
    - apply Hd_cong;
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; apply aw_iF
        | apply aw_ElDeq ].
    - apply eq_sort_exp_ty;
        [ apply aw_DF' | apply aw_iF | ].
      apply eq_wk_lift_ty;
        [ exact HD | exact HG | apply aw_iF | apply aw_ElG | apply aw_ElD'
        | exact Hw' | apply aw_ElsubW' ].
  Qed.

  (* ---- the codomain code ---- *)

  Lemma aw_codcode
    : eqt (sCode (oExtC D rF lF (wkCode D G w' rF lF F)) oRel lG)
        (wkCodCodeRel D G w rF lF lG F B) (wkCodCodeRel D G w' rF lF lG F B).
  Proof.
    unfold wkCodCodeRel.
    eapply eqt_Usub_c
      with (G' := oExtC G rF lF F) (g := oLift D G w' rF lF F)
           (r := oRel) (l := lG);
      [ apply aw_DF' | apply aw_GF
      | apply wf_oLift;
        [ exact HD | exact HG | exact Hw' | exact HrF | exact HlF | exact HF ]
      | apply wf_Rel | exact HlG | ].
    apply ExpSubst_cong
      with (G1 := oExtC D rF lF (wkCode D G w rF lF F))
           (G2 := oExtC D rF lF (wkCode D G w' rF lF F))
           (G1' := oExtC G rF lF F) (G2' := oExtC G rF lF F)
           (g1 := oLift D G w rF lF F) (g2 := oLift D G w' rF lF F)
           (i1 := iCode lG) (i2 := iCode lG)
           (A1 := oU (oExtC G rF lF F) oRel lG)
           (A2 := oU (oExtC G rF lF F) oRel lG) (v1 := B) (v2 := B);
      [ apply aw_DFeq
      | apply eq_term_refl; apply aw_GF
      | apply aw_lift
      | apply eq_term_refl; apply aw_cG
      | apply eq_term_refl; apply wf_U;
        [ apply aw_GF | apply wf_Rel | exact HlG ]
      | apply eq_term_refl; exact HB ].
  Qed.

  (* ---- the weakened function ---- *)

  Context (He : wft e (sElt G oRel lG (oPiRel G rF lF lG F B))).

  Lemma aw_Pi : wft (oPiRel G rF lF lG F B) (sCode G oRel lG).
  Proof.
    apply wf_PiRel;
      [ exact HG | exact HrF | exact HlF | exact HlG | exact HF | exact HB ].
  Qed.

  Lemma aw_ElPi
    : wft (oEl G oRel lG (oPiRel G rF lF lG F B)) (sTy G (iEl oRel lG)).
  Proof. apply wf_El; [ exact HG | apply wf_Rel | exact HlG | apply aw_Pi ]. Qed.

  Lemma aw_fun
    : eqt (sElt D oRel lG
             (oPiRel D rF lF lG (wkCode D G w' rF lF F)
                (wkCodCodeRel D G w' rF lF lG F B)))
        (wkFunRel D G w rF lF lG F B e) (wkFunRel D G w' rF lF lG F B e).
  Proof.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty;
          [ exact HD | apply aw_iG
          | apply pr_Pi_subst;
            [ exact HD | exact HG | exact HrF | exact HlF | exact HlG
            | exact Hw' | exact HF | exact HB ] ] ].
    unfold wkFunRel; apply ExpSubst_cong
      with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := w) (g2 := w')
           (i1 := iEl oRel lG) (i2 := iEl oRel lG)
           (A1 := oEl G oRel lG (oPiRel G rF lF lG F B))
           (A2 := oEl G oRel lG (oPiRel G rF lF lG F B)) (v1 := e) (v2 := e);
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HG
      | exact Hww'
      | apply eq_term_refl; apply aw_iG
      | apply eq_term_refl; apply aw_ElPi
      | apply eq_term_refl; exact He ].
  Qed.

  (* ---- the application ---- *)

  Context (Ha : wft a (sElt D rF lF (wkCode D G w' rF lF F))).

  Theorem aw_appAt
    : eqt (sExp D (iEl oRel lG) (codAtRel D G rF lF lG F B w' a))
        (appAtRel D G rF lF lG F B w e a)
        (appAtRel D G rF lF lG F B w' e a).
  Proof.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty;
          [ exact HD | apply aw_iG
          | apply ac_appConcl;
            [ exact HD | exact HG | exact HrF | exact HlF | apply wf_Rel
            | exact HlG | exact Hw' | exact HF | exact HB | exact Ha ] ] ].
    unfold appAtRel; apply AppRel_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply eq_term_refl; exact HlG
      | apply aw_code
      | apply aw_codcode
      | apply aw_fun
      | apply eq_term_refl; exact Ha ].
  Qed.

End AppW.

(* ================================================================== *)
(* 2. The codomain instance at a NAMED domain/codomain/argument         *)
(*                                                                     *)
(* [neet_app_rel] insists on the SYNTACTIC normal forms [F'], [B'] and  *)
(* [a'] in the slots where [appAtRel] carries the raw substitution      *)
(* instances.  This transports [DttLRCand.ac_appConcl] across that      *)
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
    unfold sCode; apply eq_sort_exp_cong;
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
    unfold sElt; apply eq_sort_exp_ty;
      [ exact HD | apply an_iF | ].
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
(* 3. Naming the weakened Pi type                                      *)
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
(* 4. Weakening the codomain code, at the clause's chosen [F']          *)
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
(* 5. REFLECT at the two Pi clauses: a neutral function applied to a    *)
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
      [ | apply eq_sort_exp_ty; [ wfx | wfx | exact HeqCn ] ].
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
        | apply eq_sort_exp_ty; [ wfx | wfx | exact HeqA2 ] ]
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
      [ | apply eq_sort_exp_ty; [ wfx | wfx | exact HeqCn ] ].
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
        | apply eq_sort_exp_ty; [ wfx | wfx | exact HeqA2 ] ]
      | exact Heqa1 ].
Qed.

(* ================================================================== *)
(* 6. ESCAPE at [rty_pi_rel]: this is where ETA is cashed in.          *)
(*                                                                     *)
(* [Wk] derives no bare [wkn] -- its one-step weakening is             *)
(* [oWk1 = wkn ; id] -- while "Pi_rel eta" is stated with the bare     *)
(* [wkn].  Section 1's [aw_appAt] is the bridge.                        *)
(* ================================================================== *)

(* At the one-step weakening and the head variable, the raw codomain
   instance IS the codomain type: [<wkn,hd> = id]. *)
Lemma eq_codAt_wk1 G rF lF lG F B
  : wft G sEnv -> wft rF sRelevance -> wft lF sLvl -> wft lG sLvl ->
    wft F (sCode G rF lF) -> wft B (sCode (oExtC G rF lF F) oRel lG) ->
    eqt (sTy (oExtC G rF lF F) (iEl oRel lG))
      (codAtRel (oExtC G rF lF F) G rF lF lG F B
         (oWk1 G (iEl rF lF) (oEl G rF lF F))
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
               (oWk1 G (iEl rF lF) (oEl G rF lF F))
               (oHd G (iEl rF lF) (oEl G rF lF F)))
            (oId (oExtC G rF lF F))) as Hsnoc.
  { unfold instAt, oExtC.
    eapply eq_term_trans;
      [ | apply eq_snoc_wkn_hd; [ exact HG | exact HiF | exact HA ] ].
    apply Snoc_cong;
      [ apply eq_term_refl; apply wf_Ext; [ exact HG | exact HiF | exact HA ]
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; exact HiF
      | apply eq_term_refl; exact HA
      | apply eq_wk1; [ exact HG | exact HiF | exact HA ]
      | apply eq_term_refl; apply wf_Hd; [ exact HG | exact HiF | exact HA ] ]. }
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

(* THE eta STEP.  [t] is a normal form of [e] applied to the fresh
   variable; [lam t] is then a normal form of [e] ITSELF, and nothing but
   "Pi_rel eta" can supply that. *)
Lemma eq_eta_wk1 G rF lF lG F B e t
  : wft G sEnv -> wft rF sRelevance -> wft lF sLvl -> wft lG sLvl ->
    wft F (sCode G rF lF) -> wft B (sCode (oExtC G rF lF F) oRel lG) ->
    wft e (sElt G oRel lG (oPiRel G rF lF lG F B)) ->
    eqt (sExp (oExtC G rF lF F) (iEl oRel lG)
           (oEl (oExtC G rF lF F) oRel lG B))
      (appAtRel (oExtC G rF lF F) G rF lF lG F B
         (oWk1 G (iEl rF lF) (oEl G rF lF F)) e
         (oHd G (iEl rF lF) (oEl G rF lF F))) t ->
    eqt (sElt G oRel lG (oPiRel G rF lF lG F B)) e (oLamRel G rF lF lG F B t).
Proof.
  intros HG HrF HlF HlG HF HB He Ht.
  assert (wft (iEl rF lF) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]).
  assert (wft (oEl G rF lF F) (sTy G (iEl rF lF))) as HA
      by (apply wf_El; [ exact HG | exact HrF | exact HlF | exact HF ]).
  assert (wft (oExtC G rF lF F) sEnv) as HD
      by (apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]).
  assert (wft (oWkn G (iEl rF lF) (oEl G rF lF F))
            (sSub (oExtC G rF lF F) G)) as Hwkn
      by (unfold oExtC; apply wf_Wkn; [ exact HG | exact HiF | exact HA ]).
  assert (wft (oWk1 G (iEl rF lF) (oEl G rF lF F))
            (sSub (oExtC G rF lF F) G)) as Hwk1.
  { unfold oWk1, oExtC; apply wf_Cmp;
      [ apply wf_Ext; [ exact HG | exact HiF | exact HA ] | exact HG | exact HG
      | apply wf_Wkn; [ exact HG | exact HiF | exact HA ]
      | apply wf_Id; exact HG ]. }
  assert (eqt (sSub (oExtC G rF lF F) G)
            (oWkn G (iEl rF lF) (oEl G rF lF F))
            (oWk1 G (iEl rF lF) (oEl G rF lF F))) as Hww1
      by (apply eq_term_sym; unfold oExtC;
          apply eq_wk1; [ exact HG | exact HiF | exact HA ]).
  (* the head variable, typed at the weakened domain code *)
  assert (wft (oHd G (iEl rF lF) (oEl G rF lF F))
            (sElt (oExtC G rF lF F) rF lF
               (wkCode (oExtC G rF lF F) G
                  (oWk1 G (iEl rF lF) (oEl G rF lF F)) rF lF F))) as Hhd.
  { eapply wf_term_conv;
      [ unfold oExtC; apply wf_Hd; [ exact HG | exact HiF | exact HA ] | ].
    unfold sElt; apply eq_sort_exp_ty; [ exact HD | exact HiF | ].
    eapply eq_term_trans.
    - apply TySubst_cong
        with (G1 := oExtC G rF lF F) (G2 := oExtC G rF lF F)
             (G1' := G) (G2' := G)
             (g1 := oWkn G (iEl rF lF) (oEl G rF lF F))
             (g2 := oWk1 G (iEl rF lF) (oEl G rF lF F))
             (i1 := iEl rF lF) (i2 := iEl rF lF)
             (A1 := oEl G rF lF F) (A2 := oEl G rF lF F);
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HG
        | exact Hww1
        | apply eq_term_refl; exact HiF
        | apply eq_term_refl; exact HA ].
    - apply eq_El_subst;
        [ exact HD | exact HG | exact Hwk1 | exact HrF | exact HlF
        | exact HF ]. }
  (* move the application from the bare [wkn] to [oWk1] *)
  assert (eqt (sExp (oExtC G rF lF F) (iEl oRel lG)
                 (oEl (oExtC G rF lF F) oRel lG B))
            (appAtRel (oExtC G rF lF F) G rF lF lG F B
               (oWkn G (iEl rF lF) (oEl G rF lF F)) e
               (oHd G (iEl rF lF) (oEl G rF lF F)))
            t) as Hbody.
  { eapply eq_term_trans; [ | exact Ht ].
    eapply eq_term_conv;
      [ apply aw_appAt with (w := oWkn G (iEl rF lF) (oEl G rF lF F));
        [ exact HD | exact HG | exact HrF | exact HlF | exact HlG
        | exact Hwk1 | exact Hww1 | exact HF | exact HB | exact He
        | exact Hhd ]
      | ].
    apply eq_sort_exp_ty;
      [ exact HD
      | unfold iEl; apply wf_Info;
        [ apply wf_Rel | apply wf_Iota; exact HlG ]
      | apply eq_codAt_wk1;
        [ exact HG | exact HrF | exact HlF | exact HlG | exact HF
        | exact HB ] ]. }
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
    | exact Hbody ].
Qed.

(* ================================================================== *)
(* 7. Reading typing off an application / a substitution               *)
(*                                                                     *)
(* [rty_pi_rel] imposes no typing on the members of [P]; the escape     *)
(* half needs [e] to be well typed, and recovers it from the codomain   *)
(* premise's own equation, exactly as [DttLRCand.codAt_wf_a] recovers   *)
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

(* ================================================================== *)
(* 8. The head variable of the one-step weakening is reducible         *)
(* ================================================================== *)

Lemma esc_hd_var G rF lF F F1
  : EnvOk G -> NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) rF lF F1 ->
    eqt (sCode (oExtC G rF lF F) rF lF)
      (wkCode (oExtC G rF lF F) G (oWk1 G (iEl rF lF) (oEl G rF lF F))
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
  - apply TySubst_cong
      with (G1 := oExtC G rF lF F) (G2 := oExtC G rF lF F) (G1' := G) (G2' := G)
           (g1 := oWkn G (iEl rF lF) (oEl G rF lF F))
           (g2 := oWk1 G (iEl rF lF) (oEl G rF lF F))
           (i1 := iEl rF lF) (i2 := iEl rF lF)
           (A1 := oEl G rF lF F) (A2 := oEl G rF lF F);
      [ er | er
      | apply eq_term_sym; unfold oExtC; apply eq_wk1; wfx
      | er | er ].
  - eapply eq_term_trans.
    + apply eq_El_subst;
        [ wfx | wfx
        | apply Wk_wf; apply Wk_wk1; [ exact HG | exact HTA ]
        | wfx | wfx | wfx ].
    + apply El_cong; [ er | er | er | exact HeqF1 ].
Qed.

(* ================================================================== *)
(* A. ESCAPE AND REFLECT                                               *)
(*                                                                     *)
(* One induction, on DttLRBasics.v's hand-written [RTy_strong_ind]      *)
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
    assert (Wk (oExtC G rF lF F) G (oWk1 G (iEl rF lF) (oEl G rF lF F))) as HW1
        by (unfold oExtC; apply Wk_wk1; [ exact HGok | exact HTA ]).
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
      assert (Pd (oExtC G rF lF F) (oWk1 G (iEl rF lF) (oEl G rF lF F))
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
            | apply eq_codAt_wk1; wfx ] ]. }
      subst C.
      destruct (HescC _ ((proj1 (Hiff e) He) _ _ _ HW1 HDok Hhd))
        as [t (Ht1 & Ht2)].
      exists (oLamRel G rF lF lG F B t); split.
      * apply nfet_lam_rel; assumption.
      * apply eq_eta_wk1;
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

    + (* ESCAPE is free here: [Pi_irr] has no eta, so a neutral IS normal
         and the candidate carries the [HasNf] conjunct outright. *)
      intros e He; exact (proj1 (proj1 (Hiff e) He)).

    + (* REFLECT *)
      intros e HNe.
      apply Hiff; split;
        [ eapply HasNe_HasNf_pi_irr; [ exact HF | exact HB | exact HNe ] | ].
      intros D w a HW HD Ha.
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
