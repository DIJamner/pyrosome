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
   DTT NORMALIZATION, LAYER 2b: candidates are closed under provable
   equality of the subject.

   This finishes the one item src/Pyrosome/Gluing/Dtt/LogRelBasics.v left open:

     [RTy_cand_eq : forall G i A P, RTy G i A P -> CandEq G i A P]

   i.e. [RTy G i A P -> P e -> eq_term ott_dtt [] (sExp G i A) e e' -> P e'].
   The four LEAF clauses are already done in LogRelBasics.v (they are one
   use of transitivity each); ALL of the work here is the two Pi clauses,
   and it goes by LogRelBasics.v's hand-written [RTy_strong_ind] -- Rocq's
   generated [RTy_ind] has no induction hypothesis in the Pi cases.

   THE SHAPE OF THE Pi ARGUMENT.  At [rty_pi_rel],

     P e  <->  forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
                 Pc D w a (appAtRel D G rF lF lG F B w e a)

   so from [P e] and [e = e'] one must produce
   [Pc D w a (appAtRel ... e' a)].  The induction hypothesis gives
   [CandEq] for [Pc D w a] at the clause's own named codomain type [C],
   so it suffices to give the application equation at the sort
   [sExp D (iEl oRel lG) C].  That is [AppRel_cong] (only the function
   argument changes) transported twice:

     (i)  from [app_rel]'s own conclusion sort
          [sAppRelConcl D rF lF lG F[w] B[w^] a]  to the clause's raw
          codomain instance [codAtRel D G rF lF lG F B w a], and
     (ii) from there to [C], along the clause's own equation.

   Step (i) is the whole substitution-calculus content of the file and is
   isolated as [ac_appConcl] (section [AppConcl]).  It is stated ONCE,
   generically in the outer relevance/level [rG]/[lG], so the single
   lemma serves both Pi clauses:

     (El (extC D rF lF F[w]) rG lG (B[w^]))[<id_D, a>]
       =  (El (extC G rF lF F) rG lG B)[<w, a>]

   and it decomposes as "El subst" on both sides, then
   "exp_subst_cmp"/"U subst" to fuse the two code substitutions, then the
   substitution identity

     <id_D, a> o (w lifted)  =  <w, a>        ([ac_cmp_inst_lift])

   which is "cmp_snoc" followed by "cmp_assoc"/"wkn_snoc"/"id_left" on the
   substitution component and "snoc_hd" on the value component.

   THE KRIPKE ARGUMENT IS NOT JUNK.  [rty_pi_*] imposes no typing on the
   members of [Pd], so a priori [a] could be arbitrary syntax; but whenever
   [Pd D w a] holds the codomain premise fires and its equation mentions
   [a] as a subterm of [codAt*], which forces it well formed.
   [codAt_wf_a] extracts exactly that, using NfTyping.v's [con]-argument
   inversion.  No Layer-1 weakening metatheory and no extra hypothesis on
   [Pd] is used anywhere in this file.

   THE ONE EXTRA WRINKLE AT [Pi_irr].  The former "Pi_irr" stores its
   codomain code at info [rel (iota L1)] while "lam_irr"/"app_irr" -- and
   hence [LogRel.wkCodCodeIrr] -- store it at [iCode L0] (trap (A) of
   src/Pyrosome/Gluing/Dtt/NfTyping.v).  So the relevant clause gets [eq_Pi_rel_subst] for free
   whereas the irrelevant one has to move an [exp_subst] between the two
   spellings twice; [eq_expsubst_info] is that move, and it is the only
   thing the two Pi cases do not share.

   EXPORTS: [ac_appConcl] (the substitution bridge), [codAt_wf_a],
   [eq_expsubst_info], [pr_appAt]/[pi_appAt] (the two application
   congruences at the clause's codomain sort), [RTy_cand_eq], and the now
   unconditional [RTm_eq]/[RTmN_eq] (LogRelBasics.v's conditional
   [RTm_eq_of]/[RTmN_eq_of] discharged at [RTy_CandEqOk]).
   ===================================================================== *)

Notation term := (@Term.term string).
Notation sort := (@Term.sort string).

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* ================================================================== *)
(* 0. Argument inversion for the two [con]s we must peel               *)
(* ================================================================== *)

Lemma wft_TySubst_args G G' g i A t
  : wft (oTySubst G G' g i A) t ->
    wft G sEnv /\ wft G' sEnv /\ wft g (sSub G G')
    /\ wft i sInfo /\ wft A (sTy G' i).
Proof.
  unfold oTySubst; intro H; con_args_inv H; repeat split; assumption.
Qed.

Lemma wft_Snoc_args G G' i A g v t
  : wft (oSnoc G G' i A g v) t ->
    wft G sEnv /\ wft G' sEnv /\ wft i sInfo /\ wft A (sTy G' i)
    /\ wft g (sSub G G')
    /\ wft v (sExp G i (oTySubst G G' g i A)).
Proof.
  unfold oSnoc; intro H; con_args_inv H; repeat split; assumption.
Qed.

(* ================================================================== *)
(* 1. The substitution identity behind the Pi clauses                  *)
(* ================================================================== *)

(* [oLift] is written with [let]s; this is its expanded reading. *)
Lemma oLift_eq (D G g rF lF F : term)
  : oLift D G g rF lF F
    = oSnoc (oExtC D rF lF (wkCode D G g rF lF F)) G (iEl rF lF)
        (oEl G rF lF F)
        (oCmp (oExtC D rF lF (wkCode D G g rF lF F)) D G
           (oWkn D (iEl rF lF) (oEl D rF lF (wkCode D G g rF lF F))) g)
        (oHd D (iEl rF lF) (oEl D rF lF (wkCode D G g rF lF F))).
Proof. reflexivity. Qed.

Section AppConcl.

  Context (D G rF lF rG lG F B w a : term).

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
    (Ha : wft a (sElt D rF lF (wkCode D G w rF lF F))).

  Local Notation Fw := (wkCode D G w rF lF F).
  Local Notation GF := (oExtC G rF lF F).
  Local Notation DF := (oExtC D rF lF (wkCode D G w rF lF F)).
  Local Notation wknD :=
    (oWkn D (iEl rF lF) (oEl D rF lF (wkCode D G w rF lF F))).
  Local Notation hdD :=
    (oHd D (iEl rF lF) (oEl D rF lF (wkCode D G w rF lF F))).
  Local Notation cw :=
    (oCmp (oExtC D rF lF (wkCode D G w rF lF F)) D G
       (oWkn D (iEl rF lF) (oEl D rF lF (wkCode D G w rF lF F))) w).

  (* ---- the routine well-formedness facts ---- *)

  Lemma ac_iEl : wft (iEl rF lF) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]. Qed.

  Lemma ac_iG : wft (iEl rG lG) sInfo.
  Proof. unfold iEl; apply wf_Info; [ exact HrG | apply wf_Iota; exact HlG ]. Qed.

  Lemma ac_cF : wft (iCode lF) sInfo.
  Proof.
    unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlF ].
  Qed.

  Lemma ac_cG : wft (iCode lG) sInfo.
  Proof.
    unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlG ].
  Qed.

  Lemma ac_Fw : wft Fw (sCode D rF lF).
  Proof.
    unfold wkCode; eapply wf_term_conv.
    - apply wf_ExpSubst;
        [ exact HD | exact HG | exact Hw | apply ac_cF
        | apply wf_U; [ exact HG | exact HrF | exact HlF ]
        | exact HF ].
    - apply eq_sort_exp_ty.
      apply eq_U_subst;
        [ exact HD | exact HG | exact Hw | exact HrF | exact HlF ].
  Qed.

  Lemma ac_ElG : wft (oEl G rF lF F) (sTy G (iEl rF lF)).
  Proof. apply wf_El; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  Lemma ac_ElD : wft (oEl D rF lF Fw) (sTy D (iEl rF lF)).
  Proof. apply wf_El; [ exact HD | exact HrF | exact HlF | apply ac_Fw ]. Qed.

  Lemma ac_GF : wft GF sEnv.
  Proof. apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  Lemma ac_DF : wft DF sEnv.
  Proof. apply wf_ExtC; [ exact HD | exact HrF | exact HlF | apply ac_Fw ]. Qed.

  Lemma ac_wknD : wft wknD (sSub DF D).
  Proof.
    unfold oExtC; apply wf_Wkn; [ exact HD | apply ac_iEl | apply ac_ElD ].
  Qed.

  Lemma ac_cw : wft cw (sSub DF G).
  Proof.
    apply wf_Cmp;
      [ apply ac_DF | exact HD | exact HG | apply ac_wknD | exact Hw ].
  Qed.

  Lemma ac_hdD
    : wft hdD (sExp DF (iEl rF lF) (oTySubst DF D wknD (iEl rF lF)
                                     (oEl D rF lF Fw))).
  Proof.
    unfold oExtC; apply wf_Hd; [ exact HD | apply ac_iEl | apply ac_ElD ].
  Qed.

  (* [F[w]] really does name the weakened domain type. *)
  Lemma ac_El_w
    : eqt (sTy D (iEl rF lF))
        (oTySubst D G w (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF Fw).
  Proof.
    apply eq_El_subst;
      [ exact HD | exact HG | exact Hw | exact HrF | exact HlF | exact HF ].
  Qed.

  (* The bridging equation of the lifted substitution. *)
  Lemma ac_lift_ty
    : eqt (sTy DF (iEl rF lF))
        (oTySubst DF D wknD (iEl rF lF) (oEl D rF lF Fw))
        (oTySubst DF G cw (iEl rF lF) (oEl G rF lF F)).
  Proof.
    unfold oExtC; apply eq_wk_lift_ty;
      [ exact HD | exact HG | apply ac_iEl | apply ac_ElG | apply ac_ElD
      | exact Hw | apply ac_El_w ].
  Qed.

  Lemma ac_hdD'
    : wft hdD (sExp DF (iEl rF lF)
                 (oTySubst DF G cw (iEl rF lF) (oEl G rF lF F))).
  Proof.
    eapply wf_term_conv; [ apply ac_hdD | ].
    apply eq_sort_exp_ty; apply ac_lift_ty.
  Qed.

  Lemma ac_lift : wft (oLift D G w rF lF F) (sSub DF GF).
  Proof.
    rewrite oLift_eq; unfold oExtC at 3.
    apply wf_Snoc;
      [ apply ac_DF | exact HG | apply ac_iEl | apply ac_ElG
      | apply ac_cw | apply ac_hdD' ].
  Qed.


  Local Notation instD := (oInst D rF lF (wkCode D G w rF lF F) a).
  Local Notation instW := (instAt D G rF lF F w a).

  Lemma ac_a_id
    : wft a (sExp D (iEl rF lF)
               (oTySubst D D (oId D) (iEl rF lF) (oEl D rF lF Fw))).
  Proof.
    eapply wf_term_conv; [ exact Ha | ].
    apply eq_sort_exp_ty.
    apply eq_term_sym, eq_ty_subst_id;
      [ exact HD | apply ac_iEl | apply ac_ElD ].
  Qed.

  Lemma ac_instD : wft instD (sSub D DF).
  Proof.
    unfold oInst, oExtC; apply wf_Snoc;
      [ exact HD | exact HD | apply ac_iEl | apply ac_ElD
      | apply wf_Id; exact HD | apply ac_a_id ].
  Qed.

  Lemma ac_a_w
    : wft a (sExp D (iEl rF lF)
               (oTySubst D G w (iEl rF lF) (oEl G rF lF F))).
  Proof.
    eapply wf_term_conv; [ exact Ha | ].
    apply eq_sort_exp_ty.
    apply eq_term_sym, ac_El_w.
  Qed.

  Lemma ac_instW : wft instW (sSub D GF).
  Proof.
    unfold instAt, oExtC; apply wf_Snoc;
      [ exact HD | exact HG | apply ac_iEl | apply ac_ElG
      | exact Hw | apply ac_a_w ].
  Qed.

  (* ---- the two collapses ---- *)

  Lemma ac_wkn_inst : eqt (sSub D D) (oCmp D DF D instD wknD) (oId D).
  Proof.
    unfold oInst, oExtC; apply eq_wkn_snoc;
      [ exact HD | exact HD | apply wf_Id; exact HD | apply ac_iEl
      | apply ac_ElD | apply ac_a_id ].
  Qed.

  Lemma ac_cmp_w : eqt (sSub D G) (oCmp D DF G instD cw) w.
  Proof.
    eapply eq_term_trans.
    { apply eq_cmp_assoc with (G2 := DF) (G3 := D);
        [ exact HD | apply ac_DF | exact HD | exact HG
        | apply ac_instD | apply ac_wknD | exact Hw ]. }
    eapply eq_term_trans.
    { apply Cmp_cong;
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HG
        | apply ac_wkn_inst
        | apply eq_term_refl; exact Hw ]. }
    apply eq_id_left; [ exact HD | exact HG | exact Hw ].
  Qed.

  Lemma ac_inst_ty
    : eqt (sTy D (iEl rF lF))
        (oTySubst D DF instD (iEl rF lF)
           (oTySubst DF D wknD (iEl rF lF) (oEl D rF lF Fw)))
        (oEl D rF lF Fw).
  Proof.
    eapply eq_term_trans.
    { apply eq_ty_subst_cmp with (G2 := DF);
        [ exact HD | apply ac_DF | exact HD | apply ac_instD | apply ac_wknD
        | apply ac_iEl | apply ac_ElD ]. }
    eapply eq_term_trans.
    { apply TySubst_cong with (g2 := oId D) (A2 := oEl D rF lF Fw);
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HD
        | apply ac_wkn_inst
        | apply eq_term_refl; apply ac_iEl
        | apply eq_term_refl; apply ac_ElD ]. }
    apply eq_ty_subst_id; [ exact HD | apply ac_iEl | apply ac_ElD ].
  Qed.

  Lemma ac_hd_inst
    : eqt (sExp D (iEl rF lF)
             (oTySubst D G w (iEl rF lF) (oEl G rF lF F)))
        (oExpSubst D DF instD (iEl rF lF)
           (oTySubst DF G cw (iEl rF lF) (oEl G rF lF F)) hdD)
        a.
  Proof.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply eq_term_sym; apply ac_El_w ].
    eapply eq_term_trans.
    { eapply eq_term_conv.
      - apply ExpSubst_cong
          with (A2 := oTySubst DF D wknD (iEl rF lF) (oEl D rF lF Fw))
               (v2 := hdD);
          [ apply eq_term_refl; exact HD
          | apply eq_term_refl; apply ac_DF
          | apply eq_term_refl; apply ac_instD
          | apply eq_term_refl; apply ac_iEl
          | apply eq_term_sym; apply ac_lift_ty
          | apply eq_term_refl; apply ac_hdD ].
      - apply eq_sort_exp_ty; apply ac_inst_ty. }
    eapply eq_term_conv.
    - unfold oInst, oExtC; apply eq_snoc_hd;
        [ exact HD | exact HD | apply wf_Id; exact HD | apply ac_iEl
        | apply ac_ElD | apply ac_a_id ].
    - apply eq_sort_exp_ty.
      apply eq_ty_subst_id; [ exact HD | apply ac_iEl | apply ac_ElD ].
  Qed.

  Lemma ac_cmp_inst_lift
    : eqt (sSub D GF) (oCmp D DF GF instD (oLift D G w rF lF F)) instW.
  Proof.
    rewrite oLift_eq.
    eapply eq_term_trans.
    { unfold oExtC at 2; apply eq_cmp_snoc;
        [ exact HD | apply ac_DF | exact HG | apply ac_instD | apply ac_cw
        | apply ac_iEl | apply ac_ElG | apply ac_hdD' ]. }
    unfold instAt, oExtC at 2.
    apply Snoc_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; apply ac_iEl
      | apply eq_term_refl; apply ac_ElG
      | apply ac_cmp_w
      | apply ac_hd_inst ].
  Qed.


  Local Notation Bw :=
    (oExpSubst (oExtC D rF lF (wkCode D G w rF lF F)) (oExtC G rF lF F)
       (oLift D G w rF lF F) (iCode lG) (oU (oExtC G rF lF F) rG lG) B).

  Lemma ac_Bw_raw
    : wft Bw (sExp DF (iCode lG)
                (oTySubst DF GF (oLift D G w rF lF F) (iCode lG)
                   (oU GF rG lG))).
  Proof.
    apply wf_ExpSubst;
      [ apply ac_DF | apply ac_GF | apply ac_lift | apply ac_cG
      | apply wf_U; [ apply ac_GF | exact HrG | exact HlG ]
      | exact HB ].
  Qed.

  Lemma ac_Bw : wft Bw (sCode DF rG lG).
  Proof.
    eapply wf_term_conv; [ apply ac_Bw_raw | ].
    apply eq_sort_exp_ty.
    apply eq_U_subst;
      [ apply ac_DF | apply ac_GF | apply ac_lift | exact HrG | exact HlG ].
  Qed.

  Lemma ac_S1_ty
    : eqt (sTy D (iCode lG))
        (oTySubst D DF instD (iCode lG)
           (oTySubst DF GF (oLift D G w rF lF F) (iCode lG) (oU GF rG lG)))
        (oU D rG lG).
  Proof.
    eapply eq_term_trans.
    { apply eq_ty_subst_cmp with (G2 := DF);
        [ exact HD | apply ac_DF | apply ac_GF | apply ac_instD | apply ac_lift
        | apply ac_cG
        | apply wf_U; [ apply ac_GF | exact HrG | exact HlG ] ]. }
    eapply eq_term_trans.
    { apply TySubst_cong with (g2 := instW) (A2 := oU GF rG lG);
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; apply ac_GF
        | apply ac_cmp_inst_lift
        | apply eq_term_refl; apply ac_cG
        | apply eq_term_refl; apply wf_U;
          [ apply ac_GF | exact HrG | exact HlG ] ]. }
    apply eq_U_subst;
      [ exact HD | apply ac_GF | apply ac_instW | exact HrG | exact HlG ].
  Qed.

  Lemma ac_S2_ty
    : eqt (sTy D (iCode lG))
        (oTySubst D GF instW (iCode lG) (oU GF rG lG)) (oU D rG lG).
  Proof.
    apply eq_U_subst;
      [ exact HD | apply ac_GF | apply ac_instW | exact HrG | exact HlG ].
  Qed.

  (* The code equation: [B] transported along the lifted [w] and then
     instantiated at [a] is [B] instantiated along [<w,a>]. *)
  Lemma ac_code
    : eqt (sCode D rG lG)
        (oExpSubst D DF instD (iCode lG) (oU DF rG lG) Bw)
        (oExpSubst D GF instW (iCode lG) (oU GF rG lG) B).
  Proof.
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ | apply eq_sort_exp_ty; apply ac_S1_ty ].
      eapply eq_term_trans.
      - apply ExpSubst_cong
          with (A2 := oTySubst DF GF (oLift D G w rF lF F) (iCode lG)
                        (oU GF rG lG))
               (v2 := Bw);
          [ apply eq_term_refl; exact HD
          | apply eq_term_refl; apply ac_DF
          | apply eq_term_refl; apply ac_instD
          | apply eq_term_refl; apply ac_cG
          | apply eq_term_sym; apply eq_U_subst;
            [ apply ac_DF | apply ac_GF | apply ac_lift | exact HrG
            | exact HlG ]
          | apply eq_term_refl; apply ac_Bw_raw ].
      - apply eq_exp_subst_cmp with (G2 := DF);
          [ exact HD | apply ac_DF | apply ac_GF | apply ac_instD
          | apply ac_lift | apply ac_cG
          | apply wf_U; [ apply ac_GF | exact HrG | exact HlG ]
          | exact HB ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply ac_S2_ty ].
    apply ExpSubst_cong with (g2 := instW) (A2 := oU GF rG lG) (v2 := B);
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; apply ac_GF
      | apply ac_cmp_inst_lift
      | apply eq_term_refl; apply ac_cG
      | apply eq_term_refl; apply wf_U;
        [ apply ac_GF | exact HrG | exact HlG ]
      | apply eq_term_refl; exact HB ].
  Qed.

  (* THE bridge: the [app] rule's own conclusion sort is the clause's raw
     codomain instance. *)
  Theorem ac_appConcl
    : eqt (sTy D (iEl rG lG))
        (oTySubst D DF instD (iEl rG lG) (oEl DF rG lG Bw))
        (oTySubst D GF instW (iEl rG lG) (oEl GF rG lG B)).
  Proof.
    eapply eq_term_trans.
    { apply eq_El_subst;
        [ exact HD | apply ac_DF | apply ac_instD | exact HrG | exact HlG
        | apply ac_Bw ]. }
    eapply eq_term_trans.
    { apply El_cong with (e2 := oExpSubst D GF instW (iCode lG)
                                 (oU GF rG lG) B);
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HrG
        | apply eq_term_refl; exact HlG
        | apply ac_code ]. }
    apply eq_term_sym.
    apply eq_El_subst;
      [ exact HD | apply ac_GF | apply ac_instW | exact HrG | exact HlG
      | exact HB ].
  Qed.

End AppConcl.

(* ================================================================== *)
(* 2. Well-formedness of the Kripke argument                           *)
(* ================================================================== *)

(* [rty_pi_*] imposes no typing on the members of [Pd]; it does not have
   to.  Whenever [Pd D w a] holds the codomain premise fires, and its
   equation has [a] as a subterm of [codAt*], which is enough. *)
Lemma codAt_wf_a D G rF lF rG lG F B w a t
  : wft D sEnv -> wft G sEnv -> wft rF sRelevance -> wft lF sLvl ->
    wft w (sSub D G) -> wft F (sCode G rF lF) ->
    wft (oTySubst D (oExtC G rF lF F) (instAt D G rF lF F w a) (iEl rG lG)
           (oEl (oExtC G rF lF F) rG lG B)) t ->
    wft a (sElt D rF lF (wkCode D G w rF lF F)).
Proof.
  intros HD HG HrF HlF Hw HF Ht.
  assert (wft (iEl rF lF) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact HrF | apply wf_Iota; exact HlF ]).
  apply wft_TySubst_args in Ht.
  destruct Ht as [_ [_ [Hs _]]].
  unfold instAt in Hs; apply wft_Snoc_args in Hs.
  destruct Hs as [_ [_ [_ [_ [_ Hv]]]]].
  eapply wf_term_conv; [ exact Hv | ].
  apply eq_sort_exp_ty.
  apply eq_El_subst;
    [ exact HD | exact HG | exact Hw | exact HrF | exact HlF | exact HF ].
Qed.

(* ================================================================== *)
(* 3. The relevant Pi clause                                           *)
(* ================================================================== *)

Section PiRel.

  Context (D G rF lF lG F B w a e e' : term).

  Context
    (HD : wft D sEnv)
    (HG : wft G sEnv)
    (HrF : wft rF sRelevance)
    (HlF : wft lF sLvl)
    (HlG : wft lG sLvl)
    (Hw : wft w (sSub D G))
    (HF : wft F (sCode G rF lF))
    (HB : wft B (sCode (oExtC G rF lF F) oRel lG))
    (Ha : wft a (sElt D rF lF (wkCode D G w rF lF F))).

  Lemma pr_Pi : wft (oPiRel G rF lF lG F B) (sCode G oRel lG).
  Proof.
    apply wf_PiRel;
      [ exact HG | exact HrF | exact HlF | exact HlG | exact HF | exact HB ].
  Qed.

  Lemma pr_ElPi
    : wft (oEl G oRel lG (oPiRel G rF lF lG F B)) (sTy G (iEl oRel lG)).
  Proof.
    apply wf_El;
      [ exact HG | apply wf_Rel | exact HlG | apply pr_Pi ].
  Qed.

  (* [(Pi_rel F B)[w]] IS the [Pi_rel] the clause's application names. *)
  Lemma pr_Pi_subst
    : eqt (sTy D (iEl oRel lG))
        (oTySubst D G w (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)))
        (oEl D oRel lG
           (oPiRel D rF lF lG (wkCode D G w rF lF F)
              (wkCodCodeRel D G w rF lF lG F B))).
  Proof.
    eapply eq_term_trans.
    { apply eq_El_subst;
        [ exact HD | exact HG | exact Hw | apply wf_Rel | exact HlG
        | apply pr_Pi ]. }
    apply El_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; apply wf_Rel
      | apply eq_term_refl; exact HlG
      | ].
    apply eq_Pi_rel_subst;
      [ exact HD | exact HG | exact Hw | exact HrF | exact HlF | exact HlG
      | exact HF | exact HB ].
  Qed.

  Lemma pr_wkFun
    : eqt (sExp G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B))) e e' ->
      eqt (sElt D oRel lG
             (oPiRel D rF lF lG (wkCode D G w rF lF F)
                (wkCodCodeRel D G w rF lF lG F B)))
        (wkFunRel D G w rF lF lG F B e) (wkFunRel D G w rF lF lG F B e').
  Proof.
    intro Heq.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply pr_Pi_subst ].
    unfold wkFunRel; apply ExpSubst_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; exact Hw
      | apply eq_term_refl; unfold iEl; apply wf_Info;
        [ apply wf_Rel | apply wf_Iota; exact HlG ]
      | apply eq_term_refl; apply pr_ElPi
      | exact Heq ].
  Qed.

  Theorem pr_appAt
    : eqt (sExp G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B))) e e' ->
      eqt (sExp D (iEl oRel lG) (codAtRel D G rF lF lG F B w a))
        (appAtRel D G rF lF lG F B w e a)
        (appAtRel D G rF lF lG F B w e' a).
  Proof.
    intro Heq.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply ac_appConcl;
            [ exact HD | exact HG | exact HrF | exact HlF | apply wf_Rel
            | exact HlG | exact Hw | exact HF | exact HB | exact Ha ] ].
    unfold appAtRel; apply AppRel_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply eq_term_refl; exact HlG
      | apply eq_term_refl; apply ac_Fw;
        [ exact HD | exact HG | exact HrF | exact HlF | exact Hw | exact HF ]
      | apply eq_term_refl; apply ac_Bw;
        [ exact HD | exact HG | exact HrF | exact HlF | apply wf_Rel
        | exact HlG | exact Hw | exact HF | exact HB ]
      | apply pr_wkFun; exact Heq
      | apply eq_term_refl; exact Ha ].
  Qed.

End PiRel.

(* ================================================================== *)
(* 4. The irrelevant Pi clause                                         *)
(* ================================================================== *)

(* The [Pi_irr] former stores its codomain code at info [rel (iota L1)]
   while [lam_irr]/[app_irr] -- and hence [LogRel.wkCodCodeIrr] -- store it
   at [iCode L0].  This moves an [exp_subst] of an irrelevant-L0 code
   between the two spellings. *)
Lemma eq_expsubst_info D G g v
  : wft D sEnv -> wft G sEnv -> wft g (sSub D G) ->
    wft v (sCode G oIrr oL0) ->
    eqt (sCode D oIrr oL0)
      (oExpSubst D G g (iCode oL0) (oU G oIrr oL0) v)
      (oExpSubst D G g (oInfo oRel (oIota oL1)) (oU G oIrr oL0) v).
Proof.
  intros HD HG Hg Hv.
  assert (eqt (sTy D (iCode oL0))
            (oTySubst D G g (oInfo oRel (oIota oL1)) (oU G oIrr oL0))
            (oU D oIrr oL0)) as Hty.
  { eapply eq_term_trans.
    - apply TySubst_cong with (i2 := iCode oL0) (A2 := oU G oIrr oL0);
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; exact HG
        | apply eq_term_refl; exact Hg
        | apply eq_term_sym; apply eq_info_next0
        | apply eq_term_refl; apply wf_U;
          [ exact HG | apply wf_Irr | apply wf_L0 ] ].
    - apply eq_U_subst;
        [ exact HD | exact HG | exact Hg | apply wf_Irr | apply wf_L0 ]. }
  eapply eq_term_conv.
  - apply ExpSubst_cong with (i2 := oInfo oRel (oIota oL1))
                             (A2 := oU G oIrr oL0) (v2 := v);
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; exact Hg
      | apply eq_info_next0
      | apply eq_term_refl; apply wf_U_irr0'; exact HG
      | apply eq_term_refl; apply wft_U0irr_next; [ exact HG | exact Hv ] ].
  - apply sExp_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_sym; apply eq_info_next0
      | exact Hty ].
Qed.

Section PiIrr.

  Context (D G rF lF F B w a e e' : term).

  Context
    (HD : wft D sEnv)
    (HG : wft G sEnv)
    (HrF : wft rF sRelevance)
    (HlF : wft lF sLvl)
    (Hw : wft w (sSub D G))
    (HF : wft F (sCode G rF lF))
    (HB : wft B (sCode (oExtC G rF lF F) oIrr oL0))
    (Ha : wft a (sElt D rF lF (wkCode D G w rF lF F))).

  Lemma pi_GF : wft (oExtC G rF lF F) sEnv.
  Proof. apply wf_ExtC; [ exact HG | exact HrF | exact HlF | exact HF ]. Qed.

  Lemma pi_Fw : wft (wkCode D G w rF lF F) (sCode D rF lF).
  Proof.
    apply ac_Fw;
      [ exact HD | exact HG | exact HrF | exact HlF | exact Hw | exact HF ].
  Qed.

  Lemma pi_DF : wft (oExtC D rF lF (wkCode D G w rF lF F)) sEnv.
  Proof. apply wf_ExtC; [ exact HD | exact HrF | exact HlF | apply pi_Fw ]. Qed.

  Lemma pi_lift
    : wft (oLift D G w rF lF F)
        (sSub (oExtC D rF lF (wkCode D G w rF lF F)) (oExtC G rF lF F)).
  Proof.
    apply ac_lift;
      [ exact HD | exact HG | exact HrF | exact HlF | exact Hw | exact HF ].
  Qed.

  Lemma pi_Bw
    : wft (wkCodCodeIrr D G w rF lF F B)
        (sCode (oExtC D rF lF (wkCode D G w rF lF F)) oIrr oL0).
  Proof.
    apply ac_Bw;
      [ exact HD | exact HG | exact HrF | exact HlF | apply wf_Irr
      | apply wf_L0 | exact Hw | exact HF | exact HB ].
  Qed.

  Lemma pi_Pi : wft (oPiIrr G rF lF F B) (sCode G oIrr oL0).
  Proof.
    apply wft_U0irr_iota; [ exact HG | ].
    apply wf_PiIrr;
      [ exact HG | exact HrF | exact HlF | exact HF
      | apply wft_U0irr_next; [ apply pi_GF | exact HB ] ].
  Qed.

  Lemma pi_ElPi
    : wft (oEl G oIrr oL0 (oPiIrr G rF lF F B)) (sTy G (iEl oIrr oL0)).
  Proof.
    apply wf_El; [ exact HG | apply wf_Irr | apply wf_L0 | apply pi_Pi ].
  Qed.

  Lemma pi_code
    : eqt (sCode D oIrr oL0)
        (oExpSubst D G w (iCode oL0) (oU G oIrr oL0) (oPiIrr G rF lF F B))
        (oPiIrr D rF lF (wkCode D G w rF lF F)
           (wkCodCodeIrr D G w rF lF F B)).
  Proof.
    eapply eq_term_trans.
    { apply eq_expsubst_info;
        [ exact HD | exact HG | exact Hw | apply pi_Pi ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_Pi_irr_subst;
          [ exact HD | exact HG | exact Hw | exact HrF | exact HlF | exact HF
          | apply wft_U0irr_next; [ apply pi_GF | exact HB ] ]
        | apply eq_sort_sym; apply eq_sort_U_irr0; exact HD ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_sym; apply eq_sort_U_irr0; exact HD ].
    apply PiIrr_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply eq_term_refl; apply pi_Fw
      | ].
    eapply eq_term_conv;
      [ | apply eq_sort_U_irr0; apply pi_DF ].
    apply eq_term_sym.
    unfold wkCodCodeIrr; apply eq_expsubst_info;
      [ apply pi_DF | apply pi_GF | apply pi_lift | exact HB ].
  Qed.

  Lemma pi_Pi_subst
    : eqt (sTy D (iEl oIrr oL0))
        (oTySubst D G w (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)))
        (oEl D oIrr oL0
           (oPiIrr D rF lF (wkCode D G w rF lF F)
              (wkCodCodeIrr D G w rF lF F B))).
  Proof.
    eapply eq_term_trans.
    { apply eq_El_subst;
        [ exact HD | exact HG | exact Hw | apply wf_Irr | apply wf_L0
        | apply pi_Pi ]. }
    apply El_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; apply wf_Irr
      | apply eq_term_refl; apply wf_L0
      | apply pi_code ].
  Qed.

  Lemma pi_iInfo : wft (iEl oIrr oL0) sInfo.
  Proof.
    unfold iEl; apply wf_Info; [ apply wf_Irr | apply wf_Iota; apply wf_L0 ].
  Qed.

  Lemma pi_wkFun
    : eqt (sExp G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B))) e e' ->
      eqt (sElt D oIrr oL0
             (oPiIrr D rF lF (wkCode D G w rF lF F)
                (wkCodCodeIrr D G w rF lF F B)))
        (wkFunIrr D G w rF lF F B e) (wkFunIrr D G w rF lF F B e').
  Proof.
    intro Heq.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply pi_Pi_subst ].
    unfold wkFunIrr; apply ExpSubst_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HG
      | apply eq_term_refl; exact Hw
      | apply eq_term_refl; apply pi_iInfo
      | apply eq_term_refl; apply pi_ElPi
      | exact Heq ].
  Qed.

  Theorem pi_appAt
    : eqt (sExp G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B))) e e' ->
      eqt (sExp D (iEl oIrr oL0) (codAtIrr D G rF lF F B w a))
        (appAtIrr D G rF lF F B w e a)
        (appAtIrr D G rF lF F B w e' a).
  Proof.
    intro Heq.
    eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; apply ac_appConcl;
            [ exact HD | exact HG | exact HrF | exact HlF | apply wf_Irr
            | apply wf_L0 | exact Hw | exact HF | exact HB | exact Ha ] ].
    unfold appAtIrr; apply AppIrr_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HrF
      | apply eq_term_refl; exact HlF
      | apply eq_term_refl; apply pi_Fw
      | apply eq_term_refl; apply pi_Bw
      | apply pi_wkFun; exact Heq
      | apply eq_term_refl; exact Ha ].
  Qed.

End PiIrr.

(* ================================================================== *)
(* 5. Candidates are closed under provable equality of the subject     *)
(* ================================================================== *)

Theorem RTy_cand_eq : forall G i A P, RTy G i A P -> CandEq G i A P.
Proof.
  apply (@RTy_strong_ind CandEq).

  (* ---- U ---- *)
  - intros G r l P HG Hr Hl Hiff.
    apply RTy_cand_eq_U; apply rty_U; assumption.

  (* ---- Nat ---- *)
  - intros G P HG Hiff.
    apply RTy_cand_eq_nat; apply rty_nat; assumption.

  (* ---- Empty ---- *)
  - intros G P HG Hiff.
    apply RTy_cand_eq_empty; apply rty_empty; assumption.

  (* ---- a variable code ---- *)
  - intros G r l c P Hx Hiff.
    eapply RTy_cand_eq_var; [ exact Hx | apply rty_var; assumption ].

  (* ---- Pi_rel ---- *)
  - intros G rF lF lG F B P Pd Pc HrF HlF HlG HF HB Hd Hc Hiff.
    assert (wft F (sCode G rF lF)) as HFw by (apply NfCode_wf; exact HF).
    assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact HFw).
    assert (wft B (sCode (oExtC G rF lF F) oRel lG)) as HBw
        by (apply NfCode_wf; exact HB).
    intros e e' He Heq.
    apply Hiff; intros D w a Hw HD Ha.
    destruct (Hc D w a Hw HD Ha) as [C (HT & Heqc & HR & HCE)].
    assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
    assert (wft w (sSub D G)) as Hww by (apply Wk_wf; exact Hw).
    assert (wft a (sElt D rF lF (wkCode D G w rF lF F))) as Haw.
    { eapply codAt_wf_a with (rG := oRel) (lG := lG) (B := B);
        [ exact HDw | exact HGw | apply RelNf_wf; exact HrF
        | apply LvlNf_wf; exact HlF | exact Hww | exact HFw
        | apply (eqt_wf_l Heqc) ]. }
    eapply HCE; [ apply (proj1 (Hiff e) He D w a Hw HD Ha) | ].
    eapply eq_term_conv.
    + apply pr_appAt;
        [ exact HDw | exact HGw | apply RelNf_wf; exact HrF
        | apply LvlNf_wf; exact HlF | apply LvlNf_wf; exact HlG
        | exact Hww | exact HFw | exact HBw | exact Haw | exact Heq ].
    + apply eq_sort_exp_ty; exact Heqc.

  (* ---- Pi_irr ---- *)
  - intros G rF lF F B P Pd Pc HrF HlF HF HB Hd Hc Hiff.
    assert (wft F (sCode G rF lF)) as HFw by (apply NfCode_wf; exact HF).
    assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact HFw).
    assert (wft B (sCode (oExtC G rF lF F) oIrr oL0)) as HBw
        by (apply NfCode_wf; exact HB).
    intros e e' He Heq.
    destruct (proj1 (Hiff e) He) as [Hnf Happ].
    apply Hiff; split; [ eapply HasNf_eq; [ exact Hnf | exact Heq ] | ].
    intros D w a Hw HD Ha.
    destruct (Hc D w a Hw HD Ha) as [C (HT & Heqc & HR & HCE)].
    assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
    assert (wft w (sSub D G)) as Hww by (apply Wk_wf; exact Hw).
    assert (wft a (sElt D rF lF (wkCode D G w rF lF F))) as Haw.
    { eapply codAt_wf_a with (rG := oIrr) (lG := oL0) (B := B);
        [ exact HDw | exact HGw | apply RelNf_wf; exact HrF
        | apply LvlNf_wf; exact HlF | exact Hww | exact HFw
        | apply (eqt_wf_l Heqc) ]. }
    eapply HCE; [ apply (Happ D w a Hw HD Ha) | ].
    eapply eq_term_conv.
    + apply pi_appAt;
        [ exact HDw | exact HGw | apply RelNf_wf; exact HrF
        | apply LvlNf_wf; exact HlF
        | exact Hww | exact HFw | exact HBw | exact Haw | exact Heq ].
    + apply eq_sort_exp_ty; exact Heqc.
Qed.

(* ================================================================== *)
(* 6. The corollaries, now unconditional                               *)
(* ================================================================== *)

Definition RTy_CandEqOk : CandEqOk := @RTy_cand_eq.

Lemma RTm_eq G i A e e'
  : RTm G i A e -> eqt (sExp G i A) e e' -> RTm G i A e'.
Proof. apply (LogRelBasics.RTm_eq_of RTy_CandEqOk). Qed.

Lemma RTmN_eq G i A e e'
  : RTmN G i A e -> eqt (sExp G i A) e e' -> RTmN G i A e'.
Proof. apply (LogRelBasics.RTmN_eq_of RTy_CandEqOk). Qed.

(* The introduction direction of [RTm] and full functionality still need
   Layer 0.5 ([NfCodeInj]/[TyOkInj]); nothing here changes that. *)
