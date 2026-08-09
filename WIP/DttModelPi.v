Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel.
Require Import WIP.DttSyntax WIP.DttWf WIP.DttEqns WIP.DttNf WIP.DttNfWf
  WIP.DttNfWk WIP.DttInj WIP.DttLR WIP.DttLRBasics WIP.DttLRCand
  WIP.DttLRCore WIP.DttLRFun WIP.DttLRElim WIP.DttRSub WIP.DttRSubOk
  WIP.DttCeq WIP.DttModelStruct.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4b: the [cterm_cong] and [cterm_by]
   obligations for the BINDER FRAGMENT of [ott_dtt] --

     Emptyrec  Pi_rel  Pi_irr  lam_rel  lam_irr  app_rel  app_irr

   and the ten equations that live over them,

     "Pi_rel subst"  "Pi_irr subst"  "lam_rel subst"  "lam_irr subst"
     "app_rel subst" "app_irr subst" "Emptyrec subst"
     "Pi_rel beta"   "Pi_irr beta"   "Pi_rel eta"

   THREE STRUCTURAL OBSERVATIONS ORGANISE THE WHOLE FILE.

   (1) EVERY "X subst" EQUATION IS THE SAME MOVE.  Its left-hand side is
       [g[X args]], and [Ceq_term]'s semantic conjunct constrains only the
       LEFT term, so the entire content is: under a further reducible [g'],
       [g'[g[X args]]] collapses by "exp_subst_cmp" to [(g' o g)[X args]],
       and [Ceq_sub]'s conjunct says [g' o g] is reducible.  That is
       [ceq_exp_subst_l] below, stated ONCE; each of the seven substitution
       equations is then that lemma applied to the fragment's own
       congruence, plus the equation itself.  (The universe/base fragment
       rediscovered this move twice, in "El subst" and "suc subst"; here it
       would have been rediscovered seven times.)

   (2) THE TWO BETA RULES ARE A CONGRUENCE COMPOSITION.  [Ceq_term]'s left
       term of "Pi_rel beta" is [app_rel (lam_rel t) a], so
       [cong_AppRel] applied to [cong_LamRel] already produces a
       [Ceq_term] whose left term is exactly it; the rule then only has to
       move the RIGHT term, which is free.  Nothing semantic is proved
       twice.

   (3) ETA IS THE CHEAPEST OF THE TEN.  Its right-hand side is the bare
       argument [f], whose clause is a hypothesis; the left-hand side is
       provably equal to it by the rule, and [ceq_exp_eq_l] transports the
       clause across.  No reducibility reasoning at all.

   THE ONE GENUINELY NEW PIECE OF MACHINERY is [binder_lift] (section 2).
   Every binder congruence must feed its codomain argument's clause a
   reducible substitution into [oExtC G rF lF F] -- and Layer 3's
   [RSubN_liftC] demands [NfCode G rF lF F], i.e. NORMALITY OF THE DOMAIN
   CODE IN THE SOURCE ENVIRONMENT, which a congruence does not have: [G]
   and [F] there are arbitrary syntax.  What it does have is [RSubN D G g],
   whose witness environment [G0] IS normal.  So the domain code is first
   normalised AT [G0], along the identity substitution -- which is
   reducible, [RSub_id] -- and Layer 3's lifting is applied at [G0].  The
   [oLift] that the substitution equations actually name (whose extended
   domain is [oExtC D rF lF (g[F])], not normal) is then reached by one
   [Snoc_cong].
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ================================================================== *)
(* 0.  Glue                                                            *)
(* ================================================================== *)

(* [Ceq_term]'s semantic conjunct constrains only the LEFT term, so a
   reflexive instance at the RIGHT one is one use of symmetry and one of
   transitivity.  (Both are WIP/DttModelStruct.v's.) *)

Lemma ceq_refl_l t e1 e2 : Ceq_term t e1 e2 -> Ceq_term t e1 e1.
Proof. intro H; exact (term_trans_obligation H (term_sym_obligation H)). Qed.

Lemma ceq_refl_r t e1 e2 : Ceq_term t e1 e2 -> Ceq_term t e2 e2.
Proof. intro H; exact (term_trans_obligation (term_sym_obligation H) H). Qed.

(* Replacing the RIGHT term by a provably equal one is free. *)
Lemma ceq_exp_eq_r G i A e1 e2 e3
  : Ceq_term (sExp G i A) e1 e2 -> eqt (sExp G i A) e2 e3 ->
    Ceq_term (sExp G i A) e1 e3.
Proof.
  intros H Heq; apply Ceq_exp_e in H as [Ha Hb].
  apply ceq_exp; [ eapply eq_term_trans; eassumption | exact Hb ].
Qed.

(* Replacing the LEFT term costs one transport of the semantic conjunct. *)
Lemma ceq_exp_eq_l G i A e1 e2 e3
  : eqt (sExp G i A) e1 e2 -> Ceq_term (sExp G i A) e2 e3 ->
    Ceq_term (sExp G i A) e1 e3.
Proof.
  intros Heq H; apply Ceq_exp_e in H as [Ha Hb].
  destruct (wft_exp_inv (eqt_wf_l Heq)) as [HwG [Hwi HwA]].
  apply ceq_exp; [ eapply eq_term_trans; eassumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  apply RTmN_eq with (e := oExpSubst D G g i A e2); [ apply Hb; assumption | ].
  apply ExpSubst_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_refl; exact HwG
    | apply eq_term_refl; apply RSubN_wf; exact Hg
    | apply eq_term_refl; exact Hwi
    | apply eq_term_refl; exact HwA
    | apply eq_term_sym; exact Heq ].
Qed.

(* ---- reading a normal code off a code argument's clause ---------- *)

(* [RTmN_HasNfCode] (WIP/DttLRElim.v) wants the type already stripped of
   the substitution; this is the composite with "U subst", which is the
   form every code argument of this fragment is handed. *)
Lemma ceq_code_nf G r l c D g
  : RelNf r -> LvlNf l -> EnvOk D -> RSubN D G g ->
    RTmN D (iCode l) (oTySubst D G g (iCode l) (oU G r l))
         (oExpSubst D G g (iCode l) (oU G r l) c) ->
    HasNfCode D r l (oExpSubst D G g (iCode l) (oU G r l) c).
Proof.
  intros Hr Hl HD Hg HR.
  assert (wft r sRelevance) as Hrw by (apply RelNf_wf; exact Hr).
  assert (wft l sLvl) as Hlw by (apply LvlNf_wf; exact Hl).
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact Hg).
  assert (wft D sEnv) as HDw by (eapply wft_sub_dom; exact Hgw).
  assert (wft G sEnv) as HGw by (eapply wft_sub_cod; exact Hgw).
  eapply RTmN_elim with (i0 := iCode l) (A0 := oU D r l)
                        (P := HasNfCode D r l).
  - exact HR.
  - apply eq_term_refl; wfa.
  - apply tyok_U; assumption.
  - apply eq_U_subst; assumption.
  - apply RTy_U_i; assumption.
Qed.

(* ---- the substitution-equation move, once ------------------------ *)

(* THE lemma behind all seven "X subst" cases (observation (1) of the
   header).  Note that only a REFLEXIVE instance is produced: the semantic
   conjunct does not mention the right-hand term at all, and the right-hand
   term of the obligation is reached afterwards by [ceq_exp_eq_r] from the
   rule itself. *)
Lemma ceq_exp_subst_l G G' g1 g2 i A e1 e2
  : Ceq_term (sSub G G') g1 g2 -> Ceq_term (sExp G' i A) e1 e2 ->
    Ceq_term (sExp G i (oTySubst G G' g1 i A))
             (oExpSubst G G' g1 i A e1) (oExpSubst G G' g1 i A e1).
Proof.
  intros Hg He.
  apply Ceq_sub_e in Hg as [Hga Hgb].
  apply Ceq_exp_e in He as [Hea Heb].
  assert (wft g1 (sSub G G')) as Hg1w by (eapply eqt_wf_l; exact Hga).
  assert (wft e1 (sExp G' i A)) as He1w by (eapply eqt_wf_l; exact Hea).
  assert (wft G sEnv) as HGw by (eapply wft_sub_dom; exact Hg1w).
  assert (wft G' sEnv) as HG'w by (eapply wft_sub_cod; exact Hg1w).
  assert (wft i sInfo) as Hiw by (eapply wft_exp_info; exact He1w).
  assert (wft A (sTy G' i)) as HAw by (eapply wft_exp_ty; exact He1w).
  apply ceq_exp; [ apply eq_term_refl; apply wf_ExpSubst; assumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact Hg).
  pose proof (Hgb D g HD Hg) as Hh.
  eapply RTmN_eq.
  - eapply RTmN_eq_ty;
      [ exact (Heb D (oCmp D G G' g g1) HD Hh)
      | apply eq_term_sym; apply eq_ty_subst_cmp; assumption ].
  - apply eq_term_sym; apply eq_exp_subst_cmp; assumption.
Qed.

(* ================================================================== *)
(* 1.  [Emptyrec]                                                      *)
(* ================================================================== *)

(* THE ONE PLACE IN LAYER 4 WHERE [RTy_reflect] IS SPENT.  [Emptyrec]'s
   argument sits at [El _ irr L0 (Empty _)], whose candidate IS [HasNe]
   (there is no introduction form for the empty type at all), so the
   argument's clause hands back a NEUTRAL; [neet_emptyrec] makes the
   eliminator neutral at the result type, and reflect puts it back in the
   result type's candidate. *)
Lemma cong_Emptyrec G1 G2 rA1 rA2 lA1 lA2 A1 A2 e1 e2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rA1 rA2 ->
    Ceq_term sLvl lA1 lA2 ->
    Ceq_term (sCode G2 rA2 lA2) A1 A2 ->
    Ceq_term (sElt G2 oIrr oL0 (oEmpty G2)) e1 e2 ->
    Ceq_term (sElt G2 rA2 lA2 A2)
      (oEmptyrec G1 rA1 lA1 A1 e1) (oEmptyrec G2 rA2 lA2 A2 e2).
Proof.
  intros HGc Hr Hl HAc Hec.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rA1.
  apply Ceq_lvl_e in Hl as [Hlq Hlnf]; subst lA1.
  apply Ceq_exp_e in HAc as [HAa HAb].
  apply Ceq_exp_e in Hec as [Hea Heb].
  assert (wft rA2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lA2 sLvl) as Hwl by (apply LvlNf_wf; exact Hlnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft A1 (sCode G2 rA2 lA2)) as HwA1 by (eapply eqt_wf_l; exact HAa).
  assert (wft A2 (sCode G2 rA2 lA2)) as HwA2 by (eapply eqt_wf_r; exact HAa).
  assert (wft e1 (sElt G2 oIrr oL0 (oEmpty G2))) as Hwe1
      by (eapply eqt_wf_l; exact Hea).
  assert (wft (oEmpty G2) (sCode G2 oIrr oL0)) as HwEmp2
      by (apply wft_U0irr_iota; [ exact HwG2 | apply wf_Empty; exact HwG2 ]).
  (* the Emptyrec at the "1" arguments, retyped over [G2] *)
  assert (eqt (sElt G2 rA2 lA2 A1)
            (oEmptyrec G1 rA2 lA2 A1 e1) (oEmptyrec G2 rA2 lA2 A1 e1)) as Hret.
  { apply Emptyrec_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact Hwl
      | apply eq_term_refl; exact HwA1
      | apply eq_term_refl; exact Hwe1 ]. }
  apply ceq_exp.
  { apply Emptyrec_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact Hwl
      | exact HAa
      | exact Hea ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  (* (a) the result code's normal form *)
  destruct (ceq_code_nf Hrnf Hlnf HD Hg (HAb D g HD Hg)) as [A0 [HA0 HA0eq]].
  assert (eqt (sTy D (iEl rA2 lA2))
            (oTySubst D G2 g (iEl rA2 lA2) (oEl G2 rA2 lA2 A1))
            (oEl D rA2 lA2 A0)) as Hty1.
  { eapply eq_term_trans; [ apply eq_El_subst; assumption | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact Hwl
      | exact HA0eq ]. }
  assert (eqt (sTy D (iEl rA2 lA2))
            (oTySubst D G2 g (iEl rA2 lA2) (oEl G2 rA2 lA2 A2))
            (oEl D rA2 lA2 A0)) as Hty2.
  { eapply eq_term_trans; [ | exact Hty1 ].
    apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact Hwg
      | apply eq_term_refl; wfa
      | apply El_cong;
        [ apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact Hwl
        | apply eq_term_sym; exact HAa ] ]. }
  (* (b) the argument's neutral form *)
  assert (eqt (sTy D (iEl oIrr oL0))
            (oTySubst D G2 g (iEl oIrr oL0) (oEl G2 oIrr oL0 (oEmpty G2)))
            (oEl D oIrr oL0 (oEmpty D))) as HtyE.
  { eapply eq_term_trans;
      [ apply eq_El_subst; auto using wf_Irr, wf_L0 | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Irr
      | apply eq_term_refl; apply wf_L0
      | apply eq_Empty_subst; assumption ]. }
  assert (HasNe D (iEl oIrr oL0) (oEl D oIrr oL0 (oEmpty D))
            (oExpSubst D G2 g (iEl oIrr oL0)
               (oEl G2 oIrr oL0 (oEmpty G2)) e1)) as Hne.
  { eapply RTmN_elim with
      (i0 := iEl oIrr oL0) (A0 := oEl D oIrr oL0 (oEmpty D))
      (P := HasNe D (iEl oIrr oL0) (oEl D oIrr oL0 (oEmpty D))).
    - apply Heb; assumption.
    - apply eq_term_refl; wfa.
    - apply tyok_El; apply nfcode_empty; exact HD.
    - exact HtyE.
    - apply RTy_empty_i; exact HD. }
  destruct Hne as [n [Hn Hneq]].
  (* (c) assemble *)
  destruct (RTyEx_of_NfCode HA0) as [P HP].
  eapply RTmN_intro with
    (i0 := iEl rA2 lA2) (A0 := oEl D rA2 lA2 A0) (P := P).
  - apply eq_term_refl; wfa.
  - apply tyok_El; exact HA0.
  - exact Hty2.
  - exact HP.
  - apply (RTy_reflect HP).
    exists (oEmptyrec D rA2 lA2 A0 n); split;
      [ apply neet_emptyrec; [ exact HA0 | exact Hn ] | ].
    eapply eq_term_trans.
    { eapply eq_term_conv.
      - apply ExpSubst_cong
          with (G1 := D) (G2 := D) (G1' := G2) (G2' := G2)
               (g1 := g) (g2 := g) (i1 := iEl rA2 lA2) (i2 := iEl rA2 lA2)
               (A1 := oEl G2 rA2 lA2 A2) (A2 := oEl G2 rA2 lA2 A1)
               (v1 := oEmptyrec G1 rA2 lA2 A1 e1)
               (v2 := oEmptyrec G2 rA2 lA2 A1 e1);
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact HwG2
          | apply eq_term_refl; exact Hwg
          | apply eq_term_refl; wfa
          | apply El_cong;
            [ apply eq_term_refl; exact HwG2
            | apply eq_term_refl; exact Hwr
            | apply eq_term_refl; exact Hwl
            | apply eq_term_sym; exact HAa ]
          | exact Hret ].
      - apply eq_sort_exp_ty; [ exact HwD | wfa | exact Hty1 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_Emptyrec_subst; assumption
        | apply eq_sort_exp_ty; [ exact HwD | wfa | exact Hty1 ] ]. }
    apply Emptyrec_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact Hwl
      | exact HA0eq
      | exact Hneq ].
Qed.

(* ================================================================== *)
(* 2.  Going under a binder                                            *)
(* ================================================================== *)

(* [Pi_irr]'s codomain code sits at info [rel (iota L1)] rather than at
   [iCode L0] (trap (A) of WIP/DttNfWf.v), so the code reading has to
   tolerate an arbitrary provably-equal info. *)
Lemma ceq_code_nf' G r l c D g i
  : RelNf r -> LvlNf l -> EnvOk D -> RSubN D G g ->
    eqt sInfo i (iCode l) ->
    RTmN D i (oTySubst D G g i (oU G r l)) (oExpSubst D G g i (oU G r l) c) ->
    HasNfCode D r l (oExpSubst D G g i (oU G r l) c).
Proof.
  intros Hr Hl HD Hg Hi HR.
  assert (wft r sRelevance) as Hrw by (apply RelNf_wf; exact Hr).
  assert (wft l sLvl) as Hlw by (apply LvlNf_wf; exact Hl).
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact Hg).
  assert (wft D sEnv) as HDw by (eapply wft_sub_dom; exact Hgw).
  assert (wft G sEnv) as HGw by (eapply wft_sub_cod; exact Hgw).
  eapply RTmN_elim with (i0 := iCode l) (A0 := oU D r l)
                        (P := HasNfCode D r l).
  - exact HR.
  - exact Hi.
  - apply tyok_U; assumption.
  - eapply eq_term_trans.
    + apply TySubst_cong
        with (G1 := D) (G2 := D) (G1' := G) (G2' := G) (g1 := g) (g2 := g)
             (i1 := i) (i2 := iCode l) (A1 := oU G r l) (A2 := oU G r l);
        [ apply eq_term_refl; exact HDw
        | apply eq_term_refl; exact HGw
        | apply eq_term_refl; exact Hgw
        | exact Hi
        | apply eq_term_refl; apply wf_U; assumption ].
    + apply eq_U_subst; assumption.
  - apply RTy_U_i; assumption.
Qed.

(* [eq_liftW_cong] (WIP/DttNfWk.v) varies only the lifted type's normal
   representative; going under a binder here has to vary the CODOMAIN
   ENVIRONMENT as well, because the binder's domain code is normalised at
   the reducible substitution's witness environment, not at the one the
   rule names.  Same proof, three more moving parts. *)
Lemma eq_liftW_gen D G1 G2 w i A1 A2 A1' A2'
  : wft D sEnv -> wft G1 sEnv -> wft G2 sEnv -> wft i sInfo ->
    wft A1 (sTy G1 i) -> wft A2 (sTy G2 i) ->
    wft A1' (sTy D i) -> wft A2' (sTy D i) ->
    wft w (sSub D G1) ->
    eqt sEnv G1 G2 -> eqt (sTy G2 i) A1 A2 ->
    eqt (sTy D i) (oTySubst D G1 w i A1) A1' ->
    eqt (sTy D i) (oTySubst D G2 w i A2) A2' ->
    eqt (sSub (oExt D i A2') (oExt G2 i A2))
      (oLiftW D G1 w i A1 A1') (oLiftW D G2 w i A2 A2').
Proof.
  intros HD HG1 HG2 Hi HA1 HA2 HA1' HA2' Hw HG12 HA12 Heq1 Heq2.
  assert (wft w (sSub D G2)) as Hw2.
  { eapply wf_term_conv; [ exact Hw | ].
    apply sSub_cong; [ apply eq_term_refl; exact HD | exact HG12 ]. }
  assert (eqt (sTy D i) A1' A2') as H12.
  { eapply eq_term_trans; [ apply eq_term_sym; exact Heq1 | ].
    eapply eq_term_trans; [ | exact Heq2 ].
    apply TySubst_cong;
      [ apply eq_term_refl; exact HD
      | exact HG12
      | apply eq_term_refl; exact Hw2
      | apply eq_term_refl; exact Hi
      | exact HA12 ]. }
  assert (eqt sEnv (oExt D i A1') (oExt D i A2')) as HE.
  { apply Ext_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact Hi
      | exact H12 ]. }
  unfold oLiftW; apply Snoc_cong;
    [ exact HE
    | exact HG12
    | apply eq_term_refl; exact Hi
    | exact HA12
    | apply Cmp_cong;
      [ exact HE
      | apply eq_term_refl; exact HD
      | exact HG12
      | apply Wkn_cong;
        [ apply eq_term_refl; exact HD
        | apply eq_term_refl; exact Hi
        | exact H12 ]
      | apply eq_term_refl; exact Hw2 ]
    | ].
  eapply eq_term_conv.
  - apply Hd_cong;
      [ apply eq_term_refl; exact HD
      | apply eq_term_refl; exact Hi
      | exact H12 ].
  - apply eq_sort_exp_ty;
      [ apply wf_Ext; assumption | exact Hi
      | apply eq_wk_lift_ty; assumption ].
Qed.

(* THE lemma the four binder congruences share (observation in the header).

   Given the domain code argument's clause, and a reducible [g : D -> G],
   it produces (i) the normal code [F0] of [g[F]] over [D], and (ii) a
   REDUCIBLE substitution [h] into [oExtC G rF lF F], provably equal to the
   [oLift g] that "Pi_rel subst" and friends name.

   The work is (ii).  Layer 3's [RSubN_liftC] wants [NfCode G rF lF F],
   which a congruence has no reason to have -- [G] and [F] are arbitrary
   syntax there.  But [RSubN D G g] carries a NORMAL witness environment
   [G0], and the identity substitution at [G0] is reducible ([RSub_id]),
   so the clause itself produces the normal representative [Fw] of [F] over
   [G0]; lifting happens there, and [eq_liftW_gen] moves the result back. *)
Lemma binder_lift G rF lF F D g
  : RelNf rF -> LvlNf lF -> wft F (sCode G rF lF) ->
    (forall D' g', EnvOk D' -> RSubN D' G g' ->
       RTmN D' (iCode lF) (oTySubst D' G g' (iCode lF) (oU G rF lF))
            (oExpSubst D' G g' (iCode lF) (oU G rF lF) F)) ->
    EnvOk D -> RSubN D G g ->
    exists F0 h,
      NfCode D rF lF F0
      /\ eqt (sCode D rF lF)
             (oExpSubst D G g (iCode lF) (oU G rF lF) F) F0
      /\ EnvOk (oExtC D rF lF F0)
      /\ RSubN (oExtC D rF lF F0) (oExtC G rF lF F) h
      /\ eqt (sSub (oExtC D rF lF F0) (oExtC G rF lF F))
             (oLift D G g rF lF F) h.
Proof.
  intros HrF HlF HFw HFb HD Hg.
  assert (wft rF sRelevance) as HrFw by (apply RelNf_wf; exact HrF).
  assert (wft lF sLvl) as HlFw by (apply LvlNf_wf; exact HlF).
  assert (wft (iEl rF lF) sInfo) as HiFw
      by (unfold iEl; apply wf_Info; [ exact HrFw | apply wf_Iota; exact HlFw ]).
  assert (wft (iCode lF) sInfo) as HcFw
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlFw ]).
  assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact HFw).
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact Hg).
  pose proof Hg as Hg'.
  destruct (ceq_code_nf HrF HlF HD Hg' (HFb D g HD Hg')) as [F0 [HF0 HF0eq]].
  assert (wft F0 (sCode D rF lF)) as HF0w by (apply NfCode_wf; exact HF0).
  destruct Hg as [G0 (HG0 & HGeq & HR)].
  assert (wft G0 sEnv) as HG0w by (apply EnvOk_wf; exact HG0).
  assert (RSubN G0 G (oId G0)) as HidR.
  { exists G0; repeat split;
      [ exact HG0 | exact HGeq | apply RSub_id; exact HG0 ]. }
  destruct (ceq_code_nf HrF HlF HG0 HidR (HFb G0 (oId G0) HG0 HidR))
    as [Fw [HFw' HFweq]].
  assert (wft Fw (sCode G0 rF lF)) as HFww by (apply NfCode_wf; exact HFw').
  assert (wft F (sCode G0 rF lF)) as HF1w0.
  { eapply wf_term_conv; [ exact HFw | ].
    apply sExp_cong;
      [ exact HGeq | apply eq_term_refl; exact HcFw
      | apply U_cong;
        [ exact HGeq
        | apply eq_term_refl; exact HrFw
        | apply eq_term_refl; exact HlFw ] ]. }
  assert (eqt (sCode G0 rF lF) F Fw) as HFFw.
  { eapply eq_term_trans; [ | exact HFweq ].
    apply eq_term_sym.
    eapply eq_term_trans.
    - eapply eq_term_conv.
      + apply ExpSubst_cong
          with (G1 := G0) (G2 := G0) (G1' := G) (G2' := G0)
               (g1 := oId G0) (g2 := oId G0)
               (i1 := iCode lF) (i2 := iCode lF)
               (A1 := oU G rF lF) (A2 := oU G0 rF lF) (v1 := F) (v2 := F);
          [ apply eq_term_refl; exact HG0w
          | exact HGeq
          | apply eq_term_refl; apply wf_Id; exact HG0w
          | apply eq_term_refl; exact HcFw
          | apply U_cong;
            [ exact HGeq
            | apply eq_term_refl; exact HrFw
            | apply eq_term_refl; exact HlFw ]
          | apply eq_term_refl; exact HF1w0 ].
      + apply eq_sort_exp_ty;
          [ exact HG0w | exact HcFw
          | apply eq_ty_subst_id;
            [ exact HG0w | exact HcFw | apply wf_U; assumption ] ].
    - apply eq_exp_subst_id;
        [ exact HG0w | exact HcFw | apply wf_U; assumption | exact HF1w0 ]. }
  assert (eqt (sCode G rF lF) Fw F) as HFwF.
  { eapply eq_term_conv; [ apply eq_term_sym; exact HFFw | ].
    apply sExp_cong;
      [ apply eq_term_sym; exact HGeq
      | apply eq_term_refl; exact HcFw
      | apply U_cong;
        [ apply eq_term_sym; exact HGeq
        | apply eq_term_refl; exact HrFw
        | apply eq_term_refl; exact HlFw ] ]. }
  assert (eqt (sCode D rF lF)
            (oExpSubst D G0 g (iCode lF) (oU G0 rF lF) Fw) F0) as HFwsub.
  { eapply eq_term_trans; [ | exact HF0eq ].
    eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D) (G2 := D) (G1' := G0) (G2' := G)
             (g1 := g) (g2 := g) (i1 := iCode lF) (i2 := iCode lF)
             (A1 := oU G0 rF lF) (A2 := oU G rF lF) (v1 := Fw) (v2 := F);
        [ apply eq_term_refl; exact HDw
        | apply eq_term_sym; exact HGeq
        | apply eq_term_refl; exact Hgw
        | apply eq_term_refl; exact HcFw
        | apply U_cong;
          [ apply eq_term_sym; exact HGeq
          | apply eq_term_refl; exact HrFw
          | apply eq_term_refl; exact HlFw ]
        | exact HFwF ].
    - apply eq_sort_exp_ty;
        [ exact HDw | exact HcFw | apply eq_U_subst; assumption ]. }
  destruct (RSub_liftC (D := D) (G := G0) (g := g) (rF := rF) (lF := lF)
              (F := Fw) (F' := F0) HR HD HFw' HF0 HFwsub)
    as [HL [HEok HeqEl]].
  assert (eqt sEnv (oExtC G rF lF F) (oExtC G0 rF lF Fw)) as HEnvEq.
  { unfold oExtC; apply Ext_cong;
      [ exact HGeq | apply eq_term_refl; exact HiFw
      | apply El_cong;
        [ exact HGeq
        | apply eq_term_refl; exact HrFw
        | apply eq_term_refl; exact HlFw
        | exact HFFw ] ]. }
  exists F0, (oLiftW D G0 g (iEl rF lF) (oEl G0 rF lF Fw) (oEl D rF lF F0)).
  repeat split; [ exact HF0 | exact HF0eq | exact HEok | | ].
  - exists (oExtC G0 rF lF Fw); repeat split;
      [ unfold oExtC; apply envok_ext; [ exact HG0 | apply tyok_El; exact HFw' ]
      | exact HEnvEq
      | exact HL ].
  - eapply eq_term_conv.
    + rewrite oLift_oLiftW.
      apply eq_liftW_gen with (G1 := G) (A1 := oEl G rF lF F);
        [ exact HDw | exact HGw | exact HG0w | exact HiFw
        | apply wf_El; assumption
        | apply wf_El; assumption
        | apply wf_El; [ exact HDw | exact HrFw | exact HlFw
                       | eapply eqt_wf_l; exact HF0eq ]
        | apply wf_El; assumption
        | exact Hgw
        | exact HGeq
        | apply El_cong;
          [ exact HGeq
          | apply eq_term_refl; exact HrFw
          | apply eq_term_refl; exact HlFw
          | exact HFFw ]
        | apply eq_El_subst; assumption
        | exact HeqEl ].
    + apply sSub_cong;
        [ apply eq_term_refl; apply EnvOk_wf; exact HEok
        | apply eq_term_sym; exact HEnvEq ].
Qed.

(* ================================================================== *)
(* 3.  The two [Pi] congruences                                        *)
(* ================================================================== *)

(* A [Pi] concludes at a CODE sort, so the semantic content is
   [HasNfCode] of the instance: push the substitution in with
   "Pi_rel subst", take the domain's normal code from its own clause and
   the codomain's from its clause AT THE LIFTED SUBSTITUTION (section 2),
   and assemble with [nfcode_pi_rel]. *)
Lemma cong_PiRel G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 -> Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sCode G2 oRel lG2)
      (oPiRel G1 rF1 lF1 lG1 F1 B1) (oPiRel G2 rF2 lF2 lG2 F2 B2).
Proof.
  intros HGc Hr Hlf Hlg HFc HBc.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_exp_e in HFc as [HFa HFb].
  apply Ceq_exp_e in HBc as [HBa HBb].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft lG2 sLvl) as HwlG by (apply LvlNf_wf; exact Hlgnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft F1 (sCode G2 rF2 lF2)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G2 rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B1 (sCode (oExtC G2 rF2 lF2 F2) oRel lG2)) as HwB1
      by (eapply eqt_wf_l; exact HBa).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (iCode lG2) sInfo) as HcG
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlG ]).
  assert (wft (oExtC G2 rF2 lF2 F2) sEnv) as HwGF2
      by (apply wf_ExtC; assumption).
  assert (wft (oExtC G2 rF2 lF2 F1) sEnv) as HwGF1
      by (apply wf_ExtC; assumption).
  assert (eqt sEnv (oExtC G2 rF2 lF2 F2) (oExtC G2 rF2 lF2 F1)) as HExtEq.
  { unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact HiF
      | apply El_cong;
        [ apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_sym; exact HFa ] ]. }
  assert (wft B1 (sCode (oExtC G2 rF2 lF2 F1) oRel lG2)) as HwB1'.
  { eapply wf_term_conv; [ exact HwB1 | ].
    apply sExp_cong;
      [ exact HExtEq | apply eq_term_refl; exact HcG
      | apply U_cong;
        [ exact HExtEq
        | apply eq_term_refl; apply wf_Rel
        | apply eq_term_refl; exact HwlG ] ]. }
  apply ceq_exp.
  { apply PiRel_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | apply eq_term_refl; exact HwlG
      | exact HFa
      | exact HBa ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  destruct (binder_lift Hrnf Hlfnf HwF1 HFb HD Hg)
    as [F0 [h (HF0 & HF0eq & HEok & HRS & HLeq)]].
  assert (wft (oExtC D rF2 lF2 F0) sEnv) as HwDF
      by (apply EnvOk_wf; exact HEok).
  assert (RSubN (oExtC D rF2 lF2 F0) (oExtC G2 rF2 lF2 F2) h) as HRS2
      by (eapply RSubN_env; [ exact HRS | apply eq_term_sym; exact HExtEq ]).
  assert (wft h (sSub (oExtC D rF2 lF2 F0) (oExtC G2 rF2 lF2 F2))) as Hwh
      by (apply RSubN_wf; exact HRS2).
  destruct (ceq_code_nf relnf_rel Hlgnf HEok HRS2
              (HBb (oExtC D rF2 lF2 F0) h HEok HRS2)) as [B0 [HB0 HB0eq]].
  (* ---- the equation ---- *)
  assert (eqt (sCode D oRel lG2)
            (oExpSubst D G2 g (iCode lG2) (oU G2 oRel lG2)
               (oPiRel G1 rF2 lF2 lG2 F1 B1))
            (oExpSubst D G2 g (iCode lG2) (oU G2 oRel lG2)
               (oPiRel G2 rF2 lF2 lG2 F1 B1))) as HstepA.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D) (G2 := D) (G1' := G2) (G2' := G2)
             (g1 := g) (g2 := g) (i1 := iCode lG2) (i2 := iCode lG2)
             (A1 := oU G2 oRel lG2) (A2 := oU G2 oRel lG2)
             (v1 := oPiRel G1 rF2 lF2 lG2 F1 B1)
             (v2 := oPiRel G2 rF2 lF2 lG2 F1 B1);
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; exact HcG
        | apply eq_term_refl; apply wf_U;
          [ exact HwG2 | apply wf_Rel | exact HwlG ]
        | apply PiRel_cong;
          [ exact HG
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | apply eq_term_refl; exact HwlG
          | apply eq_term_refl; exact HwF1
          | apply eq_term_refl; exact HwB1' ] ].
    - apply eq_sort_exp_ty;
        [ exact HwD | exact HcG
        | apply eq_U_subst;
          [ exact HwD | exact HwG2 | exact Hwg | apply wf_Rel | exact HwlG ] ]. }
  assert (eqt (sCode (oExtC D rF2 lF2 F0) oRel lG2)
            (oExpSubst (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F1))
               (oExtC G2 rF2 lF2 F1) (oLift D G2 g rF2 lF2 F1)
               (iCode lG2) (oU (oExtC G2 rF2 lF2 F1) oRel lG2) B1)
            (oExpSubst (oExtC D rF2 lF2 F0) (oExtC G2 rF2 lF2 F2) h
               (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B1))
    as HstepB.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F1))
             (G2 := oExtC D rF2 lF2 F0)
             (G1' := oExtC G2 rF2 lF2 F1) (G2' := oExtC G2 rF2 lF2 F2)
             (g1 := oLift D G2 g rF2 lF2 F1) (g2 := h)
             (i1 := iCode lG2) (i2 := iCode lG2)
             (A1 := oU (oExtC G2 rF2 lF2 F1) oRel lG2)
             (A2 := oU (oExtC G2 rF2 lF2 F2) oRel lG2)
             (v1 := B1) (v2 := B1);
        [ unfold oExtC; apply Ext_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact HiF
          | apply El_cong;
            [ apply eq_term_refl; exact HwD
            | apply eq_term_refl; exact Hwr
            | apply eq_term_refl; exact HwlF
            | exact HF0eq ] ]
        | apply eq_term_sym; exact HExtEq
        | eapply eq_term_conv;
          [ exact HLeq
          | apply sSub_cong;
            [ apply eq_term_refl; exact HwDF
            | apply eq_term_sym; exact HExtEq ] ]
        | apply eq_term_refl; exact HcG
        | apply U_cong;
          [ apply eq_term_sym; exact HExtEq
          | apply eq_term_refl; apply wf_Rel
          | apply eq_term_refl; exact HwlG ]
        | apply eq_term_refl; exact HwB1 ].
    - apply eq_sort_exp_ty;
        [ exact HwDF | exact HcG
        | apply eq_U_subst;
          [ exact HwDF | exact HwGF2 | exact Hwh | apply wf_Rel
          | exact HwlG ] ]. }
  (* ---- assemble ---- *)
  eapply RTmN_intro with
    (i0 := iCode lG2) (A0 := oU D oRel lG2) (P := HasNfCode D oRel lG2).
  - apply eq_term_refl; exact HcG.
  - apply tyok_U; [ exact HD | constructor | exact Hlgnf ].
  - apply eq_U_subst;
      [ exact HwD | exact HwG2 | exact Hwg | apply wf_Rel | exact HwlG ].
  - apply RTy_U_i; [ exact HD | constructor | exact Hlgnf ].
  - exists (oPiRel D rF2 lF2 lG2 F0 B0); split;
      [ apply nfcode_pi_rel; assumption | ].
    eapply eq_term_trans; [ exact HstepA | ].
    eapply eq_term_trans;
      [ apply eq_Pi_rel_subst;
        [ exact HwD | exact HwG2 | exact Hwg | exact Hwr | exact HwlF
        | exact HwlG | exact HwF1 | exact HwB1' ] | ].
    apply PiRel_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | apply eq_term_refl; exact HwlG
      | exact HF0eq
      | eapply eq_term_trans; [ exact HstepB | exact HB0eq ] ].
Qed.

(* ---- the [iota L1] spelling of a level-0 universe ----------------- *)

(* [Pi_irr] and its substitution commutation state the codomain code and
   the conclusion at info [rel (iota L1)], where every other rule of the
   fragment uses [iCode L0 = rel (next L0)].  Both name the same sort, via
   "next0"; these two lemmas are the bridge, and they are the only place
   the mismatch is paid for. *)
Lemma eq_U_subst_i1c G G' g r
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') -> wft r sRelevance ->
    eqt (sTy G (iCode oL0))
      (oTySubst G G' g (oInfo oRel (oIota oL1)) (oU G' r oL0)) (oU G r oL0).
Proof.
  intros HG HG' Hg Hr.
  assert (wft (oU G' r oL0) (sTy G' (iCode oL0))) as HU'
      by (apply wf_U; [ exact HG' | exact Hr | apply wf_L0 ]).
  eapply eq_term_trans.
  - apply TySubst_cong
      with (G1 := G) (G2 := G) (G1' := G') (G2' := G') (g1 := g) (g2 := g)
           (i1 := oInfo oRel (oIota oL1)) (i2 := iCode oL0)
           (A1 := oU G' r oL0) (A2 := oU G' r oL0);
      [ apply eq_term_refl; exact HG
      | apply eq_term_refl; exact HG'
      | apply eq_term_refl; exact Hg
      | apply eq_term_sym; apply eq_info_next0
      | apply eq_term_refl; exact HU' ].
  - apply eq_U_subst;
      [ exact HG | exact HG' | exact Hg | exact Hr | apply wf_L0 ].
Qed.

Lemma eq_U_subst_i1 G G' g r
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') -> wft r sRelevance ->
    eqt (sTy G (oInfo oRel (oIota oL1)))
      (oTySubst G G' g (oInfo oRel (oIota oL1)) (oU G' r oL0)) (oU G r oL0).
Proof.
  intros HG HG' Hg Hr.
  eapply eq_term_conv;
    [ apply eq_U_subst_i1c; assumption
    | apply sTy_cong;
      [ apply eq_term_refl; exact HG | apply eq_info_next0 ] ].
Qed.

(* The mirror of [cong_PiRel].  Everything is the same except that the
   codomain code and the conclusion live at [rel (iota L1)]: the code
   reading goes through [ceq_code_nf'] and the equation chain is run at the
   [iota] spelling and converted to [sCode] once, at the end. *)
Lemma cong_PiIrr G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sExp (oExtC G2 rF2 lF2 F2) (oInfo oRel (oIota oL1))
                (oU (oExtC G2 rF2 lF2 F2) oIrr oL0)) B1 B2 ->
    Ceq_term (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0))
      (oPiIrr G1 rF1 lF1 F1 B1) (oPiIrr G2 rF2 lF2 F2 B2).
Proof.
  intros HGc Hr Hlf HFc HBc.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_exp_e in HFc as [HFa HFb].
  apply Ceq_exp_e in HBc as [HBa HBb].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft F1 (sCode G2 rF2 lF2)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G2 rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B1 (sExp (oExtC G2 rF2 lF2 F2) (oInfo oRel (oIota oL1))
                    (oU (oExtC G2 rF2 lF2 F2) oIrr oL0))) as HwB1
      by (eapply eqt_wf_l; exact HBa).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (oInfo oRel (oIota oL1)) sInfo) as Hi1L
      by (apply wf_Info; [ apply wf_Rel | apply wf_Iota; apply wf_L1 ]).
  assert (wft (oExtC G2 rF2 lF2 F2) sEnv) as HwGF2
      by (apply wf_ExtC; assumption).
  assert (wft (oExtC G2 rF2 lF2 F1) sEnv) as HwGF1
      by (apply wf_ExtC; assumption).
  assert (eqt sEnv (oExtC G2 rF2 lF2 F2) (oExtC G2 rF2 lF2 F1)) as HExtEq.
  { unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact HiF
      | apply El_cong;
        [ apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_sym; exact HFa ] ]. }
  assert (wft B1 (sExp (oExtC G2 rF2 lF2 F1) (oInfo oRel (oIota oL1))
                    (oU (oExtC G2 rF2 lF2 F1) oIrr oL0))) as HwB1'.
  { eapply wf_term_conv; [ exact HwB1 | ].
    apply sExp_cong;
      [ exact HExtEq | apply eq_term_refl; exact Hi1L
      | eapply eq_term_conv;
        [ apply U_cong;
          [ exact HExtEq
          | apply eq_term_refl; apply wf_Irr
          | apply eq_term_refl; apply wf_L0 ]
        | apply sTy_cong;
          [ apply eq_term_refl; exact HwGF1 | apply eq_info_next0 ] ] ]. }
  apply ceq_exp.
  { apply PiIrr_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HFa
      | exact HBa ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  destruct (binder_lift Hrnf Hlfnf HwF1 HFb HD Hg)
    as [F0 [h (HF0 & HF0eq & HEok & HRS & HLeq)]].
  assert (wft (oExtC D rF2 lF2 F0) sEnv) as HwDF
      by (apply EnvOk_wf; exact HEok).
  assert (RSubN (oExtC D rF2 lF2 F0) (oExtC G2 rF2 lF2 F2) h) as HRS2
      by (eapply RSubN_env; [ exact HRS | apply eq_term_sym; exact HExtEq ]).
  assert (wft h (sSub (oExtC D rF2 lF2 F0) (oExtC G2 rF2 lF2 F2))) as Hwh
      by (apply RSubN_wf; exact HRS2).
  destruct (ceq_code_nf' (r := oIrr) (l := oL0) relnf_irr lvlnf_L0 HEok HRS2
              (eq_term_sym eq_info_next0)
              (HBb (oExtC D rF2 lF2 F0) h HEok HRS2)) as [B0 [HB0 HB0eq]].
  (* ---- the equation, run at the [iota L1] spelling ---- *)
  assert (eqt (sExp D (oInfo oRel (oIota oL1)) (oU D oIrr oL0))
            (oExpSubst D G2 g (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0)
               (oPiIrr G1 rF2 lF2 F1 B1))
            (oExpSubst D G2 g (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0)
               (oPiIrr G2 rF2 lF2 F1 B1))) as HstepA.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D) (G2 := D) (G1' := G2) (G2' := G2)
             (g1 := g) (g2 := g)
             (i1 := oInfo oRel (oIota oL1)) (i2 := oInfo oRel (oIota oL1))
             (A1 := oU G2 oIrr oL0) (A2 := oU G2 oIrr oL0)
             (v1 := oPiIrr G1 rF2 lF2 F1 B1)
             (v2 := oPiIrr G2 rF2 lF2 F1 B1);
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; exact Hi1L
        | apply eq_term_refl; apply wf_U_irr0'; exact HwG2
        | apply PiIrr_cong;
          [ exact HG
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | apply eq_term_refl; exact HwF1
          | apply eq_term_refl; exact HwB1' ] ].
    - apply eq_sort_exp_ty;
        [ exact HwD | exact Hi1L
        | apply eq_U_subst_i1;
          [ exact HwD | exact HwG2 | exact Hwg | apply wf_Irr ] ]. }
  assert (eqt (sExp (oExtC D rF2 lF2 F0) (oInfo oRel (oIota oL1))
                 (oU (oExtC D rF2 lF2 F0) oIrr oL0))
            (oExpSubst (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F1))
               (oExtC G2 rF2 lF2 F1) (oLift D G2 g rF2 lF2 F1)
               (oInfo oRel (oIota oL1)) (oU (oExtC G2 rF2 lF2 F1) oIrr oL0) B1)
            (oExpSubst (oExtC D rF2 lF2 F0) (oExtC G2 rF2 lF2 F2) h
               (oInfo oRel (oIota oL1)) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B1))
    as HstepB.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F1))
             (G2 := oExtC D rF2 lF2 F0)
             (G1' := oExtC G2 rF2 lF2 F1) (G2' := oExtC G2 rF2 lF2 F2)
             (g1 := oLift D G2 g rF2 lF2 F1) (g2 := h)
             (i1 := oInfo oRel (oIota oL1)) (i2 := oInfo oRel (oIota oL1))
             (A1 := oU (oExtC G2 rF2 lF2 F1) oIrr oL0)
             (A2 := oU (oExtC G2 rF2 lF2 F2) oIrr oL0)
             (v1 := B1) (v2 := B1);
        [ unfold oExtC; apply Ext_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact HiF
          | apply El_cong;
            [ apply eq_term_refl; exact HwD
            | apply eq_term_refl; exact Hwr
            | apply eq_term_refl; exact HwlF
            | exact HF0eq ] ]
        | apply eq_term_sym; exact HExtEq
        | eapply eq_term_conv;
          [ exact HLeq
          | apply sSub_cong;
            [ apply eq_term_refl; exact HwDF
            | apply eq_term_sym; exact HExtEq ] ]
        | apply eq_term_refl; exact Hi1L
        | eapply eq_term_conv;
          [ apply U_cong;
            [ apply eq_term_sym; exact HExtEq
            | apply eq_term_refl; apply wf_Irr
            | apply eq_term_refl; apply wf_L0 ]
          | apply sTy_cong;
            [ apply eq_term_refl; exact HwGF2 | apply eq_info_next0 ] ]
        | apply eq_term_refl; exact HwB1 ].
    - apply eq_sort_exp_ty;
        [ exact HwDF | exact Hi1L
        | apply eq_U_subst_i1;
          [ exact HwDF | exact HwGF2 | exact Hwh | apply wf_Irr ] ]. }
  (* ---- assemble ---- *)
  eapply RTmN_intro with
    (i0 := iCode oL0) (A0 := oU D oIrr oL0) (P := HasNfCode D oIrr oL0).
  - apply eq_term_sym; apply eq_info_next0.
  - apply tyok_U; [ exact HD | constructor | constructor ].
  - apply eq_U_subst_i1c;
      [ exact HwD | exact HwG2 | exact Hwg | apply wf_Irr ].
  - apply RTy_U_i; [ exact HD | constructor | constructor ].
  - exists (oPiIrr D rF2 lF2 F0 B0); split;
      [ apply nfcode_pi_irr; assumption | ].
    eapply eq_term_conv;
      [ | apply eq_sort_sym; apply eq_sort_U_irr0; exact HwD ].
    eapply eq_term_trans; [ exact HstepA | ].
    eapply eq_term_trans;
      [ apply eq_Pi_irr_subst;
        [ exact HwD | exact HwG2 | exact Hwg | exact Hwr | exact HwlF
        | exact HwF1 | exact HwB1' ] | ].
    apply PiIrr_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HF0eq
      | eapply eq_term_trans;
        [ exact HstepB
        | eapply eq_term_conv;
          [ exact HB0eq
          | apply eq_sort_U_irr0; exact HwDF ] ] ].
Qed.

(* ================================================================== *)
(* 4.  The binder toolkit, factored                                    *)
(* ================================================================== *)

(* The identity trick of [binder_lift], isolated: a congruence's domain
   code [F] is arbitrary syntax over an arbitrary [G], but [RSubN D G g]
   carries a NORMAL witness environment [G0] provably equal to [G], and the
   identity substitution at [G0] is reducible ([RSub_id]).  Running the code
   argument's own clause there produces the normal representative of [F]
   over [G0] -- which is what every Layer-3 lifting and snoc lemma
   demands. *)
Lemma binder_witness G rF lF F D g
  : RelNf rF -> LvlNf lF -> wft F (sCode G rF lF) ->
    (forall D' g', EnvOk D' -> RSubN D' G g' ->
       RTmN D' (iCode lF) (oTySubst D' G g' (iCode lF) (oU G rF lF))
            (oExpSubst D' G g' (iCode lF) (oU G rF lF) F)) ->
    EnvOk D -> RSubN D G g ->
    exists G0 Fw,
      EnvOk G0 /\ NfCode G0 rF lF Fw
      /\ eqt sEnv G G0 /\ eqt (sCode G0 rF lF) F Fw
      /\ RSub D G0 g.
Proof.
  intros HrF HlF HFw HFb HD Hg.
  assert (wft rF sRelevance) as HrFw by (apply RelNf_wf; exact HrF).
  assert (wft lF sLvl) as HlFw by (apply LvlNf_wf; exact HlF).
  assert (wft (iCode lF) sInfo) as HcFw
      by (unfold iCode; apply wf_Info;
          [ apply wf_Rel | apply wf_Next; exact HlFw ]).
  assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact HFw).
  destruct Hg as [G0 (HG0 & HGeq & HR)].
  assert (wft G0 sEnv) as HG0w by (apply EnvOk_wf; exact HG0).
  assert (RSubN G0 G (oId G0)) as HidR.
  { exists G0; repeat split;
      [ exact HG0 | exact HGeq | apply RSub_id; exact HG0 ]. }
  destruct (ceq_code_nf HrF HlF HG0 HidR (HFb G0 (oId G0) HG0 HidR))
    as [Fw [HFw' HFweq]].
  assert (wft F (sCode G0 rF lF)) as HFw0.
  { eapply wf_term_conv; [ exact HFw | ].
    apply sExp_cong;
      [ exact HGeq | apply eq_term_refl; exact HcFw
      | apply U_cong;
        [ exact HGeq | apply eq_term_refl; exact HrFw
        | apply eq_term_refl; exact HlFw ] ]. }
  exists G0, Fw; repeat split;
    [ exact HG0 | exact HFw' | exact HGeq | | exact HR ].
  eapply eq_term_trans; [ | exact HFweq ].
  apply eq_term_sym.
  eapply eq_term_trans.
  - eapply eq_term_conv.
    + apply ExpSubst_cong
        with (G1 := G0) (G2 := G0) (G1' := G) (G2' := G0)
             (g1 := oId G0) (g2 := oId G0)
             (i1 := iCode lF) (i2 := iCode lF)
             (A1 := oU G rF lF) (A2 := oU G0 rF lF) (v1 := F) (v2 := F);
        [ apply eq_term_refl; exact HG0w
        | exact HGeq
        | apply eq_term_refl; apply wf_Id; exact HG0w
        | apply eq_term_refl; exact HcFw
        | apply U_cong;
          [ exact HGeq | apply eq_term_refl; exact HrFw
          | apply eq_term_refl; exact HlFw ]
        | apply eq_term_refl; exact HFw0 ].
    + apply eq_sort_exp_ty;
        [ exact HG0w | exact HcFw
        | apply eq_ty_subst_id;
          [ exact HG0w | exact HcFw | apply wf_U; assumption ] ].
  - apply eq_exp_subst_id;
      [ exact HG0w | exact HcFw | apply wf_U; assumption | exact HFw0 ].
Qed.

(* The companion of [binder_lift] the two [lam] cases need: the
   substitution that instantiates a binder with a reducible argument is a
   [snoc], not a lift, and it too has to land in [oExtC G rF lF F] whose
   normality is not available. *)
Lemma binder_snoc G rF lF F
  : RelNf rF -> LvlNf lF -> wft F (sCode G rF lF) ->
    (forall D' g', EnvOk D' -> RSubN D' G g' ->
       RTmN D' (iCode lF) (oTySubst D' G g' (iCode lF) (oU G rF lF))
            (oExpSubst D' G g' (iCode lF) (oU G rF lF) F)) ->
    forall D u b, EnvOk D -> RSubN D G u ->
      wft b (sExp D (iEl rF lF) (oTySubst D G u (iEl rF lF) (oEl G rF lF F))) ->
      RTmN D (iEl rF lF) (oTySubst D G u (iEl rF lF) (oEl G rF lF F)) b ->
      RSubN D (oExtC G rF lF F)
        (oSnoc D G (iEl rF lF) (oEl G rF lF F) u b).
Proof.
  intros HrF HlF HFw HFb D u b HD Hu Hbw Hb.
  assert (wft rF sRelevance) as HrFw by (apply RelNf_wf; exact HrF).
  assert (wft lF sLvl) as HlFw by (apply LvlNf_wf; exact HlF).
  assert (wft (iEl rF lF) sInfo) as HiFw
      by (unfold iEl; apply wf_Info; [ exact HrFw | apply wf_Iota; exact HlFw ]).
  assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact HFw).
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft u (sSub D G)) as Huw by (apply RSubN_wf; exact Hu).
  destruct (binder_witness HrF HlF HFw HFb HD Hu)
    as [G0 [Fw (HG0 & HFw' & HGeq & HFFw & HR)]].
  assert (wft G0 sEnv) as HG0w by (apply EnvOk_wf; exact HG0).
  assert (wft Fw (sCode G0 rF lF)) as HFww by (apply NfCode_wf; exact HFw').
  assert (wft u (sSub D G0)) as Huw0.
  { eapply wf_term_conv; [ exact Huw | ].
    apply sSub_cong; [ apply eq_term_refl; exact HDw | exact HGeq ]. }
  assert (eqt (sTy G0 (iEl rF lF)) (oEl G rF lF F) (oEl G0 rF lF Fw)) as HElq
      by (apply El_cong;
          [ exact HGeq | apply eq_term_refl; exact HrFw
          | apply eq_term_refl; exact HlFw | exact HFFw ]).
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G u (iEl rF lF) (oEl G rF lF F))
            (oTySubst D G0 u (iEl rF lF) (oEl G0 rF lF Fw))) as HtyEq.
  { apply TySubst_cong;
      [ apply eq_term_refl; exact HDw
      | exact HGeq
      | apply eq_term_refl; exact Huw0
      | apply eq_term_refl; exact HiFw
      | exact HElq ]. }
  assert (wft b (sExp D (iEl rF lF)
                   (oTySubst D G0 u (iEl rF lF) (oEl G0 rF lF Fw)))) as Hbw0
      by (eapply wf_term_conv;
          [ exact Hbw
          | apply eq_sort_exp_ty; [ exact HDw | exact HiFw | exact HtyEq ] ]).
  exists (oExtC G0 rF lF Fw); repeat split.
  - unfold oExtC; apply envok_ext; [ exact HG0 | apply tyok_El; exact HFw' ].
  - unfold oExtC; apply Ext_cong;
      [ exact HGeq | apply eq_term_refl; exact HiFw | exact HElq ].
  - unfold oExtC; apply RSub_ext_intro.
    exists u, b; repeat split.
    + apply Snoc_cong;
        [ apply eq_term_refl; exact HDw
        | exact HGeq
        | apply eq_term_refl; exact HiFw
        | exact HElq
        | apply eq_term_refl; exact Huw0
        | apply eq_term_refl; exact Hbw0 ].
    + exact HR.
    + eapply RTmN_eq_ty; [ exact Hb | exact HtyEq ].
Qed.

(* ---- the normal Pi code of an instance, once ---------------------- *)

(* Everything the four [Pi]-shaped cases need out of the domain and
   codomain arguments' clauses.  Stated at the RIGHT-hand arguments
   throughout (the clauses constrain the left ones, and [RTmN_eq] moves
   them across), which is what keeps the substitution bookkeeping down to
   one [ExpSubst_cong]. *)
Lemma pi_rel_nf G rF lF lG F1 F2 B1 B2 D g
  : RelNf rF -> LvlNf lF -> LvlNf lG ->
    eqt (sCode G rF lF) F1 F2 ->
    (forall D' g', EnvOk D' -> RSubN D' G g' ->
       RTmN D' (iCode lF) (oTySubst D' G g' (iCode lF) (oU G rF lF))
            (oExpSubst D' G g' (iCode lF) (oU G rF lF) F1)) ->
    eqt (sCode (oExtC G rF lF F2) oRel lG) B1 B2 ->
    (forall D' g', EnvOk D' -> RSubN D' (oExtC G rF lF F2) g' ->
       RTmN D' (iCode lG)
         (oTySubst D' (oExtC G rF lF F2) g' (iCode lG)
            (oU (oExtC G rF lF F2) oRel lG))
         (oExpSubst D' (oExtC G rF lF F2) g' (iCode lG)
            (oU (oExtC G rF lF F2) oRel lG) B1)) ->
    EnvOk D -> RSubN D G g ->
    exists F0 B0,
      NfCode D rF lF F0
      /\ NfCode (oExtC D rF lF F0) oRel lG B0
      /\ eqt (sCode D rF lF)
             (oExpSubst D G g (iCode lF) (oU G rF lF) F2) F0
      /\ eqt (sCode (oExtC D rF lF F0) oRel lG)
             (oExpSubst (oExtC D rF lF (oCodeSubst D G g rF lF F2))
                (oExtC G rF lF F2) (oLift D G g rF lF F2)
                (iCode lG) (oU (oExtC G rF lF F2) oRel lG) B2) B0
      /\ eqt (sCode D oRel lG)
             (oExpSubst D G g (iCode lG) (oU G oRel lG)
                (oPiRel G rF lF lG F2 B2))
             (oPiRel D rF lF lG F0 B0).
Proof.
  intros HrF HlF HlG HFa HFb HBa HBb HD Hg.
  assert (wft rF sRelevance) as HrFw by (apply RelNf_wf; exact HrF).
  assert (wft lF sLvl) as HlFw by (apply LvlNf_wf; exact HlF).
  assert (wft lG sLvl) as HlGw by (apply LvlNf_wf; exact HlG).
  assert (wft F1 (sCode G rF lF)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G rF lF)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact HwF1).
  assert (wft B2 (sCode (oExtC G rF lF F2) oRel lG)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft (iCode lF) sInfo) as HcF
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlFw ]).
  assert (wft (iCode lG) sInfo) as HcG
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HlGw ]).
  assert (wft (iEl rF lF) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact HrFw | apply wf_Iota; exact HlFw ]).
  assert (wft (oExtC G rF lF F2) sEnv) as HwGF2 by (apply wf_ExtC; assumption).
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact Hg).
  (* the clauses, moved to the right-hand arguments *)
  assert (forall D' g', EnvOk D' -> RSubN D' G g' ->
            RTmN D' (iCode lF) (oTySubst D' G g' (iCode lF) (oU G rF lF))
                 (oExpSubst D' G g' (iCode lF) (oU G rF lF) F2)) as HFb2.
  { intros D' g' HD' Hg'.
    assert (wft D' sEnv) as HD'w by (apply EnvOk_wf; exact HD').
    assert (wft g' (sSub D' G)) as Hg'w by (apply RSubN_wf; exact Hg').
    eapply RTmN_eq; [ apply HFb; assumption | ].
    apply ExpSubst_cong;
      [ apply eq_term_refl; exact HD'w
      | apply eq_term_refl; exact HGw
      | apply eq_term_refl; exact Hg'w
      | apply eq_term_refl; exact HcF
      | apply eq_term_refl; apply wf_U; assumption
      | exact HFa ]. }
  assert (forall D' g', EnvOk D' -> RSubN D' (oExtC G rF lF F2) g' ->
            RTmN D' (iCode lG)
              (oTySubst D' (oExtC G rF lF F2) g' (iCode lG)
                 (oU (oExtC G rF lF F2) oRel lG))
              (oExpSubst D' (oExtC G rF lF F2) g' (iCode lG)
                 (oU (oExtC G rF lF F2) oRel lG) B2)) as HBb2.
  { intros D' g' HD' Hg'.
    assert (wft D' sEnv) as HD'w by (apply EnvOk_wf; exact HD').
    assert (wft g' (sSub D' (oExtC G rF lF F2))) as Hg'w
        by (apply RSubN_wf; exact Hg').
    eapply RTmN_eq; [ apply HBb; assumption | ].
    apply ExpSubst_cong;
      [ apply eq_term_refl; exact HD'w
      | apply eq_term_refl; exact HwGF2
      | apply eq_term_refl; exact Hg'w
      | apply eq_term_refl; exact HcG
      | apply eq_term_refl; apply wf_U;
        [ exact HwGF2 | apply wf_Rel | exact HlGw ]
      | exact HBa ]. }
  destruct (binder_lift HrF HlF HwF2 HFb2 HD Hg)
    as [F0 [h (HF0 & HF0eq & HEok & HRS & HLeq)]].
  assert (wft (oExtC D rF lF F0) sEnv) as HwDF
      by (apply EnvOk_wf; exact HEok).
  assert (wft h (sSub (oExtC D rF lF F0) (oExtC G rF lF F2))) as Hwh
      by (apply RSubN_wf; exact HRS).
  destruct (ceq_code_nf relnf_rel HlG HEok HRS
              (HBb2 (oExtC D rF lF F0) h HEok HRS)) as [B0 [HB0 HB0eq]].
  assert (eqt (sCode (oExtC D rF lF F0) oRel lG)
            (oExpSubst (oExtC D rF lF (oCodeSubst D G g rF lF F2))
               (oExtC G rF lF F2) (oLift D G g rF lF F2)
               (iCode lG) (oU (oExtC G rF lF F2) oRel lG) B2)
            (oExpSubst (oExtC D rF lF F0) (oExtC G rF lF F2) h
               (iCode lG) (oU (oExtC G rF lF F2) oRel lG) B2)) as HstepB.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := oExtC D rF lF (oCodeSubst D G g rF lF F2))
             (G2 := oExtC D rF lF F0)
             (G1' := oExtC G rF lF F2) (G2' := oExtC G rF lF F2)
             (g1 := oLift D G g rF lF F2) (g2 := h)
             (i1 := iCode lG) (i2 := iCode lG)
             (A1 := oU (oExtC G rF lF F2) oRel lG)
             (A2 := oU (oExtC G rF lF F2) oRel lG)
             (v1 := B2) (v2 := B2);
        [ unfold oExtC; apply Ext_cong;
          [ apply eq_term_refl; exact HDw
          | apply eq_term_refl; exact HiF
          | apply El_cong;
            [ apply eq_term_refl; exact HDw
            | apply eq_term_refl; exact HrFw
            | apply eq_term_refl; exact HlFw
            | exact HF0eq ] ]
        | apply eq_term_refl; exact HwGF2
        | exact HLeq
        | apply eq_term_refl; exact HcG
        | apply eq_term_refl; apply wf_U;
          [ exact HwGF2 | apply wf_Rel | exact HlGw ]
        | apply eq_term_refl; exact HwB2 ].
    - apply eq_sort_exp_ty;
        [ exact HwDF | exact HcG
        | apply eq_U_subst;
          [ exact HwDF | exact HwGF2 | exact Hwh | apply wf_Rel
          | exact HlGw ] ]. }
  assert (eqt (sCode (oExtC D rF lF F0) oRel lG)
            (oExpSubst (oExtC D rF lF (oCodeSubst D G g rF lF F2))
               (oExtC G rF lF F2) (oLift D G g rF lF F2)
               (iCode lG) (oU (oExtC G rF lF F2) oRel lG) B2) B0) as HB
      by (eapply eq_term_trans; [ exact HstepB | exact HB0eq ]).
  exists F0, B0; repeat split;
    [ exact HF0 | exact HB0 | exact HF0eq | exact HB | ].
  eapply eq_term_trans;
    [ apply eq_Pi_rel_subst;
      [ exact HDw | exact HGw | exact Hgw | exact HrFw | exact HlFw
      | exact HlGw | exact HwF2 | exact HwB2 ] | ].
  apply PiRel_cong;
    [ apply eq_term_refl; exact HDw
    | apply eq_term_refl; exact HrFw
    | apply eq_term_refl; exact HlFw
    | apply eq_term_refl; exact HlGw
    | exact HF0eq
    | exact HB ].
Qed.

(* ================================================================== *)
(* 5.  The equations that need only the [Pi] and [Emptyrec] congruences *)
(* ================================================================== *)

(* THE RECIPE (observation (1) of the header), spelled out once here and
   reused verbatim below:

     goal      Ceq_term t2 (g1[X args1]) (X (g2-substituted args2))
     step 1    [ceq_exp_eq_l]: replace the left term by [g2[X args2]] --
               one [ExpSubst_cong] over the argument equations;
     step 2    [ceq_exp_eq_r]: the remaining [Ceq_term t2 (g2[X args2])
               (g2[X args2])] is [ceq_exp_subst_l] applied to the
               substitution argument's clause and to THIS FRAGMENT'S OWN
               congruence at the reflexive right arguments, transported to
               the goal's sort by [ceq_exp_transfer];
     step 3    the right term is reached by the language's own equation.

   Only steps 1 and 3 mention the rule at all; nothing semantic is
   reproved. *)

Lemma by_PiRel_subst G1 G2 G1' G2' g1 g2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rF1 rF2 -> Ceq_term sLvl lF1 lF2 ->
    Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2' rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2' rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sCode G2 oRel lG2)
      (oExpSubst G1 G1' g1 (iCode lG1) (oU G1' oRel lG1)
         (oPiRel G1' rF1 lF1 lG1 F1 B1))
      (oPiRel G2 rF2 lF2 lG2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode lG2) (oU (oExtC G2' rF2 lF2 F2) oRel lG2) B2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf Hlg HFc HBc.
  pose proof (ceq_refl_r Hgc) as Hg2c.
  pose proof (ceq_refl_r (cong_PiRel HGc' Hr Hlf Hlg HFc HBc)) as HPi2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft lG2 sLvl) as HwlG by (apply LvlNf_wf; exact Hlgnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft F2 (sCode G2' rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B2 (sCode (oExtC G2' rF2 lF2 F2) oRel lG2)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft (iCode lG2) sInfo) as HcG
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlG ]).
  eapply ceq_exp_eq_l with
    (e2 := oExpSubst G2 G2' g2 (iCode lG2) (oU G2' oRel lG2)
             (oPiRel G2' rF2 lF2 lG2 F2 B2)).
  - eapply eq_term_conv.
    + apply ExpSubst_cong;
        [ exact HG | exact HG' | exact Hga
        | apply eq_term_refl; exact HcG
        | apply U_cong;
          [ exact HG' | apply eq_term_refl; apply wf_Rel
          | apply eq_term_refl; exact HwlG ]
        | apply PiRel_cong;
          [ exact HG'
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | apply eq_term_refl; exact HwlG
          | exact HFa | exact HBa ] ].
    + apply eq_sort_exp_ty;
        [ exact HwG2 | exact HcG
        | apply eq_U_subst;
          [ exact HwG2 | exact HwG2' | exact Hwg2 | apply wf_Rel
          | exact HwlG ] ].
  - eapply ceq_exp_eq_r.
    + eapply ceq_exp_transfer;
        [ apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact HcG
        | apply eq_U_subst;
          [ exact HwG2 | exact HwG2' | exact Hwg2 | apply wf_Rel
          | exact HwlG ]
        | eapply ceq_exp_subst_l; [ exact Hg2c | exact HPi2 ] ].
    + apply eq_Pi_rel_subst;
        [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact HwlF
        | exact HwlG | exact HwF2 | exact HwB2 ].
Qed.

Lemma by_PiIrr_subst G1 G2 G1' G2' g1 g2 rF1 rF2 lF1 lF2 F1 F2 B1 B2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rF1 rF2 -> Ceq_term sLvl lF1 lF2 ->
    Ceq_term (sCode G2' rF2 lF2) F1 F2 ->
    Ceq_term (sExp (oExtC G2' rF2 lF2 F2) (oInfo oRel (oIota oL1))
                (oU (oExtC G2' rF2 lF2 F2) oIrr oL0)) B1 B2 ->
    Ceq_term (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0))
      (oExpSubst G1 G1' g1 (oInfo oRel (oIota oL1)) (oU G1' oIrr oL0)
         (oPiIrr G1' rF1 lF1 F1 B1))
      (oPiIrr G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (oInfo oRel (oIota oL1)) (oU (oExtC G2' rF2 lF2 F2) oIrr oL0) B2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf HFc HBc.
  pose proof (ceq_refl_r Hgc) as Hg2c.
  pose proof (ceq_refl_r (cong_PiIrr HGc' Hr Hlf HFc HBc)) as HPi2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft F2 (sCode G2' rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B2 (sExp (oExtC G2' rF2 lF2 F2) (oInfo oRel (oIota oL1))
                    (oU (oExtC G2' rF2 lF2 F2) oIrr oL0))) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft (oInfo oRel (oIota oL1)) sInfo) as Hi1L
      by (apply wf_Info; [ apply wf_Rel | apply wf_Iota; apply wf_L1 ]).
  eapply ceq_exp_eq_l with
    (e2 := oExpSubst G2 G2' g2 (oInfo oRel (oIota oL1)) (oU G2' oIrr oL0)
             (oPiIrr G2' rF2 lF2 F2 B2)).
  - eapply eq_term_conv.
    + apply ExpSubst_cong;
        [ exact HG | exact HG' | exact Hga
        | apply eq_term_refl; exact Hi1L
        | eapply eq_term_conv;
          [ apply U_cong;
            [ exact HG' | apply eq_term_refl; apply wf_Irr
            | apply eq_term_refl; apply wf_L0 ]
          | apply sTy_cong;
            [ apply eq_term_refl; exact HwG2' | apply eq_info_next0 ] ]
        | apply PiIrr_cong;
          [ exact HG'
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | exact HFa | exact HBa ] ].
    + apply eq_sort_exp_ty;
        [ exact HwG2 | exact Hi1L
        | apply eq_U_subst_i1;
          [ exact HwG2 | exact HwG2' | exact Hwg2 | apply wf_Irr ] ].
  - eapply ceq_exp_eq_r.
    + eapply ceq_exp_transfer;
        [ apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hi1L
        | apply eq_U_subst_i1;
          [ exact HwG2 | exact HwG2' | exact Hwg2 | apply wf_Irr ]
        | eapply ceq_exp_subst_l; [ exact Hg2c | exact HPi2 ] ].
    + apply eq_Pi_irr_subst;
        [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact HwlF
        | exact HwF2 | exact HwB2 ].
Qed.

(* [Emptyrec]'s conclusion sort is the substituted type verbatim, so no
   transfer is needed at all. *)
Lemma by_Emptyrec_subst G1 G2 G1' G2' g1 g2 rA1 rA2 lA1 lA2 A1 A2 e1 e2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rA1 rA2 -> Ceq_term sLvl lA1 lA2 ->
    Ceq_term (sCode G2' rA2 lA2) A1 A2 ->
    Ceq_term (sElt G2' oIrr oL0 (oEmpty G2')) e1 e2 ->
    Ceq_term (sExp G2 (iEl rA2 lA2)
                (oTySubst G2 G2' g2 (iEl rA2 lA2) (oEl G2' rA2 lA2 A2)))
      (oExpSubst G1 G1' g1 (iEl rA1 lA1) (oEl G1' rA1 lA1 A1)
         (oEmptyrec G1' rA1 lA1 A1 e1))
      (oEmptyrec G2 rA2 lA2 (oCodeSubst G2 G2' g2 rA2 lA2 A2)
         (oExpSubst G2 G2' g2 (iEl oIrr oL0) (oEl G2' oIrr oL0 (oEmpty G2')) e2)).
Proof.
  intros HGc HGc' Hgc Hr Hl HAc Hec.
  pose proof (ceq_refl_r Hgc) as Hg2c.
  pose proof (ceq_refl_r (cong_Emptyrec HGc' Hr Hl HAc Hec)) as HEr2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rA1.
  apply Ceq_lvl_e in Hl as [Hlq Hlnf]; subst lA1.
  apply Ceq_exp_e in HAc as [HAa _].
  apply Ceq_exp_e in Hec as [Hea _].
  assert (wft rA2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lA2 sLvl) as Hwl by (apply LvlNf_wf; exact Hlnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft A2 (sCode G2' rA2 lA2)) as HwA2 by (eapply eqt_wf_r; exact HAa).
  assert (wft e2 (sElt G2' oIrr oL0 (oEmpty G2'))) as Hwe2
      by (eapply eqt_wf_r; exact Hea).
  assert (wft (iEl rA2 lA2) sInfo) as HiA
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact Hwl ]).
  eapply ceq_exp_eq_l with
    (e2 := oExpSubst G2 G2' g2 (iEl rA2 lA2) (oEl G2' rA2 lA2 A2)
             (oEmptyrec G2' rA2 lA2 A2 e2)).
  - apply ExpSubst_cong;
      [ exact HG | exact HG' | exact Hga
      | apply eq_term_refl; exact HiA
      | apply El_cong;
        [ exact HG' | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact Hwl | exact HAa ]
      | apply Emptyrec_cong;
        [ exact HG' | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact Hwl | exact HAa | exact Hea ] ].
  - eapply ceq_exp_eq_r.
    + eapply ceq_exp_subst_l; [ exact Hg2c | exact HEr2 ].
    + apply eq_Emptyrec_subst;
        [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact Hwl
        | exact HwA2 | exact Hwe2 ].
Qed.

(* THE CHEAPEST OF THE TEN.  The right-hand side of "Pi_rel eta" IS the
   function argument, whose clause is a hypothesis; the left-hand side is
   provably equal to it by the rule, and [ceq_exp_eq_l] carries the clause
   across.  No reducibility reasoning whatever -- which is the point: eta
   is what Layer 1 spends, not Layer 4. *)
Lemma by_PiRel_eta G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2 f1 f2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 -> Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2)) f1 f2 ->
    Ceq_term (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
      (oLamRel G1 rF1 lF1 lG1 F1 B1
         (oAppRel (oExtC G1 rF1 lF1 F1) rF1 lF1 lG1
            (oCodeSubst (oExtC G1 rF1 lF1 F1) G1
               (oWkn G1 (iEl rF1 lF1) (oEl G1 rF1 lF1 F1)) rF1 lF1 F1)
            (oExpSubst
               (oExtC (oExtC G1 rF1 lF1 F1) rF1 lF1
                  (oCodeSubst (oExtC G1 rF1 lF1 F1) G1
                     (oWkn G1 (iEl rF1 lF1) (oEl G1 rF1 lF1 F1)) rF1 lF1 F1))
               (oExtC G1 rF1 lF1 F1)
               (oLift (oExtC G1 rF1 lF1 F1) G1
                  (oWkn G1 (iEl rF1 lF1) (oEl G1 rF1 lF1 F1)) rF1 lF1 F1)
               (iCode lG1) (oU (oExtC G1 rF1 lF1 F1) oRel lG1) B1)
            (oExpSubst (oExtC G1 rF1 lF1 F1) G1
               (oWkn G1 (iEl rF1 lF1) (oEl G1 rF1 lF1 F1))
               (iEl oRel lG1) (oEl G1 oRel lG1 (oPiRel G1 rF1 lF1 lG1 F1 B1)) f1)
            (oHd G1 (iEl rF1 lF1) (oEl G1 rF1 lF1 F1))))
      f2.
Proof.
  intros HGc Hr Hlf Hlg HFc HBc Hfc.
  pose proof Hfc as Hfc0.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  apply Ceq_exp_e in Hfc as [Hfa _].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft lG2 sLvl) as HwlG by (apply LvlNf_wf; exact Hlgnf).
  assert (wft G1 sEnv) as HwG1 by (eapply eqt_wf_l; exact HG).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft F1 (sCode G2 rF2 lF2)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G2 rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B1 (sCode (oExtC G2 rF2 lF2 F2) oRel lG2)) as HwB1
      by (eapply eqt_wf_l; exact HBa).
  assert (wft f1 (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))) as Hwf1
      by (eapply eqt_wf_l; exact Hfa).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (iCode lG2) sInfo) as HcG
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlG ]).
  assert (wft (iCode lF2) sInfo) as HcF
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlF ]).
  (* the "1" arguments, retyped over [G1] *)
  assert (wft F1 (sCode G1 rF2 lF2)) as HwF1'.
  { eapply wf_term_conv; [ exact HwF1 | ].
    apply sExp_cong;
      [ apply eq_term_sym; exact HG | apply eq_term_refl; exact HcF
      | apply U_cong;
        [ apply eq_term_sym; exact HG | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF ] ]. }
  assert (eqt (sCode G1 rF2 lF2) F2 F1) as HFa'.
  { eapply eq_term_conv; [ apply eq_term_sym; exact HFa | ].
    apply sExp_cong;
      [ apply eq_term_sym; exact HG | apply eq_term_refl; exact HcF
      | apply U_cong;
        [ apply eq_term_sym; exact HG | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF ] ]. }
  assert (eqt sEnv (oExtC G2 rF2 lF2 F2) (oExtC G1 rF2 lF2 F1)) as HExtEq.
  { unfold oExtC; apply Ext_cong;
      [ apply eq_term_sym; exact HG | apply eq_term_refl; exact HiF
      | apply El_cong;
        [ apply eq_term_sym; exact HG | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF | exact HFa' ] ]. }
  assert (wft (oExtC G1 rF2 lF2 F1) sEnv) as HwGF1
      by (apply wf_ExtC; assumption).
  assert (wft B1 (sCode (oExtC G1 rF2 lF2 F1) oRel lG2)) as HwB1'.
  { eapply wf_term_conv; [ exact HwB1 | ].
    apply sExp_cong;
      [ exact HExtEq | apply eq_term_refl; exact HcG
      | apply U_cong;
        [ exact HExtEq | apply eq_term_refl; apply wf_Rel
        | apply eq_term_refl; exact HwlG ] ]. }
  assert (eqt (sTy G2 (iEl oRel lG2))
            (oEl G1 oRel lG2 (oPiRel G1 rF2 lF2 lG2 F1 B1))
            (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))) as HElPi.
  { apply El_cong;
      [ exact HG | apply eq_term_refl; apply wf_Rel
      | apply eq_term_refl; exact HwlG
      | apply PiRel_cong;
        [ exact HG | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_refl; exact HwlG
        | exact HFa | exact HBa ] ]. }
  assert (wft f1 (sElt G1 oRel lG2 (oPiRel G1 rF2 lF2 lG2 F1 B1))) as Hwf1'.
  { eapply wf_term_conv; [ exact Hwf1 | ].
    apply eq_sort_sym; apply sExp_cong;
      [ exact HG | apply eq_term_refl; unfold iEl; apply wf_Info;
        [ apply wf_Rel | apply wf_Iota; exact HwlG ]
      | exact HElPi ]. }
  eapply ceq_exp_eq_l with (e2 := f1); [ | exact Hfc0 ].
  eapply eq_term_conv.
  - apply eq_Pi_rel_eta;
      [ exact HwG1 | exact Hwr | exact HwlF | exact HwlG | exact HwF1'
      | exact HwB1' | exact Hwf1' ].
  - apply sExp_cong;
      [ exact HG
      | apply eq_term_refl; unfold iEl; apply wf_Info;
        [ apply wf_Rel | apply wf_Iota; exact HwlG ]
      | exact HElPi ].
Qed.

(* ================================================================== *)
(* 6.  [app_rel]                                                       *)
(* ================================================================== *)

(* THE DUAL OF THE BINDER CASES.  The function argument's clause says its
   instance is in the Pi candidate, and at a Pi THAT IS the application
   property; [RTy_pi_rel_e] reads it back.  Instantiating the clause's
   Kripke quantifier at the IDENTITY weakening and at the argument's own
   instance produces membership in the codomain candidate of exactly the
   application -- and the codomain candidate is at the representative the
   clause chose, which is where the obligation's own conclusion sort has to
   be met.

   ALL THREE TYPES INVOLVED -- the obligation's own [ty_subst g] of
   [app_rel]'s declared conclusion sort, the clause's raw codomain instance
   [codAtRel], and [app_rel]'s conclusion sort at the substituted arguments
   -- are provably equal to ONE hub,

     <g, g[a]> [ El (extC G rF lF F) rel lG B ],

   and Layer 2 supplies two of the three bridges already
   ([DttLRCore.an_appConcl] and [DttLRCand.ac_appConcl]); only the first,
   which is "cmp_snoc + id_right + ty_subst_id", is new here. *)
Lemma cong_AppRel G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2 f1 f2 a1 a2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 -> Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2)) f1 f2 ->
    Ceq_term (sElt G2 rF2 lF2 F2) a1 a2 ->
    Ceq_term (sAppRelConcl G2 rF2 lF2 lG2 F2 B2 a2)
      (oAppRel G1 rF1 lF1 lG1 F1 B1 f1 a1) (oAppRel G2 rF2 lF2 lG2 F2 B2 f2 a2).
Proof.
  intros HGc Hr Hlf Hlg HFc HBc Hfc Hac.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_exp_e in HFc as [HFa HFb].
  apply Ceq_exp_e in HBc as [HBa HBb].
  apply Ceq_exp_e in Hfc as [Hfa Hfb].
  apply Ceq_exp_e in Hac as [Haa Hab].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft lG2 sLvl) as HwlG by (apply LvlNf_wf; exact Hlgnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft F1 (sCode G2 rF2 lF2)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G2 rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B1 (sCode (oExtC G2 rF2 lF2 F2) oRel lG2)) as HwB1
      by (eapply eqt_wf_l; exact HBa).
  assert (wft B2 (sCode (oExtC G2 rF2 lF2 F2) oRel lG2)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft f1 (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))) as Hwf1
      by (eapply eqt_wf_l; exact Hfa).
  assert (wft a1 (sElt G2 rF2 lF2 F2)) as Hwa1 by (eapply eqt_wf_l; exact Haa).
  assert (wft a2 (sElt G2 rF2 lF2 F2)) as Hwa2 by (eapply eqt_wf_r; exact Haa).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (iEl oRel lG2) sInfo) as HiG
      by (unfold iEl; apply wf_Info; [ apply wf_Rel | apply wf_Iota; exact HwlG ]).
  assert (wft (iCode lF2) sInfo) as HcF
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlF ]).
  assert (wft (iCode lG2) sInfo) as HcG
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlG ]).
  assert (wft (oExtC G2 rF2 lF2 F2) sEnv) as HwGF by (apply wf_ExtC; assumption).
  assert (wft (oEl G2 rF2 lF2 F2) (sTy G2 (iEl rF2 lF2))) as HwElF
      by (apply wf_El; assumption).
  assert (wft (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)
            (sTy (oExtC G2 rF2 lF2 F2) (iEl oRel lG2))) as HwElB
      by (apply wf_El; [ exact HwGF | apply wf_Rel | exact HwlG | exact HwB2 ]).
  apply ceq_exp.
  { apply AppRel_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | apply eq_term_refl; exact HwlG
      | exact HFa | exact HBa | exact Hfa | exact Haa ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  destruct (pi_rel_nf Hrnf Hlfnf Hlgnf HFa HFb HBa HBb HD Hg)
    as [F0 [B0 (HF0 & HB0 & HF0eq & HB & HPi)]].
  assert (NfCode D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0)) as HnfPi
      by (apply nfcode_pi_rel; assumption).
  assert (wft F0 (sCode D rF2 lF2)) as HwF0 by (apply NfCode_wf; exact HF0).
  assert (wft (oExtC D rF2 lF2 F0) sEnv) as HwDF by (apply wf_ExtC; assumption).
  assert (wft B0 (sCode (oExtC D rF2 lF2 F0) oRel lG2)) as HwB0
      by (apply NfCode_wf; exact HB0).
  (* the instances of the two term arguments *)
  pose (fg := oExpSubst D G2 g (iEl oRel lG2)
                (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2)) f1).
  pose (ag := oExpSubst D G2 g (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) a1).
  assert (wft ag (sExp D (iEl rF2 lF2)
                    (oTySubst D G2 g (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)))) as Hwag
      by (unfold ag; apply wf_ExpSubst; assumption).
  assert (eqt (sTy D (iEl rF2 lF2))
            (oTySubst D G2 g (iEl rF2 lF2) (oEl G2 rF2 lF2 F2))
            (oEl D rF2 lF2 F0)) as HtyF.
  { eapply eq_term_trans; [ apply eq_El_subst; assumption | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HF0eq ]. }
  assert (wft ag (sElt D rF2 lF2 F0)) as Hwag'
      by (eapply wf_term_conv;
          [ exact Hwag
          | apply eq_sort_exp_ty; [ exact HwD | exact HiF | exact HtyF ] ]).
  assert (wft ag (sElt D rF2 lF2 (wkCode D G2 g rF2 lF2 F2))) as Hwag''.
  { eapply wf_term_conv; [ exact Hwag | ].
    apply eq_sort_exp_ty;
      [ exact HwD | exact HiF
      | unfold wkCode; apply eq_El_subst; assumption ]. }
  assert (eqt (sTy D (iEl oRel lG2))
            (oTySubst D G2 g (iEl oRel lG2)
               (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2)))
            (oEl D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0))) as HtyPi.
  { eapply eq_term_trans;
      [ apply eq_El_subst;
        [ exact HwD | exact HwG2 | exact Hwg | apply wf_Rel | exact HwlG
        | apply wf_PiRel; assumption ] | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Rel
      | apply eq_term_refl; exact HwlG
      | exact HPi ]. }
  assert (wft fg (sElt D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0))) as Hwfg.
  { eapply wf_term_conv;
      [ unfold fg; apply wf_ExpSubst;
        [ exact HwD | exact HwG2 | exact Hwg | exact HiG
        | apply wf_El; [ exact HwG2 | apply wf_Rel | exact HwlG
                       | apply wf_PiRel; assumption ]
        | exact Hwf1 ]
      | apply eq_sort_exp_ty; [ exact HwD | exact HiG | exact HtyPi ] ]. }
  (* the function's instance is in the Pi candidate *)
  destruct (RTyEx_of_NfCode HnfPi) as [P HP].
  assert (P fg) as HPf.
  { eapply RTmN_elim with
      (i0 := iEl oRel lG2)
      (A0 := oEl D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0)) (P := P);
      [ apply Hfb; assumption
      | apply eq_term_refl; exact HiG
      | apply tyok_El; exact HnfPi
      | exact HtyPi
      | exact HP ]. }
  destruct (RTy_pi_rel_e HP)
    as [Pd [Pc (Hrn & Hlfn & Hlgn & HnF0 & HnB0 & Hdom & Hcod & Hiff)]].
  (* the argument is reducible at the identity weakening *)
  destruct (Hdom D (oId D) (wk_id HD) HD) as [F' (HnF' & HeqF' & HRd)].
  assert (wft F' (sCode D rF2 lF2)) as HwF' by (apply NfCode_wf; exact HnF').
  assert (eqt (sCode D rF2 lF2) F0 F') as HF0F'.
  { eapply eq_term_trans; [ | exact HeqF' ].
    apply eq_term_sym; unfold wkCode; apply eq_exp_subst_id;
      [ exact HwD | exact HcF | apply wf_U; assumption | exact HwF0 ]. }
  assert (Pd D (oId D) ag) as HPda.
  { eapply RTmN_elim with
      (i0 := iEl rF2 lF2) (A0 := oEl D rF2 lF2 F') (P := Pd D (oId D));
      [ apply Hab; assumption
      | apply eq_term_refl; exact HiF
      | apply tyok_El; exact HnF'
      | eapply eq_term_trans; [ exact HtyF | ]
      | exact HRd ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HF0F' ]. }
  pose proof (proj1 (Hiff fg) HPf D (oId D) ag (wk_id HD) HD HPda) as Hres.
  destruct (Hcod D (oId D) ag (wk_id HD) HD HPda)
    as [C (HTyC & HeqC & HRc)].
  (* ---- the hub type ---- *)
  assert (eqt (sSub D (oExtC G2 rF2 lF2 F2))
            (oCmp D G2 (oExtC G2 rF2 lF2 F2) g (oInst G2 rF2 lF2 F2 a1))
            (oSnoc D G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) g ag)) as Hinst.
  { unfold oInst, oExtC.
    eapply eq_term_trans.
    { apply eq_cmp_snoc;
        [ exact HwD | exact HwG2 | exact HwG2 | exact Hwg
        | apply wf_Id; exact HwG2 | exact HiF | exact HwElF
        | eapply wf_term_conv;
          [ exact Hwa1
          | apply eq_sort_exp_ty;
            [ exact HwG2 | exact HiF
            | apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwG2 | exact HiF | exact HwElF ] ] ] ]. }
    apply Snoc_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact HiF
      | apply eq_term_refl; exact HwElF
      | apply eq_id_right; [ exact HwD | exact HwG2 | exact Hwg ]
      | ].
    apply ExpSubst_cong
      with (G1 := D) (G2 := D) (G1' := G2) (G2' := G2) (g1 := g) (g2 := g)
           (i1 := iEl rF2 lF2) (i2 := iEl rF2 lF2)
           (A1 := oTySubst G2 G2 (oId G2) (iEl rF2 lF2) (oEl G2 rF2 lF2 F2))
           (A2 := oEl G2 rF2 lF2 F2) (v1 := a1) (v2 := a1);
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact Hwg
      | apply eq_term_refl; exact HiF
      | apply eq_ty_subst_id; [ exact HwG2 | exact HiF | exact HwElF ]
      | apply eq_term_refl; exact Hwa1 ]. }
  assert (eqt (sTy D (iEl oRel lG2))
            (oTySubst D G2 g (iEl oRel lG2)
               (oTySubst G2 (oExtC G2 rF2 lF2 F2) (oInst G2 rF2 lF2 F2 a1)
                  (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)))
            (oTySubst D (oExtC G2 rF2 lF2 F2)
               (oSnoc D G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) g ag)
               (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)))
    as Hhub1.
  { eapply eq_term_trans.
    - apply eq_ty_subst_cmp;
        [ exact HwD | exact HwG2 | exact HwGF | exact Hwg
        | apply wf_oInst; assumption
        | exact HiG | exact HwElB ].
    - apply TySubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwGF
        | exact Hinst
        | apply eq_term_refl; exact HiG
        | apply eq_term_refl; exact HwElB ]. }
  (* [an_appConcl]: the clause's raw codomain instance is the hub *)
  assert (eqt (sTy D (iEl oRel lG2))
            (codAtRel D D rF2 lF2 lG2 F0 B0 (oId D) ag)
            (oTySubst D (oExtC G2 rF2 lF2 F2)
               (oSnoc D G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) g ag)
               (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)))
    as Hhub2.
  { unfold codAtRel, instAt.
    eapply eq_term_trans;
      [ | apply an_appConcl with (rG := oRel) (G := G2) (w := g) (F := F2)
            (B := B2) (a := ag) (F' := F0) (B' := B0) (a' := ag);
          first [ assumption | apply wf_Rel
                | apply eq_term_refl; assumption ] ].
    apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwDF
      | unfold oInst, oExtC;
        apply eq_term_refl; apply wf_Snoc;
        [ exact HwD | exact HwD | exact HiF
        | apply wf_El; assumption
        | apply wf_Id; exact HwD
        | eapply wf_term_conv;
          [ exact Hwag'
          | apply eq_sort_exp_ty;
            [ exact HwD | exact HiF
            | apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwD | exact HiF | apply wf_El; assumption ] ] ] ]
      | apply eq_term_refl; exact HiG
      | apply eq_term_refl; apply wf_El;
        [ exact HwDF | apply wf_Rel | exact HwlG | exact HwB0 ] ]. }
  (* ---- the type of the obligation ---- *)
  assert (eqt (sTy D (iEl oRel lG2))
            (oTySubst D G2 g (iEl oRel lG2)
               (oTySubst G2 (oExtC G2 rF2 lF2 F2) (oInst G2 rF2 lF2 F2 a2)
                  (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)))
            C) as HtyGoal.
  { eapply eq_term_trans; [ | eapply eq_term_trans; [ | exact HeqC ] ].
    2:{ apply eq_term_sym; exact Hhub2. }
    eapply eq_term_trans; [ | exact Hhub1 ].
    apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact Hwg
      | apply eq_term_refl; exact HiG
      | apply TySubst_cong;
        [ apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact HwGF
        | unfold oInst, oExtC; apply Snoc_cong;
          [ apply eq_term_refl; exact HwG2
          | apply eq_term_refl; exact HwG2
          | apply eq_term_refl; exact HiF
          | apply eq_term_refl; exact HwElF
          | apply eq_term_refl; apply wf_Id; exact HwG2
          | eapply eq_term_conv;
            [ apply eq_term_sym; exact Haa
            | apply eq_sort_exp_ty;
              [ exact HwG2 | exact HiF
              | apply eq_term_sym; apply eq_ty_subst_id;
                [ exact HwG2 | exact HiF | exact HwElF ] ] ] ]
        | apply eq_term_refl; exact HiG
        | apply eq_term_refl; exact HwElB ] ]. }
  eapply RTmN_intro with (i0 := iEl oRel lG2) (A0 := C) (P := Pc D (oId D) ag);
    [ apply eq_term_refl; exact HiG | exact HTyC | exact HtyGoal | exact HRc | ].
  (* ---- the subject: beta-free, purely the application ---- *)
  eapply (RTy_cand_eq HRc); [ exact Hres | ].
  (* [ac_appConcl]: [app_rel]'s own conclusion sort is the hub too *)
  assert (eqt (sTy D (iEl oRel lG2))
            (oTySubst D (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (oInst D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2) ag)
               (iEl oRel lG2)
               (oEl (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)) oRel lG2
                  (oExpSubst
                     (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                     (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)))
            (oTySubst D (oExtC G2 rF2 lF2 F2)
               (oSnoc D G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) g ag)
               (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)))
    as Hhub3.
  { apply ac_appConcl with (rG := oRel) (a := ag);
      first [ assumption | apply wf_Rel ]. }
  (* the [lift] of the identity is the identity *)
  assert (eqt (sCode (oExtC D rF2 lF2 F0) oRel lG2)
            (wkCodCodeRel D D (oId D) rF2 lF2 lG2 F0 B0) B0) as HidB.
  { assert (eqt (sCode D rF2 lF2)
              (oCodeSubst D D (oId D) rF2 lF2 F0) F0) as HF0id
        by (unfold oCodeSubst; apply eq_exp_subst_id;
            [ exact HwD | exact HcF | apply wf_U; assumption | exact HwF0 ]).
    assert (eqt (sSub (oExtC D rF2 lF2 F0) (oExtC D rF2 lF2 F0))
              (oLift D D (oId D) rF2 lF2 F0)
              (oId (oExtC D rF2 lF2 F0))) as HlidF.
    { rewrite oLift_oLiftW.
      eapply eq_term_trans.
      - apply eq_liftW_cong
          with (A1 := oEl D rF2 lF2 (oCodeSubst D D (oId D) rF2 lF2 F0))
               (A2 := oEl D rF2 lF2 F0);
          [ exact HwD | exact HwD | exact HiF
          | apply wf_El; assumption
          | apply wf_El;
            [ exact HwD | exact Hwr | exact HwlF
            | eapply eqt_wf_l; exact HF0id ]
          | apply wf_El; assumption
          | apply wf_Id; exact HwD
          | apply eq_El_subst;
            [ exact HwD | exact HwD | apply wf_Id; exact HwD | exact Hwr
            | exact HwlF | exact HwF0 ]
          | apply eq_ty_subst_id;
            [ exact HwD | exact HiF | apply wf_El; assumption ] ].
      - apply eq_liftW_id;
          [ exact HwD | exact HiF | apply wf_El; assumption
          | apply wf_Id; exact HwD
          | apply eq_term_refl; apply wf_Id; exact HwD ]. }
    unfold wkCodCodeRel, wkCode.
    eapply eq_term_trans.
    - eapply eq_term_conv.
      + apply ExpSubst_cong
          with (G1 := oExtC D rF2 lF2 (oCodeSubst D D (oId D) rF2 lF2 F0))
               (G2 := oExtC D rF2 lF2 F0)
               (G1' := oExtC D rF2 lF2 F0) (G2' := oExtC D rF2 lF2 F0)
               (g1 := oLift D D (oId D) rF2 lF2 F0)
               (g2 := oId (oExtC D rF2 lF2 F0))
               (i1 := iCode lG2) (i2 := iCode lG2)
               (A1 := oU (oExtC D rF2 lF2 F0) oRel lG2)
               (A2 := oU (oExtC D rF2 lF2 F0) oRel lG2)
               (v1 := B0) (v2 := B0);
          [ unfold oExtC; apply Ext_cong;
            [ apply eq_term_refl; exact HwD
            | apply eq_term_refl; exact HiF
            | apply El_cong;
              [ apply eq_term_refl; exact HwD
              | apply eq_term_refl; exact Hwr
              | apply eq_term_refl; exact HwlF
              | exact HF0id ] ]
          | apply eq_term_refl; exact HwDF
          | exact HlidF
          | apply eq_term_refl; exact HcG
          | apply eq_term_refl; apply wf_U;
            [ exact HwDF | apply wf_Rel | exact HwlG ]
          | apply eq_term_refl; exact HwB0 ].
      + apply eq_sort_exp_ty;
          [ exact HwDF | exact HcG
          | apply eq_ty_subst_id;
            [ exact HwDF | exact HcG
            | apply wf_U; [ exact HwDF | apply wf_Rel | exact HwlG ] ] ].
    - apply eq_exp_subst_id;
        [ exact HwDF | exact HcG
        | apply wf_U; [ exact HwDF | apply wf_Rel | exact HwlG ]
        | exact HwB0 ]. }
  (* the three-step equation *)
  eapply eq_term_conv.
  2:{ apply eq_sort_exp_ty; [ exact HwD | exact HiG | ].
      eapply eq_term_trans; [ apply eq_term_sym; exact Hhub2 | exact HeqC ]. }
  apply eq_term_sym.
  eapply eq_term_trans.
  { (* the obligation's subject, retyped and moved to the "2" arguments *)
    eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D) (G2 := D) (G1' := G2) (G2' := G2) (g1 := g) (g2 := g)
             (i1 := iEl oRel lG2) (i2 := iEl oRel lG2)
             (A1 := oTySubst G2 (oExtC G2 rF2 lF2 F2)
                      (oInst G2 rF2 lF2 F2 a2) (iEl oRel lG2)
                      (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2))
             (A2 := oTySubst G2 (oExtC G2 rF2 lF2 F2)
                      (oInst G2 rF2 lF2 F2 a1) (iEl oRel lG2)
                      (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2))
             (v1 := oAppRel G1 rF2 lF2 lG2 F1 B1 f1 a1)
             (v2 := oAppRel G2 rF2 lF2 lG2 F2 B2 f1 a1);
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; exact HiG
        | apply TySubst_cong;
          [ apply eq_term_refl; exact HwG2
          | apply eq_term_refl; exact HwGF
          | unfold oInst, oExtC; apply Snoc_cong;
            [ apply eq_term_refl; exact HwG2
            | apply eq_term_refl; exact HwG2
            | apply eq_term_refl; exact HiF
            | apply eq_term_refl; exact HwElF
            | apply eq_term_refl; apply wf_Id; exact HwG2
            | eapply eq_term_conv;
              [ apply eq_term_sym; exact Haa
              | apply eq_sort_exp_ty;
                [ exact HwG2 | exact HiF
                | apply eq_term_sym; apply eq_ty_subst_id;
                  [ exact HwG2 | exact HiF | exact HwElF ] ] ] ]
          | apply eq_term_refl; exact HiG
          | apply eq_term_refl; exact HwElB ]
        | apply AppRel_cong;
          [ exact HG
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | apply eq_term_refl; exact HwlG
          | exact HFa | exact HBa
          | apply eq_term_refl; exact Hwf1
          | apply eq_term_refl; exact Hwa1 ] ].
    - apply eq_sort_exp_ty; [ exact HwD | exact HiG | exact Hhub1 ]. }
  eapply eq_term_trans.
  { eapply eq_term_conv;
      [ apply eq_app_rel_subst;
        [ exact HwD | exact HwG2 | exact Hwg | exact Hwr | exact HwlF
        | exact HwlG | exact HwF2 | exact HwB2 | exact Hwf1 | exact Hwa1 ]
      | apply eq_sort_exp_ty; [ exact HwD | exact HiG | exact Hhub1 ] ]. }
  (* and finally back to [appAtRel] *)
  eapply eq_term_conv.
  2:{ apply eq_sort_exp_ty; [ exact HwD | exact HiG | exact Hhub3 ]. }
  apply eq_term_sym.
  unfold appAtRel, wkFunRel.
  apply AppRel_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_refl; exact Hwr
    | apply eq_term_refl; exact HwlF
    | apply eq_term_refl; exact HwlG
    | (* the domain code *)
      unfold wkCode; eapply eq_term_trans;
      [ apply eq_exp_subst_id;
        [ exact HwD | exact HcF | apply wf_U; assumption | exact HwF0 ]
      | apply eq_term_sym; exact HF0eq ]
    | (* the codomain code *)
      eapply eq_term_conv;
      [ eapply eq_term_trans; [ exact HidB | apply eq_term_sym; exact HB ]
      | apply sExp_cong;
        [ unfold oExtC; apply Ext_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact HiF
          | apply El_cong;
            [ apply eq_term_refl; exact HwD
            | apply eq_term_refl; exact Hwr
            | apply eq_term_refl; exact HwlF
            | apply eq_term_sym; exact HF0eq ] ]
        | apply eq_term_refl; exact HcG
        | apply U_cong;
          [ unfold oExtC; apply Ext_cong;
            [ apply eq_term_refl; exact HwD
            | apply eq_term_refl; exact HiF
            | apply El_cong;
              [ apply eq_term_refl; exact HwD
              | apply eq_term_refl; exact Hwr
              | apply eq_term_refl; exact HwlF
              | apply eq_term_sym; exact HF0eq ] ]
          | apply eq_term_refl; apply wf_Rel
          | apply eq_term_refl; exact HwlG ] ] ]
    | (* the function *)
      eapply eq_term_conv;
      [ apply eq_exp_subst_id;
        [ exact HwD | exact HiG
        | apply wf_El;
          [ exact HwD | apply wf_Rel | exact HwlG
          | apply wf_PiRel; assumption ]
        | exact Hwfg ]
      | apply eq_sort_exp_ty; [ exact HwD | exact HiG | ];
        apply El_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; apply wf_Rel
        | apply eq_term_refl; exact HwlG
        | apply PiRel_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | apply eq_term_refl; exact HwlG
          | apply eq_term_sym; exact HF0eq
          | eapply eq_term_conv;
            [ apply eq_term_sym; exact HB
            | apply sExp_cong;
              [ unfold oExtC; apply Ext_cong;
                [ apply eq_term_refl; exact HwD
                | apply eq_term_refl; exact HiF
                | apply El_cong;
                  [ apply eq_term_refl; exact HwD
                  | apply eq_term_refl; exact Hwr
                  | apply eq_term_refl; exact HwlF
                  | apply eq_term_sym; exact HF0eq ] ]
              | apply eq_term_refl; exact HcG
              | apply U_cong;
                [ unfold oExtC; apply Ext_cong;
                  [ apply eq_term_refl; exact HwD
                  | apply eq_term_refl; exact HiF
                  | apply El_cong;
                    [ apply eq_term_refl; exact HwD
                    | apply eq_term_refl; exact Hwr
                    | apply eq_term_refl; exact HwlF
                    | apply eq_term_sym; exact HF0eq ] ]
                | apply eq_term_refl; apply wf_Rel
                | apply eq_term_refl; exact HwlG ] ] ] ] ] ]
    | apply eq_term_refl; exact Hwag'' ].
Qed.

(* ---- "app_rel subst" ---------------------------------------------- *)

(* The recipe of section 5 again, and here it is exact: [app_rel]'s
   conclusion sort IS the substituted type, so neither the left-hand
   [ceq_exp_eq_l] nor the reflexive instance needs any conversion. *)
Lemma by_AppRel_subst G1 G2 G1' G2' g1 g2 rF1 rF2 lF1 lF2 lG1 lG2
                      F1 F2 B1 B2 f1 f2 a1 a2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rF1 rF2 -> Ceq_term sLvl lF1 lF2 ->
    Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2' rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2' rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sElt G2' oRel lG2 (oPiRel G2' rF2 lF2 lG2 F2 B2)) f1 f2 ->
    Ceq_term (sElt G2' rF2 lF2 F2) a1 a2 ->
    Ceq_term
      (sExp G2 (iEl oRel lG2)
         (oTySubst G2 G2' g2 (iEl oRel lG2)
            (oTySubst G2' (oExtC G2' rF2 lF2 F2) (oInst G2' rF2 lF2 F2 a2)
               (iEl oRel lG2) (oEl (oExtC G2' rF2 lF2 F2) oRel lG2 B2))))
      (oExpSubst G1 G1' g1 (iEl oRel lG1)
         (oTySubst G1' (oExtC G1' rF1 lF1 F1) (oInst G1' rF1 lF1 F1 a1)
            (iEl oRel lG1) (oEl (oExtC G1' rF1 lF1 F1) oRel lG1 B1))
         (oAppRel G1' rF1 lF1 lG1 F1 B1 f1 a1))
      (oAppRel G2 rF2 lF2 lG2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode lG2) (oU (oExtC G2' rF2 lF2 F2) oRel lG2) B2)
         (oExpSubst G2 G2' g2 (iEl oRel lG2)
            (oEl G2' oRel lG2 (oPiRel G2' rF2 lF2 lG2 F2 B2)) f2)
         (oExpSubst G2 G2' g2 (iEl rF2 lF2) (oEl G2' rF2 lF2 F2) a2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf Hlg HFc HBc Hfc Hac.
  pose proof (ceq_refl_r Hgc) as Hg2c.
  pose proof (ceq_refl_r (cong_AppRel HGc' Hr Hlf Hlg HFc HBc Hfc Hac)) as HAp2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  apply Ceq_exp_e in Hfc as [Hfa _].
  apply Ceq_exp_e in Hac as [Haa _].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft lG2 sLvl) as HwlG by (apply LvlNf_wf; exact Hlgnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G1' sEnv) as HwG1' by (eapply eqt_wf_l; exact HG').
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft F1 (sCode G2' rF2 lF2)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G2' rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B2 (sCode (oExtC G2' rF2 lF2 F2) oRel lG2)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft f2 (sElt G2' oRel lG2 (oPiRel G2' rF2 lF2 lG2 F2 B2))) as Hwf2
      by (eapply eqt_wf_r; exact Hfa).
  assert (wft a2 (sElt G2' rF2 lF2 F2)) as Hwa2 by (eapply eqt_wf_r; exact Haa).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (iEl oRel lG2) sInfo) as HiG
      by (unfold iEl; apply wf_Info; [ apply wf_Rel | apply wf_Iota; exact HwlG ]).
  assert (wft (oExtC G2' rF2 lF2 F2) sEnv) as HwGF
      by (apply wf_ExtC; assumption).
  assert (wft (oEl G2' rF2 lF2 F2) (sTy G2' (iEl rF2 lF2))) as HwElF
      by (apply wf_El; assumption).
  eapply ceq_exp_eq_l with
    (e2 := oExpSubst G2 G2' g2 (iEl oRel lG2)
             (oTySubst G2' (oExtC G2' rF2 lF2 F2) (oInst G2' rF2 lF2 F2 a2)
                (iEl oRel lG2) (oEl (oExtC G2' rF2 lF2 F2) oRel lG2 B2))
             (oAppRel G2' rF2 lF2 lG2 F2 B2 f2 a2)).
  - apply ExpSubst_cong;
      [ exact HG | exact HG' | exact Hga
      | apply eq_term_refl; exact HiG
      | (* the two conclusion types agree *)
        apply TySubst_cong;
        [ exact HG'
        | unfold oExtC; apply Ext_cong;
          [ exact HG' | apply eq_term_refl; exact HiF
          | apply El_cong;
            [ exact HG' | apply eq_term_refl; exact Hwr
            | apply eq_term_refl; exact HwlF | exact HFa ] ]
        | unfold oInst, oExtC; apply Snoc_cong;
          [ exact HG' | exact HG' | apply eq_term_refl; exact HiF
          | apply El_cong;
            [ exact HG' | apply eq_term_refl; exact Hwr
            | apply eq_term_refl; exact HwlF | exact HFa ]
          | apply Id_cong; exact HG'
          | eapply eq_term_conv;
            [ exact Haa
            | apply eq_sort_exp_ty;
              [ exact HwG2' | exact HiF
              | apply eq_term_sym; apply eq_ty_subst_id;
                [ exact HwG2' | exact HiF | exact HwElF ] ] ] ]
        | apply eq_term_refl; exact HiG
        | apply El_cong;
          [ unfold oExtC; apply Ext_cong;
            [ exact HG' | apply eq_term_refl; exact HiF
            | apply El_cong;
              [ exact HG' | apply eq_term_refl; exact Hwr
              | apply eq_term_refl; exact HwlF | exact HFa ] ]
          | apply eq_term_refl; apply wf_Rel
          | apply eq_term_refl; exact HwlG
          | exact HBa ] ]
      | apply AppRel_cong;
        [ exact HG'
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_refl; exact HwlG
        | exact HFa | exact HBa | exact Hfa | exact Haa ] ].
  - eapply ceq_exp_eq_r.
    + eapply ceq_exp_subst_l; [ exact Hg2c | exact HAp2 ].
    + apply eq_app_rel_subst;
        [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact HwlF
        | exact HwlG | exact HwF2 | exact HwB2 | exact Hwf2 | exact Hwa2 ].
Qed.
