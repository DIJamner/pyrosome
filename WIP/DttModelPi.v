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
