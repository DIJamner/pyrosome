Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.NfWk Pyrosome.Gluing.Dtt.Inj Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelCand
  Pyrosome.Gluing.Dtt.LogRelCore Pyrosome.Gluing.Dtt.LogRelFun Pyrosome.Gluing.Dtt.LogRelElim Pyrosome.Gluing.Dtt.RSub Pyrosome.Gluing.Dtt.RSubOk
  Pyrosome.Gluing.Dtt.Ceq Pyrosome.Gluing.Dtt.ModelStruct Pyrosome.Gluing.Dtt.ModelGlue.
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
       congruence, plus the equation itself -- and the equation is now
       HANDED DOWN, not proved: it is [dtt_eqt_by]
       (src/Pyrosome/Gluing/Dtt/ModelGlue.v), the generic [cterm_by] recipe
       read in the syntactic model.  (The universe/base fragment
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
       clause across.  No reducibility reasoning at all -- with the
       equation handed down, the whole obligation is
       [ceq_exp_eq_l Heq (ceq_refl_r Hfc)].

   STATUS.  ALL SEVENTEEN are proved here and axiom-free, and the two
   dispatchers at the end are stated over all of them.

   THE IRRELEVANT HALF IS NOT A COPY OF THE RELEVANT ONE, for one reason
   (section 9 pays for it): the codomain code's info.  "Pi_irr" states it
   at [rel (iota L1)] while "lam_irr"/"app_irr" -- and hence
   [LogRel.wkCodCodeIrr] and [nfcode_pi_irr] -- state it at [iCode L0], so
   [pi_irr_nf] moves an [exp_subst] between the two spellings twice
   ([LogRelCand.eq_expsubst_info]), and "Pi_irr beta" has to move its
   codomain argument's CLAUSE across as well ([ceq_exp_transfer]).
   [rty_pi_irr]'s candidate is otherwise the plain Kripke one, same as
   [rty_pi_rel]'s (escape at [Pi_irr] is now supplied by the
   ["proof irrelevance"] rule instead of eta -- see LogRelCore.v's
   [RTy_escape_reflect]), so [cong_LamIrr] and [cong_LamRel] are the same
   shape.

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

(* The clause transports ([ceq_refl_r], [ceq_clause_r], [ceq_exp_eq_l],
   [ceq_exp_eq_r]) and the [iota L1] spelling of a level-0 universe
   ([eq_U_subst_i1c], [eq_U_subst_iota1]) are shared with the other three
   fragments: src/Pyrosome/Gluing/Dtt/ModelGlue.v. *)

(* ---- reading a normal code off a code argument's clause ---------- *)

(* [RTmN_HasNfCode] (src/Pyrosome/Gluing/Dtt/LogRelElim.v) wants the type already stripped of
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
      - apply eq_sort_exp_ty; exact Hty1. }
    eapply eq_term_trans.
    { eapply eq_term_conv;
        [ apply eq_Emptyrec_subst; assumption
        | apply eq_sort_exp_ty; exact Hty1 ]. }
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
   [iCode L0] (trap (A) of src/Pyrosome/Gluing/Dtt/NfTyping.v), so the code reading has to
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

(* [eq_liftW_cong] (src/Pyrosome/Gluing/Dtt/NfWk.v) varies only the lifted type's normal
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
  - apply eq_sort_exp_ty; apply eq_wk_lift_ty; assumption.
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
      + apply eq_sort_exp_ty; apply eq_ty_subst_id;
            [ exact HG0w | exact HcFw | apply wf_U; assumption ].
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
    - apply eq_sort_exp_ty; apply eq_U_subst; assumption. }
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
    - apply eq_sort_exp_ty; apply eq_U_subst;
          [ exact HwD | exact HwG2 | exact Hwg | apply wf_Rel | exact HwlG ]. }
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
    - apply eq_sort_exp_ty; apply eq_U_subst;
          [ exact HwDF | exact HwGF2 | exact Hwh | apply wf_Rel
          | exact HwlG ]. }
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
    - apply eq_sort_exp_ty; apply eq_U_subst_iota1;
          [ exact HwD | exact HwG2 | exact Hwg | apply wf_Irr ]. }
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
    - apply eq_sort_exp_ty; apply eq_U_subst_iota1;
          [ exact HwDF | exact HwGF2 | exact Hwh | apply wf_Irr ]. }
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
    + apply eq_sort_exp_ty; apply eq_ty_subst_id;
          [ exact HG0w | exact HcFw | apply wf_U; assumption ].
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
          | apply eq_sort_exp_ty; exact HtyEq ]).
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
    - apply eq_sort_exp_ty; apply eq_U_subst;
          [ exact HwDF | exact HwGF2 | exact Hwh | apply wf_Rel
          | exact HlGw ]. }
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
     step 1    [ceq_exp_eq_l] against the GIVEN equation [Heq], which
               reduces the goal to the right-hand side's own reflexive
               clause;
     step 2    that clause is [ceq_exp_subst_l] applied to the substitution
               argument's clause and to THIS FRAGMENT'S OWN congruence at
               the reflexive right arguments, transported to the goal's
               sort by [ceq_exp_transfer], and moved onto the right-hand
               side by [ceq_exp_eq_r] and the language's own "X subst".

   Nothing semantic is reproved, and nothing about the rule's left-hand
   side is spelled out: step 1 used to be a twenty-line [ExpSubst_cong]
   over the argument equations, and is now the hypothesis. *)

Lemma by_PiRel_subst G1 G2 G1' G2' g1 g2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rF1 rF2 -> Ceq_term sLvl lF1 lF2 ->
    Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2' rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2' rF2 lF2 F2) oRel lG2) B1 B2 ->
    eqt (sCode G2 oRel lG2)
      (oExpSubst G1 G1' g1 (iCode lG1) (oU G1' oRel lG1)
         (oPiRel G1' rF1 lF1 lG1 F1 B1))
      (oPiRel G2 rF2 lF2 lG2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode lG2) (oU (oExtC G2' rF2 lF2 F2) oRel lG2) B2)) ->
    Ceq_term (sCode G2 oRel lG2)
      (oExpSubst G1 G1' g1 (iCode lG1) (oU G1' oRel lG1)
         (oPiRel G1' rF1 lF1 lG1 F1 B1))
      (oPiRel G2 rF2 lF2 lG2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode lG2) (oU (oExtC G2' rF2 lF2 F2) oRel lG2) B2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf Hlg HFc HBc Heq.
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
  eapply ceq_exp_eq_l; [ exact Heq | ].
  eapply ceq_refl_r.
  eapply ceq_exp_eq_r.
  - eapply ceq_exp_transfer;
      [ apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact HcG
      | apply eq_U_subst;
        [ exact HwG2 | exact HwG2' | exact Hwg2 | apply wf_Rel
        | exact HwlG ]
      | eapply ceq_exp_subst_l; [ exact Hg2c | exact HPi2 ] ].
  - apply eq_Pi_rel_subst;
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
    eqt (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0))
      (oExpSubst G1 G1' g1 (oInfo oRel (oIota oL1)) (oU G1' oIrr oL0)
         (oPiIrr G1' rF1 lF1 F1 B1))
      (oPiIrr G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (oInfo oRel (oIota oL1)) (oU (oExtC G2' rF2 lF2 F2) oIrr oL0) B2)) ->
    Ceq_term (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0))
      (oExpSubst G1 G1' g1 (oInfo oRel (oIota oL1)) (oU G1' oIrr oL0)
         (oPiIrr G1' rF1 lF1 F1 B1))
      (oPiIrr G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (oInfo oRel (oIota oL1)) (oU (oExtC G2' rF2 lF2 F2) oIrr oL0) B2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf HFc HBc Heq.
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
  eapply ceq_exp_eq_l; [ exact Heq | ].
  eapply ceq_refl_r.
  eapply ceq_exp_eq_r.
  - eapply ceq_exp_transfer;
      [ apply eq_term_refl; exact HwG2
      | apply eq_term_refl; exact Hi1L
      | apply eq_U_subst_iota1;
        [ exact HwG2 | exact HwG2' | exact Hwg2 | apply wf_Irr ]
      | eapply ceq_exp_subst_l; [ exact Hg2c | exact HPi2 ] ].
  - apply eq_Pi_irr_subst;
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
    eqt (sExp G2 (iEl rA2 lA2)
                (oTySubst G2 G2' g2 (iEl rA2 lA2) (oEl G2' rA2 lA2 A2)))
      (oExpSubst G1 G1' g1 (iEl rA1 lA1) (oEl G1' rA1 lA1 A1)
         (oEmptyrec G1' rA1 lA1 A1 e1))
      (oEmptyrec G2 rA2 lA2 (oCodeSubst G2 G2' g2 rA2 lA2 A2)
         (oExpSubst G2 G2' g2 (iEl oIrr oL0) (oEl G2' oIrr oL0 (oEmpty G2')) e2)) ->
    Ceq_term (sExp G2 (iEl rA2 lA2)
                (oTySubst G2 G2' g2 (iEl rA2 lA2) (oEl G2' rA2 lA2 A2)))
      (oExpSubst G1 G1' g1 (iEl rA1 lA1) (oEl G1' rA1 lA1 A1)
         (oEmptyrec G1' rA1 lA1 A1 e1))
      (oEmptyrec G2 rA2 lA2 (oCodeSubst G2 G2' g2 rA2 lA2 A2)
         (oExpSubst G2 G2' g2 (iEl oIrr oL0) (oEl G2' oIrr oL0 (oEmpty G2')) e2)).
Proof.
  intros HGc HGc' Hgc Hr Hl HAc Hec Heq.
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
  eapply ceq_exp_eq_l; [ exact Heq | ].
  eapply ceq_refl_r.
  eapply ceq_exp_eq_r.
  - eapply ceq_exp_subst_l; [ exact Hg2c | exact HEr2 ].
  - apply eq_Emptyrec_subst;
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
    eqt (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
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
      f2 ->
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
  intros HGc Hr Hlf Hlg HFc HBc Hfc Heq.
  exact (ceq_exp_eq_l Heq (ceq_refl_r Hfc)).
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
   ([LogRelCore.an_appConcl] and [LogRelCand.ac_appConcl]); only the first,
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
          | apply eq_sort_exp_ty; exact HtyF ]).
  assert (wft ag (sElt D rF2 lF2 (wkCode D G2 g rF2 lF2 F2))) as Hwag''.
  { eapply wf_term_conv; [ exact Hwag | ].
    apply eq_sort_exp_ty; unfold wkCode; apply eq_El_subst; assumption. }
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
      | apply eq_sort_exp_ty; exact HtyPi ]. }
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
          | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwG2 | exact HiF | exact HwElF ] ] ]. }
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
          | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwD | exact HiF | apply wf_El; assumption ] ] ]
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
            | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
                [ exact HwG2 | exact HiF | exact HwElF ] ] ]
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
      + apply eq_sort_exp_ty; apply eq_ty_subst_id;
            [ exact HwDF | exact HcG
            | apply wf_U; [ exact HwDF | apply wf_Rel | exact HwlG ] ].
    - apply eq_exp_subst_id;
        [ exact HwDF | exact HcG
        | apply wf_U; [ exact HwDF | apply wf_Rel | exact HwlG ]
        | exact HwB0 ]. }
  (* the three-step equation *)
  eapply eq_term_conv.
  2:{ apply eq_sort_exp_ty.
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
              | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
                  [ exact HwG2 | exact HiF | exact HwElF ] ] ]
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
    - apply eq_sort_exp_ty; exact Hhub1. }
  eapply eq_term_trans.
  { eapply eq_term_conv;
      [ apply eq_app_rel_subst;
        [ exact HwD | exact HwG2 | exact Hwg | exact Hwr | exact HwlF
        | exact HwlG | exact HwF2 | exact HwB2 | exact Hwf1 | exact Hwa1 ]
      | apply eq_sort_exp_ty; exact Hhub1 ]. }
  (* and finally back to [appAtRel] *)
  eapply eq_term_conv.
  2:{ apply eq_sort_exp_ty; exact Hhub3. }
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
      | apply eq_sort_exp_ty;
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
    eqt
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
         (oExpSubst G2 G2' g2 (iEl rF2 lF2) (oEl G2' rF2 lF2 F2) a2)) ->
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
  intros HGc HGc' Hgc Hr Hlf Hlg HFc HBc Hfc Hac Heq.
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
  eapply ceq_exp_eq_l; [ exact Heq | ].
  eapply ceq_refl_r.
  eapply ceq_exp_eq_r.
  - eapply ceq_exp_subst_l; [ exact Hg2c | exact HAp2 ].
  - apply eq_app_rel_subst;
      [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact HwlF
      | exact HwlG | exact HwF2 | exact HwB2 | exact Hwf2 | exact Hwa2 ].
Qed.

(* ================================================================== *)
(* 7.  [lam_rel]                                                       *)
(* ================================================================== *)

(* A [lam] concludes at [El (Pi ...)], and at a Pi the candidate is
   "applied to any reducible argument, land in the codomain candidate".
   So the Kripke quantifier is opened, and the application of the lambda
   is reduced by "lam_rel subst" followed by "Pi_rel beta" to
   [t[<w;g, a>]] -- at which point the body's OWN clause applies, because
   [binder_snoc] makes [<w;g, a>] a reducible substitution into
   [extC G rF lF F].

   Two [sigma] identities carry the case: [eq_snoc_liftW] ("instantiate
   after lifting is instantiate at the composite"), which is what turns
   the beta-reduct into the body's instance, and [eq_liftW_cmp] ("lifting
   composes"), which is what identifies the codomain code the Kripke
   quantifier names with the one the substitution rules produce. *)
Lemma cong_LamRel G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2 t1 t2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 -> Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sElt (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t1 t2 ->
    Ceq_term (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
      (oLamRel G1 rF1 lF1 lG1 F1 B1 t1) (oLamRel G2 rF2 lF2 lG2 F2 B2 t2).
Proof.
  intros HGc Hr Hlf Hlg HFc HBc Htc.
  pose proof (ceq_clause_r HFc) as HFb2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_exp_e in HFc as [HFa HFb].
  apply Ceq_exp_e in HBc as [HBa HBb].
  apply Ceq_exp_e in Htc as [Hta Htb].
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
  assert (wft t1 (sElt (oExtC G2 rF2 lF2 F2) oRel lG2 B2)) as Hwt1
      by (eapply eqt_wf_l; exact Hta).
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
  assert (wft (oPiRel G2 rF2 lF2 lG2 F2 B2) (sCode G2 oRel lG2)) as HwPi
      by (apply wf_PiRel; assumption).
  assert (wft (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
            (sTy G2 (iEl oRel lG2))) as HwElPi
      by (apply wf_El; [ exact HwG2 | apply wf_Rel | exact HwlG | exact HwPi ]).
  apply ceq_exp.
  { apply LamRel_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | apply eq_term_refl; exact HwlG
      | exact HFa | exact HBa | exact Hta ]. }
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
  assert (eqt (sTy D (iEl rF2 lF2))
            (oTySubst D G2 g (iEl rF2 lF2) (oEl G2 rF2 lF2 F2))
            (oEl D rF2 lF2 F0)) as HtyF.
  { eapply eq_term_trans; [ apply eq_El_subst; assumption | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HF0eq ]. }
  assert (eqt (sTy D (iEl oRel lG2))
            (oTySubst D G2 g (iEl oRel lG2)
               (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2)))
            (oEl D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0))) as HtyPi.
  { eapply eq_term_trans;
      [ apply eq_El_subst;
        [ exact HwD | exact HwG2 | exact Hwg | apply wf_Rel | exact HwlG
        | exact HwPi ] | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Rel
      | apply eq_term_refl; exact HwlG
      | exact HPi ]. }
  destruct (RTyEx_of_NfCode HnfPi) as [P HP].
  eapply RTmN_intro with
    (i0 := iEl oRel lG2)
    (A0 := oEl D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0)) (P := P);
    [ apply eq_term_refl; exact HiG
    | apply tyok_El; exact HnfPi
    | exact HtyPi
    | exact HP
    | ].
  destruct (RTy_pi_rel_e HP)
    as [Pd [Pc (Hrn & Hlfn & Hlgn & HnF0 & HnB0 & Hdom & Hcod & Hiff)]].
  apply (proj2 (Hiff _)).
  intros D' w a HW HD' Hpd.
  assert (wft D' sEnv) as HwD' by (apply EnvOk_wf; exact HD').
  assert (wft w (sSub D' D)) as Hww by (apply Wk_wf; exact HW).
  destruct (Hcod D' w a HW HD' Hpd) as [C (HTyC & HeqC & HRc)].
  assert (wft a (sElt D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))) as Hawf.
  { eapply codAt_wf_a with (rG := oRel) (lG := lG2) (B := B0);
      [ exact HwD' | exact HwD | exact Hwr | exact HwlF | exact Hww
      | exact HwF0 | eapply eqt_wf_l; exact HeqC ]. }
  (* ---- the composite substitution and its data ---- *)
  assert (RSubN D' G2 (oCmp D' D G2 w g)) as Hwgr
      by (eapply RSubN_wk; [ exact Hg | exact HW | exact HD' ]).
  assert (wft (oCmp D' D G2 w g) (sSub D' G2)) as Hwgw
      by (apply RSubN_wf; exact Hwgr).
  (* [w;g] applied to the domain code *)
  assert (eqt (sCode D' rF2 lF2)
            (wkCode D' D w rF2 lF2 F0)
            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) as HeqFw.
  { unfold wkCode.
    eapply eq_term_trans.
    2:{ eapply eq_term_conv;
          [ apply eq_exp_subst_cmp;
            [ exact HwD' | exact HwD | exact HwG2 | exact Hww | exact Hwg
            | exact HcF | apply wf_U; assumption | exact HwF2 ]
          | apply eq_sort_exp_ty;
            eapply eq_term_trans;
            [ apply TySubst_cong
                with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                     (g1 := w) (g2 := w) (i1 := iCode lF2) (i2 := iCode lF2)
                     (A1 := oTySubst D G2 g (iCode lF2) (oU G2 rF2 lF2))
                     (A2 := oU D rF2 lF2);
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact HwD
              | apply eq_term_refl; exact Hww
              | apply eq_term_refl; exact HcF
              | apply eq_U_subst; assumption ]
            | apply eq_U_subst; assumption ] ]. }
    apply eq_term_sym.
    eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D') (G2 := D') (G1' := D) (G2' := D) (g1 := w) (g2 := w)
             (i1 := iCode lF2) (i2 := iCode lF2)
             (A1 := oTySubst D G2 g (iCode lF2) (oU G2 rF2 lF2))
             (A2 := oU D rF2 lF2)
             (v1 := oExpSubst D G2 g (iCode lF2) (oU G2 rF2 lF2) F2)
             (v2 := F0);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hww
        | apply eq_term_refl; exact HcF
        | apply eq_U_subst; assumption
        | exact HF0eq ].
    - apply eq_sort_exp_ty; apply eq_U_subst; assumption. }
  assert (wft (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
            (sCode D' rF2 lF2)) as HwFw2
      by (eapply eqt_wf_r; exact HeqFw).
  assert (wft (oExtC D' rF2 lF2 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
            sEnv) as HwD'F by (apply wf_ExtC; assumption).
  assert (eqt (sTy D' (iEl rF2 lF2))
            (oTySubst D' G2 (oCmp D' D G2 w g) (iEl rF2 lF2)
               (oEl G2 rF2 lF2 F2))
            (oEl D' rF2 lF2 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
    as HtyFw
      by (apply eq_El_subst; assumption).
  assert (wft a (sElt D' rF2 lF2
                   (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))) as Hawf2.
  { eapply wf_term_conv; [ exact Hawf | ].
    apply eq_sort_exp_ty.
    apply El_cong;
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HeqFw ]. }
  assert (wft a (sExp D' (iEl rF2 lF2)
                   (oTySubst D' G2 (oCmp D' D G2 w g) (iEl rF2 lF2)
                      (oEl G2 rF2 lF2 F2)))) as Hawf3
      by (eapply wf_term_conv;
          [ exact Hawf2
          | apply eq_sort_exp_ty; apply eq_term_sym; exact HtyFw ]).
  (* ---- the argument is reducible at the composite ---- *)
  destruct (Hdom D' w HW HD') as [F' (HnF' & HeqF' & HRd)].
  assert (RTmN D' (iEl rF2 lF2)
            (oTySubst D' G2 (oCmp D' D G2 w g) (iEl rF2 lF2)
               (oEl G2 rF2 lF2 F2)) a) as Harm.
  { eapply RTmN_intro with
      (i0 := iEl rF2 lF2) (A0 := oEl D' rF2 lF2 F') (P := Pd D' w);
      [ apply eq_term_refl; exact HiF
      | apply tyok_El; exact HnF'
      | eapply eq_term_trans; [ exact HtyFw | ]
      | exact HRd
      | exact Hpd ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | eapply eq_term_trans; [ apply eq_term_sym; exact HeqFw | exact HeqF' ] ]. }
  assert (RSubN D' (oExtC G2 rF2 lF2 F2)
            (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
               (oCmp D' D G2 w g) a)) as HRSs
      by (eapply binder_snoc;
          [ exact Hrnf | exact Hlfnf | exact HwF2 | exact HFb2
          | exact HD' | exact Hwgr | exact Hawf3 | exact Harm ]).
  (* ---- LIFTING COMPOSES: the codomain code the Kripke quantifier names
         is the one the substitution rules produce ---- *)
  assert (eqt (sSub (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)))
            (oLift D' D w rF2 lF2 F0)
            (oLiftW D' D w (iEl rF2 lF2)
               (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (oEl D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))) as Hliftmove.
  { rewrite oLift_oLiftW.
    apply eq_liftW_gen with (G1 := D) (A1 := oEl D rF2 lF2 F0);
      [ exact HwD' | exact HwD | exact HwD | exact HiF
      | apply wf_El; assumption
      | apply wf_El;
        [ exact HwD | exact Hwr | exact HwlF
        | eapply eqt_wf_l; exact HF0eq ]
      | apply wf_El;
        [ exact HwD' | exact Hwr | exact HwlF
        | eapply eqt_wf_l; exact HeqFw ]
      | apply wf_El; assumption
      | exact Hww
      | apply eq_term_refl; exact HwD
      | apply El_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_sym; exact HF0eq ]
      | apply eq_El_subst; assumption
      | eapply eq_term_trans;
        [ apply eq_El_subst;
          [ exact HwD' | exact HwD | exact Hww | exact Hwr | exact HwlF
          | eapply eqt_wf_l; exact HF0eq ]
        | apply El_cong;
          [ apply eq_term_refl; exact HwD'
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | eapply eq_term_trans;
            [ eapply eq_term_conv;
              [ apply ExpSubst_cong
                  with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                       (g1 := w) (g2 := w) (i1 := iCode lF2) (i2 := iCode lF2)
                       (A1 := oU D rF2 lF2) (A2 := oU D rF2 lF2)
                       (v1 := oCodeSubst D G2 g rF2 lF2 F2) (v2 := F0);
                [ apply eq_term_refl; exact HwD'
                | apply eq_term_refl; exact HwD
                | apply eq_term_refl; exact Hww
                | apply eq_term_refl; exact HcF
                | apply eq_term_refl; apply wf_U; assumption
                | exact HF0eq ]
              | apply eq_sort_exp_ty; apply eq_U_subst; assumption ]
            | exact HeqFw ] ] ] ]. }
  assert (eqt (sCode (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oRel lG2)
            (oExpSubst (oExtC D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))
               (oExtC D rF2 lF2 F0) (oLift D' D w rF2 lF2 F0)
               (iCode lG2) (oU (oExtC D rF2 lF2 F0) oRel lG2) B0)
            (oExpSubst
               (oExtC D' rF2 lF2 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2)
               (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
               (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)) as HeqBw.
  { assert (eqt sEnv (oExtC D rF2 lF2 F0)
              (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))) as HEnvD.
    { unfold oExtC; apply Ext_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HiF
        | apply El_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | apply eq_term_sym; exact HF0eq ] ]. }
    assert (wft (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)) sEnv) as HwDFg
        by (eapply eqt_wf_r; exact HEnvD).
    assert (wft (oLiftW D' D w (iEl rF2 lF2)
                  (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                  (oEl D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
              (sSub (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)))) as HwLW
        by (eapply eqt_wf_r; exact Hliftmove).
    assert (wft (oLift D G2 g rF2 lF2 F2)
              (sSub (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (oExtC G2 rF2 lF2 F2))) as HwLg
        by (apply wf_oLift; assumption).
    eapply eq_term_trans.
    { (* replace [B0] by its own reading, and move to the "g" envs *)
      eapply eq_term_conv.
      - apply ExpSubst_cong
          with (G1 := oExtC D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))
               (G2 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G1' := oExtC D rF2 lF2 F0)
               (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (g1 := oLift D' D w rF2 lF2 F0)
               (g2 := oLiftW D' D w (iEl rF2 lF2)
                        (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oEl D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (i1 := iCode lG2) (i2 := iCode lG2)
               (A1 := oU (oExtC D rF2 lF2 F0) oRel lG2)
               (A2 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        oRel lG2)
               (v1 := B0)
               (v2 := oExpSubst
                        (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2);
          [ unfold oExtC; apply Ext_cong;
            [ apply eq_term_refl; exact HwD'
            | apply eq_term_refl; exact HiF
            | apply El_cong;
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact Hwr
              | apply eq_term_refl; exact HwlF
              | exact HeqFw ] ]
          | exact HEnvD
          | exact Hliftmove
          | apply eq_term_refl; exact HcG
          | apply U_cong;
            [ exact HEnvD | apply eq_term_refl; apply wf_Rel
            | apply eq_term_refl; exact HwlG ]
          | eapply eq_term_conv;
            [ apply eq_term_sym; exact HB
            | apply sExp_cong;
              [ exact HEnvD | apply eq_term_refl; exact HcG
              | apply U_cong;
                [ exact HEnvD | apply eq_term_refl; apply wf_Rel
                | apply eq_term_refl; exact HwlG ] ] ] ].
      - apply eq_sort_exp_ty; apply eq_U_subst;
            [ exact HwD'F | exact HwDFg | exact HwLW
            | apply wf_Rel | exact HwlG ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv.
      - apply ExpSubst_cong
          with (G1 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G2 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G1' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (g1 := oLiftW D' D w (iEl rF2 lF2)
                        (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oEl D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (g2 := oLiftW D' D w (iEl rF2 lF2)
                        (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oEl D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (i1 := iCode lG2) (i2 := iCode lG2)
               (A1 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        oRel lG2)
               (A2 := oTySubst (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2))
               (v1 := oExpSubst
                        (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)
               (v2 := oExpSubst
                        (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2);
          [ apply eq_term_refl; exact HwD'F
          | apply eq_term_refl; exact HwDFg
          | apply eq_term_refl; exact HwLW
          | apply eq_term_refl; exact HcG
          | apply eq_term_sym; apply eq_U_subst;
            [ exact HwDFg | exact HwGF | exact HwLg | apply wf_Rel
            | exact HwlG ]
          | apply eq_term_refl; apply wf_ExpSubst;
            [ exact HwDFg | exact HwGF | exact HwLg | exact HcG
            | apply wf_U; [ exact HwGF | apply wf_Rel | exact HwlG ]
            | exact HwB2 ] ].
      - apply eq_sort_exp_ty.
        eapply eq_term_trans.
        + apply TySubst_cong
            with (G1 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G2 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G1' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (g1 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (g2 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (i1 := iCode lG2) (i2 := iCode lG2)
                 (A1 := oTySubst
                          (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                          (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2))
                 (A2 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          oRel lG2);
            [ apply eq_term_refl; exact HwD'F
            | apply eq_term_refl; exact HwDFg
            | apply eq_term_refl; exact HwLW
            | apply eq_term_refl; exact HcG
            | apply eq_U_subst;
              [ exact HwDFg | exact HwGF | exact HwLg | apply wf_Rel
              | exact HwlG ] ].
        + apply eq_U_subst;
            [ exact HwD'F | exact HwDFg | exact HwLW | apply wf_Rel
            | exact HwlG ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv.
      - apply eq_exp_subst_cmp
          with (G1 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G2 := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (G3 := oExtC G2 rF2 lF2 F2)
               (f := oLiftW D' D w (iEl rF2 lF2)
                       (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                       (oEl D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (g := oLift D G2 g rF2 lF2 F2) (i := iCode lG2)
               (A := oU (oExtC G2 rF2 lF2 F2) oRel lG2) (v := B2);
          [ exact HwD'F | exact HwDFg | exact HwGF | exact HwLW | exact HwLg
          | exact HcG
          | apply wf_U; [ exact HwGF | apply wf_Rel | exact HwlG ]
          | exact HwB2 ].
      - apply eq_sort_exp_ty.
        eapply eq_term_trans.
        + apply TySubst_cong
            with (G1 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G2 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G1' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (g1 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (g2 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (i1 := iCode lG2) (i2 := iCode lG2)
                 (A1 := oTySubst
                          (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                          (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2))
                 (A2 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          oRel lG2);
            [ apply eq_term_refl; exact HwD'F
            | apply eq_term_refl; exact HwDFg
            | apply eq_term_refl; exact HwLW
            | apply eq_term_refl; exact HcG
            | apply eq_U_subst;
              [ exact HwDFg | exact HwGF | exact HwLg | apply wf_Rel
              | exact HwlG ] ].
        + apply eq_U_subst;
            [ exact HwD'F | exact HwDFg | exact HwLW | apply wf_Rel
            | exact HwlG ]. }
    eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := oExtC D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (G2 := oExtC D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (G1' := oExtC G2 rF2 lF2 F2) (G2' := oExtC G2 rF2 lF2 F2)
             (g1 := oCmp (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLiftW D' D w (iEl rF2 lF2)
                         (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                         (oEl D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                      (oLift D G2 g rF2 lF2 F2))
             (g2 := oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (i1 := iCode lG2) (i2 := iCode lG2)
             (A1 := oU (oExtC G2 rF2 lF2 F2) oRel lG2)
             (A2 := oU (oExtC G2 rF2 lF2 F2) oRel lG2)
             (v1 := B2) (v2 := B2);
        [ apply eq_term_refl; exact HwD'F
        | apply eq_term_refl; exact HwGF
        | rewrite oLift_oLiftW;
          apply eq_liftW_cmp
            with (D := D) (A' := oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2));
          [ exact HwD' | exact HwD | exact HwG2 | exact HiF
          | apply wf_El; assumption
          | apply wf_El;
            [ exact HwD | exact Hwr | exact HwlF
            | eapply eqt_wf_l; exact HF0eq ]
          | apply wf_El;
            [ exact HwD' | exact Hwr | exact HwlF
            | eapply eqt_wf_r; exact HeqFw ]
          | exact Hwg | exact Hww | exact Hwgw
          | apply eq_El_subst; assumption
          | eapply eq_term_trans;
            [ apply eq_El_subst;
              [ exact HwD' | exact HwD | exact Hww | exact Hwr | exact HwlF
              | eapply eqt_wf_l; exact HF0eq ]
            | apply El_cong;
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact Hwr
              | apply eq_term_refl; exact HwlF
              | eapply eq_term_trans;
                [ eapply eq_term_conv;
                  [ apply ExpSubst_cong
                      with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                           (g1 := w) (g2 := w)
                           (i1 := iCode lF2) (i2 := iCode lF2)
                           (A1 := oU D rF2 lF2) (A2 := oU D rF2 lF2)
                           (v1 := oCodeSubst D G2 g rF2 lF2 F2) (v2 := F0);
                    [ apply eq_term_refl; exact HwD'
                    | apply eq_term_refl; exact HwD
                    | apply eq_term_refl; exact Hww
                    | apply eq_term_refl; exact HcF
                    | apply eq_term_refl; apply wf_U; assumption
                    | exact HF0eq ]
                  | apply eq_sort_exp_ty; apply eq_U_subst; assumption ]
                | exact HeqFw ] ] ]
          | apply eq_term_refl; exact Hwgw ]
        | apply eq_term_refl; exact HcG
        | apply eq_term_refl; apply wf_U;
          [ exact HwGF | apply wf_Rel | exact HwlG ]
        | apply eq_term_refl; exact HwB2 ].
    - apply eq_sort_exp_ty; apply eq_U_subst;
          [ exact HwD'F | exact HwGF
          | apply wf_oLift; assumption
          | apply wf_Rel | exact HwlG ]. }
  assert (wft (oExpSubst
                 (oExtC D' rF2 lF2
                    (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC G2 rF2 lF2 F2)
                 (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                 (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)
            (sCode (oExtC D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oRel lG2))
    as HwBw2 by (eapply eqt_wf_r; exact HeqBw).
  assert (wft (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
            (sSub (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2))) as HwLwg
      by (apply wf_oLift; assumption).
  (* ---- the codomain type: three readings of one hub ---- *)
  assert (eqt (sTy D' (iEl oRel lG2))
            (oTySubst D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (iEl oRel lG2)
               (oEl (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oRel lG2
                  (oExpSubst
                     (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2)
                     (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                     (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)))
            (oTySubst D' (oExtC G2 rF2 lF2 F2)
               (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                  (oCmp D' D G2 w g) a)
               (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)))
    as Hac.
  { apply ac_appConcl with (rG := oRel) (a := a) (w := oCmp D' D G2 w g);
      first [ assumption | apply wf_Rel ]. }
  assert (eqt (sTy D' (iEl oRel lG2))
            (oTySubst D' (oExtC G2 rF2 lF2 F2)
               (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                  (oCmp D' D G2 w g) a)
               (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)) C)
    as HtyC.
  { eapply eq_term_trans; [ apply eq_term_sym; exact Hac | ].
    eapply eq_term_trans; [ | exact HeqC ].
    apply an_appConcl with (rG := oRel) (G := D) (w := w) (F := F0)
      (B := B0) (a := a)
      (F' := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
      (B' := oExpSubst
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2)
               (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
               (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)
      (a' := a);
      first [ assumption | apply wf_Rel | apply eq_term_refl; assumption ]. }
  assert (eqt (sTy D' (iEl oRel lG2))
            (oTySubst D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (iEl oRel lG2)
               (oEl (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oRel lG2
                  (oExpSubst
                     (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2)
                     (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                     (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2))) C)
    as HtyAC by (eapply eq_term_trans; [ exact Hac | exact HtyC ]).
  (* ---- the lambda's own type at the composite substitution ---- *)
  assert (eqt (sTy D' (iEl oRel lG2))
            (oTySubst D' G2 (oCmp D' D G2 w g) (iEl oRel lG2)
               (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2)))
            (oEl D' oRel lG2
               (oPiRel D' rF2 lF2 lG2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                  (oExpSubst
                     (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2)
                     (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                     (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2))))
    as HtyPiW.
  { eapply eq_term_trans;
      [ apply eq_El_subst;
        [ exact HwD' | exact HwG2 | exact Hwgw | apply wf_Rel | exact HwlG
        | exact HwPi ] | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; apply wf_Rel
      | apply eq_term_refl; exact HwlG
      | apply eq_Pi_rel_subst;
        [ exact HwD' | exact HwG2 | exact Hwgw | exact Hwr | exact HwlF
        | exact HwlG | exact HwF2 | exact HwB2 ] ]. }
  (* ---- the body, transported ---- *)
  assert (wft (oExpSubst
                 (oExtC D' rF2 lF2
                    (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC G2 rF2 lF2 F2)
                 (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                 (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t1)
            (sElt (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oRel lG2
               (oExpSubst
                  (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                  (oExtC G2 rF2 lF2 F2)
                  (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                  (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)))
    as Hwtw.
  { eapply wf_term_conv;
      [ apply wf_ExpSubst;
        [ exact HwD'F | exact HwGF | exact HwLwg | exact HiG | exact HwElB
        | exact Hwt1 ]
      | apply eq_sort_exp_ty;
        apply eq_El_subst;
        [ exact HwD'F | exact HwGF | exact HwLwg | apply wf_Rel | exact HwlG
        | exact HwB2 ] ]. }
  (* ---- instantiate after lifting = instantiate at the composite ---- *)
  assert (eqt (sSub D' (oExtC G2 rF2 lF2 F2))
            (oCmp D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2)
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
            (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
               (oCmp D' D G2 w g) a)) as Hsnoc.
  { eapply eq_term_trans.
    - unfold oInst, oExtC; rewrite oLift_oLiftW.
      apply eq_snoc_liftW with (D2 := D') (D := D') (G := G2)
        (w2 := oId D') (w := oCmp D' D G2 w g) (i := iEl rF2 lF2)
        (A := oEl G2 rF2 lF2 F2)
        (A' := oEl D' rF2 lF2
                 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) (a := a);
        [ exact HwD' | exact HwD' | exact HwG2 | exact HiF
        | exact HwElF
        | apply wf_El;
          [ exact HwD' | exact Hwr | exact HwlF | exact HwFw2 ]
        | exact Hwgw | apply wf_Id; exact HwD'
        | exact HtyFw
        | eapply wf_term_conv;
          [ exact Hawf2
          | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwD' | exact HiF
              | apply wf_El;
                [ exact HwD' | exact Hwr | exact HwlF | exact HwFw2 ] ] ] ].
    - apply Snoc_cong;
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact HiF
        | apply eq_term_refl; exact HwElF
        | apply eq_id_left; [ exact HwD' | exact HwG2 | exact Hwgw ]
        | apply eq_term_refl; exact Hawf3 ]. }
  (* ================================================================ *)
  (* the Kripke obligation                                            *)
  (* ================================================================ *)
  eapply (RTy_cand_eq HRc).
  { eapply RTmN_elim with (i0 := iEl oRel lG2) (A0 := C) (P := Pc D' w a);
      [ apply Htb; [ exact HD' | exact HRSs ]
      | apply eq_term_refl; exact HiG
      | exact HTyC
      | exact HtyC
      | exact HRc ]. }
  apply eq_term_sym.
  (* [app_rel] of the weakened lambda, reduced *)
  eapply eq_term_trans.
  { eapply eq_term_conv.
    - unfold appAtRel, wkFunRel.
      apply AppRel_cong
        with (G1 := D') (G2 := D') (rF1 := rF2) (rF2 := rF2)
             (lF1 := lF2) (lF2 := lF2) (lG1 := lG2) (lG2 := lG2)
             (F1 := wkCode D' D w rF2 lF2 F0)
             (F2 := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (B1 := oExpSubst (oExtC D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))
                      (oExtC D rF2 lF2 F0) (oLift D' D w rF2 lF2 F0)
                      (iCode lG2) (oU (oExtC D rF2 lF2 F0) oRel lG2) B0)
             (B2 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)
             (f1 := oExpSubst D' D w (iEl oRel lG2)
                      (oEl D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0))
                      (oExpSubst D G2 g (iEl oRel lG2)
                         (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
                         (oLamRel G1 rF2 lF2 lG2 F1 B1 t1)))
             (f2 := oExpSubst D' G2 (oCmp D' D G2 w g) (iEl oRel lG2)
                      (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
                      (oLamRel G2 rF2 lF2 lG2 F2 B2 t1))
             (a1 := a) (a2 := a);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_refl; exact HwlG
        | exact HeqFw
        | exact HeqBw
        | (* the function *)
          eapply eq_term_conv;
          [ eapply eq_term_trans;
            [ apply ExpSubst_cong
                with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                     (g1 := w) (g2 := w)
                     (i1 := iEl oRel lG2) (i2 := iEl oRel lG2)
                     (A1 := oEl D oRel lG2 (oPiRel D rF2 lF2 lG2 F0 B0))
                     (A2 := oTySubst D G2 g (iEl oRel lG2)
                              (oEl G2 oRel lG2
                                 (oPiRel G2 rF2 lF2 lG2 F2 B2)))
                     (v1 := oExpSubst D G2 g (iEl oRel lG2)
                              (oEl G2 oRel lG2
                                 (oPiRel G2 rF2 lF2 lG2 F2 B2))
                              (oLamRel G1 rF2 lF2 lG2 F1 B1 t1))
                     (v2 := oExpSubst D G2 g (iEl oRel lG2)
                              (oEl G2 oRel lG2
                                 (oPiRel G2 rF2 lF2 lG2 F2 B2))
                              (oLamRel G1 rF2 lF2 lG2 F1 B1 t1));
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact HwD
              | apply eq_term_refl; exact Hww
              | apply eq_term_refl; exact HiG
              | apply eq_term_sym; exact HtyPi
              | apply eq_term_refl; apply wf_ExpSubst;
                [ exact HwD | exact HwG2 | exact Hwg | exact HiG
                | exact HwElPi
                | eapply eqt_wf_l; apply LamRel_cong;
                  [ exact HG
                  | apply eq_term_refl; exact Hwr
                  | apply eq_term_refl; exact HwlF
                  | apply eq_term_refl; exact HwlG
                  | exact HFa | exact HBa | exact Hta ] ] ]
            | eapply eq_term_trans;
              [ apply eq_exp_subst_cmp;
                [ exact HwD' | exact HwD | exact HwG2 | exact Hww | exact Hwg
                | exact HiG | exact HwElPi
                | eapply eqt_wf_l; apply LamRel_cong;
                  [ exact HG
                  | apply eq_term_refl; exact Hwr
                  | apply eq_term_refl; exact HwlF
                  | apply eq_term_refl; exact HwlG
                  | exact HFa | exact HBa | exact Hta ] ]
              | eapply eq_term_conv;
                [ apply ExpSubst_cong
                    with (G1 := D') (G2 := D') (G1' := G2) (G2' := G2)
                         (g1 := oCmp D' D G2 w g) (g2 := oCmp D' D G2 w g)
                         (i1 := iEl oRel lG2) (i2 := iEl oRel lG2)
                         (A1 := oEl G2 oRel lG2
                                  (oPiRel G2 rF2 lF2 lG2 F2 B2))
                         (A2 := oEl G2 oRel lG2
                                  (oPiRel G2 rF2 lF2 lG2 F2 B2))
                         (v1 := oLamRel G1 rF2 lF2 lG2 F1 B1 t1)
                         (v2 := oLamRel G2 rF2 lF2 lG2 F2 B2 t1);
                  [ apply eq_term_refl; exact HwD'
                  | apply eq_term_refl; exact HwG2
                  | apply eq_term_refl; exact Hwgw
                  | apply eq_term_refl; exact HiG
                  | apply eq_term_refl; exact HwElPi
                  | apply LamRel_cong;
                    [ exact HG
                    | apply eq_term_refl; exact Hwr
                    | apply eq_term_refl; exact HwlF
                    | apply eq_term_refl; exact HwlG
                    | exact HFa | exact HBa
                    | apply eq_term_refl; exact Hwt1 ] ]
                | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_cmp;
                    [ exact HwD' | exact HwD | exact HwG2 | exact Hww
                    | exact Hwg | exact HiG | exact HwElPi ] ] ] ]
          | apply eq_sort_exp_ty; eapply eq_term_trans;
              [ apply eq_ty_subst_cmp;
                [ exact HwD' | exact HwD | exact HwG2 | exact Hww | exact Hwg
                | exact HiG | exact HwElPi ]
              | exact HtyPiW ] ]
        | apply eq_term_refl; exact Hawf2 ].
    - apply eq_sort_exp_ty; exact HtyAC. }
  eapply eq_term_trans.
  { eapply eq_term_conv.
    - apply AppRel_cong
        with (G1 := D') (G2 := D') (rF1 := rF2) (rF2 := rF2)
             (lF1 := lF2) (lF2 := lF2) (lG1 := lG2) (lG2 := lG2)
             (F1 := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (F2 := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (B1 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)
             (B2 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)
             (f1 := oExpSubst D' G2 (oCmp D' D G2 w g) (iEl oRel lG2)
                      (oEl G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
                      (oLamRel G2 rF2 lF2 lG2 F2 B2 t1))
             (f2 := oLamRel D' rF2 lF2 lG2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (oExpSubst
                         (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                         (oExtC G2 rF2 lF2 F2)
                         (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                         (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2)
                      (oExpSubst
                         (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                         (oExtC G2 rF2 lF2 F2)
                         (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                         (iEl oRel lG2)
                         (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t1))
             (a1 := a) (a2 := a);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_refl; exact HwlG
        | apply eq_term_refl; exact HwFw2
        | apply eq_term_refl; exact HwBw2
        | eapply eq_term_conv;
          [ apply eq_lam_rel_subst;
            [ exact HwD' | exact HwG2 | exact Hwgw | exact Hwr | exact HwlF
            | exact HwlG | exact HwF2 | exact HwB2 | exact Hwt1 ]
          | apply eq_sort_exp_ty; exact HtyPiW ]
        | apply eq_term_refl; exact Hawf2 ].
    - apply eq_sort_exp_ty; exact HtyAC. }
  eapply eq_term_trans.
  { eapply eq_term_conv;
      [ apply eq_Pi_rel_beta;
        [ exact HwD' | exact Hwr | exact HwlF | exact HwlG | exact HwFw2
        | exact HwBw2 | exact Hwtw | exact Hawf2 ]
      | apply eq_sort_exp_ty; exact HtyAC ]. }
  (* and the beta-reduct is the body's own instance *)
  assert (eqt (sTy D' (iEl oRel lG2))
            (oTySubst D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (iEl oRel lG2)
               (oTySubst
                  (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                  (oExtC G2 rF2 lF2 F2)
                  (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                  (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)))
            C) as HS1C.
  { eapply eq_term_trans;
      [ apply eq_ty_subst_cmp
          with (G1 := D')
               (G2 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G3 := oExtC G2 rF2 lF2 F2)
               (f := oInst D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (g := oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
               (i := iEl oRel lG2)
               (A := oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2);
        [ exact HwD' | exact HwD'F | exact HwGF
        | apply wf_oInst; assumption
        | exact HwLwg | exact HiG | exact HwElB ] | ].
    eapply eq_term_trans; [ | exact HtyC ].
    apply TySubst_cong
      with (G1 := D') (G2 := D')
           (G1' := oExtC G2 rF2 lF2 F2) (G2' := oExtC G2 rF2 lF2 F2)
           (g1 := oCmp D'
                    (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                    (oExtC G2 rF2 lF2 F2)
                    (oInst D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
                    (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
           (g2 := oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                    (oCmp D' D G2 w g) a)
           (i1 := iEl oRel lG2) (i2 := iEl oRel lG2)
           (A1 := oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)
           (A2 := oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2);
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; exact HwGF
      | exact Hsnoc
      | apply eq_term_refl; exact HiG
      | apply eq_term_refl; exact HwElB ]. }
  eapply eq_term_trans.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D') (G2 := D')
             (G1' := oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (G2' := oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (g1 := oInst D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
             (g2 := oInst D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
             (i1 := iEl oRel lG2) (i2 := iEl oRel lG2)
             (A1 := oEl (oExtC D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      oRel lG2
                      (oExpSubst
                         (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                         (oExtC G2 rF2 lF2 F2)
                         (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                         (iCode lG2) (oU (oExtC G2 rF2 lF2 F2) oRel lG2) B2))
             (A2 := oTySubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iEl oRel lG2)
                      (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2))
             (v1 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iEl oRel lG2)
                      (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t1)
             (v2 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iEl oRel lG2)
                      (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t1);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact HwD'F
        | apply eq_term_refl; apply wf_oInst; assumption
        | apply eq_term_refl; exact HiG
        | apply eq_term_sym; apply eq_El_subst;
          [ exact HwD'F | exact HwGF | exact HwLwg | apply wf_Rel
          | exact HwlG | exact HwB2 ]
        | apply eq_term_refl; apply wf_ExpSubst;
          [ exact HwD'F | exact HwGF | exact HwLwg | exact HiG | exact HwElB
          | exact Hwt1 ] ].
    - apply eq_sort_exp_ty; exact HS1C. }
  eapply eq_term_trans.
  { eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HS1C ].
    apply eq_exp_subst_cmp
      with (G1 := D')
           (G2 := oExtC D' rF2 lF2
                    (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
           (G3 := oExtC G2 rF2 lF2 F2)
           (f := oInst D' rF2 lF2
                   (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
           (g := oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
           (i := iEl oRel lG2)
           (A := oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2) (v := t1);
      [ exact HwD' | exact HwD'F | exact HwGF
      | apply wf_oInst; assumption
      | exact HwLwg | exact HiG | exact HwElB | exact Hwt1 ]. }
  eapply eq_term_conv;
    [ | apply eq_sort_exp_ty; exact HtyC ].
  apply ExpSubst_cong
    with (G1 := D') (G2 := D')
         (G1' := oExtC G2 rF2 lF2 F2) (G2' := oExtC G2 rF2 lF2 F2)
         (g1 := oCmp D'
                  (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                  (oExtC G2 rF2 lF2 F2)
                  (oInst D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
                  (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
         (g2 := oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                  (oCmp D' D G2 w g) a)
         (i1 := iEl oRel lG2) (i2 := iEl oRel lG2)
         (A1 := oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)
         (A2 := oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2)
         (v1 := t1) (v2 := t1);
    [ apply eq_term_refl; exact HwD'
    | apply eq_term_refl; exact HwGF
    | exact Hsnoc
    | apply eq_term_refl; exact HiG
    | apply eq_term_refl; exact HwElB
    | apply eq_term_refl; exact Hwt1 ].
Qed.
(* ================================================================== *)
(* 8.  The remaining relevant equations                                *)
(* ================================================================== *)

(* ---- "lam_rel subst" ---------------------------------------------- *)

(* Section 5's recipe once more; like [app_rel], [lam_rel]'s conclusion
   sort is already the substituted type, so nothing needs converting. *)
Lemma by_LamRel_subst G1 G2 G1' G2' g1 g2 rF1 rF2 lF1 lF2 lG1 lG2
                      F1 F2 B1 B2 t1 t2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rF1 rF2 -> Ceq_term sLvl lF1 lF2 ->
    Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2' rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2' rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sElt (oExtC G2' rF2 lF2 F2) oRel lG2 B2) t1 t2 ->
    eqt
      (sExp G2 (iEl oRel lG2)
         (oTySubst G2 G2' g2 (iEl oRel lG2)
            (oEl G2' oRel lG2 (oPiRel G2' rF2 lF2 lG2 F2 B2))))
      (oExpSubst G1 G1' g1 (iEl oRel lG1)
         (oEl G1' oRel lG1 (oPiRel G1' rF1 lF1 lG1 F1 B1))
         (oLamRel G1' rF1 lF1 lG1 F1 B1 t1))
      (oLamRel G2 rF2 lF2 lG2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode lG2) (oU (oExtC G2' rF2 lF2 F2) oRel lG2) B2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iEl oRel lG2) (oEl (oExtC G2' rF2 lF2 F2) oRel lG2 B2) t2)) ->
    Ceq_term
      (sExp G2 (iEl oRel lG2)
         (oTySubst G2 G2' g2 (iEl oRel lG2)
            (oEl G2' oRel lG2 (oPiRel G2' rF2 lF2 lG2 F2 B2))))
      (oExpSubst G1 G1' g1 (iEl oRel lG1)
         (oEl G1' oRel lG1 (oPiRel G1' rF1 lF1 lG1 F1 B1))
         (oLamRel G1' rF1 lF1 lG1 F1 B1 t1))
      (oLamRel G2 rF2 lF2 lG2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode lG2) (oU (oExtC G2' rF2 lF2 F2) oRel lG2) B2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iEl oRel lG2) (oEl (oExtC G2' rF2 lF2 F2) oRel lG2 B2) t2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf Hlg HFc HBc Htc Heq.
  pose proof (ceq_refl_r Hgc) as Hg2c.
  pose proof (ceq_refl_r (cong_LamRel HGc' Hr Hlf Hlg HFc HBc Htc)) as HLm2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  apply Ceq_exp_e in Htc as [Hta _].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft lG2 sLvl) as HwlG by (apply LvlNf_wf; exact Hlgnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft F2 (sCode G2' rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B2 (sCode (oExtC G2' rF2 lF2 F2) oRel lG2)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft t2 (sElt (oExtC G2' rF2 lF2 F2) oRel lG2 B2)) as Hwt2
      by (eapply eqt_wf_r; exact Hta).
  assert (wft (iEl oRel lG2) sInfo) as HiG
      by (unfold iEl; apply wf_Info; [ apply wf_Rel | apply wf_Iota; exact HwlG ]).
  eapply ceq_exp_eq_l; [ exact Heq | ].
  eapply ceq_refl_r.
  eapply ceq_exp_eq_r.
  - eapply ceq_exp_subst_l; [ exact Hg2c | exact HLm2 ].
  - apply eq_lam_rel_subst;
      [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact HwlF
      | exact HwlG | exact HwF2 | exact HwB2 | exact Hwt2 ].
Qed.

(* ---- "Pi_rel beta" ------------------------------------------------ *)

(* Observation (2) of the header: the left-hand side IS an [app_rel] of a
   [lam_rel], so [cong_AppRel] applied to [cong_LamRel] already has the
   right left term and the rule only has to move the right one. *)
Lemma by_PiRel_beta G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2 t1 t2 a1 a2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 -> Ceq_term sLvl lG1 lG2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    Ceq_term (sElt (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t1 t2 ->
    Ceq_term (sElt G2 rF2 lF2 F2) a1 a2 ->
    Ceq_term (sAppRelConcl G2 rF2 lF2 lG2 F2 B2 a2)
      (oAppRel G1 rF1 lF1 lG1 F1 B1 (oLamRel G1 rF1 lF1 lG1 F1 B1 t1) a1)
      (oExpSubst G2 (oExtC G2 rF2 lF2 F2) (oInst G2 rF2 lF2 F2 a2)
         (iEl oRel lG2) (oEl (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t2).
Proof.
  intros HGc Hr Hlf Hlg HFc HBc Htc Hac.
  eapply ceq_exp_eq_r;
    [ apply cong_AppRel;
      [ exact HGc | exact Hr | exact Hlf | exact Hlg | exact HFc | exact HBc
      | apply cong_LamRel;
        [ exact HGc | exact Hr | exact Hlf | exact Hlg | exact HFc | exact HBc
        | exact Htc ]
      | exact Hac ] | ].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_lvl_e in Hlg as [Hlgq Hlgnf]; subst lG1.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  apply Ceq_exp_e in Htc as [Hta _].
  apply Ceq_exp_e in Hac as [Haa _].
  apply eq_Pi_rel_beta;
    [ eapply eqt_wf_r; exact HG
    | apply RelNf_wf; exact Hrnf
    | apply LvlNf_wf; exact Hlfnf
    | apply LvlNf_wf; exact Hlgnf
    | eapply eqt_wf_r; exact HFa
    | eapply eqt_wf_r; exact HBa
    | eapply eqt_wf_r; exact Hta
    | eapply eqt_wf_r; exact Haa ].
Qed.

(* ================================================================== *)
(* 9.  The irrelevant binder fragment                                  *)
(* ================================================================== *)

(* [Pi_irr] differs from [Pi_rel] in exactly one way, paid for here rather
   than anywhere else.

   THE INFO SPELLING.  The former "Pi_irr" stores its codomain code at
   [rel (iota L1)] while "lam_irr"/"app_irr" -- and hence
   [LogRel.wkCodCodeIrr] and [nfcode_pi_irr] -- store it at [iCode L0].
   [LogRelCand.eq_expsubst_info] moves an [exp_subst] of an
   irrelevant-L0 code between the two, and [pi_irr_nf] below uses it
   twice: once on the [Pi_irr] itself and once on its codomain.

   [rty_pi_irr]'s candidate is otherwise the plain Kripke one, same as
   [rty_pi_rel]'s, so [cong_LamIrr] is the same shape as [cong_LamRel]. *)

(* ---- the normal [Pi_irr] code of an instance ---------------------- *)

(* The [Pi_irr] analogue of [pi_rel_nf], and it exports more: the
   [lam_irr]-specific step of reading the body's normal form back needs
   the reducible lift [h] and its equation with [oLift] as well. *)
Lemma pi_irr_nf G rF lF F1 F2 B1 B2 D g
  : RelNf rF -> LvlNf lF ->
    Ceq_term (sCode G rF lF) F1 F2 ->
    Ceq_term (sCode (oExtC G rF lF F2) oIrr oL0) B1 B2 ->
    EnvOk D -> RSubN D G g ->
    exists F0 B0 h,
      NfCode D rF lF F0
      /\ NfCode (oExtC D rF lF F0) oIrr oL0 B0
      /\ EnvOk (oExtC D rF lF F0)
      /\ RSubN (oExtC D rF lF F0) (oExtC G rF lF F2) h
      /\ eqt (sSub (oExtC D rF lF F0) (oExtC G rF lF F2))
             (oLift D G g rF lF F2) h
      /\ eqt (sCode D rF lF) (oExpSubst D G g (iCode lF) (oU G rF lF) F2) F0
      /\ eqt (sCode (oExtC D rF lF F0) oIrr oL0)
             (oExpSubst (oExtC D rF lF F0) (oExtC G rF lF F2) h (iCode oL0)
                (oU (oExtC G rF lF F2) oIrr oL0) B2) B0
      /\ eqt (sCode (oExtC D rF lF F0) oIrr oL0)
             (oExpSubst (oExtC D rF lF (oCodeSubst D G g rF lF F2))
                (oExtC G rF lF F2) (oLift D G g rF lF F2)
                (iCode oL0) (oU (oExtC G rF lF F2) oIrr oL0) B2) B0
      /\ eqt (sCode D oIrr oL0)
             (oExpSubst D G g (iCode oL0) (oU G oIrr oL0)
                (oPiIrr G rF lF F2 B2))
             (oPiIrr D rF lF F0 B0).
Proof.
  intros HrF HlF HFc HBc HD Hg.
  pose proof (ceq_clause_r HFc) as HFb2.
  pose proof (ceq_clause_r HBc) as HBb2.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  assert (wft rF sRelevance) as HrFw by (apply RelNf_wf; exact HrF).
  assert (wft lF sLvl) as HlFw by (apply LvlNf_wf; exact HlF).
  assert (wft F2 (sCode G rF lF)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact HwF2).
  assert (wft B2 (sCode (oExtC G rF lF F2) oIrr oL0)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft (iEl rF lF) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact HrFw | apply wf_Iota; exact HlFw ]).
  assert (wft (iCode oL0) sInfo) as HcG
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; apply wf_L0 ]).
  assert (wft (oExtC G rF lF F2) sEnv) as HwGF by (apply wf_ExtC; assumption).
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact Hg).
  destruct (binder_lift HrF HlF HwF2 HFb2 HD Hg)
    as [F0 [h (HF0 & HF0eq & HEok & HRS & HLeq)]].
  assert (wft (oExtC D rF lF F0) sEnv) as HwDF by (apply EnvOk_wf; exact HEok).
  assert (wft h (sSub (oExtC D rF lF F0) (oExtC G rF lF F2))) as Hwh
      by (apply RSubN_wf; exact HRS).
  destruct (ceq_code_nf relnf_irr lvlnf_L0 HEok HRS
              (HBb2 (oExtC D rF lF F0) h HEok HRS)) as [B0 [HB0 HB0eq]].
  assert (wft F0 (sCode D rF lF)) as HwF0 by (apply NfCode_wf; exact HF0).
  assert (wft B0 (sCode (oExtC D rF lF F0) oIrr oL0)) as HwB0
      by (apply NfCode_wf; exact HB0).
  assert (wft (oCodeSubst D G g rF lF F2) (sCode D rF lF)) as HwFg
      by (eapply eqt_wf_l; exact HF0eq).
  assert (wft (oExtC D rF lF (oCodeSubst D G g rF lF F2)) sEnv) as HwDFg
      by (apply wf_ExtC; assumption).
  assert (eqt sEnv (oExtC D rF lF (oCodeSubst D G g rF lF F2))
            (oExtC D rF lF F0)) as HEnvFg.
  { unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HDw
      | apply eq_term_refl; exact HiF
      | apply El_cong;
        [ apply eq_term_refl; exact HDw
        | apply eq_term_refl; exact HrFw
        | apply eq_term_refl; exact HlFw
        | exact HF0eq ] ]. }
  (* the [oLift] spelling of the codomain instance *)
  assert (eqt (sCode (oExtC D rF lF F0) oIrr oL0)
            (oExpSubst (oExtC D rF lF (oCodeSubst D G g rF lF F2))
               (oExtC G rF lF F2) (oLift D G g rF lF F2)
               (iCode oL0) (oU (oExtC G rF lF F2) oIrr oL0) B2)
            (oExpSubst (oExtC D rF lF F0) (oExtC G rF lF F2) h
               (iCode oL0) (oU (oExtC G rF lF F2) oIrr oL0) B2)) as HstepB.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := oExtC D rF lF (oCodeSubst D G g rF lF F2))
             (G2 := oExtC D rF lF F0)
             (G1' := oExtC G rF lF F2) (G2' := oExtC G rF lF F2)
             (g1 := oLift D G g rF lF F2) (g2 := h)
             (i1 := iCode oL0) (i2 := iCode oL0)
             (A1 := oU (oExtC G rF lF F2) oIrr oL0)
             (A2 := oU (oExtC G rF lF F2) oIrr oL0)
             (v1 := B2) (v2 := B2);
        [ exact HEnvFg
        | apply eq_term_refl; exact HwGF
        | exact HLeq
        | apply eq_term_refl; exact HcG
        | apply eq_term_refl; apply wf_U;
          [ exact HwGF | apply wf_Irr | apply wf_L0 ]
        | apply eq_term_refl; exact HwB2 ].
    - apply eq_sort_exp_ty; apply eq_U_subst;
          [ exact HwDF | exact HwGF | exact Hwh | apply wf_Irr
          | apply wf_L0 ]. }
  assert (eqt (sCode (oExtC D rF lF F0) oIrr oL0)
            (oExpSubst (oExtC D rF lF (oCodeSubst D G g rF lF F2))
               (oExtC G rF lF F2) (oLift D G g rF lF F2)
               (iCode oL0) (oU (oExtC G rF lF F2) oIrr oL0) B2) B0) as HB
      by (eapply eq_term_trans; [ exact HstepB | exact HB0eq ]).
  exists F0, B0, h; repeat split;
    [ exact HF0 | exact HB0 | exact HEok | exact HRS | exact HLeq
    | exact HF0eq | exact HB0eq | exact HB | ].
  (* ---- the [Pi_irr] code itself, across the two info spellings ---- *)
  eapply eq_term_trans.
  { apply eq_expsubst_info;
      [ exact HDw | exact HGw | exact Hgw
      | apply wft_U0irr_iota;
        [ exact HGw | apply wf_PiIrr;
          [ exact HGw | exact HrFw | exact HlFw | exact HwF2
          | apply wft_U0irr_next; [ exact HwGF | exact HwB2 ] ] ] ]. }
  eapply eq_term_conv;
    [ | apply eq_sort_sym; apply eq_sort_U_irr0; exact HDw ].
  eapply eq_term_trans.
  { apply eq_Pi_irr_subst;
      [ exact HDw | exact HGw | exact Hgw | exact HrFw | exact HlFw
      | exact HwF2
      | apply wft_U0irr_next; [ exact HwGF | exact HwB2 ] ]. }
  apply PiIrr_cong;
    [ apply eq_term_refl; exact HDw
    | apply eq_term_refl; exact HrFw
    | apply eq_term_refl; exact HlFw
    | exact HF0eq
    | ].
  (* the codomain, moved from [iota L1] to [iCode L0] and then to [B0] *)
  eapply eq_term_conv;
    [ | apply eq_sort_U_irr0; exact HwDF ].
  eapply eq_term_trans; [ | exact HB ].
  apply eq_term_sym.
  eapply eq_term_conv.
  - apply eq_expsubst_info;
      [ exact HwDFg | exact HwGF
      | apply wf_oLift; assumption
      | exact HwB2 ].
  - apply sExp_cong;
      [ exact HEnvFg | apply eq_term_refl; exact HcG
      | apply U_cong;
        [ exact HEnvFg | apply eq_term_refl; apply wf_Irr
        | apply eq_term_refl; apply wf_L0 ] ].
Qed.


(* ---- [app_irr] ---------------------------------------------------- *)

(* [cong_AppRel] transposed.  Only two things are not a transcription:
   [PiIrr_cong] wants its codomain equation at [rel (iota L1)] while
   everything else here is at [iCode L0], which [eq_sort_U_irr0] bridges;
   and [wf_PiIrr] concludes at [rel (iota L1)], which [wft_U0irr_iota]
   brings back. *)
Lemma cong_AppIrr G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2 f1 f2 a1 a2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0) B1 B2 ->
    Ceq_term (sElt G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2)) f1 f2 ->
    Ceq_term (sElt G2 rF2 lF2 F2) a1 a2 ->
    Ceq_term (sAppIrrConcl G2 rF2 lF2 F2 B2 a2)
      (oAppIrr G1 rF1 lF1 F1 B1 f1 a1) (oAppIrr G2 rF2 lF2 F2 B2 f2 a2).
Proof.
  intros HGc Hr Hlf HFc HBc Hfc Hac.
  pose proof HFc as HFc0. pose proof HBc as HBc0.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_exp_e in HFc as [HFa HFb].
  apply Ceq_exp_e in HBc as [HBa HBb].
  apply Ceq_exp_e in Hfc as [Hfa Hfb].
  apply Ceq_exp_e in Hac as [Haa Hab].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft F1 (sCode G2 rF2 lF2)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G2 rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B2 (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft f1 (sElt G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2))) as Hwf1
      by (eapply eqt_wf_l; exact Hfa).
  assert (wft a1 (sElt G2 rF2 lF2 F2)) as Hwa1 by (eapply eqt_wf_l; exact Haa).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (iEl oIrr oL0) sInfo) as HiG
      by (unfold iEl; apply wf_Info;
          [ apply wf_Irr | apply wf_Iota; apply wf_L0 ]).
  assert (wft (iCode lF2) sInfo) as HcF
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlF ]).
  assert (wft (iCode oL0) sInfo) as HcG
      by (unfold iCode; apply wf_Info;
          [ apply wf_Rel | apply wf_Next; apply wf_L0 ]).
  assert (wft (oExtC G2 rF2 lF2 F2) sEnv) as HwGF by (apply wf_ExtC; assumption).
  assert (wft (oEl G2 rF2 lF2 F2) (sTy G2 (iEl rF2 lF2))) as HwElF
      by (apply wf_El; assumption).
  assert (wft (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)
            (sTy (oExtC G2 rF2 lF2 F2) (iEl oIrr oL0))) as HwElB
      by (apply wf_El;
          [ exact HwGF | apply wf_Irr | apply wf_L0 | exact HwB2 ]).
  assert (wft (oPiIrr G2 rF2 lF2 F2 B2) (sCode G2 oIrr oL0)) as HwPi
      by (apply wft_U0irr_iota;
          [ exact HwG2
          | apply wf_PiIrr;
            [ exact HwG2 | exact Hwr | exact HwlF | exact HwF2
            | apply wft_U0irr_next; [ exact HwGF | exact HwB2 ] ] ]).
  apply ceq_exp.
  { apply AppIrr_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HFa | exact HBa | exact Hfa | exact Haa ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  destruct (pi_irr_nf Hrnf Hlfnf HFc0 HBc0 HD Hg)
    as [F0 [B0 [h (HF0 & HB0 & HEok & HRS & HLeq & HF0eq & HB0eq & HB & HPi)]]].
  assert (NfCode D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0)) as HnfPi
      by (apply nfcode_pi_irr; assumption).
  assert (wft F0 (sCode D rF2 lF2)) as HwF0 by (apply NfCode_wf; exact HF0).
  assert (wft (oExtC D rF2 lF2 F0) sEnv) as HwDF by (apply wf_ExtC; assumption).
  assert (wft B0 (sCode (oExtC D rF2 lF2 F0) oIrr oL0)) as HwB0
      by (apply NfCode_wf; exact HB0).
  pose (fg := oExpSubst D G2 g (iEl oIrr oL0)
                (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2)) f1).
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
          | apply eq_sort_exp_ty; exact HtyF ]).
  assert (wft ag (sElt D rF2 lF2 (wkCode D G2 g rF2 lF2 F2))) as Hwag''.
  { eapply wf_term_conv; [ exact Hwag | ].
    apply eq_sort_exp_ty; unfold wkCode; apply eq_El_subst; assumption. }
  assert (eqt (sTy D (iEl oIrr oL0))
            (oTySubst D G2 g (iEl oIrr oL0)
               (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2)))
            (oEl D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0))) as HtyPi.
  { eapply eq_term_trans;
      [ apply eq_El_subst;
        [ exact HwD | exact HwG2 | exact Hwg | apply wf_Irr | apply wf_L0
        | exact HwPi ] | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Irr
      | apply eq_term_refl; apply wf_L0
      | exact HPi ]. }
  assert (wft fg (sElt D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0))) as Hwfg.
  { eapply wf_term_conv;
      [ unfold fg; apply wf_ExpSubst;
        [ exact HwD | exact HwG2 | exact Hwg | exact HiG
        | apply wf_El;
          [ exact HwG2 | apply wf_Irr | apply wf_L0 | exact HwPi ]
        | exact Hwf1 ]
      | apply eq_sort_exp_ty; exact HtyPi ]. }
  destruct (RTyEx_of_NfCode HnfPi) as [P HP].
  assert (P fg) as HPf.
  { eapply RTmN_elim with
      (i0 := iEl oIrr oL0)
      (A0 := oEl D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0)) (P := P);
      [ apply Hfb; assumption
      | apply eq_term_refl; exact HiG
      | apply tyok_El; exact HnfPi
      | exact HtyPi
      | exact HP ]. }
  destruct (RTy_pi_irr_e HP)
    as [Pd [Pc (Hrn & Hlfn & HnF0 & HnB0 & Hdom & Hcod & Hiff)]].
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
  pose proof ((proj1 (Hiff fg) HPf) D (oId D) ag (wk_id HD) HD HPda)
    as Hres.
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
          | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwG2 | exact HiF | exact HwElF ] ] ]. }
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
  assert (eqt (sTy D (iEl oIrr oL0))
            (oTySubst D G2 g (iEl oIrr oL0)
               (oTySubst G2 (oExtC G2 rF2 lF2 F2) (oInst G2 rF2 lF2 F2 a1)
                  (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)))
            (oTySubst D (oExtC G2 rF2 lF2 F2)
               (oSnoc D G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) g ag)
               (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)))
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
  assert (eqt (sTy D (iEl oIrr oL0))
            (codAtIrr D D rF2 lF2 F0 B0 (oId D) ag)
            (oTySubst D (oExtC G2 rF2 lF2 F2)
               (oSnoc D G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) g ag)
               (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)))
    as Hhub2.
  { unfold codAtIrr, instAt.
    eapply eq_term_trans;
      [ | apply an_appConcl with (rG := oIrr) (lG := oL0) (G := G2) (w := g)
            (F := F2) (B := B2) (a := ag) (F' := F0) (B' := B0) (a' := ag);
          first [ assumption | apply wf_Irr | apply wf_L0
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
          | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwD | exact HiF | apply wf_El; assumption ] ] ]
      | apply eq_term_refl; exact HiG
      | apply eq_term_refl; apply wf_El;
        [ exact HwDF | apply wf_Irr | apply wf_L0 | exact HwB0 ] ]. }
  assert (eqt (sTy D (iEl oIrr oL0))
            (oTySubst D G2 g (iEl oIrr oL0)
               (oTySubst G2 (oExtC G2 rF2 lF2 F2) (oInst G2 rF2 lF2 F2 a2)
                  (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)))
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
            | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
                [ exact HwG2 | exact HiF | exact HwElF ] ] ]
        | apply eq_term_refl; exact HiG
        | apply eq_term_refl; exact HwElB ] ]. }
  eapply RTmN_intro with (i0 := iEl oIrr oL0) (A0 := C) (P := Pc D (oId D) ag);
    [ apply eq_term_refl; exact HiG | exact HTyC | exact HtyGoal | exact HRc | ].
  eapply (RTy_cand_eq HRc); [ exact Hres | ].
  assert (eqt (sTy D (iEl oIrr oL0))
            (oTySubst D (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (oInst D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2) ag)
               (iEl oIrr oL0)
               (oEl (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)) oIrr oL0
                  (oExpSubst
                     (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                     (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)))
            (oTySubst D (oExtC G2 rF2 lF2 F2)
               (oSnoc D G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2) g ag)
               (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)))
    as Hhub3.
  { apply ac_appConcl with (rG := oIrr) (lG := oL0) (a := ag);
      first [ assumption | apply wf_Irr | apply wf_L0 ]. }
  (* the [lift] of the identity is the identity *)
  assert (eqt (sCode (oExtC D rF2 lF2 F0) oIrr oL0)
            (wkCodCodeIrr D D (oId D) rF2 lF2 F0 B0) B0) as HidB.
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
    unfold wkCodCodeIrr, wkCode.
    eapply eq_term_trans.
    - eapply eq_term_conv.
      + apply ExpSubst_cong
          with (G1 := oExtC D rF2 lF2 (oCodeSubst D D (oId D) rF2 lF2 F0))
               (G2 := oExtC D rF2 lF2 F0)
               (G1' := oExtC D rF2 lF2 F0) (G2' := oExtC D rF2 lF2 F0)
               (g1 := oLift D D (oId D) rF2 lF2 F0)
               (g2 := oId (oExtC D rF2 lF2 F0))
               (i1 := iCode oL0) (i2 := iCode oL0)
               (A1 := oU (oExtC D rF2 lF2 F0) oIrr oL0)
               (A2 := oU (oExtC D rF2 lF2 F0) oIrr oL0)
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
            [ exact HwDF | apply wf_Irr | apply wf_L0 ]
          | apply eq_term_refl; exact HwB0 ].
      + apply eq_sort_exp_ty; apply eq_ty_subst_id;
            [ exact HwDF | exact HcG
            | apply wf_U; [ exact HwDF | apply wf_Irr | apply wf_L0 ] ].
    - apply eq_exp_subst_id;
        [ exact HwDF | exact HcG
        | apply wf_U; [ exact HwDF | apply wf_Irr | apply wf_L0 ]
        | exact HwB0 ]. }
  (* the [Pi_irr] at the substituted arguments *)
  assert (eqt sEnv (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
            (oExtC D rF2 lF2 F0)) as HEnvFg.
  { unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HiF
      | apply El_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | exact HF0eq ] ]. }
  assert (wft (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)) sEnv) as HwDFg
      by (eapply eqt_wf_l; exact HEnvFg).
  assert (eqt (sTy D (iEl oIrr oL0))
            (oEl D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0))
            (oEl D oIrr oL0
               (oPiIrr D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)
                  (oExpSubst
                     (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                     (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2))))
    as HElPiFg.
  { apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Irr
      | apply eq_term_refl; apply wf_L0
      | ].
    eapply eq_term_conv;
      [ | apply eq_sort_sym; apply eq_sort_U_irr0; exact HwD ].
    apply PiIrr_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | apply eq_term_sym; exact HF0eq
      | eapply eq_term_conv;
        [ apply eq_term_sym; exact HB
        | eapply eq_sort_trans;
          [ apply sExp_cong;
            [ apply eq_term_sym; exact HEnvFg
            | apply eq_term_refl; exact HcG
            | apply U_cong;
              [ apply eq_term_sym; exact HEnvFg
              | apply eq_term_refl; apply wf_Irr
              | apply eq_term_refl; apply wf_L0 ] ]
          | apply eq_sort_U_irr0; exact HwDFg ] ] ]. }
  (* the three-step equation *)
  eapply eq_term_conv.
  2:{ apply eq_sort_exp_ty.
      eapply eq_term_trans; [ apply eq_term_sym; exact Hhub2 | exact HeqC ]. }
  apply eq_term_sym.
  eapply eq_term_trans.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D) (G2 := D) (G1' := G2) (G2' := G2) (g1 := g) (g2 := g)
             (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
             (A1 := oTySubst G2 (oExtC G2 rF2 lF2 F2)
                      (oInst G2 rF2 lF2 F2 a2) (iEl oIrr oL0)
                      (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2))
             (A2 := oTySubst G2 (oExtC G2 rF2 lF2 F2)
                      (oInst G2 rF2 lF2 F2 a1) (iEl oIrr oL0)
                      (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2))
             (v1 := oAppIrr G1 rF2 lF2 F1 B1 f1 a1)
             (v2 := oAppIrr G2 rF2 lF2 F2 B2 f1 a1);
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
              | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
                  [ exact HwG2 | exact HiF | exact HwElF ] ] ]
          | apply eq_term_refl; exact HiG
          | apply eq_term_refl; exact HwElB ]
        | apply AppIrr_cong;
          [ exact HG
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | exact HFa | exact HBa
          | apply eq_term_refl; exact Hwf1
          | apply eq_term_refl; exact Hwa1 ] ].
    - apply eq_sort_exp_ty; exact Hhub1. }
  eapply eq_term_trans.
  { eapply eq_term_conv;
      [ apply eq_app_irr_subst;
        [ exact HwD | exact HwG2 | exact Hwg | exact Hwr | exact HwlF
        | exact HwF2 | exact HwB2 | exact Hwf1 | exact Hwa1 ]
      | apply eq_sort_exp_ty; exact Hhub1 ]. }
  eapply eq_term_conv.
  2:{ apply eq_sort_exp_ty; exact Hhub3. }
  apply eq_term_sym.
  unfold appAtIrr, wkFunIrr.
  apply AppIrr_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_refl; exact Hwr
    | apply eq_term_refl; exact HwlF
    | unfold wkCode; eapply eq_term_trans;
      [ apply eq_exp_subst_id;
        [ exact HwD | exact HcF | apply wf_U; assumption | exact HwF0 ]
      | apply eq_term_sym; exact HF0eq ]
    | eapply eq_term_conv;
      [ eapply eq_term_trans; [ exact HidB | apply eq_term_sym; exact HB ]
      | apply sExp_cong;
        [ apply eq_term_sym; exact HEnvFg
        | apply eq_term_refl; exact HcG
        | apply U_cong;
          [ apply eq_term_sym; exact HEnvFg
          | apply eq_term_refl; apply wf_Irr
          | apply eq_term_refl; apply wf_L0 ] ] ]
    | eapply eq_term_conv;
      [ apply eq_exp_subst_id;
        [ exact HwD | exact HiG
        | apply wf_El;
          [ exact HwD | apply wf_Irr | apply wf_L0
          | apply wft_U0irr_iota;
            [ exact HwD
            | apply wf_PiIrr;
              [ exact HwD | exact Hwr | exact HwlF | exact HwF0
              | apply wft_U0irr_next; [ exact HwDF | exact HwB0 ] ] ] ]
        | exact Hwfg ]
      | apply eq_sort_exp_ty; exact HElPiFg ]
    | apply eq_term_refl; exact Hwag'' ].
Qed.


(* ---- [lam_irr] ---------------------------------------------------- *)

Lemma cong_LamIrr G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2 t1 t2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0) B1 B2 ->
    Ceq_term (sElt (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t1 t2 ->
    Ceq_term (sElt G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2))
      (oLamIrr G1 rF1 lF1 F1 B1 t1) (oLamIrr G2 rF2 lF2 F2 B2 t2).
Proof.
  intros HGc Hr Hlf HFc HBc Htc.
  pose proof HFc as HFc0. pose proof HBc as HBc0.
  pose proof (ceq_clause_r HFc) as HFb2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_exp_e in HFc as [HFa HFb].
  apply Ceq_exp_e in HBc as [HBa HBb].
  apply Ceq_exp_e in Htc as [Hta Htb].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft oL0 sLvl) as HwlG by (apply wf_L0).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft F1 (sCode G2 rF2 lF2)) as HwF1 by (eapply eqt_wf_l; exact HFa).
  assert (wft F2 (sCode G2 rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B1 (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0)) as HwB1
      by (eapply eqt_wf_l; exact HBa).
  assert (wft B2 (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft t1 (sElt (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)) as Hwt1
      by (eapply eqt_wf_l; exact Hta).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (iEl oIrr oL0) sInfo) as HiG
      by (unfold iEl; apply wf_Info; [ apply wf_Irr | apply wf_Iota; apply wf_L0 ]).
  assert (wft (iCode lF2) sInfo) as HcF
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; exact HwlF ]).
  assert (wft (iCode oL0) sInfo) as HcG
      by (unfold iCode; apply wf_Info; [ apply wf_Rel | apply wf_Next; apply wf_L0 ]).
  assert (wft (oExtC G2 rF2 lF2 F2) sEnv) as HwGF by (apply wf_ExtC; assumption).
  assert (wft (oEl G2 rF2 lF2 F2) (sTy G2 (iEl rF2 lF2))) as HwElF
      by (apply wf_El; assumption).
  assert (wft (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)
            (sTy (oExtC G2 rF2 lF2 F2) (iEl oIrr oL0))) as HwElB
      by (apply wf_El; [ exact HwGF | apply wf_Irr | apply wf_L0 | exact HwB2 ]).
  assert (wft (oPiIrr G2 rF2 lF2 F2 B2) (sCode G2 oIrr oL0)) as HwPi
      by (apply wft_U0irr_iota;
          [ exact HwG2
          | apply wf_PiIrr;
            [ exact HwG2 | exact Hwr | exact HwlF | exact HwF2
            | apply wft_U0irr_next; [ exact HwGF | exact HwB2 ] ] ]).
  assert (wft (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2))
            (sTy G2 (iEl oIrr oL0))) as HwElPi
      by (apply wf_El; [ exact HwG2 | apply wf_Irr | apply wf_L0 | exact HwPi ]).
  apply ceq_exp.
  { apply LamIrr_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HFa | exact HBa | exact Hta ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  destruct (pi_irr_nf Hrnf Hlfnf HFc0 HBc0 HD Hg)
    as [F0 [B0 [h (HF0 & HB0 & HEok & HRS & HLeq & HF0eq & HB0eq & HB & HPi)]]].
  assert (NfCode D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0)) as HnfPi
      by (apply nfcode_pi_irr; assumption).
  assert (wft F0 (sCode D rF2 lF2)) as HwF0 by (apply NfCode_wf; exact HF0).
  assert (wft (oExtC D rF2 lF2 F0) sEnv) as HwDF by (apply wf_ExtC; assumption).
  assert (wft B0 (sCode (oExtC D rF2 lF2 F0) oIrr oL0)) as HwB0
      by (apply NfCode_wf; exact HB0).
  assert (eqt (sTy D (iEl rF2 lF2))
            (oTySubst D G2 g (iEl rF2 lF2) (oEl G2 rF2 lF2 F2))
            (oEl D rF2 lF2 F0)) as HtyF.
  { eapply eq_term_trans; [ apply eq_El_subst; assumption | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HF0eq ]. }
  assert (eqt (sTy D (iEl oIrr oL0))
            (oTySubst D G2 g (iEl oIrr oL0)
               (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2)))
            (oEl D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0))) as HtyPi.
  { eapply eq_term_trans;
      [ apply eq_El_subst;
        [ exact HwD | exact HwG2 | exact Hwg | apply wf_Irr | apply wf_L0
        | exact HwPi ] | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Irr
      | apply eq_term_refl; apply wf_L0
      | exact HPi ]. }
  destruct (RTyEx_of_NfCode HnfPi) as [P HP].
  eapply RTmN_intro with
    (i0 := iEl oIrr oL0)
    (A0 := oEl D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0)) (P := P);
    [ apply eq_term_refl; exact HiG
    | apply tyok_El; exact HnfPi
    | exact HtyPi
    | exact HP
    | ].
  destruct (RTy_pi_irr_e HP)
    as [Pd [Pc (Hrn & Hlfn & HnF0 & HnB0 & Hdom & Hcod & Hiff)]].
  assert (eqt sEnv (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
            (oExtC D rF2 lF2 F0)) as HEnvFg.
  { unfold oExtC; apply Ext_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HiF
      | apply El_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | exact HF0eq ] ]. }
  apply (proj2 (Hiff _)).
  intros D' w a HW HD' Hpd.
  assert (wft D' sEnv) as HwD' by (apply EnvOk_wf; exact HD').
  assert (wft w (sSub D' D)) as Hww by (apply Wk_wf; exact HW).
  destruct (Hcod D' w a HW HD' Hpd) as [C (HTyC & HeqC & HRc)].
  assert (wft a (sElt D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))) as Hawf.
  { eapply codAt_wf_a with (rG := oIrr) (lG := oL0) (B := B0);
      [ exact HwD' | exact HwD | exact Hwr | exact HwlF | exact Hww
      | exact HwF0 | eapply eqt_wf_l; exact HeqC ]. }
  (* ---- the composite substitution and its data ---- *)
  assert (RSubN D' G2 (oCmp D' D G2 w g)) as Hwgr
      by (eapply RSubN_wk; [ exact Hg | exact HW | exact HD' ]).
  assert (wft (oCmp D' D G2 w g) (sSub D' G2)) as Hwgw
      by (apply RSubN_wf; exact Hwgr).
  (* [w;g] applied to the domain code *)
  assert (eqt (sCode D' rF2 lF2)
            (wkCode D' D w rF2 lF2 F0)
            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) as HeqFw.
  { unfold wkCode.
    eapply eq_term_trans.
    2:{ eapply eq_term_conv;
          [ apply eq_exp_subst_cmp;
            [ exact HwD' | exact HwD | exact HwG2 | exact Hww | exact Hwg
            | exact HcF | apply wf_U; assumption | exact HwF2 ]
          | apply eq_sort_exp_ty;
            eapply eq_term_trans;
            [ apply TySubst_cong
                with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                     (g1 := w) (g2 := w) (i1 := iCode lF2) (i2 := iCode lF2)
                     (A1 := oTySubst D G2 g (iCode lF2) (oU G2 rF2 lF2))
                     (A2 := oU D rF2 lF2);
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact HwD
              | apply eq_term_refl; exact Hww
              | apply eq_term_refl; exact HcF
              | apply eq_U_subst; assumption ]
            | apply eq_U_subst; assumption ] ]. }
    apply eq_term_sym.
    eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D') (G2 := D') (G1' := D) (G2' := D) (g1 := w) (g2 := w)
             (i1 := iCode lF2) (i2 := iCode lF2)
             (A1 := oTySubst D G2 g (iCode lF2) (oU G2 rF2 lF2))
             (A2 := oU D rF2 lF2)
             (v1 := oExpSubst D G2 g (iCode lF2) (oU G2 rF2 lF2) F2)
             (v2 := F0);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hww
        | apply eq_term_refl; exact HcF
        | apply eq_U_subst; assumption
        | exact HF0eq ].
    - apply eq_sort_exp_ty; apply eq_U_subst; assumption. }
  assert (wft (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
            (sCode D' rF2 lF2)) as HwFw2
      by (eapply eqt_wf_r; exact HeqFw).
  assert (wft (oExtC D' rF2 lF2 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
            sEnv) as HwD'F by (apply wf_ExtC; assumption).
  assert (eqt (sTy D' (iEl rF2 lF2))
            (oTySubst D' G2 (oCmp D' D G2 w g) (iEl rF2 lF2)
               (oEl G2 rF2 lF2 F2))
            (oEl D' rF2 lF2 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
    as HtyFw
      by (apply eq_El_subst; assumption).
  assert (wft a (sElt D' rF2 lF2
                   (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))) as Hawf2.
  { eapply wf_term_conv; [ exact Hawf | ].
    apply eq_sort_exp_ty.
    apply El_cong;
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | exact HeqFw ]. }
  assert (wft a (sExp D' (iEl rF2 lF2)
                   (oTySubst D' G2 (oCmp D' D G2 w g) (iEl rF2 lF2)
                      (oEl G2 rF2 lF2 F2)))) as Hawf3
      by (eapply wf_term_conv;
          [ exact Hawf2
          | apply eq_sort_exp_ty; apply eq_term_sym; exact HtyFw ]).
  (* ---- the argument is reducible at the composite ---- *)
  destruct (Hdom D' w HW HD') as [F' (HnF' & HeqF' & HRd)].
  assert (RTmN D' (iEl rF2 lF2)
            (oTySubst D' G2 (oCmp D' D G2 w g) (iEl rF2 lF2)
               (oEl G2 rF2 lF2 F2)) a) as Harm.
  { eapply RTmN_intro with
      (i0 := iEl rF2 lF2) (A0 := oEl D' rF2 lF2 F') (P := Pd D' w);
      [ apply eq_term_refl; exact HiF
      | apply tyok_El; exact HnF'
      | eapply eq_term_trans; [ exact HtyFw | ]
      | exact HRd
      | exact Hpd ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | eapply eq_term_trans; [ apply eq_term_sym; exact HeqFw | exact HeqF' ] ]. }
  assert (RSubN D' (oExtC G2 rF2 lF2 F2)
            (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
               (oCmp D' D G2 w g) a)) as HRSs
      by (eapply binder_snoc;
          [ exact Hrnf | exact Hlfnf | exact HwF2 | exact HFb2
          | exact HD' | exact Hwgr | exact Hawf3 | exact Harm ]).
  (* ---- LIFTING COMPOSES: the codomain code the Kripke quantifier names
         is the one the substitution rules produce ---- *)
  assert (eqt (sSub (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)))
            (oLift D' D w rF2 lF2 F0)
            (oLiftW D' D w (iEl rF2 lF2)
               (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (oEl D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))) as Hliftmove.
  { rewrite oLift_oLiftW.
    apply eq_liftW_gen with (G1 := D) (A1 := oEl D rF2 lF2 F0);
      [ exact HwD' | exact HwD | exact HwD | exact HiF
      | apply wf_El; assumption
      | apply wf_El;
        [ exact HwD | exact Hwr | exact HwlF
        | eapply eqt_wf_l; exact HF0eq ]
      | apply wf_El;
        [ exact HwD' | exact Hwr | exact HwlF
        | eapply eqt_wf_l; exact HeqFw ]
      | apply wf_El; assumption
      | exact Hww
      | apply eq_term_refl; exact HwD
      | apply El_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_sym; exact HF0eq ]
      | apply eq_El_subst; assumption
      | eapply eq_term_trans;
        [ apply eq_El_subst;
          [ exact HwD' | exact HwD | exact Hww | exact Hwr | exact HwlF
          | eapply eqt_wf_l; exact HF0eq ]
        | apply El_cong;
          [ apply eq_term_refl; exact HwD'
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | eapply eq_term_trans;
            [ eapply eq_term_conv;
              [ apply ExpSubst_cong
                  with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                       (g1 := w) (g2 := w) (i1 := iCode lF2) (i2 := iCode lF2)
                       (A1 := oU D rF2 lF2) (A2 := oU D rF2 lF2)
                       (v1 := oCodeSubst D G2 g rF2 lF2 F2) (v2 := F0);
                [ apply eq_term_refl; exact HwD'
                | apply eq_term_refl; exact HwD
                | apply eq_term_refl; exact Hww
                | apply eq_term_refl; exact HcF
                | apply eq_term_refl; apply wf_U; assumption
                | exact HF0eq ]
              | apply eq_sort_exp_ty; apply eq_U_subst; assumption ]
            | exact HeqFw ] ] ] ]. }
  assert (eqt (sCode (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oIrr oL0)
            (oExpSubst (oExtC D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))
               (oExtC D rF2 lF2 F0) (oLift D' D w rF2 lF2 F0)
               (iCode oL0) (oU (oExtC D rF2 lF2 F0) oIrr oL0) B0)
            (oExpSubst
               (oExtC D' rF2 lF2 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2)
               (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
               (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)) as HeqBw.
  { assert (eqt sEnv (oExtC D rF2 lF2 F0)
              (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))) as HEnvD.
    { unfold oExtC; apply Ext_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HiF
        | apply El_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact HwlF
          | apply eq_term_sym; exact HF0eq ] ]. }
    assert (wft (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)) sEnv) as HwDFg
        by (eapply eqt_wf_r; exact HEnvD).
    assert (wft (oLiftW D' D w (iEl rF2 lF2)
                  (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                  (oEl D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
              (sSub (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2)))) as HwLW
        by (eapply eqt_wf_r; exact Hliftmove).
    assert (wft (oLift D G2 g rF2 lF2 F2)
              (sSub (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (oExtC G2 rF2 lF2 F2))) as HwLg
        by (apply wf_oLift; assumption).
    eapply eq_term_trans.
    { (* replace [B0] by its own reading, and move to the "g" envs *)
      eapply eq_term_conv.
      - apply ExpSubst_cong
          with (G1 := oExtC D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))
               (G2 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G1' := oExtC D rF2 lF2 F0)
               (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (g1 := oLift D' D w rF2 lF2 F0)
               (g2 := oLiftW D' D w (iEl rF2 lF2)
                        (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oEl D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (i1 := iCode oL0) (i2 := iCode oL0)
               (A1 := oU (oExtC D rF2 lF2 F0) oIrr oL0)
               (A2 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        oIrr oL0)
               (v1 := B0)
               (v2 := oExpSubst
                        (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2);
          [ unfold oExtC; apply Ext_cong;
            [ apply eq_term_refl; exact HwD'
            | apply eq_term_refl; exact HiF
            | apply El_cong;
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact Hwr
              | apply eq_term_refl; exact HwlF
              | exact HeqFw ] ]
          | exact HEnvD
          | exact Hliftmove
          | apply eq_term_refl; exact HcG
          | apply U_cong;
            [ exact HEnvD | apply eq_term_refl; apply wf_Irr
            | apply eq_term_refl; apply wf_L0 ]
          | eapply eq_term_conv;
            [ apply eq_term_sym; exact HB
            | apply sExp_cong;
              [ exact HEnvD | apply eq_term_refl; exact HcG
              | apply U_cong;
                [ exact HEnvD | apply eq_term_refl; apply wf_Irr
                | apply eq_term_refl; apply wf_L0 ] ] ] ].
      - apply eq_sort_exp_ty; apply eq_U_subst;
            [ exact HwD'F | exact HwDFg | exact HwLW
            | apply wf_Irr | apply wf_L0 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv.
      - apply ExpSubst_cong
          with (G1 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G2 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G1' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (g1 := oLiftW D' D w (iEl rF2 lF2)
                        (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oEl D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (g2 := oLiftW D' D w (iEl rF2 lF2)
                        (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oEl D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (i1 := iCode oL0) (i2 := iCode oL0)
               (A1 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        oIrr oL0)
               (A2 := oTySubst (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0))
               (v1 := oExpSubst
                        (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)
               (v2 := oExpSubst
                        (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                        (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                        (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2);
          [ apply eq_term_refl; exact HwD'F
          | apply eq_term_refl; exact HwDFg
          | apply eq_term_refl; exact HwLW
          | apply eq_term_refl; exact HcG
          | apply eq_term_sym; apply eq_U_subst;
            [ exact HwDFg | exact HwGF | exact HwLg | apply wf_Irr
            | apply wf_L0 ]
          | apply eq_term_refl; apply wf_ExpSubst;
            [ exact HwDFg | exact HwGF | exact HwLg | exact HcG
            | apply wf_U; [ exact HwGF | apply wf_Irr | apply wf_L0 ]
            | exact HwB2 ] ].
      - apply eq_sort_exp_ty.
        eapply eq_term_trans.
        + apply TySubst_cong
            with (G1 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G2 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G1' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (g1 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (g2 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (i1 := iCode oL0) (i2 := iCode oL0)
                 (A1 := oTySubst
                          (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                          (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0))
                 (A2 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          oIrr oL0);
            [ apply eq_term_refl; exact HwD'F
            | apply eq_term_refl; exact HwDFg
            | apply eq_term_refl; exact HwLW
            | apply eq_term_refl; exact HcG
            | apply eq_U_subst;
              [ exact HwDFg | exact HwGF | exact HwLg | apply wf_Irr
              | apply wf_L0 ] ].
        + apply eq_U_subst;
            [ exact HwD'F | exact HwDFg | exact HwLW | apply wf_Irr
            | apply wf_L0 ]. }
    eapply eq_term_trans.
    { eapply eq_term_conv.
      - apply eq_exp_subst_cmp
          with (G1 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G2 := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
               (G3 := oExtC G2 rF2 lF2 F2)
               (f := oLiftW D' D w (iEl rF2 lF2)
                       (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                       (oEl D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
               (g := oLift D G2 g rF2 lF2 F2) (i := iCode oL0)
               (A := oU (oExtC G2 rF2 lF2 F2) oIrr oL0) (v := B2);
          [ exact HwD'F | exact HwDFg | exact HwGF | exact HwLW | exact HwLg
          | exact HcG
          | apply wf_U; [ exact HwGF | apply wf_Irr | apply wf_L0 ]
          | exact HwB2 ].
      - apply eq_sort_exp_ty.
        eapply eq_term_trans.
        + apply TySubst_cong
            with (G1 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G2 := oExtC D' rF2 lF2
                          (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (G1' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (G2' := oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                 (g1 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (g2 := oLiftW D' D w (iEl rF2 lF2)
                          (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oEl D' rF2 lF2
                             (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                 (i1 := iCode oL0) (i2 := iCode oL0)
                 (A1 := oTySubst
                          (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          (oExtC G2 rF2 lF2 F2) (oLift D G2 g rF2 lF2 F2)
                          (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0))
                 (A2 := oU (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                          oIrr oL0);
            [ apply eq_term_refl; exact HwD'F
            | apply eq_term_refl; exact HwDFg
            | apply eq_term_refl; exact HwLW
            | apply eq_term_refl; exact HcG
            | apply eq_U_subst;
              [ exact HwDFg | exact HwGF | exact HwLg | apply wf_Irr
              | apply wf_L0 ] ].
        + apply eq_U_subst;
            [ exact HwD'F | exact HwDFg | exact HwLW | apply wf_Irr
            | apply wf_L0 ]. }
    eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := oExtC D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (G2 := oExtC D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (G1' := oExtC G2 rF2 lF2 F2) (G2' := oExtC G2 rF2 lF2 F2)
             (g1 := oCmp (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLiftW D' D w (iEl rF2 lF2)
                         (oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2))
                         (oEl D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)))
                      (oLift D G2 g rF2 lF2 F2))
             (g2 := oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (i1 := iCode oL0) (i2 := iCode oL0)
             (A1 := oU (oExtC G2 rF2 lF2 F2) oIrr oL0)
             (A2 := oU (oExtC G2 rF2 lF2 F2) oIrr oL0)
             (v1 := B2) (v2 := B2);
        [ apply eq_term_refl; exact HwD'F
        | apply eq_term_refl; exact HwGF
        | rewrite oLift_oLiftW;
          apply eq_liftW_cmp
            with (D := D) (A' := oEl D rF2 lF2 (oCodeSubst D G2 g rF2 lF2 F2));
          [ exact HwD' | exact HwD | exact HwG2 | exact HiF
          | apply wf_El; assumption
          | apply wf_El;
            [ exact HwD | exact Hwr | exact HwlF
            | eapply eqt_wf_l; exact HF0eq ]
          | apply wf_El;
            [ exact HwD' | exact Hwr | exact HwlF
            | eapply eqt_wf_r; exact HeqFw ]
          | exact Hwg | exact Hww | exact Hwgw
          | apply eq_El_subst; assumption
          | eapply eq_term_trans;
            [ apply eq_El_subst;
              [ exact HwD' | exact HwD | exact Hww | exact Hwr | exact HwlF
              | eapply eqt_wf_l; exact HF0eq ]
            | apply El_cong;
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact Hwr
              | apply eq_term_refl; exact HwlF
              | eapply eq_term_trans;
                [ eapply eq_term_conv;
                  [ apply ExpSubst_cong
                      with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                           (g1 := w) (g2 := w)
                           (i1 := iCode lF2) (i2 := iCode lF2)
                           (A1 := oU D rF2 lF2) (A2 := oU D rF2 lF2)
                           (v1 := oCodeSubst D G2 g rF2 lF2 F2) (v2 := F0);
                    [ apply eq_term_refl; exact HwD'
                    | apply eq_term_refl; exact HwD
                    | apply eq_term_refl; exact Hww
                    | apply eq_term_refl; exact HcF
                    | apply eq_term_refl; apply wf_U; assumption
                    | exact HF0eq ]
                  | apply eq_sort_exp_ty; apply eq_U_subst; assumption ]
                | exact HeqFw ] ] ]
          | apply eq_term_refl; exact Hwgw ]
        | apply eq_term_refl; exact HcG
        | apply eq_term_refl; apply wf_U;
          [ exact HwGF | apply wf_Irr | apply wf_L0 ]
        | apply eq_term_refl; exact HwB2 ].
    - apply eq_sort_exp_ty; apply eq_U_subst;
          [ exact HwD'F | exact HwGF
          | apply wf_oLift; assumption
          | apply wf_Irr | apply wf_L0 ]. }
  assert (wft (oExpSubst
                 (oExtC D' rF2 lF2
                    (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC G2 rF2 lF2 F2)
                 (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                 (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)
            (sCode (oExtC D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oIrr oL0))
    as HwBw2 by (eapply eqt_wf_r; exact HeqBw).
  assert (wft (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
            (sSub (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2))) as HwLwg
      by (apply wf_oLift; assumption).
  (* ---- the codomain type: three readings of one hub ---- *)
  assert (eqt (sTy D' (iEl oIrr oL0))
            (oTySubst D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (iEl oIrr oL0)
               (oEl (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oIrr oL0
                  (oExpSubst
                     (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2)
                     (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                     (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)))
            (oTySubst D' (oExtC G2 rF2 lF2 F2)
               (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                  (oCmp D' D G2 w g) a)
               (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)))
    as Hac.
  { apply ac_appConcl with (rG := oIrr) (a := a) (w := oCmp D' D G2 w g);
      first [ assumption | apply wf_Irr ]. }
  assert (eqt (sTy D' (iEl oIrr oL0))
            (oTySubst D' (oExtC G2 rF2 lF2 F2)
               (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                  (oCmp D' D G2 w g) a)
               (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)) C)
    as HtyC.
  { eapply eq_term_trans; [ apply eq_term_sym; exact Hac | ].
    eapply eq_term_trans; [ | exact HeqC ].
    apply an_appConcl with (rG := oIrr) (G := D) (w := w) (F := F0)
      (B := B0) (a := a)
      (F' := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
      (B' := oExpSubst
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2)
               (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
               (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)
      (a' := a);
      first [ assumption | apply wf_Irr | apply eq_term_refl; assumption ]. }
  assert (eqt (sTy D' (iEl oIrr oL0))
            (oTySubst D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (iEl oIrr oL0)
               (oEl (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oIrr oL0
                  (oExpSubst
                     (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2)
                     (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                     (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2))) C)
    as HtyAC by (eapply eq_term_trans; [ exact Hac | exact HtyC ]).
  (* ---- the [Pi_irr] code at the composite substitution, across the two
         info spellings ---- *)
  assert (eqt (sCode D' oIrr oL0)
            (oExpSubst D' G2 (oCmp D' D G2 w g) (iCode oL0) (oU G2 oIrr oL0)
               (oPiIrr G2 rF2 lF2 F2 B2))
            (oPiIrr D' rF2 lF2
               (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
               (oExpSubst
                  (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                  (oExtC G2 rF2 lF2 F2)
                  (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                  (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)))
    as HPiW.
  { eapply eq_term_trans.
    { apply eq_expsubst_info;
        [ exact HwD' | exact HwG2 | exact Hwgw | exact HwPi ]. }
    eapply eq_term_conv;
      [ | apply eq_sort_sym; apply eq_sort_U_irr0; exact HwD' ].
    eapply eq_term_trans.
    { apply eq_Pi_irr_subst;
        [ exact HwD' | exact HwG2 | exact Hwgw | exact Hwr | exact HwlF
        | exact HwF2
        | apply wft_U0irr_next; [ exact HwGF | exact HwB2 ] ]. }
    apply PiIrr_cong;
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact HwlF
      | apply eq_term_refl; exact HwFw2
      | eapply eq_term_conv;
        [ apply eq_term_sym; apply eq_expsubst_info;
          [ exact HwD'F | exact HwGF | exact HwLwg | exact HwB2 ]
        | apply eq_sort_U_irr0; exact HwD'F ] ]. }
  (* ---- the lambda's own type at the composite substitution ---- *)
  assert (eqt (sTy D' (iEl oIrr oL0))
            (oTySubst D' G2 (oCmp D' D G2 w g) (iEl oIrr oL0)
               (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2)))
            (oEl D' oIrr oL0
               (oPiIrr D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                  (oExpSubst
                     (oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                     (oExtC G2 rF2 lF2 F2)
                     (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                     (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2))))
    as HtyPiW.
  { eapply eq_term_trans;
      [ apply eq_El_subst;
        [ exact HwD' | exact HwG2 | exact Hwgw | apply wf_Irr | apply wf_L0
        | exact HwPi ] | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; apply wf_Irr
      | apply eq_term_refl; apply wf_L0
      | exact HPiW ]. }
  (* ---- the body, transported ---- *)
  assert (wft (oExpSubst
                 (oExtC D' rF2 lF2
                    (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                 (oExtC G2 rF2 lF2 F2)
                 (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                 (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t1)
            (sElt (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) oIrr oL0
               (oExpSubst
                  (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                  (oExtC G2 rF2 lF2 F2)
                  (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                  (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)))
    as Hwtw.
  { eapply wf_term_conv;
      [ apply wf_ExpSubst;
        [ exact HwD'F | exact HwGF | exact HwLwg | exact HiG | exact HwElB
        | exact Hwt1 ]
      | apply eq_sort_exp_ty;
        apply eq_El_subst;
        [ exact HwD'F | exact HwGF | exact HwLwg | apply wf_Irr | apply wf_L0
        | exact HwB2 ] ]. }
  (* ---- instantiate after lifting = instantiate at the composite ---- *)
  assert (eqt (sSub D' (oExtC G2 rF2 lF2 F2))
            (oCmp D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oExtC G2 rF2 lF2 F2)
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
            (oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
               (oCmp D' D G2 w g) a)) as Hsnoc.
  { eapply eq_term_trans.
    - unfold oInst, oExtC; rewrite oLift_oLiftW.
      apply eq_snoc_liftW with (D2 := D') (D := D') (G := G2)
        (w2 := oId D') (w := oCmp D' D G2 w g) (i := iEl rF2 lF2)
        (A := oEl G2 rF2 lF2 F2)
        (A' := oEl D' rF2 lF2
                 (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)) (a := a);
        [ exact HwD' | exact HwD' | exact HwG2 | exact HiF
        | exact HwElF
        | apply wf_El;
          [ exact HwD' | exact Hwr | exact HwlF | exact HwFw2 ]
        | exact Hwgw | apply wf_Id; exact HwD'
        | exact HtyFw
        | eapply wf_term_conv;
          [ exact Hawf2
          | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_id;
              [ exact HwD' | exact HiF
              | apply wf_El;
                [ exact HwD' | exact Hwr | exact HwlF | exact HwFw2 ] ] ] ].
    - apply Snoc_cong;
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact HiF
        | apply eq_term_refl; exact HwElF
        | apply eq_id_left; [ exact HwD' | exact HwG2 | exact Hwgw ]
        | apply eq_term_refl; exact Hawf3 ]. }
  (* ================================================================ *)
  (* the Kripke obligation                                            *)
  (* ================================================================ *)
  eapply (RTy_cand_eq HRc).
  { eapply RTmN_elim with (i0 := iEl oIrr oL0) (A0 := C) (P := Pc D' w a);
      [ apply Htb; [ exact HD' | exact HRSs ]
      | apply eq_term_refl; exact HiG
      | exact HTyC
      | exact HtyC
      | exact HRc ]. }
  apply eq_term_sym.
  (* [app_irr] of the weakened lambda, reduced *)
  eapply eq_term_trans.
  { eapply eq_term_conv.
    - unfold appAtIrr, wkFunIrr.
      apply AppIrr_cong
        with (G1 := D') (G2 := D') (rF1 := rF2) (rF2 := rF2)
             (lF1 := lF2) (lF2 := lF2)
             (F1 := wkCode D' D w rF2 lF2 F0)
             (F2 := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (B1 := oExpSubst (oExtC D' rF2 lF2 (wkCode D' D w rF2 lF2 F0))
                      (oExtC D rF2 lF2 F0) (oLift D' D w rF2 lF2 F0)
                      (iCode oL0) (oU (oExtC D rF2 lF2 F0) oIrr oL0) B0)
             (B2 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)
             (f1 := oExpSubst D' D w (iEl oIrr oL0)
                      (oEl D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0))
                      (oExpSubst D G2 g (iEl oIrr oL0)
                         (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2))
                         (oLamIrr G1 rF2 lF2 F1 B1 t1)))
             (f2 := oExpSubst D' G2 (oCmp D' D G2 w g) (iEl oIrr oL0)
                      (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2))
                      (oLamIrr G2 rF2 lF2 F2 B2 t1))
             (a1 := a) (a2 := a);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | exact HeqFw
        | exact HeqBw
        | (* the function *)
          eapply eq_term_conv;
          [ eapply eq_term_trans;
            [ apply ExpSubst_cong
                with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                     (g1 := w) (g2 := w)
                     (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
                     (A1 := oEl D oIrr oL0 (oPiIrr D rF2 lF2 F0 B0))
                     (A2 := oTySubst D G2 g (iEl oIrr oL0)
                              (oEl G2 oIrr oL0
                                 (oPiIrr G2 rF2 lF2 F2 B2)))
                     (v1 := oExpSubst D G2 g (iEl oIrr oL0)
                              (oEl G2 oIrr oL0
                                 (oPiIrr G2 rF2 lF2 F2 B2))
                              (oLamIrr G1 rF2 lF2 F1 B1 t1))
                     (v2 := oExpSubst D G2 g (iEl oIrr oL0)
                              (oEl G2 oIrr oL0
                                 (oPiIrr G2 rF2 lF2 F2 B2))
                              (oLamIrr G1 rF2 lF2 F1 B1 t1));
              [ apply eq_term_refl; exact HwD'
              | apply eq_term_refl; exact HwD
              | apply eq_term_refl; exact Hww
              | apply eq_term_refl; exact HiG
              | apply eq_term_sym; exact HtyPi
              | apply eq_term_refl; apply wf_ExpSubst;
                [ exact HwD | exact HwG2 | exact Hwg | exact HiG
                | exact HwElPi
                | eapply eqt_wf_l; apply LamIrr_cong;
                  [ exact HG
                  | apply eq_term_refl; exact Hwr
                  | apply eq_term_refl; exact HwlF
                  | exact HFa | exact HBa | exact Hta ] ] ]
            | eapply eq_term_trans;
              [ apply eq_exp_subst_cmp;
                [ exact HwD' | exact HwD | exact HwG2 | exact Hww | exact Hwg
                | exact HiG | exact HwElPi
                | eapply eqt_wf_l; apply LamIrr_cong;
                  [ exact HG
                  | apply eq_term_refl; exact Hwr
                  | apply eq_term_refl; exact HwlF
                  | exact HFa | exact HBa | exact Hta ] ]
              | eapply eq_term_conv;
                [ apply ExpSubst_cong
                    with (G1 := D') (G2 := D') (G1' := G2) (G2' := G2)
                         (g1 := oCmp D' D G2 w g) (g2 := oCmp D' D G2 w g)
                         (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
                         (A1 := oEl G2 oIrr oL0
                                  (oPiIrr G2 rF2 lF2 F2 B2))
                         (A2 := oEl G2 oIrr oL0
                                  (oPiIrr G2 rF2 lF2 F2 B2))
                         (v1 := oLamIrr G1 rF2 lF2 F1 B1 t1)
                         (v2 := oLamIrr G2 rF2 lF2 F2 B2 t1);
                  [ apply eq_term_refl; exact HwD'
                  | apply eq_term_refl; exact HwG2
                  | apply eq_term_refl; exact Hwgw
                  | apply eq_term_refl; exact HiG
                  | apply eq_term_refl; exact HwElPi
                  | apply LamIrr_cong;
                    [ exact HG
                    | apply eq_term_refl; exact Hwr
                    | apply eq_term_refl; exact HwlF
                    | exact HFa | exact HBa
                    | apply eq_term_refl; exact Hwt1 ] ]
                | apply eq_sort_exp_ty; apply eq_term_sym; apply eq_ty_subst_cmp;
                    [ exact HwD' | exact HwD | exact HwG2 | exact Hww
                    | exact Hwg | exact HiG | exact HwElPi ] ] ] ]
          | apply eq_sort_exp_ty; eapply eq_term_trans;
              [ apply eq_ty_subst_cmp;
                [ exact HwD' | exact HwD | exact HwG2 | exact Hww | exact Hwg
                | exact HiG | exact HwElPi ]
              | exact HtyPiW ] ]
        | apply eq_term_refl; exact Hawf2 ].
    - apply eq_sort_exp_ty; exact HtyAC. }
  eapply eq_term_trans.
  { eapply eq_term_conv.
    - apply AppIrr_cong
        with (G1 := D') (G2 := D') (rF1 := rF2) (rF2 := rF2)
             (lF1 := lF2) (lF2 := lF2)
             (F1 := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (F2 := wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
             (B1 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)
             (B2 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)
             (f1 := oExpSubst D' G2 (oCmp D' D G2 w g) (iEl oIrr oL0)
                      (oEl G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2))
                      (oLamIrr G2 rF2 lF2 F2 B2 t1))
             (f2 := oLamIrr D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (oExpSubst
                         (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                         (oExtC G2 rF2 lF2 F2)
                         (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                         (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2)
                      (oExpSubst
                         (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                         (oExtC G2 rF2 lF2 F2)
                         (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                         (iEl oIrr oL0)
                         (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t1))
             (a1 := a) (a2 := a);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact HwlF
        | apply eq_term_refl; exact HwFw2
        | apply eq_term_refl; exact HwBw2
        | eapply eq_term_conv;
          [ apply eq_lam_irr_subst;
            [ exact HwD' | exact HwG2 | exact Hwgw | exact Hwr | exact HwlF
            | exact HwF2 | exact HwB2 | exact Hwt1 ]
          | apply eq_sort_exp_ty; exact HtyPiW ]
        | apply eq_term_refl; exact Hawf2 ].
    - apply eq_sort_exp_ty; exact HtyAC. }
  eapply eq_term_trans.
  { eapply eq_term_conv;
      [ apply eq_Pi_irr_beta;
        [ exact HwD' | exact Hwr | exact HwlF | exact HwFw2
        | apply wft_U0irr_next; [ exact HwD'F | exact HwBw2 ]
        | exact Hwtw | exact Hawf2 ]
      | apply eq_sort_exp_ty; exact HtyAC ]. }
  (* and the beta-reduct is the body's own instance *)
  assert (eqt (sTy D' (iEl oIrr oL0))
            (oTySubst D'
               (oExtC D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (oInst D' rF2 lF2
                  (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (iEl oIrr oL0)
               (oTySubst
                  (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                  (oExtC G2 rF2 lF2 F2)
                  (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                  (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)))
            C) as HS1C.
  { eapply eq_term_trans;
      [ apply eq_ty_subst_cmp
          with (G1 := D')
               (G2 := oExtC D' rF2 lF2
                        (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
               (G3 := oExtC G2 rF2 lF2 F2)
               (f := oInst D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
               (g := oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
               (i := iEl oIrr oL0)
               (A := oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2);
        [ exact HwD' | exact HwD'F | exact HwGF
        | apply wf_oInst; assumption
        | exact HwLwg | exact HiG | exact HwElB ] | ].
    eapply eq_term_trans; [ | exact HtyC ].
    apply TySubst_cong
      with (G1 := D') (G2 := D')
           (G1' := oExtC G2 rF2 lF2 F2) (G2' := oExtC G2 rF2 lF2 F2)
           (g1 := oCmp D'
                    (oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                    (oExtC G2 rF2 lF2 F2)
                    (oInst D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
                    (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
           (g2 := oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                    (oCmp D' D G2 w g) a)
           (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
           (A1 := oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)
           (A2 := oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2);
      [ apply eq_term_refl; exact HwD'
      | apply eq_term_refl; exact HwGF
      | exact Hsnoc
      | apply eq_term_refl; exact HiG
      | apply eq_term_refl; exact HwElB ]. }
  eapply eq_term_trans.
  { eapply eq_term_conv.
    - apply ExpSubst_cong
        with (G1 := D') (G2 := D')
             (G1' := oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (G2' := oExtC D' rF2 lF2
                       (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
             (g1 := oInst D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
             (g2 := oInst D' rF2 lF2
                      (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
             (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
             (A1 := oEl (oExtC D' rF2 lF2
                           (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      oIrr oL0
                      (oExpSubst
                         (oExtC D' rF2 lF2
                            (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                         (oExtC G2 rF2 lF2 F2)
                         (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                         (iCode oL0) (oU (oExtC G2 rF2 lF2 F2) oIrr oL0) B2))
             (A2 := oTySubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iEl oIrr oL0)
                      (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2))
             (v1 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iEl oIrr oL0)
                      (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t1)
             (v2 := oExpSubst
                      (oExtC D' rF2 lF2
                         (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                      (oExtC G2 rF2 lF2 F2)
                      (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
                      (iEl oIrr oL0)
                      (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t1);
        [ apply eq_term_refl; exact HwD'
        | apply eq_term_refl; exact HwD'F
        | apply eq_term_refl; apply wf_oInst; assumption
        | apply eq_term_refl; exact HiG
        | apply eq_term_sym; apply eq_El_subst;
          [ exact HwD'F | exact HwGF | exact HwLwg | apply wf_Irr
          | apply wf_L0 | exact HwB2 ]
        | apply eq_term_refl; apply wf_ExpSubst;
          [ exact HwD'F | exact HwGF | exact HwLwg | exact HiG | exact HwElB
          | exact Hwt1 ] ].
    - apply eq_sort_exp_ty; exact HS1C. }
  eapply eq_term_trans.
  { eapply eq_term_conv;
      [ | apply eq_sort_exp_ty; exact HS1C ].
    apply eq_exp_subst_cmp
      with (G1 := D')
           (G2 := oExtC D' rF2 lF2
                    (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
           (G3 := oExtC G2 rF2 lF2 F2)
           (f := oInst D' rF2 lF2
                   (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
           (g := oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2)
           (i := iEl oIrr oL0)
           (A := oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) (v := t1);
      [ exact HwD' | exact HwD'F | exact HwGF
      | apply wf_oInst; assumption
      | exact HwLwg | exact HiG | exact HwElB | exact Hwt1 ]. }
  eapply eq_term_conv;
    [ | apply eq_sort_exp_ty; exact HtyC ].
  apply ExpSubst_cong
    with (G1 := D') (G2 := D')
         (G1' := oExtC G2 rF2 lF2 F2) (G2' := oExtC G2 rF2 lF2 F2)
         (g1 := oCmp D'
                  (oExtC D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
                  (oExtC G2 rF2 lF2 F2)
                  (oInst D' rF2 lF2
                     (wkCode D' G2 (oCmp D' D G2 w g) rF2 lF2 F2) a)
                  (oLift D' G2 (oCmp D' D G2 w g) rF2 lF2 F2))
         (g2 := oSnoc D' G2 (iEl rF2 lF2) (oEl G2 rF2 lF2 F2)
                  (oCmp D' D G2 w g) a)
         (i1 := iEl oIrr oL0) (i2 := iEl oIrr oL0)
         (A1 := oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)
         (A2 := oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2)
         (v1 := t1) (v2 := t1);
    [ apply eq_term_refl; exact HwD'
    | apply eq_term_refl; exact HwGF
    | exact Hsnoc
    | apply eq_term_refl; exact HiG
    | apply eq_term_refl; exact HwElB
    | apply eq_term_refl; exact Hwt1 ].
Qed.

(* ---- the three irrelevant equations ------------------------------- *)

Lemma by_LamIrr_subst G1 G2 G1' G2' g1 g2 rF1 rF2 lF1 lF2 F1 F2 B1 B2 t1 t2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rF1 rF2 -> Ceq_term sLvl lF1 lF2 ->
    Ceq_term (sCode G2' rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2' rF2 lF2 F2) oIrr oL0) B1 B2 ->
    Ceq_term (sElt (oExtC G2' rF2 lF2 F2) oIrr oL0 B2) t1 t2 ->
    eqt
      (sExp G2 (iEl oIrr oL0)
         (oTySubst G2 G2' g2 (iEl oIrr oL0)
            (oEl G2' oIrr oL0 (oPiIrr G2' rF2 lF2 F2 B2))))
      (oExpSubst G1 G1' g1 (iEl oIrr oL0)
         (oEl G1' oIrr oL0 (oPiIrr G1' rF1 lF1 F1 B1))
         (oLamIrr G1' rF1 lF1 F1 B1 t1))
      (oLamIrr G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode oL0) (oU (oExtC G2' rF2 lF2 F2) oIrr oL0) B2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iEl oIrr oL0) (oEl (oExtC G2' rF2 lF2 F2) oIrr oL0 B2) t2)) ->
    Ceq_term
      (sExp G2 (iEl oIrr oL0)
         (oTySubst G2 G2' g2 (iEl oIrr oL0)
            (oEl G2' oIrr oL0 (oPiIrr G2' rF2 lF2 F2 B2))))
      (oExpSubst G1 G1' g1 (iEl oIrr oL0)
         (oEl G1' oIrr oL0 (oPiIrr G1' rF1 lF1 F1 B1))
         (oLamIrr G1' rF1 lF1 F1 B1 t1))
      (oLamIrr G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode oL0) (oU (oExtC G2' rF2 lF2 F2) oIrr oL0) B2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iEl oIrr oL0) (oEl (oExtC G2' rF2 lF2 F2) oIrr oL0 B2) t2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf HFc HBc Htc Heq.
  pose proof (ceq_refl_r Hgc) as Hg2c.
  pose proof (ceq_refl_r (cong_LamIrr HGc' Hr Hlf HFc HBc Htc)) as HLm2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  apply Ceq_exp_e in Htc as [Hta _].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft F2 (sCode G2' rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B2 (sCode (oExtC G2' rF2 lF2 F2) oIrr oL0)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft t2 (sElt (oExtC G2' rF2 lF2 F2) oIrr oL0 B2)) as Hwt2
      by (eapply eqt_wf_r; exact Hta).
  assert (wft (iEl oIrr oL0) sInfo) as HiG
      by (unfold iEl; apply wf_Info;
          [ apply wf_Irr | apply wf_Iota; apply wf_L0 ]).
  assert (wft (oExtC G2' rF2 lF2 F2) sEnv) as HwGF
      by (apply wf_ExtC; assumption).
  eapply ceq_exp_eq_l; [ exact Heq | ].
  eapply ceq_refl_r.
  eapply ceq_exp_eq_r.
  - eapply ceq_exp_subst_l; [ exact Hg2c | exact HLm2 ].
  - apply eq_lam_irr_subst;
      [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact HwlF
      | exact HwF2 | exact HwB2 | exact Hwt2 ].
Qed.

Lemma by_AppIrr_subst G1 G2 G1' G2' g1 g2 rF1 rF2 lF1 lF2
                      F1 F2 B1 B2 f1 f2 a1 a2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance rF1 rF2 -> Ceq_term sLvl lF1 lF2 ->
    Ceq_term (sCode G2' rF2 lF2) F1 F2 ->
    Ceq_term (sCode (oExtC G2' rF2 lF2 F2) oIrr oL0) B1 B2 ->
    Ceq_term (sElt G2' oIrr oL0 (oPiIrr G2' rF2 lF2 F2 B2)) f1 f2 ->
    Ceq_term (sElt G2' rF2 lF2 F2) a1 a2 ->
    eqt
      (sExp G2 (iEl oIrr oL0)
         (oTySubst G2 G2' g2 (iEl oIrr oL0)
            (oTySubst G2' (oExtC G2' rF2 lF2 F2) (oInst G2' rF2 lF2 F2 a2)
               (iEl oIrr oL0) (oEl (oExtC G2' rF2 lF2 F2) oIrr oL0 B2))))
      (oExpSubst G1 G1' g1 (iEl oIrr oL0)
         (oTySubst G1' (oExtC G1' rF1 lF1 F1) (oInst G1' rF1 lF1 F1 a1)
            (iEl oIrr oL0) (oEl (oExtC G1' rF1 lF1 F1) oIrr oL0 B1))
         (oAppIrr G1' rF1 lF1 F1 B1 f1 a1))
      (oAppIrr G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode oL0) (oU (oExtC G2' rF2 lF2 F2) oIrr oL0) B2)
         (oExpSubst G2 G2' g2 (iEl oIrr oL0)
            (oEl G2' oIrr oL0 (oPiIrr G2' rF2 lF2 F2 B2)) f2)
         (oExpSubst G2 G2' g2 (iEl rF2 lF2) (oEl G2' rF2 lF2 F2) a2)) ->
    Ceq_term
      (sExp G2 (iEl oIrr oL0)
         (oTySubst G2 G2' g2 (iEl oIrr oL0)
            (oTySubst G2' (oExtC G2' rF2 lF2 F2) (oInst G2' rF2 lF2 F2 a2)
               (iEl oIrr oL0) (oEl (oExtC G2' rF2 lF2 F2) oIrr oL0 B2))))
      (oExpSubst G1 G1' g1 (iEl oIrr oL0)
         (oTySubst G1' (oExtC G1' rF1 lF1 F1) (oInst G1' rF1 lF1 F1 a1)
            (iEl oIrr oL0) (oEl (oExtC G1' rF1 lF1 F1) oIrr oL0 B1))
         (oAppIrr G1' rF1 lF1 F1 B1 f1 a1))
      (oAppIrr G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2)
         (oExpSubst (oExtC G2 rF2 lF2 (oCodeSubst G2 G2' g2 rF2 lF2 F2))
            (oExtC G2' rF2 lF2 F2) (oLift G2 G2' g2 rF2 lF2 F2)
            (iCode oL0) (oU (oExtC G2' rF2 lF2 F2) oIrr oL0) B2)
         (oExpSubst G2 G2' g2 (iEl oIrr oL0)
            (oEl G2' oIrr oL0 (oPiIrr G2' rF2 lF2 F2 B2)) f2)
         (oExpSubst G2 G2' g2 (iEl rF2 lF2) (oEl G2' rF2 lF2 F2) a2)).
Proof.
  intros HGc HGc' Hgc Hr Hlf HFc HBc Hfc Hac Heq.
  pose proof (ceq_refl_r Hgc) as Hg2c.
  pose proof (ceq_refl_r (cong_AppIrr HGc' Hr Hlf HFc HBc Hfc Hac)) as HAp2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst rF1.
  apply Ceq_lvl_e in Hlf as [Hlfq Hlfnf]; subst lF1.
  apply Ceq_exp_e in HFc as [HFa _].
  apply Ceq_exp_e in HBc as [HBa _].
  apply Ceq_exp_e in Hfc as [Hfa _].
  apply Ceq_exp_e in Hac as [Haa _].
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft F2 (sCode G2' rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa).
  assert (wft B2 (sCode (oExtC G2' rF2 lF2 F2) oIrr oL0)) as HwB2
      by (eapply eqt_wf_r; exact HBa).
  assert (wft f2 (sElt G2' oIrr oL0 (oPiIrr G2' rF2 lF2 F2 B2))) as Hwf2
      by (eapply eqt_wf_r; exact Hfa).
  assert (wft a2 (sElt G2' rF2 lF2 F2)) as Hwa2 by (eapply eqt_wf_r; exact Haa).
  assert (wft (iEl rF2 lF2) sInfo) as HiF
      by (unfold iEl; apply wf_Info; [ exact Hwr | apply wf_Iota; exact HwlF ]).
  assert (wft (iEl oIrr oL0) sInfo) as HiG
      by (unfold iEl; apply wf_Info;
          [ apply wf_Irr | apply wf_Iota; apply wf_L0 ]).
  assert (wft (oExtC G2' rF2 lF2 F2) sEnv) as HwGF
      by (apply wf_ExtC; assumption).
  assert (wft (oEl G2' rF2 lF2 F2) (sTy G2' (iEl rF2 lF2))) as HwElF
      by (apply wf_El; assumption).
  eapply ceq_exp_eq_l; [ exact Heq | ].
  eapply ceq_refl_r.
  eapply ceq_exp_eq_r.
  - eapply ceq_exp_subst_l; [ exact Hg2c | exact HAp2 ].
  - apply eq_app_irr_subst;
      [ exact HwG2 | exact HwG2' | exact Hwg2 | exact Hwr | exact HwlF
      | exact HwF2 | exact HwB2 | exact Hwf2 | exact Hwa2 ].
Qed.

(* "Pi_irr beta" is [cong_AppIrr] of [cong_LamIrr], exactly as "Pi_rel
   beta" was -- except that the rule states its codomain code at
   [rel (iota L1)] whereas both congruences want [iCode L0], so the
   codomain argument's clause is moved across by [ceq_exp_transfer]
   first. *)
Lemma by_PiIrr_beta G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2 t1 t2 a1 a2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance rF1 rF2 ->
    Ceq_term sLvl lF1 lF2 ->
    Ceq_term (sCode G2 rF2 lF2) F1 F2 ->
    Ceq_term (sExp (oExtC G2 rF2 lF2 F2) (oInfo oRel (oIota oL1))
                (oU (oExtC G2 rF2 lF2 F2) oIrr oL0)) B1 B2 ->
    Ceq_term (sElt (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t1 t2 ->
    Ceq_term (sElt G2 rF2 lF2 F2) a1 a2 ->
    Ceq_term (sAppIrrConcl G2 rF2 lF2 F2 B2 a2)
      (oAppIrr G1 rF1 lF1 F1 B1 (oLamIrr G1 rF1 lF1 F1 B1 t1) a1)
      (oExpSubst G2 (oExtC G2 rF2 lF2 F2) (oInst G2 rF2 lF2 F2 a2)
         (iEl oIrr oL0) (oEl (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t2).
Proof.
  intros HGc Hr Hlf HFc HBc Htc Hac.
  pose proof HFc as HFc0.
  apply Ceq_exp_e in HFc0 as [HFa0 _].
  assert (wft F2 (sCode G2 rF2 lF2)) as HwF2 by (eapply eqt_wf_r; exact HFa0).
  assert (wft G2 sEnv) as HwG2 by (eapply wft_exp_env; exact HwF2).
  destruct (Ceq_relevance_e Hr) as [Hrq Hrnf]; subst rF1.
  destruct (Ceq_lvl_e Hlf) as [Hlfq Hlfnf]; subst lF1.
  assert (wft rF2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft lF2 sLvl) as HwlF by (apply LvlNf_wf; exact Hlfnf).
  assert (wft (oExtC G2 rF2 lF2 F2) sEnv) as HwGF
      by (apply wf_ExtC; assumption).
  (* the codomain clause, moved from [rel (iota L1)] to [iCode L0] *)
  assert (Ceq_term (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0) B1 B2) as HBc'.
  { eapply ceq_exp_transfer;
      [ apply eq_term_refl; exact HwGF
      | apply eq_term_sym; apply eq_info_next0
      | apply eq_term_refl; apply wf_U;
        [ exact HwGF | apply wf_Irr | apply wf_L0 ]
      | exact HBc ]. }
  eapply ceq_exp_eq_r;
    [ apply cong_AppIrr;
      [ exact HGc | exact Hr | exact Hlf | exact HFc | exact HBc'
      | apply cong_LamIrr;
        [ exact HGc | exact Hr | exact Hlf | exact HFc | exact HBc' | exact Htc ]
      | exact Hac ] | ].
  apply Ceq_exp_e in HBc as [HBa _].
  apply Ceq_exp_e in Htc as [Hta _].
  apply Ceq_exp_e in Hac as [Haa _].
  apply eq_Pi_irr_beta;
    [ exact HwG2 | exact Hwr | exact HwlF | exact HwF2
    | eapply eqt_wf_r; exact HBa
    | eapply eqt_wf_r; exact Hta
    | eapply eqt_wf_r; exact Haa ].
Qed.

(* ================================================================== *)
(* 9.  The dispatchers                                                 *)
(* ================================================================== *)

(* Both are stated in exactly the shape of the corresponding
   [CutTModel_ok] field, with the rule name restricted to this fragment.
   The name is pinned FIRST and the rule looked up afterwards, so each case
   costs one rule rather than a 32-way disjunction of all of them --
   [rule_pin], src/Pyrosome/Gluing/Dtt/ModelStruct.v.

   [eapply]/[eassumption] rather than [apply]/[assumption]: several of
   these rules do not mention every argument in their conclusion sort
   ([Pi_rel]'s is just [U G rel lG]), and [assumption] is conversion-only
   -- it will not instantiate the resulting evars. *)

Lemma pi_cong_obligation
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    (name = "Emptyrec" \/ name = "Pi_rel" \/ name = "Pi_irr"
     \/ name = "lam_rel" \/ name = "lam_irr"
     \/ name = "app_rel" \/ name = "app_irr") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hname Hargs.
  destruct Hname as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; rule_pin.
  - (* Emptyrec *) eapply cong_Emptyrec; eassumption.
  - (* Pi_rel *)   eapply cong_PiRel; eassumption.
  - (* Pi_irr *)   eapply cong_PiIrr; eassumption.
  - (* lam_rel *)  eapply cong_LamRel; eassumption.
  - (* lam_irr *)  eapply cong_LamIrr; eassumption.
  - (* app_rel *)  eapply cong_AppRel; eassumption.
  - (* app_irr *)  eapply cong_AppIrr; eassumption.
Qed.

Lemma pi_by_obligation
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    (name = "Pi_rel subst" \/ name = "Pi_irr subst"
     \/ name = "lam_rel subst" \/ name = "lam_irr subst"
     \/ name = "app_rel subst" \/ name = "app_irr subst"
     \/ name = "Emptyrec subst"
     \/ name = "Pi_rel beta" \/ name = "Pi_irr beta"
     \/ name = "Pi_rel eta") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
             e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hname Hargs.
  pose proof (dtt_eqt_by Hin Hargs) as Heq.
  destruct Hname
    as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    rule_pin.
  - (* Pi_rel subst *)   eapply by_PiRel_subst; eassumption.
  - (* Pi_irr subst *)   eapply by_PiIrr_subst; eassumption.
  - (* lam_rel subst *)  eapply by_LamRel_subst; eassumption.
  - (* lam_irr subst *)  eapply by_LamIrr_subst; eassumption.
  - (* app_rel subst *)  eapply by_AppRel_subst; eassumption.
  - (* app_irr subst *)  eapply by_AppIrr_subst; eassumption.
  - (* Emptyrec subst *) eapply by_Emptyrec_subst; eassumption.
  - (* Pi_rel beta *)    eapply by_PiRel_beta; eassumption.
  - (* Pi_irr beta *)    eapply by_PiIrr_beta; eassumption.
  - (* Pi_rel eta *)     eapply by_PiRel_eta; eassumption.
Qed.
