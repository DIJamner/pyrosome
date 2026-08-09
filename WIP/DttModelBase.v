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
  WIP.DttLR WIP.DttLRBasics WIP.DttLRCand WIP.DttLRCore WIP.DttLRFun
  WIP.DttRSub WIP.DttCeq WIP.DttModelStruct.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4b: the [cterm_cong] and [cterm_by]
   obligations for the UNIVERSE AND BASE-TYPE FRAGMENT of [ott_dtt] --
   the six formers whose congruences do not go under a binder,

       U   El   Nat   zero   suc   Empty

   and the six substitution commutations that go with them,

       "U subst"  "El subst"  "Nat subst"  "zero subst"  "suc subst"
       "Empty subst"

   THE SHAPE OF EVERY PROOF.  The semantic conjunct of [Ceq_term] at an
   [exp]/[ty] sort quantifies over reducible substitutions: one is GIVEN
   [EnvOk D] and [RSubN D G g] and must produce [RTmN]/[RTyN] of the
   instance.  So each case is

     (1) push the substitution in, with the matching [eq_X_subst] of
         WIP/DttEqns.v;
     (2) exhibit the normal representative and its candidate;
     (3) close with [RTmN_intro] (WIP/DttLRFun.v), which builds the
         forall-over-all-representatives relation from a SINGLE
         representative -- that is exactly what Layer 0.5's rigidity
         bought -- or, at a [ty] sort, with [RTyN]'s existential directly.

   TWO SPELLING TRAPS, both documented in WIP/DttEqns.v's header, and both
   paid for here rather than anywhere else:

     - the term rule "Nat" concludes at info [rel (next L0)] (= [iCode L0])
       but the equation "Nat subst" at [rel (iota L1)];
     - the term rule "Empty" concludes at [rel (iota L1)] but "Empty subst"
       at [rel (next L0)].

   [RTmN]/[RTyN] quantify the INFO as well as the type precisely so that
   these bridge by transitivity ([RTmN_eq_info]/[RTyN_eq_info], and
   [eq_info_next0] for the equation itself).  Section 1 below restates
   "Nat subst" at the [iCode] spelling once and for all, which is what the
   [zero]/[suc] cases need (their types mention [Nat], and [El subst]
   delivers the code at the [iCode] info).

   NOTHING HERE CONSTRUCTS A REDUCIBLE SUBSTITUTION.  Layer 3's
   [RSub_id]/[RSub_wk]/[RSub_lift] are not used and not needed: every
   obligation is handed its [RSubN D G g].
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ================================================================== *)
(* 0.  Glue                                                            *)
(* ================================================================== *)

(* [Ceq_term]'s semantic conjunct constrains only the LEFT term, so a
   reflexive instance at the RIGHT one is not immediate -- it is one use
   of symmetry (which recovers the missing half from the equation) and one
   of transitivity.  Both are WIP/DttModelStruct.v's, already proved. *)

Lemma ceq_refl_l t e1 e2 : Ceq_term t e1 e2 -> Ceq_term t e1 e1.
Proof.
  intro H; exact (term_trans_obligation H (term_sym_obligation H)).
Qed.

Lemma ceq_refl_r t e1 e2 : Ceq_term t e1 e2 -> Ceq_term t e2 e2.
Proof.
  intro H; exact (term_trans_obligation (term_sym_obligation H) H).
Qed.

(* Replacing the RIGHT term by a provably equal one is free: the semantic
   conjunct does not mention it. *)

Lemma ceq_ty_eq_r G i A1 A2 A3
  : Ceq_term (sTy G i) A1 A2 -> eqt (sTy G i) A2 A3 ->
    Ceq_term (sTy G i) A1 A3.
Proof.
  intros H Heq; apply Ceq_ty_e in H as [Ha Hb].
  apply ceq_ty; [ eapply eq_term_trans; eassumption | exact Hb ].
Qed.

Lemma ceq_exp_eq_r G i A e1 e2 e3
  : Ceq_term (sExp G i A) e1 e2 -> eqt (sExp G i A) e2 e3 ->
    Ceq_term (sExp G i A) e1 e3.
Proof.
  intros H Heq; apply Ceq_exp_e in H as [Ha Hb].
  apply ceq_exp; [ eapply eq_term_trans; eassumption | exact Hb ].
Qed.

(* Replacing the LEFT term costs one transport of the semantic conjunct,
   through the side-condition-free closure lemmas [RTyN_eq]/[RTmN_eq] and
   the matching congruence of WIP/DttEqns.v -- exactly as
   [term_sym_obligation] does. *)

Lemma ceq_ty_eq_l G i A1 A2 A3
  : eqt (sTy G i) A1 A2 -> Ceq_term (sTy G i) A2 A3 ->
    Ceq_term (sTy G i) A1 A3.
Proof.
  intros Heq H; apply Ceq_ty_e in H as [Ha Hb].
  destruct (wft_ty_inv (eqt_wf_l Heq)) as [HwG Hwi].
  apply ceq_ty; [ eapply eq_term_trans; eassumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  apply RTyN_eq with (A := oTySubst D G g i A2); [ apply Hb; assumption | ].
  apply TySubst_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_refl; exact HwG
    | apply eq_term_refl; apply RSubN_wf; exact Hg
    | apply eq_term_refl; exact Hwi
    | apply eq_term_sym; exact Heq ].
Qed.

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

(* ---- the two info spellings of a level-0 universe ----------------- *)

Lemma wf_U0_iota1 G r
  : wft G sEnv -> wft r sRelevance ->
    wft (oU G r oL0) (sTy G (oInfo oRel (oIota oL1))).
Proof.
  intros HG Hr; eapply wf_term_conv;
    [ apply wf_U; [ exact HG | exact Hr | apply wf_L0 ] | ].
  apply eq_sort_ty_cong; [ apply eq_term_refl; exact HG | apply eq_info_next0 ].
Qed.

Lemma eq_sort_U0 G r
  : wft G sEnv -> wft r sRelevance ->
    eq_sort ott_dtt [] (sCode G r oL0)
      (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)).
Proof.
  intros HG Hr; apply eq_sort_exp_cong;
    [ apply eq_term_refl; exact HG
    | apply eq_info_next0
    | apply eq_term_refl; apply wf_U0_iota1; assumption ].
Qed.

(* "Nat subst" at the [iCode] spelling of the info.  The rule itself is
   stated at [rel (iota L1)]; the [zero]/[suc] cases need it at
   [iCode L0 = rel (next L0)], because that is the info at which
   "El subst" hands the code back. *)
Lemma eq_Nat_subst' G G' g
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    eqt (sCode G oRel oL0)
      (oExpSubst G G' g (iCode oL0) (oU G' oRel oL0) (oNat G'))
      (oNat G).
Proof.
  intros HG HG' Hg.
  (* the substituted type, at the [iota L1] spelling of the info *)
  assert (eqt (sTy G (oInfo oRel (oIota oL1)))
              (oTySubst G G' g (oInfo oRel (oIota oL1)) (oU G' oRel oL0))
              (oU G oRel oL0)) as HU'.
  { eapply eq_term_trans.
    - apply eq_term_sym.
      apply TySubst_cong;
        [ apply eq_term_refl; exact HG
        | apply eq_term_refl; exact HG'
        | apply eq_term_refl; exact Hg
        | apply eq_info_next0
        | apply eq_term_refl; apply wf_U0_iota1; [ exact HG' | apply wf_Rel ] ].
    - eapply eq_term_conv.
      + apply eq_U_subst; auto using wf_Rel, wf_L0.
      + apply eq_sort_ty_cong;
          [ apply eq_term_refl; exact HG | apply eq_info_next0 ]. }
  eapply eq_term_conv.
  2:{ apply eq_sort_sym; apply eq_sort_U0; [ exact HG | apply wf_Rel ]. }
  eapply eq_term_trans; [ | apply (@eq_Nat_subst G G' g); assumption ].
  eapply eq_term_conv.
  - apply ExpSubst_cong;
      [ apply eq_term_refl; exact HG
      | apply eq_term_refl; exact HG'
      | apply eq_term_refl; exact Hg
      | apply eq_info_next0
      | apply eq_term_refl; apply wf_U0_iota1; [ exact HG' | apply wf_Rel ]
      | apply eq_term_refl; eapply wf_term_conv;
        [ apply wf_Nat; exact HG'
        | apply eq_sort_U0; [ exact HG' | apply wf_Rel ] ] ].
  - apply eq_sort_exp_ty;
      [ exact HG
      | apply wf_Info; [ apply wf_Rel | apply wf_Iota; apply wf_L1 ]
      | exact HU' ].
Qed.

(* ================================================================== *)
(* 1.  The six congruences                                             *)
(* ================================================================== *)

(* ---- U ---------------------------------------------------------- *)

Lemma cong_U G1 G2 r1 r2 l1 l2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance r1 r2 -> Ceq_term sLvl l1 l2 ->
    Ceq_term (sTy G2 (iCode l2)) (oU G1 r1 l1) (oU G2 r2 l2).
Proof.
  intros HGc Hr Hl.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst r1.
  apply Ceq_lvl_e in Hl as [Hlq Hlnf]; subst l1.
  assert (wft r2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft l2 sLvl) as Hwl by (apply LvlNf_wf; exact Hlnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  apply ceq_ty.
  { apply U_cong;
      [ exact HG | apply eq_term_refl; exact Hwr | apply eq_term_refl; exact Hwl ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  exists (iCode l2), (oU D r2 l2), (HasNfCode D r2 l2).
  repeat split.
  - apply eq_term_refl; wfa.
  - apply tyok_U; assumption.
  - eapply eq_term_trans.
    + apply TySubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; wfa
        | apply U_cong;
          [ exact HG
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact Hwl ] ].
    + apply eq_U_subst; assumption.
  - apply RTy_U_i; assumption.
Qed.

(* ---- El --------------------------------------------------------- *)

(* The argument [c] is a CODE, so its [Ceq_term] gives [RTmN] at a
   universe, i.e. [HasNfCode D r l (g[c])]; the normal code it names is
   fed to [RTyEx_of_NfCode] for the candidate, and "El subst" supplies the
   representative. *)
Lemma cong_El G1 G2 r1 r2 l1 l2 c1 c2
  : Ceq_term sEnv G1 G2 -> Ceq_term sRelevance r1 r2 -> Ceq_term sLvl l1 l2 ->
    Ceq_term (sCode G2 r2 l2) c1 c2 ->
    Ceq_term (sTy G2 (iEl r2 l2)) (oEl G1 r1 l1 c1) (oEl G2 r2 l2 c2).
Proof.
  intros HGc Hr Hl Hc.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst r1.
  apply Ceq_lvl_e in Hl as [Hlq Hlnf]; subst l1.
  apply Ceq_exp_e in Hc as [Hca Hcb].
  assert (wft r2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft l2 sLvl) as Hwl by (apply LvlNf_wf; exact Hlnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft c1 (sCode G2 r2 l2)) as Hwc1 by (eapply eqt_wf_l; exact Hca).
  apply ceq_ty.
  { apply El_cong;
      [ exact HG
      | apply eq_term_refl; exact Hwr
      | apply eq_term_refl; exact Hwl
      | exact Hca ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  (* the code's normal form at [D] *)
  assert (HasNfCode D r2 l2
            (oExpSubst D G2 g (iCode l2) (oU G2 r2 l2) c1)) as Hnf.
  { eapply RTm_elim; [ apply RTy_U_i; assumption | ].
    apply Hcb; try assumption.
    - apply eq_term_refl; wfa.
    - apply tyok_U; assumption.
    - apply eq_U_subst; assumption. }
  destruct Hnf as [c0 [Hc0 Hc0eq]].
  destruct (RTyEx_of_NfCode Hc0) as [P HP].
  exists (iEl r2 l2), (oEl D r2 l2 c0), P.
  repeat split.
  - apply eq_term_refl; wfa.
  - apply tyok_El; exact Hc0.
  - eapply eq_term_trans.
    + apply TySubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; wfa
        | apply El_cong;
          [ exact HG
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact Hwl
          | apply eq_term_refl; exact Hwc1 ] ].
    + eapply eq_term_trans; [ apply eq_El_subst; assumption | ].
      apply El_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact Hwl
        | exact Hc0eq ].
  - exact HP.
Qed.

(* ---- Nat -------------------------------------------------------- *)

Lemma cong_Nat G1 G2
  : Ceq_term sEnv G1 G2 -> Ceq_term (sCode G2 oRel oL0) (oNat G1) (oNat G2).
Proof.
  intro HGc; apply Ceq_env_e in HGc as [HG _].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  apply ceq_exp; [ apply Nat_cong; exact HG | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  eapply RTmN_intro with (i0 := iCode oL0) (A0 := oU D oRel oL0).
  - apply eq_term_refl; wfa.
  - apply tyok_U; [ exact HD | constructor | constructor ].
  - apply eq_U_subst; auto using wf_Rel, wf_L0.
  - apply RTy_U_i; [ exact HD | constructor | constructor ].
  - (* the normal code is [Nat D] *)
    exists (oNat D); split; [ apply nfcode_nat; exact HD | ].
    eapply eq_term_trans; [ | apply (@eq_Nat_subst' D G2 g); assumption ].
    eapply eq_term_conv.
    + apply ExpSubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; wfa
        | apply eq_term_refl; apply wf_U; auto using wf_Rel, wf_L0
        | apply Nat_cong; exact HG ].
    + apply eq_sort_exp_ty;
        [ exact HwD | wfa | apply eq_U_subst; auto using wf_Rel, wf_L0 ].
Qed.

(* ---- zero ------------------------------------------------------- *)

Lemma cong_zero G1 G2
  : Ceq_term sEnv G1 G2 ->
    Ceq_term (sElt G2 oRel oL0 (oNat G2)) (oZero G1) (oZero G2).
Proof.
  intro HGc; apply Ceq_env_e in HGc as [HG _].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  apply ceq_exp; [ apply Zero_cong; exact HG | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  assert (eqt (sTy D (iEl oRel oL0))
              (oTySubst D G2 g (iEl oRel oL0) (oEl G2 oRel oL0 (oNat G2)))
              (oEl D oRel oL0 (oNat D))) as Hty.
  { eapply eq_term_trans;
      [ apply eq_El_subst; auto using wf_Rel, wf_L0, wf_Nat | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Rel
      | apply eq_term_refl; apply wf_L0
      | apply eq_Nat_subst'; assumption ]. }
  eapply RTmN_intro with (i0 := iEl oRel oL0) (A0 := oEl D oRel oL0 (oNat D)).
  - apply eq_term_refl; wfa.
  - apply tyok_El; apply nfcode_nat; exact HD.
  - exact Hty.
  - apply RTy_nat_i; exact HD.
  - exists (oZero D); split; [ apply nfet_zero; exact HD | ].
    eapply eq_term_trans; [ | apply (@eq_zero_subst D G2 g); assumption ].
    eapply eq_term_conv.
    + apply ExpSubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; wfa
        | apply eq_term_refl; apply wf_El;
          auto using wf_Rel, wf_L0, wf_Nat
        | apply Zero_cong; exact HG ].
    + apply eq_sort_exp_ty; [ exact HwD | wfa | exact Hty ].
Qed.

(* ---- suc -------------------------------------------------------- *)

Lemma cong_suc G1 G2 n1 n2
  : Ceq_term sEnv G1 G2 ->
    Ceq_term (sElt G2 oRel oL0 (oNat G2)) n1 n2 ->
    Ceq_term (sElt G2 oRel oL0 (oNat G2)) (oSuc G1 n1) (oSuc G2 n2).
Proof.
  intros HGc Hn.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_exp_e in Hn as [Hna Hnb].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft n1 (sElt G2 oRel oL0 (oNat G2))) as Hwn1
      by (eapply eqt_wf_l; exact Hna).
  apply ceq_exp; [ apply Suc_cong; assumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  assert (eqt (sTy D (iEl oRel oL0))
              (oTySubst D G2 g (iEl oRel oL0) (oEl G2 oRel oL0 (oNat G2)))
              (oEl D oRel oL0 (oNat D))) as Hty.
  { eapply eq_term_trans;
      [ apply eq_El_subst; auto using wf_Rel, wf_L0, wf_Nat | ].
    apply El_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; apply wf_Rel
      | apply eq_term_refl; apply wf_L0
      | apply eq_Nat_subst'; assumption ]. }
  (* the argument's normal form at [D] *)
  assert (HasNf D (iEl oRel oL0) (oEl D oRel oL0 (oNat D))
            (oExpSubst D G2 g (iEl oRel oL0) (oEl G2 oRel oL0 (oNat G2)) n1))
    as Hnf.
  { eapply RTm_elim; [ apply RTy_nat_i; exact HD | ].
    apply Hnb; try assumption.
    all: first [ apply eq_term_refl; wfa
               | apply tyok_El; apply nfcode_nat; exact HD
               | exact Hty ]. }
  destruct Hnf as [nn [Hnn Hnneq]].
  eapply RTmN_intro with (i0 := iEl oRel oL0) (A0 := oEl D oRel oL0 (oNat D)).
  - apply eq_term_refl; wfa.
  - apply tyok_El; apply nfcode_nat; exact HD.
  - exact Hty.
  - apply RTy_nat_i; exact HD.
  - exists (oSuc D nn); split; [ apply nfet_suc; exact Hnn | ].
    eapply eq_term_trans.
    2:{ apply Suc_cong; [ apply eq_term_refl; exact HwD | exact Hnneq ]. }
    eapply eq_term_trans; [ | apply (@eq_suc_subst D G2 g n1); assumption ].
    eapply eq_term_conv.
    + apply ExpSubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_refl; wfa
        | apply eq_term_refl; apply wf_El;
          auto using wf_Rel, wf_L0, wf_Nat
        | apply Suc_cong;
          [ exact HG | apply eq_term_refl; exact Hwn1 ] ].
    + apply eq_sort_exp_ty; [ exact HwD | wfa | exact Hty ].
Qed.

(* ---- Empty ------------------------------------------------------ *)

(* The trap in the other direction: the term rule "Empty" concludes at
   [rel (iota L1)] while "Empty subst" is at [iCode L0].  [RTmN]'s
   quantified info absorbs the difference. *)
Lemma cong_Empty G1 G2
  : Ceq_term sEnv G1 G2 ->
    Ceq_term (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0))
             (oEmpty G1) (oEmpty G2).
Proof.
  intro HGc; apply Ceq_env_e in HGc as [HG _].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  apply ceq_exp; [ apply Empty_cong; exact HG | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  eapply RTmN_intro with (i0 := iCode oL0) (A0 := oU D oIrr oL0).
  - apply eq_term_sym; apply eq_info_next0.
  - apply tyok_U; [ exact HD | constructor | constructor ].
  - (* the type argument, moved to the [iCode] spelling *)
    eapply eq_term_trans.
    + apply TySubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_sym; apply eq_info_next0
        | apply eq_term_refl; apply wf_U; auto using wf_Irr, wf_L0 ].
    + apply eq_U_subst; auto using wf_Irr, wf_L0.
  - apply RTy_U_i; [ exact HD | constructor | constructor ].
  - exists (oEmpty D); split; [ apply nfcode_empty; exact HD | ].
    eapply eq_term_trans; [ | apply (@eq_Empty_subst D G2 g); assumption ].
    eapply eq_term_conv.
    + apply ExpSubst_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact HwG2
        | apply eq_term_refl; exact Hwg
        | apply eq_term_sym; apply eq_info_next0
        | apply eq_term_refl; apply wf_U; auto using wf_Irr, wf_L0
        | eapply eq_term_conv;
          [ apply Empty_cong; exact HG
          | apply eq_sort_sym; apply eq_sort_U_irr0; exact HwG2 ] ].
    + apply eq_sort_exp_ty;
        [ exact HwD | wfa
        | apply eq_U_subst; auto using wf_Irr, wf_L0 ].
Qed.
