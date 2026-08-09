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
  Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelCand Pyrosome.Gluing.Dtt.LogRelCore Pyrosome.Gluing.Dtt.LogRelFun
  Pyrosome.Gluing.Dtt.RSub Pyrosome.Gluing.Dtt.Ceq Pyrosome.Gluing.Dtt.ModelStruct.
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
         src/Pyrosome/Gluing/Dtt/Eqns.v;
     (2) exhibit the normal representative and its candidate;
     (3) close with [RTmN_intro] (src/Pyrosome/Gluing/Dtt/LogRelFun.v), which builds the
         forall-over-all-representatives relation from a SINGLE
         representative -- that is exactly what Layer 0.5's rigidity
         bought -- or, at a [ty] sort, with [RTyN]'s existential directly.

   TWO SPELLING TRAPS, both documented in src/Pyrosome/Gluing/Dtt/Eqns.v's header, and both
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
   of transitivity.  Both are src/Pyrosome/Gluing/Dtt/ModelStruct.v's, already proved. *)

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
   the matching congruence of src/Pyrosome/Gluing/Dtt/Eqns.v -- exactly as
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

(* "U subst" at the OTHER spelling of the info -- the one the rules "Nat"
   and "Empty" put a level-0 universe at. *)
Lemma eq_U_subst_iota1 G G' g r
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') -> wft r sRelevance ->
    eqt (sTy G (oInfo oRel (oIota oL1)))
      (oTySubst G G' g (oInfo oRel (oIota oL1)) (oU G' r oL0))
      (oU G r oL0).
Proof.
  intros HG HG' Hg Hr.
  eapply eq_term_trans.
  - apply eq_term_sym.
    apply TySubst_cong;
      [ apply eq_term_refl; exact HG
      | apply eq_term_refl; exact HG'
      | apply eq_term_refl; exact Hg
      | apply eq_info_next0
      | apply eq_term_refl; apply wf_U0_iota1; assumption ].
  - eapply eq_term_conv.
    + apply eq_U_subst; auto using wf_L0.
    + apply eq_sort_ty_cong;
        [ apply eq_term_refl; exact HG | apply eq_info_next0 ].
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
  pose proof (eq_U_subst_iota1 HG HG' Hg wf_Rel) as HU'.
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

(* The [Nat] type under a substitution.  Used by every [zero]/[suc] case:
   it is the normal representative that [RTmN_intro] is fed. *)
Lemma eq_ElNat_subst G G' g
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') ->
    eqt (sTy G (iEl oRel oL0))
      (oTySubst G G' g (iEl oRel oL0) (oEl G' oRel oL0 (oNat G')))
      (oEl G oRel oL0 (oNat G)).
Proof.
  intros HG HG' Hg.
  eapply eq_term_trans;
    [ apply eq_El_subst; auto using wf_Rel, wf_L0, wf_Nat | ].
  apply El_cong;
    [ apply eq_term_refl; exact HG
    | apply eq_term_refl; apply wf_Rel
    | apply eq_term_refl; apply wf_L0
    | apply eq_Nat_subst'; assumption ].
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

(* ================================================================== *)
(* 2.  The six equations                                               *)
(* ================================================================== *)

(* FOUR OF THE SIX ARE FREE, given section 1.  The [cterm_by] obligation
   asks for [Ceq_term t e1[/s1/] e2[/s2/]], and [Ceq_term]'s semantic
   conjunct constrains only the LEFT term; so whenever the right-hand side
   of the equation is a bare former -- [U], [Nat], [zero], [Empty] -- the
   obligation is [ceq_{ty,exp}_eq_l] applied to
     (a) the equation itself, proved inside the theory by one congruence
         plus the rule, and
     (b) the corresponding congruence of section 1 at the REFLEXIVE
         arguments ([ceq_refl_r]).

   "El subst" and "suc subst" are the two exceptions: their right-hand
   sides mention [exp_subst], whose congruence belongs to the sigma
   fragment, so their semantic conjunct is built by hand.  Both times it
   is the same move -- compose the two substitutions with
   "ty_subst_cmp"/"exp_subst_cmp" and read the argument's normal form off
   the COMPOSITE reducible substitution, which [Ceq_sub]'s conjunct
   supplies. *)

(* ---- "U subst" -------------------------------------------------- *)

Lemma by_U_subst G1 G2 G1' G2' g1 g2 r1 r2 l1 l2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance r1 r2 -> Ceq_term sLvl l1 l2 ->
    Ceq_term (sTy G2 (iCode l2))
      (oTySubst G1 G1' g1 (iCode l1) (oU G1' r1 l1)) (oU G2 r2 l2).
Proof.
  intros HGc HGc' Hgc Hr Hl.
  pose proof (ceq_refl_r HGc) as HG2c.
  pose proof (ceq_refl_r Hr) as Hr2.
  pose proof (ceq_refl_r Hl) as Hl2.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst r1.
  apply Ceq_lvl_e in Hl as [Hlq Hlnf]; subst l1.
  assert (wft r2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft l2 sLvl) as Hwl by (apply LvlNf_wf; exact Hlnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  eapply ceq_ty_eq_l;
    [ | apply cong_U; [ exact HG2c | exact Hr2 | exact Hl2 ] ].
  eapply eq_term_trans.
  - apply TySubst_cong;
      [ exact HG | exact HG' | exact Hga
      | apply eq_term_refl; wfa
      | apply U_cong;
        [ exact HG'
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact Hwl ] ].
  - apply eq_U_subst; assumption.
Qed.

(* ---- "Nat subst" ------------------------------------------------- *)

(* The conclusion is at info [rel (iota L1)] while [cong_Nat] concludes at
   [iCode L0]; [ceq_exp_transfer] (src/Pyrosome/Gluing/Dtt/ModelStruct.v) moves the
   reflexive instance across. *)
Lemma by_Nat_subst G1 G2 G1' G2' g1 g2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oRel oL0))
      (oExpSubst G1 G1' g1 (oInfo oRel (oIota oL1)) (oU G1' oRel oL0)
                 (oNat G1'))
      (oNat G2).
Proof.
  intros HGc HGc' Hgc.
  pose proof (ceq_refl_r HGc) as HG2c.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  eapply ceq_exp_eq_l.
  2:{ eapply ceq_exp_transfer;
        [ apply eq_term_refl; exact HwG2
        | apply eq_info_next0
        | apply eq_term_refl; apply wf_U0_iota1; [ exact HwG2 | apply wf_Rel ]
        | apply cong_Nat; exact HG2c ]. }
  eapply eq_term_trans; [ | apply (@eq_Nat_subst G2 G2' g2); assumption ].
  eapply eq_term_conv.
  - apply ExpSubst_cong;
      [ exact HG | exact HG' | exact Hga
      | apply eq_term_refl; wfa
      | eapply eq_term_conv;
        [ apply U_cong;
          [ exact HG'
          | apply eq_term_refl; apply wf_Rel
          | apply eq_term_refl; apply wf_L0 ]
        | apply eq_sort_ty_cong;
          [ apply eq_term_refl; exact HwG2' | apply eq_info_next0 ] ]
      | eapply eq_term_conv;
        [ apply Nat_cong; exact HG'
        | apply eq_sort_U0; [ exact HwG2' | apply wf_Rel ] ] ].
  - apply eq_sort_exp_ty;
      [ exact HwG2 | wfa | apply eq_U_subst_iota1; auto using wf_Rel ].
Qed.

(* ---- "zero subst" ------------------------------------------------ *)

Lemma by_zero_subst G1 G2 G1' G2' g1 g2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term (sElt G2 oRel oL0 (oNat G2))
      (oExpSubst G1 G1' g1 (iEl oRel oL0) (oEl G1' oRel oL0 (oNat G1'))
                 (oZero G1'))
      (oZero G2).
Proof.
  intros HGc HGc' Hgc.
  pose proof (ceq_refl_r HGc) as HG2c.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  eapply ceq_exp_eq_l; [ | apply cong_zero; exact HG2c ].
  eapply eq_term_trans; [ | apply (@eq_zero_subst G2 G2' g2); assumption ].
  eapply eq_term_conv.
  - apply ExpSubst_cong;
      [ exact HG | exact HG' | exact Hga
      | apply eq_term_refl; wfa
      | apply El_cong;
        [ exact HG'
        | apply eq_term_refl; apply wf_Rel
        | apply eq_term_refl; apply wf_L0
        | apply Nat_cong; exact HG' ]
      | apply Zero_cong; exact HG' ].
  - apply eq_sort_exp_ty;
      [ exact HwG2 | wfa | apply eq_ElNat_subst; assumption ].
Qed.

(* ---- "Empty subst" ----------------------------------------------- *)

(* The mirror image of "Nat subst": here the EQUATION is at [iCode L0] and
   the term rule at [rel (iota L1)], so the transfer goes the other way. *)
Lemma by_Empty_subst G1 G2 G1' G2' g1 g2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term (sCode G2 oIrr oL0)
      (oExpSubst G1 G1' g1 (iCode oL0) (oU G1' oIrr oL0) (oEmpty G1'))
      (oEmpty G2).
Proof.
  intros HGc HGc' Hgc.
  pose proof (ceq_refl_r HGc) as HG2c.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga _].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  eapply ceq_exp_eq_l.
  2:{ eapply ceq_exp_transfer;
        [ apply eq_term_refl; exact HwG2
        | apply eq_term_sym; apply eq_info_next0
        | apply eq_term_refl; apply wf_U; auto using wf_Irr, wf_L0
        | apply cong_Empty; exact HG2c ]. }
  eapply eq_term_trans; [ | apply (@eq_Empty_subst G2 G2' g2); assumption ].
  eapply eq_term_conv.
  - apply ExpSubst_cong;
      [ exact HG | exact HG' | exact Hga
      | apply eq_term_refl; wfa
      | apply U_cong;
        [ exact HG'
        | apply eq_term_refl; apply wf_Irr
        | apply eq_term_refl; apply wf_L0 ]
      | eapply eq_term_conv;
        [ apply Empty_cong; exact HG'
        | apply eq_sort_sym; apply eq_sort_U_irr0; exact HwG2' ] ].
  - apply eq_sort_exp_ty;
      [ exact HwG2 | wfa | apply eq_U_subst; auto using wf_Irr, wf_L0 ].
Qed.

(* ---- "El subst" -------------------------------------------------- *)

(* The right-hand side mentions [exp_subst], so the semantic conjunct is
   built directly.  Under a reducible [g], the left-hand side is a DOUBLE
   substitution; "ty_subst_cmp" collapses it to the composite
   [g o g1], which [Ceq_sub]'s conjunct says is reducible, and the code
   argument's own [Ceq_term] then hands back a normal code there. *)
Lemma by_El_subst G1 G2 G1' G2' g1 g2 r1 r2 l1 l2 c1 c2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term sRelevance r1 r2 -> Ceq_term sLvl l1 l2 ->
    Ceq_term (sCode G2' r2 l2) c1 c2 ->
    Ceq_term (sTy G2 (iEl r2 l2))
      (oTySubst G1 G1' g1 (iEl r1 l1) (oEl G1' r1 l1 c1))
      (oEl G2 r2 l2 (oExpSubst G2 G2' g2 (iCode l2) (oU G2' r2 l2) c2)).
Proof.
  intros HGc HGc' Hgc Hr Hl Hc.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga Hgb].
  apply Ceq_relevance_e in Hr as [Hrq Hrnf]; subst r1.
  apply Ceq_lvl_e in Hl as [Hlq Hlnf]; subst l1.
  apply Ceq_exp_e in Hc as [Hca Hcb].
  assert (wft r2 sRelevance) as Hwr by (apply RelNf_wf; exact Hrnf).
  assert (wft l2 sLvl) as Hwl by (apply LvlNf_wf; exact Hlnf).
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g1 (sSub G2 G2')) as Hwg1 by (eapply eqt_wf_l; exact Hga).
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft c1 (sCode G2' r2 l2)) as Hwc1 by (eapply eqt_wf_l; exact Hca).
  assert (wft c2 (sCode G2' r2 l2)) as Hwc2 by (eapply eqt_wf_r; exact Hca).
  (* the inner instance, moved to the "2" side, with [g1] kept *)
  assert (eqt (sTy G2 (iEl r2 l2))
              (oTySubst G1 G1' g1 (iEl r2 l2) (oEl G1' r2 l2 c1))
              (oTySubst G2 G2' g1 (iEl r2 l2) (oEl G2' r2 l2 c1))) as Hinner.
  { apply TySubst_cong;
      [ exact HG | exact HG' | apply eq_term_refl; exact Hwg1
      | apply eq_term_refl; wfa
      | apply El_cong;
        [ exact HG'
        | apply eq_term_refl; exact Hwr
        | apply eq_term_refl; exact Hwl
        | apply eq_term_refl; exact Hwc1 ] ]. }
  apply ceq_ty.
  { eapply eq_term_trans.
    - apply TySubst_cong;
        [ exact HG | exact HG' | exact Hga
        | apply eq_term_refl; wfa
        | apply El_cong;
          [ exact HG'
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact Hwl
          | exact Hca ] ].
    - apply eq_El_subst; assumption. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  pose proof (Hgb D g HD Hg) as Hh.
  assert (wft (oCmp D G2 G2' g g1) (sSub D G2')) as Hwh
      by (apply RSubN_wf; exact Hh).
  assert (HasNfCode D r2 l2
            (oExpSubst D G2' (oCmp D G2 G2' g g1) (iCode l2) (oU G2' r2 l2) c1))
    as Hnf.
  { eapply RTm_elim; [ apply RTy_U_i; assumption | ].
    apply Hcb; try assumption.
    all: first [ apply eq_term_refl; wfa
               | apply tyok_U; assumption
               | apply eq_U_subst; assumption ]. }
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
        | exact Hinner ].
    + eapply eq_term_trans.
      * apply eq_ty_subst_cmp;
          [ exact HwD | exact HwG2 | exact HwG2' | exact Hwg | exact Hwg1
          | wfa | apply wf_El; assumption ].
      * eapply eq_term_trans; [ apply eq_El_subst; assumption | ].
        apply El_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact Hwr
          | apply eq_term_refl; exact Hwl
          | exact Hc0eq ].
  - exact HP.
Qed.

(* ---- "suc subst" ------------------------------------------------- *)

(* Same shape as "El subst", one layer down: "exp_subst_cmp" rather than
   "ty_subst_cmp", and the argument's normal form comes from the [Nat]
   candidate ([HasNf]) rather than from [HasNfCode]. *)
Lemma by_suc_subst G1 G2 G1' G2' g1 g2 n1 n2
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_term (sSub G2 G2') g1 g2 ->
    Ceq_term (sElt G2' oRel oL0 (oNat G2')) n1 n2 ->
    Ceq_term (sElt G2 oRel oL0 (oNat G2))
      (oExpSubst G1 G1' g1 (iEl oRel oL0) (oEl G1' oRel oL0 (oNat G1'))
                 (oSuc G1' n1))
      (oSuc G2 (oExpSubst G2 G2' g2 (iEl oRel oL0)
                          (oEl G2' oRel oL0 (oNat G2')) n2)).
Proof.
  intros HGc HGc' Hgc Hn.
  apply Ceq_env_e in HGc as [HG _].
  apply Ceq_env_e in HGc' as [HG' _].
  apply Ceq_sub_e in Hgc as [Hga Hgb].
  apply Ceq_exp_e in Hn as [Hna Hnb].
  assert (wft G2 sEnv) as HwG2 by (eapply eqt_wf_r; exact HG).
  assert (wft G2' sEnv) as HwG2' by (eapply eqt_wf_r; exact HG').
  assert (wft g1 (sSub G2 G2')) as Hwg1 by (eapply eqt_wf_l; exact Hga).
  assert (wft g2 (sSub G2 G2')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft n1 (sElt G2' oRel oL0 (oNat G2'))) as Hwn1
      by (eapply eqt_wf_l; exact Hna).
  assert (wft n2 (sElt G2' oRel oL0 (oNat G2'))) as Hwn2
      by (eapply eqt_wf_r; exact Hna).
  assert (wft (oEl G2' oRel oL0 (oNat G2')) (sTy G2' (iEl oRel oL0))) as HwA'
      by (apply wf_El; auto using wf_Rel, wf_L0, wf_Nat).
  pose proof (eq_ElNat_subst HwG2 HwG2' Hwg1) as Hty1.
  apply ceq_exp.
  { eapply eq_term_trans;
      [ | apply (@eq_suc_subst G2 G2' g2 n2); assumption ].
    eapply eq_term_conv.
    - apply ExpSubst_cong;
        [ exact HG | exact HG' | exact Hga
        | apply eq_term_refl; wfa
        | apply El_cong;
          [ exact HG'
          | apply eq_term_refl; apply wf_Rel
          | apply eq_term_refl; apply wf_L0
          | apply Nat_cong; exact HG' ]
        | apply Suc_cong; [ exact HG' | exact Hna ] ].
    - apply eq_sort_exp_ty;
        [ exact HwG2 | wfa | apply eq_ElNat_subst; assumption ]. }
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  pose proof (Hgb D g HD Hg) as Hh.
  assert (wft (oCmp D G2 G2' g g1) (sSub D G2')) as Hwh
      by (apply RSubN_wf; exact Hh).
  pose proof (eq_ElNat_subst HwD HwG2' Hwh) as HtyD.
  pose proof (eq_ElNat_subst HwD HwG2 Hwg) as HtyG.
  (* the argument's normal form, at the COMPOSITE substitution *)
  assert (HasNf D (iEl oRel oL0) (oEl D oRel oL0 (oNat D))
            (oExpSubst D G2' (oCmp D G2 G2' g g1) (iEl oRel oL0)
                       (oEl G2' oRel oL0 (oNat G2')) n1)) as Hnf.
  { eapply RTm_elim; [ apply RTy_nat_i; exact HD | ].
    apply Hnb; try assumption.
    all: first [ apply eq_term_refl; wfa
               | apply tyok_El; apply nfcode_nat; exact HD
               | exact HtyD ]. }
  destruct Hnf as [nn [Hnn Hnneq]].
  eapply RTmN_intro with (i0 := iEl oRel oL0) (A0 := oEl D oRel oL0 (oNat D)).
  - apply eq_term_refl; wfa.
  - apply tyok_El; apply nfcode_nat; exact HD.
  - exact HtyG.
  - apply RTy_nat_i; exact HD.
  - exists (oSuc D nn); split; [ apply nfet_suc; exact Hnn | ].
    eapply eq_term_trans.
    2:{ apply Suc_cong; [ apply eq_term_refl; exact HwD | exact Hnneq ]. }
    eapply eq_term_trans;
      [ | apply (@eq_suc_subst D G2' (oCmp D G2 G2' g g1) n1); assumption ].
    eapply eq_term_conv.
    + eapply eq_term_trans.
      * apply ExpSubst_cong;
          [ apply eq_term_refl; exact HwD
          | apply eq_term_refl; exact HwG2
          | apply eq_term_refl; exact Hwg
          | apply eq_term_refl; wfa
          | apply eq_term_sym; exact Hty1
          | apply ExpSubst_cong;
            [ exact HG | exact HG' | apply eq_term_refl; exact Hwg1
            | apply eq_term_refl; wfa
            | apply El_cong;
              [ exact HG'
              | apply eq_term_refl; apply wf_Rel
              | apply eq_term_refl; apply wf_L0
              | apply Nat_cong; exact HG' ]
            | apply Suc_cong;
              [ exact HG' | apply eq_term_refl; exact Hwn1 ] ] ].
      * apply eq_exp_subst_cmp;
          [ exact HwD | exact HwG2 | exact HwG2' | exact Hwg | exact Hwg1
          | wfa | exact HwA'
          | apply wf_Suc; auto using wf_Nat ].
    + apply eq_sort_exp_ty;
        [ exact HwD | wfa | ].
      eapply eq_term_trans; [ | exact HtyD ].
      apply eq_ty_subst_cmp;
        [ exact HwD | exact HwG2 | exact HwG2' | exact Hwg | exact Hwg1
        | wfa | exact HwA' ].
Qed.

(* ================================================================== *)
(* 3.  The dispatchers                                                 *)
(* ================================================================== *)

(* Both are stated in exactly the shape of the corresponding
   [CutTModel_ok] field, with the rule name restricted to this fragment.
   The name is pinned FIRST and the rule looked up afterwards, so each case
   costs one rule rather than a 32-way (resp. 32-way) disjunction of all of
   them -- [rule_pin], src/Pyrosome/Gluing/Dtt/ModelStruct.v. *)

Lemma base_cong_obligation
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    (name = "U" \/ name = "El" \/ name = "Nat" \/ name = "zero"
     \/ name = "suc" \/ name = "Empty") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hname Hargs.
  destruct Hname as [-> | [-> | [-> | [-> | [-> | ->]]]]]; rule_pin.
  - (* U *) apply cong_U; assumption.
  - (* El *) apply cong_El; assumption.
  - (* Nat *) apply cong_Nat; assumption.
  - (* zero *) apply cong_zero; assumption.
  - (* suc *) apply cong_suc; assumption.
  - (* Empty *) apply cong_Empty; assumption.
Qed.

Lemma base_by_obligation
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    (name = "U subst" \/ name = "El subst" \/ name = "Nat subst"
     \/ name = "zero subst" \/ name = "suc subst" \/ name = "Empty subst") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
             e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hname Hargs.
  destruct Hname as [-> | [-> | [-> | [-> | [-> | ->]]]]]; rule_pin.
  - (* U subst *) eapply by_U_subst; eassumption.
  - (* El subst *) eapply by_El_subst; eassumption.
  - (* Nat subst *) eapply by_Nat_subst; eassumption.
  - (* zero subst *) eapply by_zero_subst; eassumption.
  - (* suc subst *) eapply by_suc_subst; eassumption.
  - (* Empty subst *) eapply by_Empty_subst; eassumption.
Qed.
