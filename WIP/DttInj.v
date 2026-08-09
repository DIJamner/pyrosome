Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttSyntax WIP.DttNf WIP.DttErase WIP.DttRigid WIP.DttRigidOk.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 0.5c: CODE RIGIDITY, ASSEMBLED.

   The three theorems Layer 0.5 exports:

     NfCode_inj : normal codes are determined by provable equality
     TyOk_inj   : normal types are determined by provable equality
     EnvOk_inj  : normal environments are determined by provable equality

   WIP/DttErase.v proves the syntactic half of this modulo the hypothesis
   [WknInj]; WIP/DttRigid.v + WIP/DttRigidOk.v supply the semantic half
   ([rigid_env]/[rigid_ty]/[rigid_code]).  What is left is the
   composition, and the composition looks circular: [WknInj] at
   [ext G j B] is discharged by the model PLUS type-injectivity at [G],
   but [DttErase.v] states [WknInj] globally.

   The design document (section 4b) proposes to break the circle with one
   strong induction on [length E], proving the environment, type, code and
   variable statements simultaneously.  That is NOT what is done here, and
   the reason is worth recording, because the induction as proposed does
   not in fact go through: the code statement's [Pi] case recurses into a
   LONGER environment (one more binder), so it cannot be justified by an
   induction hypothesis at a shorter one; and the variable statement at
   that longer environment then needs the type statement back at the
   original length.  A measure exists that repairs this (lexicographic in
   the size of the erasure and the de Bruijn index), but it is not needed,
   because of

     THE UNIVERSE OBSERVATION.  The only [WknInj] instance the code-level
     argument ever needs is the one where the named type is a UNIVERSE --
     a code variable's type is [oU G r l] and nothing else.  And at a
     universe the statement is UNCONDITIONAL: a normal type whose rigid
     interpretation is [rt_U br bl] is syntactically [oU G r l] with [r]
     and [l] determined by [br] and [bl].  There is no recursion at all.

   So the file is linear:

     1-2. Inversions for the interpretation relations of DttRigid.v.
     3.   [WknU_shape] -- the universe-restricted [WknInj], with the
          conclusion strengthened to name the type: unconditional.
     4.   [Nf_EnvOk] -- every normal-form judgement carries [EnvOk].
     5.   [Nf_ErI] -- one mutual induction producing, for a normal object,
          an erasure that is SIMULTANEOUSLY an [Er...] and an [I...]
          derivation.  This is the seam between DttErase.v's syntactic
          relations and DttRigid.v's semantic ones; running both in a
          single induction is what keeps their [renv] indices in step.
          The variable clause is where [WknU_shape] is spent.
     6.   [VarTU_erase_inj] / [NfCode_erase_inj_u] / [TyOk_erase_inj_u] /
          [EnvOk_erase_inj_u] -- DttErase.v section 8, with [WknInj]
          replaced by [WknU_shape] and therefore hypothesis-free.
     7.   [WknInj_holds], and then the three exported theorems.

   Zero axioms, zero admits.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* =====================================================================
   1. Inversions for [IEnv] / [ITy].
   ===================================================================== *)

Lemma IEnv_emp_inv E : IEnv oEmp E -> E = [].
Proof. inversion 1; reflexivity. Qed.

Lemma IEnv_ext_inv G i A E
  : IEnv (oExt G i A) E ->
    exists T E0, E = T :: E0 /\ IEnv G E0 /\ ITy E0 A T.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ITy_U_inv E G r l T
  : ITy E (oU G r l) T ->
    exists br bl, T = rt_U br bl /\ IEnv G E /\ ErRel r br /\ ErLvl l bl.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ITy_El_inv E G r l c T
  : ITy E (oEl G r l c) T ->
    exists br bl n, T = rt_El br bl n /\ IEnv G E
                    /\ ErRel r br /\ ErLvl l bl /\ ICode E c n.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ITy_subst_inv E G G' g i A T
  : ITy E (oTySubst G G' g i A) T ->
    exists E' s T0,
      IEnv G E /\ IEnv G' E' /\ ISub E E' g s /\ ITy E' A T0
      /\ T = tsub s T0.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ISub_wkn_inv E E' G i A s
  : ISub E E' (oWkn G i A) s ->
    exists T, E = T :: E' /\ IEnv G E' /\ ITy E' A T /\ s = rshift.
Proof. inversion 1; subst; eauto 10. Qed.

(* =====================================================================
   2. A normal type whose interpretation is a universe IS a universe.
   ===================================================================== *)

Lemma TyOk_ITy_U E G i A br bl
  : TyOk G i A -> ITy E A (rt_U br bl) ->
    exists r l, A = oU G r l /\ ErRel r br /\ ErLvl l bl.
Proof.
  intros Hty HI; inversion Hty; subst.
  - apply ITy_U_inv in HI.
    destruct HI as [br0 [bl0 [Heq [_ [Hr Hl]]]]].
    injection Heq as -> ->.
    eauto 10.
  - apply ITy_El_inv in HI.
    destruct HI as [br0 [bl0 [n0 [Heq _]]]]; discriminate Heq.
Qed.

(* =====================================================================
   3. [WknU_shape]: the universe-restricted [WknInj].

   Given a normal type [A] over [G] whose weakening to [ext G j B] is
   provably equal to the universe [oU (ext G j B) r l], [A] is [oU G r l]
   -- the SAME [r] and [l].  Unconditional: no induction, no appeal to
   type injectivity at any environment.

   This is the single fact that the design's [WknInj] wall reduces to,
   because the only variables a CODE can contain are universe-typed.
   ===================================================================== *)

Lemma WknU_shape G j B i A r l
  : TyOk G i A ->
    eqt (sTy (oExt G j B) i)
        (oTySubst (oExt G j B) G (oWkn G j B) i A)
        (oU (oExt G j B) r l) ->
    A = oU G r l.
Proof.
  intros Hty Heq.
  destruct (rigid_ty Heq) as [Ex [Tx [HEx [Hsub Hu]]]].
  apply ITy_U_inv in Hu.
  destruct Hu as [br [bl [HTx [_ [Hr Hl]]]]]; subst Tx.
  apply ITy_subst_inv in Hsub.
  destruct Hsub as [E' [s [T0 [_ [HG' [Hs [HT0 HTeq]]]]]]].
  apply ISub_wkn_inv in Hs.
  destruct Hs as [T [HEeq [HGE [HTB Hsr]]]]; subst s.
  destruct T0 as [ br0 bl0 | br0 bl0 n0 ]; cbn in HTeq; [ | discriminate ].
  injection HTeq as -> ->.
  destruct (TyOk_ITy_U Hty HT0) as [r0 [l0 [-> [Hr0 Hl0]]]].
  pose proof (ErRel_inj Hr0 Hr) as ->.
  pose proof (ErLvl_inj Hl0 Hl) as ->.
  reflexivity.
Qed.

(* =====================================================================
   4. Every normal-form judgement carries its environment's [EnvOk].
   ===================================================================== *)

Lemma Nf_EnvOk :
  (forall G, EnvOk G -> True)
  /\ (forall G i A, TyOk G i A -> EnvOk G)
  /\ (forall G r l c, NfCode G r l c -> EnvOk G)
  /\ (forall G i A x, VarT G i A x -> EnvOk G)
  /\ (forall G i A e, NeET G i A e -> EnvOk G)
  /\ (forall G i A e, NfET G i A e -> EnvOk G).
Proof.
  apply Nf_mutind; intros; try exact I; try assumption;
    try (econstructor; eassumption).
Qed.

Definition TyOk_EnvOk := proj1 (proj2 Nf_EnvOk).
Definition NfCode_EnvOk := proj1 (proj2 (proj2 Nf_EnvOk)).
Definition VarT_EnvOk := proj1 (proj2 (proj2 (proj2 Nf_EnvOk))).

(* =====================================================================
   5. The seam: erasure and interpretation, in one induction.

   For a normal object over a normal environment, DttErase.v's syntactic
   erasure and DttRigid.v's semantic interpretation are produced together,
   at the SAME [renv] and with the SAME image.  Doing both in one
   induction is what keeps the two systems' environment indices in step;
   proving them separately and matching afterwards would need exactly the
   agreement being proved.

   The variable clause carries the side condition that the named type is
   a universe -- which is where [ICode] lives (a variable of an [El] type
   is not a code) and is exactly the shape [nfcode_var] hands over.
   ===================================================================== *)

Lemma Nf_ErI :
  (forall G, EnvOk G -> exists E, ErEnv G E /\ IEnv G E)
  /\ (forall G i A, TyOk G i A ->
        forall E, ErEnv G E -> IEnv G E ->
          exists T, ErTy E G i A T /\ ITy E A T)
  /\ (forall G r l c, NfCode G r l c ->
        forall E, ErEnv G E -> IEnv G E ->
          exists n, ErCode E G r l c n /\ ICode E c n)
  /\ (forall G i A x, VarT G i A x ->
        forall r l, A = oU G r l ->
        forall E, ErEnv G E -> IEnv G E ->
          exists k, ErVar E G i A x k /\ ICode E x (rc_var k))
  /\ (forall G i A e, NeET G i A e -> True)
  /\ (forall G i A e, NfET G i A e -> True).
Proof.
  apply Nf_mutind; try (intros; exact I).
  (* envok_emp *)
  - exists (@nil rty); split; constructor.
  (* envok_ext *)
  - intros G i A HG IHG HA IHA.
    destruct IHG as [E [HEr HI]].
    destruct (IHA E HEr HI) as [T [HTr HTi]].
    exists (T :: E); split; econstructor; eassumption.
  (* tyok_U *)
  - intros G r l HG IHG Hr Hl E HEr HI.
    destruct (RelNf_ErRel Hr) as [br Hbr].
    destruct (LvlNf_ErLvl Hl) as [bl Hbl].
    exists (rt_U br bl); split; econstructor; eassumption.
  (* tyok_El *)
  - intros G r l c Hc IHc E HEr HI.
    destruct (NfCode_nf_indices Hc) as [Hr Hl].
    destruct (RelNf_ErRel Hr) as [br Hbr].
    destruct (LvlNf_ErLvl Hl) as [bl Hbl].
    destruct (IHc E HEr HI) as [n [Hnr Hni]].
    exists (rt_El br bl n); split; econstructor; eassumption.
  (* nfcode_nat *)
  - intros G HG IHG E HEr HI.
    exists rc_nat; split; econstructor; eassumption.
  (* nfcode_empty *)
  - intros G HG IHG E HEr HI.
    exists rc_empty; split; econstructor; eassumption.
  (* nfcode_pi_rel *)
  - intros G rF lF lG F B HrF HlF HlG HF IHF HB IHB E HEr HI.
    destruct (RelNf_ErRel HrF) as [brF HbrF].
    destruct (LvlNf_ErLvl HlF) as [blF HblF].
    destruct (IHF E HEr HI) as [nF [HnFr HnFi]].
    destruct (IHB (rt_El brF blF nF :: E)
                (ErEnv_extC HEr HbrF HblF HnFr)
                (IEnv_extC HI HbrF HblF HnFi)) as [nB [HnBr HnBi]].
    exists (rc_pi true brF blF nF nB); split; econstructor; eassumption.
  (* nfcode_pi_irr *)
  - intros G rF lF F B HrF HlF HF IHF HB IHB E HEr HI.
    destruct (RelNf_ErRel HrF) as [brF HbrF].
    destruct (LvlNf_ErLvl HlF) as [blF HblF].
    destruct (IHF E HEr HI) as [nF [HnFr HnFi]].
    destruct (IHB (rt_El brF blF nF :: E)
                (ErEnv_extC HEr HbrF HblF HnFr)
                (IEnv_extC HI HbrF HblF HnFi)) as [nB [HnBr HnBi]].
    exists (rc_pi false brF blF nF nB); split; econstructor; eassumption.
  (* nfcode_var *)
  - intros G r l c Hv IHv E HEr HI.
    destruct (IHv r l eq_refl E HEr HI) as [k [Hkr Hki]].
    exists (rc_var k); split; [ constructor | ]; assumption.
  (* vart_hd *)
  - intros G i A A' HG IHG HA IHA HA' IHA' Heq r l HA'eq E HEr HI.
    subst A'.
    pose proof (WknU_shape HA Heq) as HAeq; subst A.
    apply ErEnv_ext_inv in HEr.
    destruct HEr as [T [E0 [HEeq [HErG HTr]]]]; subst E.
    apply IEnv_ext_inv in HI.
    destruct HI as [T' [E0' [HEeq' [HIG HTi]]]].
    injection HEeq' as HTT HEE; subst T' E0'.
    apply ITy_U_inv in HTi.
    destruct HTi as [br [bl [HTeq [_ [Hbr Hbl]]]]]; subst T.
    exists 0; split.
    + econstructor; eassumption.
    + econstructor; [ eassumption | ].
      econstructor; eassumption.
  (* vart_wkn *)
  - intros G i A x j B A' Hx IHx HB IHB HA' IHA' Heq r l HA'eq E HEr HI.
    subst A'.
    pose proof (WknU_shape (VarT_TyOk Hx) Heq) as HAeq; subst A.
    apply ErEnv_ext_inv in HEr.
    destruct HEr as [TB [E0 [HEeq [HErG HTr]]]]; subst E.
    pose proof HI as HIfull.
    apply IEnv_ext_inv in HI.
    destruct HI as [T' [E0' [HEeq' [HIG HTi]]]].
    injection HEeq' as HTT HEE; subst T' E0'.
    destruct (IHx r l eq_refl E0 HErG HIG) as [k [Hkr Hki]].
    exists (S k); split.
    + econstructor; eassumption.
    + change (rc_var (S k)) with (csub rshift (rc_var k)).
      eapply icode_subst; try eassumption.
      econstructor; eassumption.
Qed.

Definition EnvOk_ErI := proj1 Nf_ErI.
Definition TyOk_ErI := proj1 (proj2 Nf_ErI).
Definition NfCode_ErI := proj1 (proj2 (proj2 Nf_ErI)).

(* =====================================================================
   6. DttErase.v's section 8, hypothesis-free.

   The proofs are DttErase.v's, with the [WknInj] application in the
   variable case replaced by [WknU_shape].  The variable statement has to
   be specialized to a universe-typed variable to make that replacement
   legal -- which costs nothing, since that is the only instance the code
   theorem uses.
   ===================================================================== *)

Theorem VarTU_erase_inj :
  forall k E G r l x1 x2,
    VarT G (iCode l) (oU G r l) x1 -> VarT G (iCode l) (oU G r l) x2 ->
    ErVar E G (iCode l) (oU G r l) x1 k ->
    ErVar E G (iCode l) (oU G r l) x2 k ->
    x1 = x2.
Proof.
  induction k; intros E G r l x1 x2 Hv1 Hv2 He1 He2.
  - (* index 0: the head variable is determined by the environment *)
    apply ErVar_0_inv in He1.
    destruct He1 as [G0 [i0 [A0 [T [E0 [_ [HGx [_ Hx1]]]]]]]]; subst.
    apply ErVar_0_inv in He2.
    destruct He2 as [G0' [i0' [A0' [T' [E0' [_ [HGx' [_ Hx2]]]]]]]]; subst.
    inversion HGx'; subst.
    reflexivity.
  - (* index k+1: the named type of the inner variable is a universe *)
    apply ErVar_S_inv in He1.
    destruct He1 as [G0 [j [B [A1 [y1 [TB [E0 [HEa [HGx [Hx1 Hi1]]]]]]]]]]; subst.
    apply ErVar_S_inv in He2.
    destruct He2 as [G0' [j' [B' [A2 [y2 [TB' [E0' [HEb [HGx' [Hx2 Hi2]]]]]]]]]].
    inversion HGx'; inversion HEb; subst.
    apply VarT_wkn_inv in Hv1; destruct Hv1 as [_ [_ [Hin1 [_ Heq1]]]].
    apply VarT_wkn_inv in Hv2; destruct Hv2 as [_ [_ [Hin2 [_ Heq2]]]].
    pose proof (WknU_shape (VarT_TyOk Hin1) Heq1) as HA1; subst A1.
    pose proof (WknU_shape (VarT_TyOk Hin2) Heq2) as HA2; subst A2.
    pose proof (IHk _ _ _ _ _ _ Hin1 Hin2 Hi1 Hi2) as ->.
    reflexivity.
Qed.

Theorem NfCode_erase_inj_u :
  forall n E G r l c1 c2,
    NfCode G r l c1 -> NfCode G r l c2 ->
    ErCode E G r l c1 n -> ErCode E G r l c2 n ->
    c1 = c2.
Proof.
  induction n as [ k | | | b brF blF nF IHF nB IHB ];
    intros E G r l c1 c2 Hc1 Hc2 He1 He2.
  - (* rc_var: both codes are variables of the SAME universe type *)
    apply ErCode_var_inv in He1; apply ErCode_var_inv in He2.
    pose proof (NfCode_of_var Hc1 He1) as Hv1.
    pose proof (NfCode_of_var Hc2 He2) as Hv2.
    eapply VarTU_erase_inj; eassumption.
  - (* rc_nat *)
    apply ErCode_nat_inv in He1; destruct He1 as [_ [_ ->]].
    apply ErCode_nat_inv in He2; destruct He2 as [_ [_ ->]].
    reflexivity.
  - (* rc_empty *)
    apply ErCode_empty_inv in He1; destruct He1 as [_ [_ ->]].
    apply ErCode_empty_inv in He2; destruct He2 as [_ [_ ->]].
    reflexivity.
  - destruct b.
    + (* Pi_rel *)
      apply ErCode_pi_true_inv in He1.
      destruct He1 as [rF1 [lF1 [F1 [B1 [Hr1 [Hc1e [HrF1 [HlF1 [HF1 HB1]]]]]]]]].
      apply ErCode_pi_true_inv in He2.
      destruct He2 as [rF2 [lF2 [F2 [B2 [Hr2 [Hc2e [HrF2 [HlF2 [HF2 HB2]]]]]]]]].
      subst.
      pose proof (ErRel_inj HrF1 HrF2) as ?; subst.
      pose proof (ErLvl_inj HlF1 HlF2) as ?; subst.
      apply NfCode_pi_rel_inv in Hc1; destruct Hc1 as [_ [_ [HNF1 HNB1]]].
      apply NfCode_pi_rel_inv in Hc2; destruct Hc2 as [_ [_ [HNF2 HNB2]]].
      pose proof (IHF _ _ _ _ _ _ HNF1 HNF2 HF1 HF2) as ?; subst.
      pose proof (IHB _ _ _ _ _ _ HNB1 HNB2 HB1 HB2) as ?; subst.
      reflexivity.
    + (* Pi_irr *)
      apply ErCode_pi_false_inv in He1.
      destruct He1 as [rF1 [lF1 [F1 [B1 [Hr1 [Hl1 [Hc1e [HrF1 [HlF1 [HF1 HB1]]]]]]]]]].
      apply ErCode_pi_false_inv in He2.
      destruct He2 as [rF2 [lF2 [F2 [B2 [Hr2 [Hl2 [Hc2e [HrF2 [HlF2 [HF2 HB2]]]]]]]]]].
      subst.
      pose proof (ErRel_inj HrF1 HrF2) as ?; subst.
      pose proof (ErLvl_inj HlF1 HlF2) as ?; subst.
      apply NfCode_pi_irr_inv in Hc1; destruct Hc1 as [_ [_ [HNF1 HNB1]]].
      apply NfCode_pi_irr_inv in Hc2; destruct Hc2 as [_ [_ [HNF2 HNB2]]].
      pose proof (IHF _ _ _ _ _ _ HNF1 HNF2 HF1 HF2) as ?; subst.
      pose proof (IHB _ _ _ _ _ _ HNB1 HNB2 HB1 HB2) as ?; subst.
      reflexivity.
Qed.

Theorem TyOk_erase_inj_u E G i1 A1 i2 A2 T
  : TyOk G i1 A1 -> TyOk G i2 A2 ->
    ErTy E G i1 A1 T -> ErTy E G i2 A2 T ->
    i1 = i2 /\ A1 = A2.
Proof.
  intros Ht1 Ht2 He1 He2.
  destruct T as [ br bl | br bl n ].
  - apply ErTy_U_inv in He1; destruct He1 as [r1 [l1 [-> [-> [Hr1 Hl1]]]]].
    apply ErTy_U_inv in He2; destruct He2 as [r2 [l2 [-> [-> [Hr2 Hl2]]]]].
    pose proof (ErRel_inj Hr1 Hr2) as ?; subst.
    pose proof (ErLvl_inj Hl1 Hl2) as ?; subst.
    split; reflexivity.
  - apply ErTy_El_inv in He1;
      destruct He1 as [r1 [l1 [cc1 [-> [-> [Hr1 [Hl1 Hc1]]]]]]].
    apply ErTy_El_inv in He2;
      destruct He2 as [r2 [l2 [cc2 [-> [-> [Hr2 [Hl2 Hc2]]]]]]].
    pose proof (ErRel_inj Hr1 Hr2) as ?; subst.
    pose proof (ErLvl_inj Hl1 Hl2) as ?; subst.
    apply TyOk_El_inv in Ht1; destruct Ht1 as [_ HN1].
    apply TyOk_El_inv in Ht2; destruct Ht2 as [_ HN2].
    pose proof (NfCode_erase_inj_u HN1 HN2 Hc1 Hc2) as ?; subst.
    split; reflexivity.
Qed.

Theorem EnvOk_erase_inj_u :
  forall E G1 G2, EnvOk G1 -> EnvOk G2 -> ErEnv G1 E -> ErEnv G2 E -> G1 = G2.
Proof.
  induction E as [ | T E IHE ]; intros G1 G2 H1 H2 He1 He2.
  - apply ErEnv_nil_inv in He1; apply ErEnv_nil_inv in He2; subst; reflexivity.
  - apply ErEnv_cons_inv in He1;
      destruct He1 as [Ga [ia [Aa [-> [HEa HTa]]]]].
    apply ErEnv_cons_inv in He2;
      destruct He2 as [Gb [ib [Ab [-> [HEb HTb]]]]].
    apply EnvOk_ext_inv in H1; destruct H1 as [HOa HTya].
    apply EnvOk_ext_inv in H2; destruct H2 as [HOb HTyb].
    pose proof (IHE _ _ HOa HOb HEa HEb) as ?; subst.
    destruct (TyOk_erase_inj_u HTya HTyb HTa HTb) as [? ?]; subst.
    reflexivity.
Qed.

(* =====================================================================
   7. The exported theorems.

   Each is: read the equation through the rigid model to get a COMMON
   interpretation; produce the erasure of each normal form together with
   its interpretation (section 5); identify the two by functionality of
   the interpretation (DttRigid.v section 5); conclude by section 6.
   ===================================================================== *)

Theorem NfCode_inj G r l c1 c2 :
  NfCode G r l c1 -> NfCode G r l c2 ->
  eq_term ott_dtt [] (sCode G r l) c1 c2 -> c1 = c2.
Proof.
  intros Hc1 Hc2 Heq.
  destruct (rigid_code Heq) as [E [n [HIG [HI1 HI2]]]].
  destruct (EnvOk_ErI (NfCode_EnvOk Hc1)) as [E0 [HEr0 HI0]].
  pose proof (IEnv_fun HI0 HIG) as ?; subst E0.
  destruct (NfCode_ErI Hc1 HEr0 HI0) as [n1 [Hn1r Hn1i]].
  destruct (NfCode_ErI Hc2 HEr0 HI0) as [n2 [Hn2r Hn2i]].
  destruct (ICode_fun Hn1i HI1) as [_ ?]; subst n1.
  destruct (ICode_fun Hn2i HI2) as [_ ?]; subst n2.
  eapply NfCode_erase_inj_u; eassumption.
Qed.

Theorem TyOk_inj G i A1 A2 :
  TyOk G i A1 -> TyOk G i A2 -> eq_term ott_dtt [] (sTy G i) A1 A2 -> A1 = A2.
Proof.
  intros Ht1 Ht2 Heq.
  destruct (rigid_ty Heq) as [E [T [HIG [HI1 HI2]]]].
  destruct (EnvOk_ErI (TyOk_EnvOk Ht1)) as [E0 [HEr0 HI0]].
  pose proof (IEnv_fun HI0 HIG) as ?; subst E0.
  destruct (TyOk_ErI Ht1 HEr0 HI0) as [T1 [HT1r HT1i]].
  destruct (TyOk_ErI Ht2 HEr0 HI0) as [T2 [HT2r HT2i]].
  destruct (ITy_fun HT1i HI1) as [_ ?]; subst T1.
  destruct (ITy_fun HT2i HI2) as [_ ?]; subst T2.
  destruct (TyOk_erase_inj_u Ht1 Ht2 HT1r HT2r) as [_ ?]; assumption.
Qed.

Theorem EnvOk_inj G1 G2 :
  EnvOk G1 -> EnvOk G2 -> eq_term ott_dtt [] sEnv G1 G2 -> G1 = G2.
Proof.
  intros H1 H2 Heq.
  destruct (rigid_env Heq) as [E [HI1 HI2]].
  destruct (EnvOk_ErI H1) as [E1 [HEr1 HIa]].
  destruct (EnvOk_ErI H2) as [E2 [HEr2 HIb]].
  pose proof (IEnv_fun HIa HI1) as ?; subst E1.
  pose proof (IEnv_fun HIb HI2) as ?; subst E2.
  eapply EnvOk_erase_inj_u; eassumption.
Qed.

(* =====================================================================
   8. [WknInj] as a corollary.

   With the three theorems in hand, DttErase.v's own hypothesis is
   discharged, so its injectivity theorems ([VarT_erase_inj] at an
   ARBITRARY named type, [EnvOk_erase_inj], ...) become available.  Note
   the direction of the dependency: nothing above uses this.
   ===================================================================== *)

Theorem WknInj_holds : WknInj.
Proof.
  intros G j B i1 A1 i2 A2 A' Ht1 Ht2 Heq1 Heq2.
  destruct (rigid_ty Heq1) as [Ex [Tx [HEx [Hs1 Hu1]]]].
  destruct (rigid_ty Heq2) as [Ey [Ty [HEy [Hs2 Hu2]]]].
  destruct (ITy_fun Hu1 Hu2) as [? ?]; subst Ey Ty.
  apply ITy_subst_inv in Hs1.
  destruct Hs1 as [E1 [s1 [T1 [_ [HG1 [Hw1 [HT1 HTx1]]]]]]].
  apply ITy_subst_inv in Hs2.
  destruct Hs2 as [E2 [s2 [T2 [_ [HG2 [Hw2 [HT2 HTx2]]]]]]].
  apply ISub_wkn_inv in Hw1; destruct Hw1 as [Ta [_ [_ [_ ->]]]].
  apply ISub_wkn_inv in Hw2; destruct Hw2 as [Tb [_ [_ [_ ->]]]].
  pose proof (IEnv_fun HG1 HG2) as ?; subst E2.
  rewrite HTx1 in HTx2.
  pose proof (tsub_shift_inj _ _ HTx2) as Hteq; subst T2.
  destruct (EnvOk_ErI (TyOk_EnvOk Ht1)) as [E0 [HEr0 HI0]].
  pose proof (IEnv_fun HI0 HG1) as ?; subst E0.
  destruct (TyOk_ErI Ht1 HEr0 HI0) as [Ta1 [HTa1r HTa1i]].
  destruct (TyOk_ErI Ht2 HEr0 HI0) as [Ta2 [HTa2r HTa2i]].
  destruct (ITy_fun HTa1i HT1) as [_ ?]; subst Ta1.
  destruct (ITy_fun HTa2i HT2) as [_ ?]; subst Ta2.
  destruct (TyOk_erase_inj_u Ht1 Ht2 HTa1r HTa2r) as [_ ?]; assumption.
Qed.
