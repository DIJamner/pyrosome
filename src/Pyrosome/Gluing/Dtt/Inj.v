Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.NormalForms
  Pyrosome.Gluing.Dtt.NfTyping Pyrosome.Gluing.Dtt.Rigid
  Pyrosome.Gluing.Dtt.RigidOk.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 0.5c: CODE RIGIDITY, ASSEMBLED.

   The three theorems Layer 0.5 exports:

     NfCode_inj : normal codes are determined by provable equality
     TyOk_inj   : normal types are determined by provable equality
     EnvOk_inj  : normal environments are determined by provable equality

   src/Pyrosome/Gluing/Dtt/Rigid.v + src/Pyrosome/Gluing/Dtt/RigidOk.v
   supply the semantic input, in exactly the form these theorems want:
   [rigid_env]/[rigid_ty]/[rigid_code] read a provable equation as a
   COMMON interpretation of the two sides, e.g.

     Req_code G e1 e2 := exists E n, IEnv G E /\ ICode E e1 n /\ ICode E e2 n.

   So injectivity is stated over the model's own relations [ICode]/[ITy]/
   [IEnv] -- two normal objects with the SAME interpretation at the SAME
   [renv] are syntactically equal -- and the export is then two lines,
   with nothing to construct.  In particular there is no second erasure
   system, no totality lemma, and no index alignment: the model has
   already chosen the [renv], and both sides are already interpreted at
   it.

   The only thing in the argument that is not routine is the variable
   case: [VarT] (NormalForms.v) NAMES the normal representative of a
   weakened type and pins it only by an [eq_term] premise, so the
   index-[k+1] variable term CONTAINS the named representative of the
   index-[k] one, and injectivity on variables is uniqueness of that
   naming.  That is settled by

     THE UNIVERSE OBSERVATION.  The named type a code variable carries is
     always a UNIVERSE -- a code variable's type is [oU G r l] and nothing
     else.  And at a universe, uniqueness of the naming is
     UNCONDITIONAL: a normal type over [G] whose weakening is provably
     equal to [oU (oExt G j B) r l] is syntactically [oU G r l], with the
     SAME [r] and [l].  There is no recursion at all.

   So the file is linear:

     1.  Inversions for the interpretation relations of Rigid.v.
     2.  [TyOk_ITy_U] -- a normal type interpreted as a universe IS one.
     3.  [WknU_shape] -- uniqueness of the naming, at a universe.
     4.  Variables: their interpretation is a de Bruijn index
         ([VarT_ICode_var]), and a weakened one is a successor over the
         tail of the [renv] ([ICode_wkn_var]).
     5.  [VarTU_I_inj] / [NfCode_I_inj] / [TyOk_I_inj] / [EnvOk_I_inj] --
         injectivity, by induction on the de Bruijn index, on the
         interpreted code, and on the [renv] respectively.
     6.  The three exported theorems, plus the info-general
         [TyOk_inj_gen] of which [TyOk_inj] is the corollary.

   Zero axioms, zero admits.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* =====================================================================
   1. Inversions for [IEnv] / [ITy] / [ICode] / [ISub].

   All of them are one [inversion] away; stating them keeps every proof
   below free of generated hypothesis names.  The [IEnv] pair is inverted
   on the shape of the [renv], the rest on the shape of the SUBJECT term.
   ===================================================================== *)

Lemma IEnv_nil_inv G : IEnv G [] -> G = oEmp.
Proof. inversion 1; reflexivity. Qed.

Lemma IEnv_cons_inv G T E
  : IEnv G (T :: E) -> exists G0 i A, G = oExt G0 i A /\ IEnv G0 E /\ ITy E A T.
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

Lemma ICode_hd_inv E G i A n : ICode E (oHd G i A) n -> n = rc_var 0.
Proof. inversion 1; subst; reflexivity. Qed.

(* NB the image here is [csub s n0], NOT a constructor pattern: the
   [icode_subst] clause applies the interpreted substitution.  That is why
   the shape of a variable's interpretation needs section 4 rather than an
   inversion. *)
Lemma ICode_subst_inv E G G' g i A v n
  : ICode E (oExpSubst G G' g i A v) n ->
    exists E' s n0, ISub E E' g s /\ ICode E' v n0 /\ n = csub s n0.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ICode_nat_inv E G0 n : ICode E (oNat G0) n -> n = rc_nat.
Proof. inversion 1; subst; reflexivity. Qed.

Lemma ICode_empty_inv E G0 n : ICode E (oEmpty G0) n -> n = rc_empty.
Proof. inversion 1; subst; reflexivity. Qed.

Lemma ICode_pi_rel_inv E G0 rF lF lG F B n
  : ICode E (oPiRel G0 rF lF lG F B) n ->
    exists brF blF nF nB,
      n = rc_pi true brF blF nF nB /\ ErRel rF brF /\ ErLvl lF blF
      /\ ICode E F nF /\ ICode (rt_El brF blF nF :: E) B nB.
Proof. inversion 1; subst; eauto 20. Qed.

Lemma ICode_pi_irr_inv E G0 rF lF F B n
  : ICode E (oPiIrr G0 rF lF F B) n ->
    exists brF blF nF nB,
      n = rc_pi false brF blF nF nB /\ ErRel rF brF /\ ErLvl lF blF
      /\ ICode E F nF /\ ICode (rt_El brF blF nF :: E) B nB.
Proof. inversion 1; subst; eauto 20. Qed.

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
   3. [WknU_shape]: uniqueness of the naming, at a universe.

   Given a normal type [A] over [G] whose weakening to [oExt G j B] is
   provably equal to the universe [oU (oExt G j B) r l], [A] is [oU G r l]
   -- the SAME [r] and [l].  Unconditional: no induction, no appeal to
   type injectivity at any environment.

   This is the whole of what the variable case needs, because the only
   variables a CODE can contain are universe-typed.
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
   4. Variables interpret to de Bruijn indices.

   [ICode]'s [icode_subst] clause produces [csub s n0], which is not a
   constructor pattern, so the shape of a variable's interpretation is not
   read off by inversion alone -- it needs the induction below.  These two
   lemmas are the whole of that cost.
   ===================================================================== *)

Lemma VarT_ICode_var G i A x (H : VarT G i A x)
  : forall E n, ICode E x n -> exists k, n = rc_var k.
Proof.
  induction H; intros E n HI.
  - apply ICode_hd_inv in HI; eauto.
  - apply ICode_subst_inv in HI.
    destruct HI as [E' [s [n0 [Hs [Hn0 ->]]]]].
    apply ISub_wkn_inv in Hs; destruct Hs as [T [-> [_ [_ ->]]]].
    destruct (IHVarT _ _ Hn0) as [k ->].
    exists (S k); reflexivity.
Qed.

(* The subject of a [VarT] is an [oHd] or a [wkn]-substituted variable. *)
Lemma VarT_shape G i A x : VarT G i A x ->
  (exists G0 i0 A0, x = oHd G0 i0 A0)
  \/ (exists G0 j B i0 A0 y,
         x = oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y).
Proof. destruct 1; [ left | right ]; eauto 10. Qed.

(* A weakened variable interprets to a SUCCESSOR, over the tail of [E]. *)
Lemma ICode_wkn_var G0 j B i0 A0 y E k
  : VarT G0 i0 A0 y ->
    ICode E (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y) (rc_var k) ->
    exists k0 E0 T, k = S k0 /\ E = T :: E0 /\ ICode E0 y (rc_var k0).
Proof.
  intros Hv Hi.
  apply ICode_subst_inv in Hi.
  destruct Hi as [E' [s [n0 [Hs [Hn0 Heq]]]]].
  apply ISub_wkn_inv in Hs; destruct Hs as [T [HE [_ [_ ->]]]].
  destruct (VarT_ICode_var Hv Hn0) as [k0 ->].
  cbn in Heq; safe_invert Heq.
  exists k0, E', T; repeat split; assumption.
Qed.

(* =====================================================================
   5. Injectivity, over the interpretation relations.

   Order: variables first (induction on the de Bruijn INDEX), then codes
   (induction on the interpreted code), then types (one case analysis) and
   environments (induction on the [renv]).
   ===================================================================== *)

(* Variables, at a universe type.  That is the only form the code-level
   theorem needs -- a code variable's type is [oU G r l], whose [r] and
   [l] the statement of [NfCode_I_inj] fixes -- and it is the form whose
   naming is settled by [WknU_shape].

   Index 0 is settled by the ambient environment's own syntax; index k+1
   is where [WknU_shape] is spent. *)
Theorem VarTU_I_inj :
  forall k E G r l x1 x2,
    VarT G (iCode l) (oU G r l) x1 -> VarT G (iCode l) (oU G r l) x2 ->
    ICode E x1 (rc_var k) -> ICode E x2 (rc_var k) -> x1 = x2.
Proof.
  induction k; intros E G r l x1 x2 Hv1 Hv2 Hi1 Hi2;
    destruct (VarT_shape Hv1) as [ [Ga [ia [Aa ->]]]
                                 | [Ga [ja [Ba [ia [Aa [ya ->]]]]]] ];
    destruct (VarT_shape Hv2) as [ [Gb [ib [Ab ->]]]
                                 | [Gb [jb [Bb [ib [Ab [yb ->]]]]]] ].
  - (* 0: hd / hd -- the ambient environment determines the head *)
    apply VarT_hd_inv in Hv1; destruct Hv1 as [-> _].
    apply VarT_hd_inv in Hv2; destruct Hv2 as [Heq _].
    unfold oExt in Heq; safe_invert Heq; reflexivity.
  - (* 0: hd / wkn -- a weakening never interprets to index 0 *)
    apply VarT_wkn_inv in Hv2; destruct Hv2 as [_ [_ [Hin2 _]]].
    destruct (ICode_wkn_var Hin2 Hi2) as [? [? [? [Habs _]]]]; discriminate.
  - apply VarT_wkn_inv in Hv1; destruct Hv1 as [_ [_ [Hin1 _]]].
    destruct (ICode_wkn_var Hin1 Hi1) as [? [? [? [Habs _]]]]; discriminate.
  - apply VarT_wkn_inv in Hv1; destruct Hv1 as [_ [_ [Hin1 _]]].
    destruct (ICode_wkn_var Hin1 Hi1) as [? [? [? [Habs _]]]]; discriminate.
  - (* S k: hd / hd -- [hd] never interprets to a successor *)
    apply ICode_hd_inv in Hi1; discriminate.
  - apply ICode_hd_inv in Hi1; discriminate.
  - apply ICode_hd_inv in Hi2; discriminate.
  - (* S k: wkn / wkn -- the named types are universes by [WknU_shape],
       and the inner variables agree by the induction hypothesis *)
    apply VarT_wkn_inv in Hv1; destruct Hv1 as [HGa [Hia [Hin1 [_ Heq1]]]].
    apply VarT_wkn_inv in Hv2; destruct Hv2 as [HGb [Hib [Hin2 [_ Heq2]]]].
    subst G; unfold oExt in HGb; safe_invert HGb.
    subst.
    pose proof (WknU_shape (VarT_TyOk Hin1) Heq1) as ->.
    pose proof (WknU_shape (VarT_TyOk Hin2) Heq2) as ->.
    f_equal.
    destruct (ICode_wkn_var Hin1 Hi1) as [ka [Ea [Ta [Hka [HEa Ha]]]]].
    subst E.
    destruct (ICode_wkn_var Hin2 Hi2) as [kb [Eb [Tb [Hkb [HEb Hb]]]]].
    safe_invert HEb; safe_invert Hka; safe_invert Hkb.
    eapply IHk; eassumption.
Qed.

(* A canonical code never interprets to a variable's index. *)
Ltac kill_var Hi :=
  match goal with
  | Hv : VarT _ _ _ _ |- _ =>
      let k := fresh in let Habs := fresh in
      destruct (VarT_ICode_var Hv Hi) as [k Habs]; discriminate
  end.

(* Codes.  The [Pi] clauses need nothing about variables: the domain's
   relevance and level are recovered from the interpretation by
   [ErRel_inj]/[ErLvl_inj] (the design point of Rigid.v section 0), after
   which the two extended [renv]s are literally the same and the induction
   hypotheses apply. *)
Theorem NfCode_I_inj :
  forall n E G r l c1 c2,
    NfCode G r l c1 -> NfCode G r l c2 ->
    ICode E c1 n -> ICode E c2 n -> c1 = c2.
Proof.
  induction n as [ k | | | b brF blF nF IHF nB IHB ];
    intros E G r l c1 c2 Hc1 Hc2 Hi1 Hi2.
  - (* rc_var *)
    destruct Hc1; try (apply ICode_nat_inv in Hi1; discriminate);
      try (apply ICode_empty_inv in Hi1; discriminate);
      try (apply ICode_pi_rel_inv in Hi1;
           destruct Hi1 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (apply ICode_pi_irr_inv in Hi1;
           destruct Hi1 as [? [? [? [? [Habs _]]]]]; discriminate).
    destruct Hc2; try (apply ICode_nat_inv in Hi2; discriminate);
      try (apply ICode_empty_inv in Hi2; discriminate);
      try (apply ICode_pi_rel_inv in Hi2;
           destruct Hi2 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (apply ICode_pi_irr_inv in Hi2;
           destruct Hi2 as [? [? [? [? [Habs _]]]]]; discriminate).
    eapply VarTU_I_inj; eassumption.
  - (* rc_nat *)
    destruct Hc1; try (apply ICode_empty_inv in Hi1; discriminate);
      try (apply ICode_pi_rel_inv in Hi1;
           destruct Hi1 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (apply ICode_pi_irr_inv in Hi1;
           destruct Hi1 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (kill_var Hi1).
    destruct Hc2; try (apply ICode_empty_inv in Hi2; discriminate);
      try (apply ICode_pi_rel_inv in Hi2;
           destruct Hi2 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (apply ICode_pi_irr_inv in Hi2;
           destruct Hi2 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (kill_var Hi2).
    reflexivity.
  - (* rc_empty *)
    destruct Hc1; try (apply ICode_nat_inv in Hi1; discriminate);
      try (apply ICode_pi_rel_inv in Hi1;
           destruct Hi1 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (apply ICode_pi_irr_inv in Hi1;
           destruct Hi1 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (kill_var Hi1).
    destruct Hc2; try (apply ICode_nat_inv in Hi2; discriminate);
      try (apply ICode_pi_rel_inv in Hi2;
           destruct Hi2 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (apply ICode_pi_irr_inv in Hi2;
           destruct Hi2 as [? [? [? [? [Habs _]]]]]; discriminate);
      try (kill_var Hi2).
    reflexivity.
  - (* rc_pi *)
    destruct Hc1; try (apply ICode_nat_inv in Hi1; discriminate);
      try (apply ICode_empty_inv in Hi1; discriminate);
      try (kill_var Hi1).
    + (* pi_rel *)
      destruct Hc2; try (apply ICode_nat_inv in Hi2; discriminate);
        try (apply ICode_empty_inv in Hi2; discriminate);
        try (kill_var Hi2).
      * apply ICode_pi_rel_inv in Hi1.
        destruct Hi1 as [br1 [bl1 [n1 [m1 [Heq1 [Hr1 [Hl1 [HF1 HB1]]]]]]]].
        apply ICode_pi_rel_inv in Hi2.
        destruct Hi2 as [br2 [bl2 [n2 [m2 [Heq2 [Hr2 [Hl2 [HF2 HB2]]]]]]]].
        safe_invert Heq1; safe_invert Heq2.
        pose proof (ErRel_inj Hr1 Hr2) as ->.
        pose proof (ErLvl_inj Hl1 Hl2) as ->.
        pose proof (IHF _ _ _ _ _ _ Hc1_1 Hc2_1 HF1 HF2) as ->.
        pose proof (IHB _ _ _ _ _ _ Hc1_2 Hc2_2 HB1 HB2) as ->.
        reflexivity.
      * apply ICode_pi_rel_inv in Hi1.
        destruct Hi1 as [? [? [? [? [Heq1 _]]]]].
        apply ICode_pi_irr_inv in Hi2.
        destruct Hi2 as [? [? [? [? [Heq2 _]]]]].
        rewrite Heq1 in Heq2; discriminate.
    + (* pi_irr *)
      destruct Hc2; try (apply ICode_nat_inv in Hi2; discriminate);
        try (apply ICode_empty_inv in Hi2; discriminate);
        try (kill_var Hi2).
      * apply ICode_pi_irr_inv in Hi1.
        destruct Hi1 as [? [? [? [? [Heq1 _]]]]].
        apply ICode_pi_rel_inv in Hi2.
        destruct Hi2 as [? [? [? [? [Heq2 _]]]]].
        rewrite Heq1 in Heq2; discriminate.
      * apply ICode_pi_irr_inv in Hi1.
        destruct Hi1 as [br1 [bl1 [n1 [m1 [Heq1 [Hr1 [Hl1 [HF1 HB1]]]]]]]].
        apply ICode_pi_irr_inv in Hi2.
        destruct Hi2 as [br2 [bl2 [n2 [m2 [Heq2 [Hr2 [Hl2 [HF2 HB2]]]]]]]].
        safe_invert Heq1; safe_invert Heq2.
        pose proof (ErRel_inj Hr1 Hr2) as ->.
        pose proof (ErLvl_inj Hl1 Hl2) as ->.
        pose proof (IHF _ _ _ _ _ _ Hc1_1 Hc2_1 HF1 HF2) as ->.
        pose proof (IHB _ _ _ _ _ _ Hc1_2 Hc2_2 HB1 HB2) as ->.
        reflexivity.
Qed.

(* Types.  Also concludes that the two info indices agree, which
   [EnvOk_I_inj] needs. *)
Theorem TyOk_I_inj E G i1 A1 i2 A2 T
  : TyOk G i1 A1 -> TyOk G i2 A2 -> ITy E A1 T -> ITy E A2 T ->
    i1 = i2 /\ A1 = A2.
Proof.
  intros Ht1 Ht2 Hi1 Hi2.
  destruct Ht1 as [ G r1 l1 | G r1 l1 c1 ];
    destruct Ht2 as [ G r2 l2 | G r2 l2 c2 ].
  - apply ITy_U_inv in Hi1; destruct Hi1 as [br1 [bl1 [-> [_ [Hr1 Hl1]]]]].
    apply ITy_U_inv in Hi2; destruct Hi2 as [br2 [bl2 [Heq [_ [Hr2 Hl2]]]]].
    safe_invert Heq.
    pose proof (ErRel_inj Hr1 Hr2) as ->.
    pose proof (ErLvl_inj Hl1 Hl2) as ->.
    split; reflexivity.
  - apply ITy_U_inv in Hi1; destruct Hi1 as [? [? [-> _]]].
    apply ITy_El_inv in Hi2; destruct Hi2 as [? [? [? [Heq _]]]]; discriminate.
  - apply ITy_U_inv in Hi2; destruct Hi2 as [? [? [-> _]]].
    apply ITy_El_inv in Hi1; destruct Hi1 as [? [? [? [Heq _]]]]; discriminate.
  - apply ITy_El_inv in Hi1;
      destruct Hi1 as [br1 [bl1 [n1 [-> [_ [Hr1 [Hl1 Hc1]]]]]]].
    apply ITy_El_inv in Hi2;
      destruct Hi2 as [br2 [bl2 [n2 [Heq [_ [Hr2 [Hl2 Hc2]]]]]]].
    safe_invert Heq.
    pose proof (ErRel_inj Hr1 Hr2) as ->.
    pose proof (ErLvl_inj Hl1 Hl2) as ->.
    pose proof (NfCode_I_inj H H0 Hc1 Hc2) as ->.
    split; reflexivity.
Qed.

Theorem EnvOk_I_inj :
  forall E G1 G2, EnvOk G1 -> EnvOk G2 -> IEnv G1 E -> IEnv G2 E -> G1 = G2.
Proof.
  induction E as [ | T E IHE ]; intros G1 G2 H1 H2 Hi1 Hi2.
  - apply IEnv_nil_inv in Hi1; apply IEnv_nil_inv in Hi2; subst; reflexivity.
  - apply IEnv_cons_inv in Hi1;
      destruct Hi1 as [Ga [ia [Aa [-> [HEa HTa]]]]].
    apply IEnv_cons_inv in Hi2;
      destruct Hi2 as [Gb [ib [Ab [-> [HEb HTb]]]]].
    apply EnvOk_ext_inv in H1; destruct H1 as [HOa HTya].
    apply EnvOk_ext_inv in H2; destruct H2 as [HOb HTyb].
    pose proof (IHE _ _ HOa HOb HEa HEb) as ->.
    destruct (TyOk_I_inj HTya HTyb HTa HTb) as [-> ->].
    reflexivity.
Qed.

(* =====================================================================
   6. The exported theorems.

   Each is: read the equation through the rigid model, which hands back a
   COMMON interpretation of the two sides at a common [renv]; then apply
   section 5.  Nothing is constructed.
   ===================================================================== *)

Theorem NfCode_inj G r l c1 c2 :
  NfCode G r l c1 -> NfCode G r l c2 ->
  eq_term ott_dtt [] (sCode G r l) c1 c2 -> c1 = c2.
Proof.
  intros Hc1 Hc2 Heq.
  destruct (rigid_code Heq) as [E [n [_ [HI1 HI2]]]].
  eapply NfCode_I_inj; eassumption.
Qed.

(* The INFO-GENERAL form: the sort [j] at which the equation is read is
   unrelated to the infos [i1]/[i2] the two normal types are pinned at.
   [rceq_term] at a [ty] sort is [Req_ty G A1 A2], which does not mention
   the info at all, and the interpretation pins the infos anyway -- so
   there is nothing extra to do.  src/Pyrosome/Gluing/Dtt/LogRelFun.v needs
   this form; the info-fixed [TyOk_inj] below is its corollary. *)
Theorem TyOk_inj_gen G j i1 A1 i2 A2
  : TyOk G i1 A1 -> TyOk G i2 A2 ->
    eq_term ott_dtt [] (sTy G j) A1 A2 -> i1 = i2 /\ A1 = A2.
Proof.
  intros Ht1 Ht2 Heq.
  destruct (rigid_ty Heq) as [E [T [_ [HI1 HI2]]]].
  eapply TyOk_I_inj; eassumption.
Qed.

Theorem TyOk_inj G i A1 A2 :
  TyOk G i A1 -> TyOk G i A2 -> eq_term ott_dtt [] (sTy G i) A1 A2 -> A1 = A2.
Proof.
  intros Ht1 Ht2 Heq.
  destruct (TyOk_inj_gen Ht1 Ht2 Heq) as [_ ?]; assumption.
Qed.

Theorem EnvOk_inj G1 G2 :
  EnvOk G1 -> EnvOk G2 -> eq_term ott_dtt [] sEnv G1 G2 -> G1 = G2.
Proof.
  intros H1 H2 Heq.
  destruct (rigid_env Heq) as [E [HI1 HI2]].
  eapply EnvOk_I_inj; eassumption.
Qed.
