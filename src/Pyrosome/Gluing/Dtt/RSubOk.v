Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.NfWk Pyrosome.Gluing.Dtt.Inj Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelCand Pyrosome.Gluing.Dtt.LogRelFun
  Pyrosome.Gluing.Dtt.LogRelCore Pyrosome.Gluing.Dtt.RSub Pyrosome.Gluing.Dtt.Ceq Pyrosome.Gluing.Dtt.ModelStruct Pyrosome.Gluing.Dtt.ModelSound.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 3 (continued): the reducible-substitution
   toolkit.

   src/Pyrosome/Gluing/Dtt/RSub.v defines [RSub]/[RSubN] and their intro/elim interface.
   This file supplies the four closure properties every later layer needs
   -- identity, weakening, projection, lifting -- and cashes them in for
   the normalization statement for closed terms.

   TWO ADJUSTMENTS TO THE SPECIFIED STATEMENTS, both forced and both
   harmless downstream (see the report at the end of the file):

   (1) [RSub_wk] needs [EnvOk G] (normality of the CODOMAIN environment).
       [RSub] is a [Fixpoint] on the syntax of [G] and its entry clause is
       [RTmN D i (A[g0]) v], which is VACUOUS when [A[g0]] has no normal
       representative.  Weakening an entry means transporting it along
       [RTy_wk], and that consumes an actual [RTy] derivation -- i.e. a
       normal representative of [A[g0]] over [D].  The representative
       exists exactly when [A] is a normal type of [G] and [g] is a
       canonical substitution, which is [TyOk_subst] applied to the
       bridge [RSub_CSub] below.  [RSubN] carries [EnvOk] of its
       representative environment already, so the [RSubN] forms are
       unaffected.

   (2) [RSub_lift] is stated at [oLiftW] (src/Pyrosome/Gluing/Dtt/NfWk.v), the lift of a
       substitution over an ARBITRARY normal type together with a named
       normal representative [A'] of [A[g]] -- exactly the shape of
       [Wk_liftC]/[CSub_lift].  [RSub_liftC] then packages it at the
       [oExtC]/[NfCode] shape the binder rules use.  Note that the
       [oLift]-shaped statement (whose extended domain environment is
       [extC D rF lF (g[F])], NOT normal) is not the useful one: its
       entry obligation is vacuous there, so it carries no content.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ================================================================== *)
(* 1.  Well-typedness of a reducible substitution                      *)
(*                                                                     *)
(* Restated here rather than imported (src/Pyrosome/Gluing/Dtt/ModelStruct.v proves the  *)
(* same two lemmas for its own use, and this file must not depend on    *)
(* the model layer for them).                                          *)
(* ================================================================== *)

(* Both [RSub] clauses hand back an equation whose LEFT-hand side is [g]
   itself, so this needs no induction at all. *)
Lemma RSub_wf D G g : RSub D G g -> wft g (sSub D G).
Proof.
  intro H; apply RSub_inv in H
    as [[-> Hf] | [G0 [i [A [g0 [v [-> [Hs _]]]]]]]];
    eapply eqt_wf_l; eassumption.
Qed.

Lemma RSubN_wf D G g : RSubN D G g -> wft g (sSub D G).
Proof.
  intros [G0 (HG0 & Heq & HR)].
  apply RSub_wf in HR.
  eapply wf_term_conv; [ exact HR | ].
  apply sSub_cong;
    [ apply eq_term_refl; eapply wft_sub_dom; exact HR
    | apply eq_term_sym; exact Heq ].
Qed.

(* ================================================================== *)
(* 2.  An induction principle for [RSub]                               *)
(*                                                                     *)
(* [RSub] is a [Fixpoint] on the syntax of the codomain environment, so *)
(* it has no generated eliminator.  The recursion is on the third       *)
(* argument of an [ext]-shaped [con], hence bounded by the length of    *)
(* that spine; [envsize] is that length, and the principle below is     *)
(* strong induction on it.  Every later proof in this file that must    *)
(* traverse [G] goes through it.                                       *)
(* ================================================================== *)

Fixpoint envsize (G : term) : nat :=
  match G with
  | con _ [_; _; G0] => S (envsize G0)
  | _ => 0
  end.

Lemma envsize_ext G i A : envsize (oExt G i A) = S (envsize G).
Proof. reflexivity. Qed.

Lemma RSub_gen_ind (Q : term -> term -> term -> Prop)
  (Hemp : forall D g, eqt (sSub D oEmp) g (oForget D) -> Q D oEmp g)
  (Hext : forall D G0 i A g g0 v,
      eqt (sSub D (oExt G0 i A)) g (oSnoc D G0 i A g0 v) ->
      RSub D G0 g0 -> Q D G0 g0 ->
      RTmN D i (oTySubst D G0 g0 i A) v ->
      Q D (oExt G0 i A) g)
  : forall D G g, RSub D G g -> Q D G g.
Proof.
  assert (forall n D G g, envsize G <= n -> RSub D G g -> Q D G g) as Hn.
  { induction n as [ | n IH ]; intros D G g Hsz HR;
      apply RSub_inv in HR
        as [[-> Hf] | [G0 [i [A [g0 [v [-> [Hs [Hg0 Hv]]]]]]]]].
    - apply Hemp; exact Hf.
    - rewrite envsize_ext in Hsz; lia.
    - apply Hemp; exact Hf.
    - rewrite envsize_ext in Hsz.
      eapply Hext; try eassumption.
      apply IH; [ lia | exact Hg0 ]. }
  intros D G g HR; exact (Hn (envsize G) D G g (le_n _) HR).
Qed.

(* Inversion of [EnvOk] at an [ext]. *)
Lemma EnvOk_inv GG
  : EnvOk GG ->
    GG = oEmp \/ exists G i A, GG = oExt G i A /\ EnvOk G /\ TyOk G i A.
Proof.
  destruct 1 as [ | G i A HG HA ];
    [ left; reflexivity | right; exists G, i, A; repeat split; assumption ].
Qed.

Lemma EnvOk_ext_inv G i A : EnvOk (oExt G i A) -> EnvOk G /\ TyOk G i A.
Proof.
  intro H; apply EnvOk_inv in H as [ Habs | [G0 [i0 [A0 [Heq [HG HA]]]]]].
  - cbv [oEmp oExt] in Habs; discriminate.
  - cbv [oExt] in Heq; safe_invert Heq; split; assumption.
Qed.

(* ================================================================== *)
(* 3.  A reducible substitution is a canonical substitution            *)
(*                                                                     *)
(* [CSub] (src/Pyrosome/Gluing/Dtt/NfWk.v) is the syntactic class over which normal      *)
(* types and normal codes are closed under substitution.  Reducibility  *)
(* implies it: escape turns each [RTmN] entry into a well-typed term,   *)
(* and at a UNIVERSE-typed slot the candidate IS [HasNfCode], which is  *)
(* the one extra condition [csub_snoc] asks for.                        *)
(*                                                                     *)
(* This is what makes [RSub_wk] possible at all: it is the source of    *)
(* the normal representative of [A[g]] that [RTy_wk] needs.             *)
(* ================================================================== *)

Lemma RSub_CSub : forall D G g, RSub D G g -> EnvOk D -> EnvOk G -> CSub D G g.
Proof.
  apply (@RSub_gen_ind
    (fun D G g => EnvOk D -> EnvOk G -> CSub D G g)).
  - (* emp *)
    intros D g Hf HD _.
    eapply csub_conv with (g := oForget D);
      [ apply csub_forget; exact HD
      | eapply eqt_wf_l; exact Hf
      | exact Hf ].
  - (* ext *)
    intros D G0 i A g g0 v Hs Hg0 IH Hv HD HGE.
    destruct (EnvOk_ext_inv HGE) as [HG0 HA].
    assert (CSub D G0 g0) as HC0 by (apply IH; assumption).
    assert (wft i sInfo) as Hiw
      by (eapply wft_ty_info; apply TyOk_wf; exact HA).
    destruct (TyOk_subst HA HC0 HD) as [An [HAn HeqAn]].
    assert (RTm D i An v) as Hv0
      by (apply Hv; [ apply eq_term_refl; exact Hiw | exact HAn | exact HeqAn ]).
    destruct (RTyEx_of_TyOk HAn) as [P HP].
    assert (P v) as HPv by (eapply RTm_elim; eassumption).
    assert (wft v (sExp D i An)) as Hvw.
    { destruct (RTy_escape HP v HPv) as [n [_ Hn]]; eapply eqt_wf_l; exact Hn. }
    eapply csub_conv with (g := oSnoc D G0 i A g0 v);
      [ | eapply eqt_wf_l; exact Hs | exact Hs ].
    apply csub_snoc with (A' := An);
      [ exact HC0 | exact HD | exact HA | exact HAn | exact HeqAn | exact Hvw | ].
    intros r l HAneq.
    assert (i = iCode l) as Hi0
      by (eapply TyOk_U_info; [ exact HAn | exact HAneq ]).
    rewrite HAneq, Hi0 in HP.
    assert (P v <-> HasNfCode D r l v) as Hiff by (eapply RTy_U_e; exact HP).
    apply Hiff; exact HPv.
Qed.

(* ================================================================== *)
(* 4.  Reducibility of a variable entry                                *)
(*                                                                     *)
(* The head variable of an extended environment is where [RTy_reflect]  *)
(* is spent: it is a [VarT], hence a [NeET], hence in the candidate of  *)
(* its (normal) type; [RTmN_intro] then lifts that to the              *)
(* quantified-over-representatives form, which is legitimate because    *)
(* Layer 0.5's [TyOk_inj] makes the representative unique.              *)
(* ================================================================== *)

Lemma RTmN_of_VarT G i A x Ax
  : VarT G i A x -> eqt (sTy G i) Ax A -> RTmN G i Ax x.
Proof.
  intros Hx Heq.
  assert (TyOk G i A) as HT by (eapply VarT_TyOk; exact Hx).
  assert (wft i sInfo) as Hiw by (eapply wft_ty_info; apply TyOk_wf; exact HT).
  destruct (RTyEx_of_TyOk HT) as [P HP].
  eapply RTmN_intro with (i0 := i) (A0 := A) (P := P);
    [ apply eq_term_refl; exact Hiw | exact HT | exact Heq | exact HP | ].
  apply (RTy_reflect HP).
  exists x; split;
    [ apply neet_var; exact Hx
    | apply eq_term_refl; eapply VarT_wf; exact Hx ].
Qed.

(* ================================================================== *)
(* 5.  [RSub_wk] : reducible substitutions compose with weakenings      *)
(* ================================================================== *)

Lemma RSub_wk : forall D G g, RSub D G g -> EnvOk G ->
  forall D' w, Wk D' D w -> EnvOk D' -> RSub D' G (oCmp D' D G w g).
Proof.
  apply (@RSub_gen_ind
    (fun D G g => EnvOk G -> forall D' w, Wk D' D w -> EnvOk D' ->
                    RSub D' G (oCmp D' D G w g))).
  - (* emp *)
    intros D g Hf _ D' w HW HD'.
    assert (EnvOk D) as HD by (eapply Wk_cod; exact HW).
    assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
    assert (wft D' sEnv) as HD'w by (apply EnvOk_wf; exact HD').
    assert (wft w (sSub D' D)) as Hww by (apply Wk_wf; exact HW).
    apply RSub_emp_intro.
    eapply eq_term_trans;
      [ apply Cmp_cong
          with (X1 := D') (Y1 := D') (X2 := D) (Y2 := D)
               (X3 := oEmp) (Y3 := oEmp) (f1 := w) (f2 := w)
               (g1 := g) (g2 := oForget D);
        [ er | er | er | er | exact Hf ]
      | apply eq_cmp_forget; assumption ].
  - (* ext *)
    intros D G0 i A g g0 v Hs Hg0 IH Hv HGE D' w HW HD'.
    destruct (EnvOk_ext_inv HGE) as [HG0 HA].
    assert (EnvOk D) as HD by (eapply Wk_cod; exact HW).
    pose proof (eqt_wf_r Hs) as Hsn.
    apply wft_Snoc_args in Hsn.
    destruct Hsn as (HDw & HG0w & Hiw & HAw & Hg0w & Hvw).
    assert (wft D' sEnv) as HD'w by (apply EnvOk_wf; exact HD').
    assert (wft w (sSub D' D)) as Hww by (apply Wk_wf; exact HW).
    assert (wft (oExt G0 i A) sEnv) as HGEw by (apply wf_Ext; assumption).
    (* the entry's normal type in [D] *)
    assert (CSub D G0 g0) as HC0 by (eapply RSub_CSub; eassumption).
    destruct (TyOk_subst HA HC0 HD) as [An [HAn HeqAn]].
    assert (RTm D i An v) as Hv0
      by (apply Hv; [ apply eq_term_refl; exact Hiw | exact HAn | exact HeqAn ]).
    destruct (RTyEx_of_TyOk HAn) as [P HP].
    assert (P v) as HPv by (eapply RTm_elim; eassumption).
    (* ... and its weakening to [D'] *)
    destruct (RTy_wk HP HW HD') as [Aw [Q [HAw' [HeqAw [HQ Hmap]]]]].
    assert (Q (oExpSubst D' D w i An v)) as HQv by (apply Hmap; exact HPv).
    assert (eqt (sTy D' i)
              (oTySubst D' D w i (oTySubst D G0 g0 i A))
              (oTySubst D' D w i An)) as HeqW.
    { apply TySubst_cong
        with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
             (g1 := w) (g2 := w) (i1 := i) (i2 := i)
             (A1 := oTySubst D G0 g0 i A) (A2 := An);
        [ er | er | er | er | exact HeqAn ]. }
    assert (eqt (sTy D' i)
              (oTySubst D' D w i (oTySubst D G0 g0 i A)) Aw) as HeqW'
      by (eapply eq_term_trans; [ exact HeqW | exact HeqAw ]).
    (* transport the candidate along the change of type argument *)
    assert (Q (oExpSubst D' D w i (oTySubst D G0 g0 i A) v)) as HQv'.
    { eapply (RTy_cand_eq HQ); [ exact HQv | ].
      eapply eq_term_conv;
        [ apply ExpSubst_cong
            with (G1 := D') (G2 := D') (G1' := D) (G2' := D)
                 (g1 := w) (g2 := w) (i1 := i) (i2 := i)
                 (A1 := An) (A2 := oTySubst D G0 g0 i A) (v1 := v) (v2 := v);
          [ er | er | er | er
          | apply eq_term_sym; exact HeqAn
          | apply eq_term_refl; exact Hvw ]
        | apply eq_sort_exp_ty; [ exact HD'w | exact Hiw | exact HeqW' ] ]. }
    (* assemble *)
    apply RSub_ext_intro.
    exists (oCmp D' D G0 w g0),
           (oExpSubst D' D w i (oTySubst D G0 g0 i A) v).
    split; [ | split ].
    + eapply eq_term_trans;
        [ apply Cmp_cong
            with (X1 := D') (Y1 := D') (X2 := D) (Y2 := D)
                 (X3 := oExt G0 i A) (Y3 := oExt G0 i A)
                 (f1 := w) (f2 := w)
                 (g1 := g) (g2 := oSnoc D G0 i A g0 v);
          [ er | er | er | er | exact Hs ]
        | apply eq_cmp_snoc; assumption ].
    + apply IH; assumption.
    + eapply RTmN_intro with (i0 := i) (A0 := Aw) (P := Q);
        [ apply eq_term_refl; exact Hiw | exact HAw' | | exact HQ | exact HQv' ].
      eapply eq_term_trans;
        [ apply eq_term_sym; apply eq_ty_subst_cmp; assumption | exact HeqW' ].
Qed.

(* One-step weakening, the form the identity and lifting proofs use. *)
Lemma RSub_wkn D G g i A'
  : RSub D G g -> EnvOk G -> EnvOk D -> TyOk D i A' ->
    RSub (oExt D i A') G (oCmp (oExt D i A') D G (oWkn D i A') g).
Proof.
  intros HR HG HD HA'.
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft A' (sTy D i)) as HA'w by (apply TyOk_wf; exact HA').
  assert (wft i sInfo) as Hiw by (eapply wft_ty_info; exact HA'w).
  assert (wft g (sSub D G)) as Hgw by (apply RSub_wf; exact HR).
  assert (wft G sEnv) as HGw by (eapply wft_sub_cod; exact Hgw).
  assert (EnvOk (oExt D i A')) as HE by (apply envok_ext; assumption).
  assert (wft (oExt D i A') sEnv) as HEw by (apply wf_Ext; assumption).
  assert (RSub (oExt D i A') G
            (oCmp (oExt D i A') D G (oWk1 D i A') g)) as Hstep
    by (eapply RSub_wk;
        [ exact HR | exact HG | apply Wk_wk1; assumption | exact HE ]).
  eapply RSub_eq; [ exact Hstep | ].
  apply Cmp_cong
    with (X1 := oExt D i A') (Y1 := oExt D i A') (X2 := D) (Y2 := D)
         (X3 := G) (Y3 := G)
         (f1 := oWk1 D i A') (f2 := oWkn D i A') (g1 := g) (g2 := g);
    [ er | er | er | apply eq_wk1; assumption | er ].
Qed.

(* ================================================================== *)
(* 6.  [RSub_id] : the identity substitution is reducible              *)
(* ================================================================== *)

Lemma RSub_id G : EnvOk G -> RSub G G (oId G).
Proof.
  induction 1 as [ | G i A HG IH HA ].
  - apply RSub_emp_intro; exact eq_id_emp_forget.
  - assert (wft G sEnv) as HGw by (apply EnvOk_wf; exact HG).
    assert (wft A (sTy G i)) as HAw by (apply TyOk_wf; exact HA).
    assert (wft i sInfo) as Hiw by (eapply wft_ty_info; exact HAw).
    assert (EnvOk (oExt G i A)) as HE by (apply envok_ext; assumption).
    assert (wft (oExt G i A) sEnv) as HEw by (apply wf_Ext; assumption).
    (* the tail: the identity, weakened, is [wkn] *)
    assert (RSub (oExt G i A) G (oWkn G i A)) as Htail.
    { assert (RSub (oExt G i A) G
                (oCmp (oExt G i A) G G (oWkn G i A) (oId G))) as Hstep
        by (eapply RSub_wkn;
            [ exact IH | exact HG | exact HG | exact HA ]).
      eapply RSub_eq;
        [ exact Hstep
        | apply eq_id_right; [ exact HEw | exact HGw | apply wf_Wkn; assumption ] ]. }
    (* the head: the head variable *)
    destruct (TyOk_wkn HG HA HA) as [A'' [HA'' HeqA'']].
    assert (VarT (oExt G i A) i A'' (oHd G i A)) as HVhd
      by (apply vart_hd; assumption).
    apply RSub_ext_intro.
    exists (oWkn G i A), (oHd G i A).
    split; [ | split ].
    + apply eq_term_sym; apply eq_snoc_wkn_hd; assumption.
    + exact Htail.
    + eapply RTmN_of_VarT; [ exact HVhd | exact HeqA'' ].
Qed.

(* ================================================================== *)
(* 7.  [RSub_proj] : the projection out of an extended environment      *)
(* ================================================================== *)

Lemma RSub_proj D G i A g
  : RSub D (oExt G i A) g ->
    RSub D G (oCmp D (oExt G i A) G g (oWkn G i A)).
Proof.
  intro H; apply RSub_ext_elim in H as [g0 [v [Hs [Hg0 Hv]]]].
  pose proof (eqt_wf_r Hs) as Hsn.
  apply wft_Snoc_args in Hsn.
  destruct Hsn as (HDw & HGw & Hiw & HAw & Hg0w & Hvw).
  assert (wft (oExt G i A) sEnv) as HEw by (apply wf_Ext; assumption).
  eapply RSub_eq; [ exact Hg0 | ].
  apply eq_term_sym.
  eapply eq_term_trans;
    [ apply Cmp_cong
        with (X1 := D) (Y1 := D) (X2 := oExt G i A) (Y2 := oExt G i A)
             (X3 := G) (Y3 := G)
             (f1 := g) (f2 := oSnoc D G i A g0 v)
             (g1 := oWkn G i A) (g2 := oWkn G i A);
      [ er | er | er | exact Hs | er ]
    | apply eq_wkn_snoc; assumption ].
Qed.

(* ================================================================== *)
(* 8.  [RSub_lift] : lifting a reducible substitution under a binder    *)
(* ================================================================== *)

Lemma RSub_lift D G g i A A'
  : RSub D G g -> EnvOk D -> TyOk G i A -> TyOk D i A' ->
    eqt (sTy D i) (oTySubst D G g i A) A' ->
    RSub (oExt D i A') (oExt G i A) (oLiftW D G g i A A').
Proof.
  intros HR HD HA HA' Heq.
  assert (EnvOk G) as HG by (eapply TyOk_EnvOk; exact HA).
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft G sEnv) as HGw by (apply EnvOk_wf; exact HG).
  assert (wft A (sTy G i)) as HAw by (apply TyOk_wf; exact HA).
  assert (wft A' (sTy D i)) as HA'w by (apply TyOk_wf; exact HA').
  assert (wft i sInfo) as Hiw by (eapply wft_ty_info; exact HAw).
  assert (wft g (sSub D G)) as Hgw by (apply RSub_wf; exact HR).
  assert (EnvOk (oExt D i A')) as HE by (apply envok_ext; assumption).
  assert (wft (oExt D i A') sEnv) as HEw by (apply wf_Ext; assumption).
  (* the tail *)
  assert (RSub (oExt D i A') G
            (oCmp (oExt D i A') D G (oWkn D i A') g)) as Htail
    by (apply RSub_wkn; assumption).
  (* the head *)
  destruct (TyOk_wkn HD HA' HA') as [A'' [HA'' HeqA'']].
  assert (VarT (oExt D i A') i A'' (oHd D i A')) as HVhd
    by (apply vart_hd; assumption).
  assert (eqt (sTy (oExt D i A') i)
            (oTySubst (oExt D i A') G
               (oCmp (oExt D i A') D G (oWkn D i A') g) i A) A'') as HeqT.
  { eapply eq_term_trans;
      [ apply eq_term_sym; apply eq_ty_subst_cmp;
        [ exact HEw | exact HDw | exact HGw
        | apply wf_Wkn; assumption | exact Hgw | exact Hiw | exact HAw ]
      | ].
    eapply eq_term_trans; [ | exact HeqA'' ].
    apply TySubst_cong
      with (G1 := oExt D i A') (G2 := oExt D i A') (G1' := D) (G2' := D)
           (g1 := oWkn D i A') (g2 := oWkn D i A') (i1 := i) (i2 := i)
           (A1 := oTySubst D G g i A) (A2 := A');
      [ er | er | er | er | exact Heq ]. }
  apply RSub_ext_intro.
  exists (oCmp (oExt D i A') D G (oWkn D i A') g), (oHd D i A').
  split; [ | split ].
  - unfold oLiftW; apply eq_term_refl; apply wf_liftW; assumption.
  - exact Htail.
  - eapply RTmN_of_VarT; [ exact HVhd | exact HeqT ].
Qed.

(* The packaging the binder rules consume: the domain is an [El] of a
   normal code, and the lifted substitution's extended domain environment
   is [oExtC] of the STRUCTURALLY substituted code.  Mirrors
   [Wk_liftC]/[CSub_liftC] exactly. *)
Lemma RSub_liftC D G g rF lF F F'
  : RSub D G g -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (oCodeSubst D G g rF lF F) F' ->
    RSub (oExtC D rF lF F') (oExtC G rF lF F)
      (oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
    /\ EnvOk (oExtC D rF lF F')
    /\ eqt (sTy D (iEl rF lF))
         (oTySubst D G g (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F').
Proof.
  intros HR HD HF HF' HeqF.
  assert (EnvOk G) as HG by (eapply NfCode_EnvOk; exact HF).
  assert (wft g (sSub D G)) as Hgw by (apply RSub_wf; exact HR).
  assert (eqt (sTy D (iEl rF lF))
            (oTySubst D G g (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F'))
    as HeqEl.
  { eapply eq_term_trans; [ apply eq_El_subst; wfx | ].
    apply El_cong; [ er | er | er | exact HeqF ]. }
  repeat split;
    [ unfold oExtC; apply RSub_lift;
      [ exact HR | exact HD | apply tyok_El; exact HF
      | apply tyok_El; exact HF' | exact HeqEl ]
    | apply envok_ext; [ exact HD | apply tyok_El; exact HF' ]
    | exact HeqEl ].
Qed.

(* ================================================================== *)
(* 9.  The [RSubN] forms                                               *)
(*                                                                     *)
(* src/Pyrosome/Gluing/Dtt/Ceq.v's [sub]/[ty]/[exp] clauses are stated with [RSubN], so  *)
(* these are what the model obligations will actually consume.  Each is *)
(* the [RSub] form plus one use of Layer 0.5's [EnvOk_inj], which is    *)
(* what identifies the representative environment [RSubN] quantifies    *)
(* with the syntactic one appearing in the goal.                        *)
(* ================================================================== *)

Lemma RSubN_id G : EnvOk G -> RSubN G G (oId G).
Proof. intro HG; apply RSubN_of_RSub; [ exact HG | apply RSub_id; exact HG ]. Qed.

(* No [EnvOk G] hypothesis: [RSubN] supplies its own normal
   representative of the codomain environment. *)
Lemma RSubN_wk D G g D' w
  : RSubN D G g -> Wk D' D w -> EnvOk D' -> RSubN D' G (oCmp D' D G w g).
Proof.
  intros HN HW HD'.
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact HN).
  destruct HN as [G0 (HG0 & Heq & HR)].
  assert (EnvOk D) as HD by (eapply Wk_cod; exact HW).
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft D' sEnv) as HD'w by (apply EnvOk_wf; exact HD').
  assert (wft w (sSub D' D)) as Hww by (apply Wk_wf; exact HW).
  assert (wft G sEnv) as HGw by (eapply eqt_wf_l; exact Heq).
  assert (wft G0 sEnv) as HG0w by (apply EnvOk_wf; exact HG0).
  exists G0; split; [ exact HG0 | split; [ exact Heq | ] ].
  assert (RSub D' G0 (oCmp D' D G0 w g)) as Hstep
    by (eapply RSub_wk; [ exact HR | exact HG0 | exact HW | exact HD' ]).
  eapply RSub_eq; [ exact Hstep | ].
  eapply eq_term_conv;
    [ apply Cmp_cong
        with (X1 := D') (Y1 := D') (X2 := D) (Y2 := D)
             (X3 := G0) (Y3 := G) (f1 := w) (f2 := w) (g1 := g) (g2 := g);
      [ er | er | apply eq_term_sym; exact Heq | er
      | apply eq_term_refl; exact Hgw ]
    | apply sSub_cong; [ apply eq_term_refl; exact HD'w | exact Heq ] ].
Qed.

Lemma RSubN_wkn D G g i A'
  : RSubN D G g -> EnvOk D -> TyOk D i A' ->
    RSubN (oExt D i A') G (oCmp (oExt D i A') D G (oWkn D i A') g).
Proof.
  intros HN HD HA'.
  assert (wft g (sSub D G)) as Hgw by (apply RSubN_wf; exact HN).
  assert (wft D sEnv) as HDw by (apply EnvOk_wf; exact HD).
  assert (wft G sEnv) as HGw by (eapply wft_sub_cod; exact Hgw).
  assert (wft A' (sTy D i)) as HA'w by (apply TyOk_wf; exact HA').
  assert (wft i sInfo) as Hiw by (eapply wft_ty_info; exact HA'w).
  assert (EnvOk (oExt D i A')) as HE by (apply envok_ext; assumption).
  assert (wft (oExt D i A') sEnv) as HEw by (apply wf_Ext; assumption).
  assert (RSubN (oExt D i A') G
            (oCmp (oExt D i A') D G (oWk1 D i A') g)) as Hstep
    by (eapply RSubN_wk;
        [ exact HN | apply Wk_wk1; assumption | exact HE ]).
  eapply RSubN_eq; [ exact Hstep | ].
  apply Cmp_cong
    with (X1 := oExt D i A') (Y1 := oExt D i A') (X2 := D) (Y2 := D)
         (X3 := G) (Y3 := G)
         (f1 := oWk1 D i A') (f2 := oWkn D i A') (g1 := g) (g2 := g);
    [ er | er | er | apply eq_wk1; assumption | er ].
Qed.

Lemma RSubN_proj D G i A g
  : TyOk G i A -> RSubN D (oExt G i A) g ->
    RSubN D G (oCmp D (oExt G i A) G g (oWkn G i A)).
Proof.
  intros HA [G0 (HG0 & Heq & HR)].
  assert (EnvOk G) as HG by (eapply TyOk_EnvOk; exact HA).
  assert (EnvOk (oExt G i A)) as HGE by (apply envok_ext; assumption).
  assert (oExt G i A = G0) as HGeq by (apply EnvOk_inj; assumption).
  rewrite <- HGeq in HR.
  apply RSubN_of_RSub; [ exact HG | apply RSub_proj; exact HR ].
Qed.

Lemma RSubN_lift D G g i A A'
  : RSubN D G g -> EnvOk D -> TyOk G i A -> TyOk D i A' ->
    eqt (sTy D i) (oTySubst D G g i A) A' ->
    RSubN (oExt D i A') (oExt G i A) (oLiftW D G g i A A').
Proof.
  intros [G0 (HG0 & Heq & HR)] HD HA HA' Hty.
  assert (EnvOk G) as HG by (eapply TyOk_EnvOk; exact HA).
  assert (G = G0) as HGeq by (apply EnvOk_inj; assumption).
  rewrite <- HGeq in HR.
  apply RSubN_of_RSub;
    [ apply envok_ext; assumption
    | apply RSub_lift; assumption ].
Qed.

Lemma RSubN_liftC D G g rF lF F F'
  : RSubN D G g -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
    eqt (sCode D rF lF) (oCodeSubst D G g rF lF F) F' ->
    RSubN (oExtC D rF lF F') (oExtC G rF lF F)
      (oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
    /\ EnvOk (oExtC D rF lF F')
    /\ eqt (sTy D (iEl rF lF))
         (oTySubst D G g (iEl rF lF) (oEl G rF lF F)) (oEl D rF lF F').
Proof.
  intros HN HD HF HF' HeqF.
  assert (EnvOk G) as HG by (eapply NfCode_EnvOk; exact HF).
  destruct HN as [G0 (HG0 & Heq & HR)].
  assert (G = G0) as HGeq by (apply EnvOk_inj; assumption).
  rewrite <- HGeq in HR.
  destruct (RSub_liftC (D := D) (G := G) (g := g) HR HD HF HF' HeqF)
    as [HL [HEok HeqEl]].
  repeat split; [ | exact HEok | exact HeqEl ].
  apply RSubN_of_RSub;
    [ unfold oExtC; apply envok_ext; [ exact HG | apply tyok_El; exact HF ]
    | exact HL ].
Qed.

(* ================================================================== *)
(* 10.  The payoff: normalization for closed terms                     *)
(*                                                                     *)
(* Reading the model's content back at the IDENTITY substitution.  The  *)
(* two obligation families of src/Pyrosome/Gluing/Dtt/ModelStruct.v are still open, so   *)
(* the statement stays parameterised by them exactly as                *)
(* src/Pyrosome/Gluing/Dtt/ModelSound.v is; discharging them makes this theorem       *)
(* unconditional by [exact].                                           *)
(* ================================================================== *)

Section WithObligations.
  Context (Hcong : CongObligation) (Hby : ByObligation).

  Corollary ott_dtt_normalization G i A e
    : EnvOk G -> TyOk G i A -> wft e (sExp G i A) -> HasNf G i A e.
  Proof.
    intros HG HA Hwf.
    assert (wft G sEnv) as HGw by (apply EnvOk_wf; exact HG).
    assert (wft A (sTy G i)) as HAw by (apply TyOk_wf; exact HA).
    assert (wft i sInfo) as Hiw by (eapply wft_ty_info; exact HAw).
    (* the model, at the identity substitution *)
    assert (RSubN G G (oId G)) as HRS by (apply RSubN_id; exact HG).
    pose proof (ott_dtt_exp_sound Hcong Hby (G := G) (i := i) (A := A) (e := e)
                  Hwf HG HRS) as Hred.
    (* strip the identity substitution from the TYPE *)
    specialize (Hred i A (eq_term_refl Hiw) HA
                  (eq_ty_subst_id HGw Hiw HAw)).
    (* turn reducibility into a normal form *)
    destruct (RTyEx_of_TyOk HA) as [P HP].
    pose proof (RTy_escape HP _ (RTm_elim HP Hred)) as Hnf.
    (* ... and strip it from the SUBJECT *)
    eapply HasNf_eq; [ exact Hnf | ].
    apply eq_exp_subst_id; assumption.
  Qed.

  (* The type-level companion: every well-formed type over a normal
     environment has a normal representative carrying a candidate. *)
  Corollary ott_dtt_ty_normalization G i A
    : EnvOk G -> wft A (sTy G i) -> RTyN G i A.
  Proof.
    intros HG HA.
    assert (wft G sEnv) as HGw by (apply EnvOk_wf; exact HG).
    assert (wft i sInfo) as Hiw by (eapply wft_ty_info; exact HA).
    assert (RSubN G G (oId G)) as HRS by (apply RSubN_id; exact HG).
    pose proof (ott_dtt_ty_sound Hcong Hby (G := G) (i := i) (A := A)
                  HA HG HRS) as Hred.
    eapply RTyN_eq; [ exact Hred | ].
    apply eq_ty_subst_id; assumption.
  Qed.

End WithObligations.
