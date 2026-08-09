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
  WIP.DttLR WIP.DttLRBasics WIP.DttLRCand WIP.DttRSub WIP.DttCeq.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4b: the STRUCTURAL and SORT obligations of
   [CutTModel_ok ott_dtt [] (CM := DttCM)].

   The analogue of Gluing/Stlc/ModelCong.v's first half.  Each field is a
   standalone top-level lemma so the record can be assembled elsewhere;
   [cterm_cong] and [cterm_by] are developed independently.

   Everything goes through WIP/DttCeq.v's constructors and clause lemmas
   ([ceq_relevance] .. [ceq_exp], [Ceq_relevance_e] .. [Ceq_exp_e]);
   [Ceq_term] is inverted by hand nowhere.

   RESULT.  Seven of the eight structural/sort obligations are proved
   outright ([cterm_var], [csort_by], [cterm_conv], [csort_trans],
   [csort_sym], [cterm_trans], [cterm_sym]), and so are six of
   [csort_cong]'s nine cases.  The three substantive [csort_cong] cases --
   [sub], [ty], [exp] -- are NOT provable against the present [Ceq_term]:
   the contract's semantic conjuncts are stated at the RAW index terms
   ([G] and [i]), but [csort_cong] varies those indices up to provable
   equality, and neither [RSub] (a [Fixpoint] on [G]'s syntax) nor
   [RTy]/[TyOk] (whose info index is deliberately un-normalized) is stable
   under it.  Section 5 makes this precise and machine-checked: from the
   [ty] transfer ALONE it derives an equation [ott_dtt] does not prove.
   The three are therefore isolated as named hypotheses in the style of
   WIP/DttLRBasics.v's [NfCodeInj]/[TyOkInj]/[CandEqOk], so that
   [sort_cong_obligation] and the record assembly (section 6) are banked
   and the gap is one named statement rather than a hole.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ================================================================== *)
(* 0.  Small glue                                                      *)
(* ================================================================== *)

(* A reducible substitution is well typed.  Both [RSub] clauses hand back
   an equation whose left-hand side is [g] itself, so this is immediate
   (the STLC development has the same lemma under the same name). *)
Lemma RSub_wf D G g : RSub D G g -> wft g (sSub D G).
Proof.
  intro H; apply RSub_inv in H
    as [[-> Hf] | [G0 [i [A [g0 [v [-> [Hs _]]]]]]]];
    eapply eqt_wf_l; eassumption.
Qed.

(* ================================================================== *)
(* 1.  The vacuous / immediate obligations                             *)
(* ================================================================== *)

(* [cterm_var]: the ambient meta-context is empty (openness is
   object-level: object variables are [hd] and its [wkn]-shifts, see
   [VarT] in WIP/DttNf.v), so there are no meta-variables to relate. *)
Lemma var_obligation
  : forall n t, In (n, t) (@nil (string * sort)) -> Ceq_term t (var n) (var n).
Proof. intros n t H; destruct H. Qed.

(* [csort_by]: [ott_dtt] has ZERO [sort_eq_rule]s (69 rules: 32 term,
   28 term_eq, 9 sort, 0 sort_eq), so the membership premise is refutable
   on the computed list. *)
Lemma sort_by_obligation
  : forall c' name t1 t2 s1 s2,
    In (name, sort_eq_rule c' t1 t2) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_sort t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
Proof.
  intros c' name t1 t2 s1 s2 Hin Hargs.
  vm_compute in Hin; repeat (destruct Hin as [Hin|Hin]);
    first [ discriminate | destruct Hin ].
Qed.

(* [cterm_conv] is a projection of [Ceq_sort], which IS the bidirectional
   transfer of [Ceq_term] -- that is the whole point of the design. *)
Lemma term_conv_obligation
  : forall t1 t2 e1 e2, Ceq_sort t1 t2 -> Ceq_term t1 e1 e2 -> Ceq_term t2 e1 e2.
Proof. intros t1 t2 e1 e2 [_ [Hf _]] H; exact (Hf _ _ H). Qed.

Lemma sort_trans_obligation
  : forall t1 t12 t2, Ceq_sort t1 t12 -> Ceq_sort t12 t2 -> Ceq_sort t1 t2.
Proof.
  intros t1 t12 t2 [He1 [Hf1 Hb1]] [He2 [Hf2 Hb2]]; repeat split.
  - eapply eq_sort_trans; eassumption.
  - intros e1 e2 H; apply Hf2, Hf1; exact H.
  - intros e1 e2 H; apply Hb1, Hb2; exact H.
Qed.

Lemma sort_sym_obligation : forall t1 t2, Ceq_sort t1 t2 -> Ceq_sort t2 t1.
Proof.
  intros t1 t2 [He [Hf Hb]]; repeat split;
    [ apply eq_sort_sym; exact He | exact Hb | exact Hf ].
Qed.

(* ================================================================== *)
(* 2.  Transitivity                                                    *)
(* ================================================================== *)

(* The [eq_term] conjunct composes; the semantic conjunct constrains only
   the FIRST argument, so it comes straight from the first hypothesis.
   The two index clauses need their [ntlvl]/[ninfo] equations composed. *)
Lemma term_trans_obligation
  : forall t e1 e12 e2, Ceq_term t e1 e12 -> Ceq_term t e12 e2 -> Ceq_term t e1 e2.
Proof.
  intros t e1 e12 e2 H1 H2; destruct H1.
  - (* relevance: the clause forces [e1 = e12] syntactically *) exact H2.
  - (* lvl: likewise *) exact H2.
  - apply Ceq_tlvl_e in H2 as (Hq & Hn & _).
    apply ceq_tlvl;
      [ eapply eq_term_trans; eassumption
      | etransitivity; eassumption
      | assumption ].
  - apply Ceq_tyinfo_e in H2 as (Hq & Hn & _).
    apply ceq_tyinfo;
      [ eapply eq_term_trans; eassumption
      | etransitivity; eassumption
      | assumption ].
  - apply Ceq_ltl_e in H2.
    apply ceq_ltl; eapply eq_term_trans; eassumption.
  - apply Ceq_env_e in H2 as [Hq _].
    apply ceq_env; [ eapply eq_term_trans; eassumption | assumption ].
  - apply Ceq_sub_e in H2 as [Hq _].
    apply ceq_sub; [ eapply eq_term_trans; eassumption | assumption ].
  - apply Ceq_ty_e in H2 as [Hq _].
    apply ceq_ty; [ eapply eq_term_trans; eassumption | assumption ].
  - apply Ceq_exp_e in H2 as [Hq _].
    apply ceq_exp; [ eapply eq_term_trans; eassumption | assumption ].
Qed.

(* ================================================================== *)
(* 3.  Symmetry                                                        *)
(* ================================================================== *)

(* The semantic conjunct of every clause constrains only the LEFT term, so
   the symmetric statement has to RECOVER it for the right one from the
   equation.  Exactly as in Gluing/Stlc/ModelCong.v's [term_sym_obligation]
   this goes through the side-condition-free closure lemmas
   [RSub_eq] / [RTyN_eq] / [RTmN_eq] together with the matching congruence
   of WIP/DttEqns.v ([Cmp_cong] / [TySubst_cong] / [ExpSubst_cong]).  Note
   that all three congruences vary ONLY the last argument here, so their
   conclusion sort is literally the sort the closure lemma wants. *)
Lemma term_sym_obligation
  : forall t e1 e2, Ceq_term t e1 e2 -> Ceq_term t e2 e1.
Proof.
  intros t e1 e2 H; destruct H as [ r Hr | l Hl
                                  | n1 n2 Ha Hn Hnf
                                  | i1 i2 Ha Hn Hnf
                                  | a b p1 p2 Ha
                                  | G1 G2 Ha [G0 [HG0 Heq0]]
                                  | G G' g1 g2 Ha Hb
                                  | G i A1 A2 Ha Hb
                                  | G i A f1 f2 Ha Hb ].
  - apply ceq_relevance; assumption.
  - apply ceq_lvl; assumption.
  - apply ceq_tlvl;
      [ apply eq_term_sym; exact Ha | symmetry; exact Hn | rewrite <- Hn; exact Hnf ].
  - apply ceq_tyinfo;
      [ apply eq_term_sym; exact Ha | symmetry; exact Hn | rewrite <- Hn; exact Hnf ].
  - apply ceq_ltl; apply eq_term_sym; exact Ha.
  - apply ceq_env; [ apply eq_term_sym; exact Ha | ].
    exists G0; split; [ exact HG0 | ].
    eapply eq_term_trans; [ apply eq_term_sym; exact Ha | exact Heq0 ].
  - (* substitutions *)
    destruct (wft_sub_inv (eqt_wf_l Ha)) as [HwG HwG'].
    apply ceq_sub; [ apply eq_term_sym; exact Ha | ].
    intros D h HD Hh.
    assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
    apply RSub_eq with (g := oCmp D G G' h g1); [ apply Hb; assumption | ].
    apply Cmp_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG
      | apply eq_term_refl; exact HwG'
      | apply eq_term_refl; apply RSub_wf; exact Hh
      | exact Ha ].
  - (* types *)
    destruct (wft_ty_inv (eqt_wf_l Ha)) as [HwG Hwi].
    apply ceq_ty; [ apply eq_term_sym; exact Ha | ].
    intros D g HD Hg.
    assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
    apply RTyN_eq with (A := oTySubst D G g i A1); [ apply Hb; assumption | ].
    apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG
      | apply eq_term_refl; apply RSub_wf; exact Hg
      | apply eq_term_refl; exact Hwi
      | exact Ha ].
  - (* terms *)
    destruct (wft_exp_inv (eqt_wf_l Ha)) as [HwG [Hwi HwA]].
    apply ceq_exp; [ apply eq_term_sym; exact Ha | ].
    intros D g HD Hg.
    assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
    apply RTmN_eq with (e := oExpSubst D G g i A f1); [ apply Hb; assumption | ].
    apply ExpSubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG
      | apply eq_term_refl; apply RSub_wf; exact Hg
      | apply eq_term_refl; exact Hwi
      | apply eq_term_refl; exact HwA
      | exact Ha ].
Qed.

(* ================================================================== *)
(* 4.  Sort congruence                                                 *)
(* ================================================================== *)

(* [ott_dtt] has nine sort rules.  Computing the membership premise splits
   the obligation nine ways; the goals come out in the language's own
   order:

     exp, ty, sub, env, tyinfo, tlvl, ltl, lvl, relevance.

   SIX of them are settled outright by [Ceq_sort_refl]:

     - [env], [tyinfo], [tlvl], [lvl], [relevance] are NULLARY sort rules,
       so [s1 = s2 = []] and the two sorts are syntactically identical;
     - [ltl]'s two arguments are at [lvl], where [Ceq_term] forces
       syntactic equality ([Ceq_lvl_e]), so again [s1 = s2].
       (Proof irrelevance -- [eq_ltl_irr] -- is not even needed: it would
       be, if [Ceq_term] at [lvl] carried an equation rather than an
       identity.)

   The remaining THREE -- [sub], [ty], [exp] -- are the substantive ones
   and are NOT provable against the present contract; see section 5.  They
   are isolated here as three named statements and taken as hypotheses, in
   the same style as WIP/DttLRBasics.v's [NfCodeInj]/[TyOkInj]/[CandEqOk],
   so that the six settled cases and the plumbing are banked. *)

Definition SubSortTransfer : Prop :=
  forall G1 G2 G1' G2',
    Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_sort (sSub G1 G1') (sSub G2 G2').

Definition TySortTransfer : Prop :=
  forall G1 G2 i1 i2,
    Ceq_term sEnv G1 G2 -> Ceq_term sInfo i1 i2 ->
    Ceq_sort (sTy G1 i1) (sTy G2 i2).

Definition ExpSortTransfer : Prop :=
  forall G1 G2 i1 i2 A1 A2,
    Ceq_term sEnv G1 G2 -> Ceq_term sInfo i1 i2 ->
    Ceq_term (sTy G2 i2) A1 A2 ->
    Ceq_sort (sExp G1 i1 A1) (sExp G2 i2 A2).

Lemma sort_cong_obligation
      (Hexp : ExpSortTransfer) (Hty : TySortTransfer) (Hsub : SubSortTransfer)
  : forall c' name args s1 s2,
    In (name, sort_rule c' args) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_sort (scon name s1) (scon name s2).
Proof.
  intros c' name args s1 s2 Hin Hargs.
  vm_compute in Hin;
    repeat (destruct Hin as [Hin|Hin]); try discriminate;
    inversion Hin; subst; clear Hin;
    repeat match goal with
           | [ H : ceq_args (_::_) _ _ |- _ ] => inversion H; subst; clear H
           | [ H : ceq_args [] _ _ |- _ ] => inversion H; subst; clear H
           end;
    cbn [ceq_term ceq_sort DttCM] in *.
  - (* exp *) apply Hexp; assumption.
  - (* ty *) apply Hty; assumption.
  - (* sub *) apply Hsub; assumption.
  - (* env *) apply Ceq_sort_refl, wf_sort_env.
  - (* tyinfo *) apply Ceq_sort_refl, wf_sort_info.
  - (* tlvl *) apply Ceq_sort_refl, wf_sort_tlvl.
  - (* ltl *)
    (* the two arguments are at [lvl]; [Ceq_term] there IS identity.  The
       sorts in [Hargs] are presented as [t[/with_names_from .../]], so the
       clause lemma is applied by unification rather than by matching. *)
    repeat match goal with
           | [ H : Ceq_term _ _ _ |- _ ] => apply Ceq_lvl_e in H as [-> ?]
           end.
    apply Ceq_sort_refl, wf_sort_ltl; apply LvlNf_wf; assumption.
  - (* lvl *) apply Ceq_sort_refl, wf_sort_lvl.
  - (* relevance *) apply Ceq_sort_refl, wf_sort_relevance.
Qed.

(* ================================================================== *)
(* 5.  Why [sub]/[ty]/[exp] do not hold against the present contract   *)
(* ================================================================== *)

(* The design note in WIP/DttCeq.v says the [Ceq_sort] transfer is cheap
   because "[Ceq_term] at [exp G i A] quantifies over the NORMAL
   REPRESENTATIVES of the type, and two provably-equal sorts have literally
   the same set of normal representatives".  That is TRUE of the TYPE
   argument [A] -- [RTmN]/[RTyN] quantify [A0] up to [eqt (sTy G i) A A0],
   so replacing [A] by a provably equal [A'] is one use of transitivity
   (that is exactly what [term_sym_obligation] above exploits).

   It is NOT true of the two INDEX arguments, and [csort_cong] varies them:

     * [i].  [RTyN G i A] asks for [A0] with [TyOk G i A0], and [TyOk]'s
       info index is SYNTACTIC -- deliberately so, per the header of
       WIP/DttNf.v: a universe is pinned at [iCode l = info rel (next l)]
       and an [El] at [iEl r l = info r (iota l)].  But "next0" makes
       [iCode L0] and [iEl rel L1] PROVABLY EQUAL infos (that is
       [eq_info_next0], WIP/DttNfWf.v), and [Ceq_term sInfo] relates them
       (it only demands equal [ninfo]s).  So the two sorts [ty G (iCode L0)]
       and [ty G (iEl rel L1)] are provably equal yet have DISJOINT sets of
       normal representatives.

     * [G].  [RSub D G g] is a [Fixpoint] on the SYNTAX of [G], and the
       [env] clause of [Ceq_term] supplies only [eqt sEnv G1 G2] (plus
       [HasNfEnv G1]).  Transferring [RSub] across a provable environment
       equality is not available -- and in the [ext] case it would demand
       exactly a normalization fact about the extension's value ([RTmN] at
       the entry type), i.e. the theorem being proved.

   The [ty] failure is not merely "unproved": it is refutable modulo
   consistency, and the lemma below MAKES THAT PRECISE, with no admits.
   From [TySortTransfer] alone it derives that the closed universe
   [U irr L0] is provably equal, at sort [ty emp (info rel (iota L1))], to
   the [El] of a closed relevant [Pi] code.  [ott_dtt] proves no such
   equation (distinct type formers, no code for a universe in
   Lang/OTT/Base.v), so [TySortTransfer] is false; it is only the absence
   of a consistency/injectivity result at this layer that keeps the
   statement from being an outright [False].

   THE FIX (a contract change, hence reported rather than applied): close
   [RSub]/[RTyN]/[RTmN] under provable equality of their INDEX arguments
   the way they are already closed under equality of the subject and of the
   type -- i.e. quantify the info existentially/universally up to [eqt],

     RTyN G i A := exists i0 A0 P, eqt sInfo i i0 /\ TyOk G i0 A0 /\ ...
     RTmN G i A e := forall i0 A0, eqt sInfo i i0 -> TyOk G i0 A0 -> ...

   and wrap [RSub] as [RSubN D G g := exists G0, EnvOk G0 /\ eqt sEnv G G0
   /\ RSub D G0 g].  Both wrappers are stable under [eqt] in the index by
   transitivity alone, in BOTH directions, which is what the two transfers
   of [Ceq_sort] need.  Nothing else in Layers 1-3 has to move. *)

Lemma HasNfEnv_emp : HasNfEnv oEmp.
Proof. exists oEmp; split; [ apply envok_emp | apply eq_term_refl, wf_Emp ]. Qed.

Lemma Ceq_env_emp : Ceq_term sEnv oEmp oEmp.
Proof. apply ceq_env; [ apply eq_term_refl, wf_Emp | apply HasNfEnv_emp ]. Qed.

(* The two spellings the elaborator left behind are related by [Ceq_term]:
   [info rel (next L0)] and [info rel (iota L1)] have the same [ninfo]. *)
Lemma Ceq_info_next0 : Ceq_term sInfo (iCode oL0) (iEl oRel oL1).
Proof.
  apply ceq_tyinfo.
  - apply eq_info_next0.
  - reflexivity.
  - change (InfoNf (oInfo oRel (oIota oL1))).
    apply infonf; [ apply relnf_rel | apply tlvlnf_iota, lvlnf_L1 ].
Qed.

(* [U irr L0] is a reducible type at the [iCode] spelling: its every
   reducible instance is [U irr L0] again ("U subst"), which is [rty_U]. *)
Lemma Ceq_ty_U_irr0
  : Ceq_term (sTy oEmp (iCode oL0)) (oU oEmp oIrr oL0) (oU oEmp oIrr oL0).
Proof.
  assert (wft (oU oEmp oIrr oL0) (sTy oEmp (iCode oL0))) as HwU by wfa.
  apply ceq_ty; [ apply eq_term_refl; exact HwU | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D oEmp)) as Hwg by (apply RSub_wf; exact Hg).
  apply RTyN_eq with (A := oU D oIrr oL0).
  - exists (oU D oIrr oL0), (HasNfCode D oIrr oL0); repeat split.
    + apply tyok_U; [ exact HD | apply relnf_irr | apply lvlnf_L0 ].
    + apply eq_term_refl; wfa.
    + apply RTy_U_i; [ exact HD | apply relnf_irr | apply lvlnf_L0 ].
  - apply eq_term_sym; apply eq_U_subst; wfa.
Qed.

(* The empty environment has no object variables. *)
Lemma VarT_not_emp i A x : ~ VarT oEmp i A x.
Proof. intro H; inversion H. Qed.

(* [TyOk] is info-directed: at an [iEl] info only [tyok_El] can fire, since
   [tyok_U]'s info is the [iCode] spelling.  This IS the rigidity that makes
   [TySortTransfer] fail. *)
Lemma TyOk_iEl_inv G r l A
  : TyOk G (iEl r l) A -> exists c, A = oEl G r l c /\ NfCode G r l c.
Proof.
  intro H; remember (iEl r l) as i eqn:Hi; destruct H.
  - unfold iEl, iCode, oInfo, oIota, oNext in Hi; congruence.
  - assert (r0 = r /\ l0 = l) as [-> ->]
      by (unfold iEl, oInfo, oIota in Hi; split; congruence).
    exists c; split; [ reflexivity | assumption ].
Qed.

(* In the EMPTY environment there are no variables, so the only normal code
   at [(rel, L1)] is a relevant [Pi]. *)
Lemma NfCode_emp_rel_L1 c
  : NfCode oEmp oRel oL1 c ->
    exists rF lF F B, c = oPiRel oEmp rF lF oL1 F B.
Proof.
  intro H.
  remember oEmp as G eqn:HG; remember oRel as r eqn:Hr; remember oL1 as l eqn:Hl.
  destruct H.
  - unfold oL0, oL1 in *; congruence.
  - unfold oRel, oIrr in *; congruence.
  - subst; eauto 6.
  - unfold oRel, oIrr in *; congruence.
  - exfalso; subst; eapply VarT_not_emp; eassumption.
Qed.

Lemma ty_transfer_absurd (H : TySortTransfer)
  : exists rF lF F B,
      eqt (sTy oEmp (iEl oRel oL1))
          (oU oEmp oIrr oL0)
          (oEl oEmp oRel oL1 (oPiRel oEmp rF lF oL1 F B)).
Proof.
  destruct (H oEmp oEmp (iCode oL0) (iEl oRel oL1) Ceq_env_emp Ceq_info_next0)
    as [_ [Hfwd _]].
  pose proof (Hfwd _ _ Ceq_ty_U_irr0) as Hc.
  apply Ceq_ty_e in Hc as [_ Hsem].
  specialize (Hsem oEmp (oForget oEmp) envok_emp).
  assert (RSub oEmp oEmp (oForget oEmp)) as Hg
      by (apply RSub_emp_intro; apply eq_term_refl; wfa).
  specialize (Hsem Hg).
  (* move the raw instance to [U irr L0]: change the info argument by
     [TySubst_cong], then fire "U subst" at its own ([iCode]) spelling. *)
  assert (eqt (sTy oEmp (iEl oRel oL1))
              (oTySubst oEmp oEmp (oForget oEmp) (iEl oRel oL1)
                        (oU oEmp oIrr oL0))
              (oU oEmp oIrr oL0)) as Hmove.
  {
    eapply eq_term_trans.
    - apply eq_term_sym.
      apply TySubst_cong with (i1 := iCode oL0);
        [ apply eq_term_refl; wfa
        | apply eq_term_refl; wfa
        | apply eq_term_refl; wfa
        | apply eq_info_next0
        | apply eq_term_refl; apply wf_U_irr0'; wfa ].
    - eapply eq_term_conv;
        [ apply eq_U_subst; wfa
        | apply eq_sort_ty_cong;
          [ apply eq_term_refl; wfa | apply eq_info_next0 ] ].
  }
  destruct (RTyN_eq Hsem Hmove) as [A0 [P (HT & Heq & _)]].
  apply TyOk_iEl_inv in HT as [c [-> Hc]].
  apply NfCode_emp_rel_L1 in Hc as [rF [lF [F [B ->]]]].
  eauto 6.
Qed.

(* ================================================================== *)
(* 6.  Assembly                                                        *)
(* ================================================================== *)

(* The two obligations developed elsewhere.  Naming them here is not
   idle: building the record below CHECKS that the sixteen statements
   above have exactly the shapes the class's fields demand (argument
   order, the [with_names_from c' s2] on the conclusion sort, the
   [ceq_term]/[ceq_sort] projections of [DttCM]). *)

Definition CongObligation : Prop :=
  forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).

Definition ByObligation : Prop :=
  forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
             e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].

Definition DttCM_ok
  (Hcong : CongObligation) (Hby : ByObligation)
  (Hexp : ExpSortTransfer) (Hty : TySortTransfer) (Hsub : SubSortTransfer)
  : CutTModel_ok (V := string) ott_dtt [] (CM := DttCM).
Proof.
  constructor.
  - exact var_obligation.
  - exact Hcong.
  - exact Hby.
  - exact term_trans_obligation.
  - exact term_sym_obligation.
  - exact term_conv_obligation.
  - exact (sort_cong_obligation Hexp Hty Hsub).
  - exact sort_by_obligation.
  - exact sort_trans_obligation.
  - exact sort_sym_obligation.
Defined.
