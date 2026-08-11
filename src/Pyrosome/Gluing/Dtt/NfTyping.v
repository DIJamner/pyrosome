Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 1: TYPING OF THE NORMAL FORMS.

   The analogue of the "typing of the (typed) canonical forms" section of
   Gluing/Stlc/NormalForms.v, for the six-way mutual block of src/Pyrosome/Gluing/Dtt/NormalForms.v.

   Contents:
     * a [wf_term] inversion principle for a [con] (peeling conversions),
       and the three argument-inversions it is used for
       ([wft_El_args], [wft_PiRel_args], [wft_PiIrr_args]);
     * the sort congruences [sTy_cong] / [sExp_cong] and the
       "next0" sort bridges;
     * the structural corollaries [Nf_EnvOk], [EnvOk_ext_inv],
       [VarT_TyOk], [VarT_hd_inv], [VarT_wkn_inv], [NeET_TyOk],
       [NfET_TyOk], [NfCode_idx];
     * the combined typing theorem [Nf_wf] and its six projections;
     * [Wk_dom] / [Wk_cod] / [Wk_wf].

   ------------------------------------------------------------------
   WHERE THE CONVERSIONS ARE (the map later layers need).

   Every [wf_term_conv] inserted below is caused by one of exactly two
   things.

   (A) THE "next0" SPELLING MISMATCH.  [ott_dtt] proves
       [next L0 = iota L1] ([eq_next0]) but the elaborator did not pick a
       representative: [Nat] is a code at [info rel (next L0)] while
       [Empty] and [Pi_irr] conclude at [info rel (iota L1)].  [NormalForms.v]
       pins every canonical form to the [iCode]/[next] spelling, so the
       [Empty]/[Pi_irr] rules have to be converted across.  Bridge:
       [eq_next0], lifted to [eq_sort] by [eq_sort_U_irr0] (which is
       [sExp_cong] applied to [Info_cong Rel_cong eq_next0]).
       Sites: [nfcode_empty], [nfcode_pi_irr] (twice: once on the codomain
       premise, once on the conclusion), [neet_app_irr] (on the codomain
       recovered from the type of the head).

   (B) THE NAMED NORMAL TYPE OF A VARIABLE / NEUTRAL.  [NormalForms.v]'s
       [vart_hd], [vart_wkn], [neet_app_rel], [neet_app_irr] each carry a
       normal representative of a substituted type together with the
       [eq_term] identifying them; the rule of [ott_dtt] concludes at the
       substituted spelling, so the derivation is converted along the
       supplied equation.  Bridge: the clause's own [eqt] premise, lifted
       by [eq_sort_exp_ty].

   [Wk_wf]'s [wk_lift] case is a (B)-shaped conversion whose bridging
   equation is not supplied but DERIVED: [eq_wk_lift_ty] chains
   [TySubst_cong] (on the clause's equation) with [eq_ty_subst_cmp].
   ===================================================================== *)

Notation term := (@Term.term string).
Notation sort := (@Term.sort string).

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* Inverting a [con]'s well-formedness down to its arguments            *)
(* ------------------------------------------------------------------ *)

(* Unlike [wf_sort], [wf_term] has a conversion constructor, so a direct
   [inversion] is useless: the derivation of a [con] may end in an
   arbitrary stack of [wf_term_conv]s.  This peels them. *)
Lemma wft_con_args c n s t
  : wf_term ott_dtt c (con n s) t ->
    exists c' args tret,
      In (n, term_rule c' args tret) ott_dtt
      /\ Model.wf_args (Model := core_model ott_dtt) c s c'.
Proof.
  intro H.
  remember (con n s) as e eqn:Heqe.
  revert n s Heqe.
  induction H; intros n' s' Heqe.
  - (* wf_term_by *)
    safe_invert Heqe.
    do 3 eexists; split; eassumption.
  - (* wf_term_conv: peel *)
    eauto.
  - (* wf_term_var *)
    safe_invert Heqe.
Qed.

Lemma ott_dtt_all_fresh : all_fresh ott_dtt.
Proof. eapply wf_lang_ext_all_fresh; exact ott_dtt_wf. Qed.

Lemma ott_dtt_lookup_of_in n r
  : In (n, r) ott_dtt -> Some r = named_list_lookup_err ott_dtt n.
Proof.
  intro H.
  apply (proj2 (all_fresh_named_list_lookup_err_in ott_dtt n r ott_dtt_all_fresh)).
  exact H.
Qed.

(* [con_args_inv H] : from [H : wft (con n s) t] with [n] a literal, recover
   the well-formedness of every element of [s] at its declared (substituted)
   sort.  [all_fresh ott_dtt] pins the rule, so no case split is needed. *)
Ltac con_args_inv H :=
  apply wft_con_args in H;
  let cc := fresh "cc" in
  let aa := fresh "aa" in
  let tt0 := fresh "tt0" in
  let Hin := fresh "Hin" in
  let Hargs := fresh "Hargs" in
  destruct H as [cc [aa [tt0 [Hin Hargs]]]];
  apply ott_dtt_lookup_of_in in Hin;
  vm_compute in Hin; safe_invert Hin;
  repeat match goal with
    | [ Ha : Model.wf_args _ (_::_) _ |- _ ] => inversion Ha; subst; clear Ha
    end;
  cbn [Model.wf_term core_model] in *;
  norm_wf_hyps.

Lemma wft_El_args G r l c t
  : wft (oEl G r l c) t ->
    wft G sEnv /\ wft r sRelevance /\ wft l sLvl /\ wft c (sCode G r l).
Proof.
  unfold oEl; intro H; con_args_inv H; repeat split; assumption.
Qed.

Lemma wft_PiRel_args G rF lF lG F B t
  : wft (oPiRel G rF lF lG F B) t ->
    wft G sEnv /\ wft rF sRelevance /\ wft lF sLvl /\ wft lG sLvl
    /\ wft F (sCode G rF lF)
    /\ wft B (sCode (oExtC G rF lF F) oRel lG).
Proof.
  unfold oPiRel; intro H; con_args_inv H; repeat split; assumption.
Qed.

(* NB the codomain [B] comes back at [info rel (iota L1)], NOT at
   [iCode L0]; see trap (A) in the header. *)
Lemma wft_PiIrr_args G rF lF F B t
  : wft (oPiIrr G rF lF F B) t ->
    wft G sEnv /\ wft rF sRelevance /\ wft lF sLvl
    /\ wft F (sCode G rF lF)
    /\ wft B (sExp (oExtC G rF lF F) (oInfo oRel (oIota oL1))
                (oU (oExtC G rF lF F) oIrr oL0)).
Proof.
  unfold oPiIrr; intro H; con_args_inv H; repeat split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Sort congruences                                                     *)
(*                                                                      *)
(* [sSub_cong]/[sTy_cong]/[sExp_cong] and the [scong_step] tactic that   *)
(* generates them are src/Pyrosome/Gluing/Dtt/Eqns.v's, next to their    *)
(* term-level twins.  The one special case below does all the work in    *)
(* this development.                                                    *)
(* ------------------------------------------------------------------ *)

(* Same environment, same info, provably equal types.  NO side conditions:
   the environment and the info are recovered by inverting the sort the
   type equation itself lives at. *)
Lemma eq_sort_exp_ty G i A1 A2
  : eqt (sTy G i) A1 A2 -> eq_sort ott_dtt [] (sExp G i A1) (sExp G i A2).
Proof.
  intro HA.
  destruct (wf_sort_ty_inv (eqt_wf_sort HA)) as [HG Hi].
  apply sExp_cong; [ apply eq_term_refl | apply eq_term_refl | ]; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Index normal forms are well typed                                    *)
(* ------------------------------------------------------------------ *)

Lemma RelNf_wf r : RelNf r -> wft r sRelevance.
Proof. destruct 1; [ apply wf_Rel | apply wf_Irr ]. Qed.

Lemma LvlNf_wf l : LvlNf l -> wft l sLvl.
Proof. destruct 1; [ apply wf_L0 | apply wf_L1 ]. Qed.

(* ------------------------------------------------------------------ *)
(* The "next0" bridge, at the sort level                                *)
(* ------------------------------------------------------------------ *)

(* [iCode L0 = info rel (next L0)] and [info rel (iota L1)] are the two
   spellings the elaborator left behind.  This is the only equation that
   relates them. *)
Lemma eq_info_next0 : eqt sInfo (iCode oL0) (oInfo oRel (oIota oL1)).
Proof. apply Info_cong; [ apply Rel_cong | apply eq_next0 ]. Qed.

Lemma wf_U_irr0 G : wft G sEnv -> wft (oU G oIrr oL0) (sTy G (iCode oL0)).
Proof. intro; apply wf_U; auto using wf_Irr, wf_L0. Qed.

Lemma wf_U_irr0' G
  : wft G sEnv -> wft (oU G oIrr oL0) (sTy G (oInfo oRel (oIota oL1))).
Proof.
  intro HG; eapply wf_term_conv; [ apply wf_U_irr0; exact HG | ].
  apply sTy_cong; [ apply eq_term_refl; exact HG | apply eq_info_next0 ].
Qed.

Lemma eq_sort_U_irr0 G
  : wft G sEnv ->
    eq_sort ott_dtt [] (sCode G oIrr oL0)
      (sExp G (oInfo oRel (oIota oL1)) (oU G oIrr oL0)).
Proof.
  intro HG; apply sExp_cong;
    [ apply eq_term_refl; exact HG
    | apply eq_info_next0
    | apply eq_term_refl; apply wf_U_irr0'; exact HG ].
Qed.

(* Move an irrelevant-L0 code from the [iCode] spelling (which [NormalForms.v]
   uses) to the [iota L1] spelling (which the rules "Empty", "Pi_irr" use)
   and back. *)
Lemma wft_U0irr_next G e
  : wft G sEnv -> wft e (sCode G oIrr oL0) ->
    wft e (sExp G (oInfo oRel (oIota oL1)) (oU G oIrr oL0)).
Proof.
  intros HG He; eapply wf_term_conv;
    [ exact He | apply eq_sort_U_irr0; exact HG ].
Qed.

Lemma wft_U0irr_iota G e
  : wft G sEnv -> wft e (sExp G (oInfo oRel (oIota oL1)) (oU G oIrr oL0)) ->
    wft e (sCode G oIrr oL0).
Proof.
  intros HG He; eapply wf_term_conv;
    [ exact He | apply eq_sort_sym; apply eq_sort_U_irr0; exact HG ].
Qed.

(* ------------------------------------------------------------------ *)
(* Index projections out of the sort-inversion lemmas                   *)
(* ------------------------------------------------------------------ *)

Lemma wft_exp_env G i A e : wft e (sExp G i A) -> wft G sEnv.
Proof. intro H; apply wft_exp_inv in H; tauto. Qed.

Lemma wft_exp_info G i A e : wft e (sExp G i A) -> wft i sInfo.
Proof. intro H; apply wft_exp_inv in H; tauto. Qed.

Lemma wft_exp_ty G i A e : wft e (sExp G i A) -> wft A (sTy G i).
Proof. intro H; apply wft_exp_inv in H; tauto. Qed.

Lemma wft_ty_env G i A : wft A (sTy G i) -> wft G sEnv.
Proof. intro H; apply wft_ty_inv in H; tauto. Qed.

Lemma wft_ty_info G i A : wft A (sTy G i) -> wft i sInfo.
Proof. intro H; apply wft_ty_inv in H; tauto. Qed.

Lemma wft_sub_dom G G' g : wft g (sSub G G') -> wft G sEnv.
Proof. intro H; apply wft_sub_inv in H; tauto. Qed.

Lemma wft_sub_cod G G' g : wft g (sSub G G') -> wft G' sEnv.
Proof. intro H; apply wft_sub_inv in H; tauto. Qed.

(* ================================================================== *)
(* Structural corollaries of the normal-form judgements                *)
(* ================================================================== *)

(* The ambient environment of every judgement of the block is [EnvOk].
   Proved by the combined scheme because [TyOk]'s [EnvOk] goes through
   [NfCode], which goes through [VarT]. *)
Theorem Nf_EnvOk :
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
Definition NeET_EnvOk := proj1 (proj2 (proj2 (proj2 (proj2 Nf_EnvOk)))).
Definition NfET_EnvOk := proj2 (proj2 (proj2 (proj2 (proj2 Nf_EnvOk)))).

(* [TyOk] is head-directed: a normal type headed by [U] is the [tyok_U]
   clause, so its relevance and level are in normal form. *)
Lemma TyOk_U_inv G i G' r l
  : TyOk G i (oU G' r l) -> RelNf r /\ LvlNf l.
Proof.
  intro H; remember (oU G' r l) as A eqn:HA; destruct H.
  - unfold oU in HA; safe_invert HA; split; assumption.
  - unfold oU, oEl in HA; congruence.
Qed.

Lemma EnvOk_ext_inv G i A : EnvOk (oExt G i A) -> EnvOk G /\ TyOk G i A.
Proof. inversion 1; subst; split; assumption. Qed.

(* Both [VarT] clauses carry the normal type as an explicit premise. *)
Lemma VarT_TyOk G i A x : VarT G i A x -> TyOk G i A.
Proof. destruct 1; assumption. Qed.

(* The two [VarT] clauses, inverted on the shape of the SUBJECT term.
   Both hand back the clause's own [eq_term] premise, which is what pins
   the NAMED normal representative [A] of the variable's (weakened) type;
   src/Pyrosome/Gluing/Dtt/Inj.v spends exactly that. *)

Lemma VarT_hd_inv Gx i A G0 i0 A0
  : VarT Gx i A (oHd G0 i0 A0) ->
    Gx = oExt G0 i0 A0 /\ i = i0
    /\ TyOk (oExt G0 i0 A0) i0 A
    /\ eqt (sTy (oExt G0 i0 A0) i0)
           (oTySubst (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i0 A0) A.
Proof. inversion 1; subst; repeat split; assumption. Qed.

Lemma VarT_wkn_inv Gx i A G0 j B i0 A0 x
  : VarT Gx i A (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 x) ->
    Gx = oExt G0 j B /\ i = i0
    /\ VarT G0 i0 A0 x
    /\ TyOk (oExt G0 j B) i0 A
    /\ eqt (sTy (oExt G0 j B) i0)
           (oTySubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0) A.
Proof. inversion 1; subst; repeat split; assumption. Qed.

Lemma NfCode_idx G r l c : NfCode G r l c -> RelNf r /\ LvlNf l.
Proof.
  destruct 1.
  - split; constructor.
  - split; constructor.
  - split; [ constructor | assumption ].
  - split; constructor.
  - eapply TyOk_U_inv, VarT_TyOk; eassumption.
Qed.

Lemma NfCode_RelNf G r l c : NfCode G r l c -> RelNf r.
Proof. intro H; apply NfCode_idx in H; tauto. Qed.

Lemma NfCode_LvlNf G r l c : NfCode G r l c -> LvlNf l.
Proof. intro H; apply NfCode_idx in H; tauto. Qed.

(* Neutrals and normals are indexed by a normal type. *)
Lemma NeET_TyOk G i A e : NeET G i A e -> TyOk G i A.
Proof.
  destruct 1.
  - eapply VarT_TyOk; eassumption.
  - assumption.
  - assumption.
  - apply tyok_El; assumption.
Qed.

Lemma NfET_TyOk G i A e : NfET G i A e -> TyOk G i A.
Proof.
  destruct 1.
  - apply tyok_U;
      [ eapply NfCode_EnvOk; eassumption
      | eapply NfCode_RelNf; eassumption
      | eapply NfCode_LvlNf; eassumption ].
  - apply tyok_El, nfcode_nat; assumption.
  - apply tyok_El, nfcode_nat; eapply NfET_EnvOk; eassumption.
  - apply tyok_El, nfcode_nat; eapply NeET_EnvOk; eassumption.
  - apply tyok_El, nfcode_empty; eapply NeET_EnvOk; eassumption.
  - apply tyok_El, nfcode_var; assumption.
  - apply tyok_El, nfcode_pi_rel; assumption.
  - apply tyok_El, nfcode_pi_irr; assumption.
Qed.

(* ================================================================== *)
(* The combined typing theorem                                         *)
(* ================================================================== *)

Theorem Nf_wf :
  (forall G, EnvOk G -> wf_term ott_dtt [] G sEnv)
  /\ (forall G i A, TyOk G i A -> wf_term ott_dtt [] A (sTy G i))
  /\ (forall G r l c, NfCode G r l c -> wf_term ott_dtt [] c (sCode G r l))
  /\ (forall G i A x, VarT G i A x -> wf_term ott_dtt [] x (sExp G i A))
  /\ (forall G i A e, NeET G i A e -> wf_term ott_dtt [] e (sExp G i A))
  /\ (forall G i A e, NfET G i A e -> wf_term ott_dtt [] e (sExp G i A)).
Proof.
  apply Nf_mutind.

  (* ---- EnvOk ---- *)
  - (* envok_emp *) apply wf_Emp.
  - (* envok_ext *)
    intros G i A HG IHG HA IHA.
    apply wf_Ext; [ exact IHG | eapply wft_ty_info; exact IHA | exact IHA ].

  (* ---- TyOk ---- *)
  - (* tyok_U *)
    intros G r l HG IHG Hr Hl.
    apply wf_U; auto using RelNf_wf, LvlNf_wf.
  - (* tyok_El *)
    intros G r l c Hc IHc.
    apply wf_El;
      [ eapply wft_exp_env; exact IHc
      | apply RelNf_wf; eapply NfCode_RelNf; exact Hc
      | apply LvlNf_wf; eapply NfCode_LvlNf; exact Hc
      | exact IHc ].

  (* ---- NfCode ---- *)
  - (* nfcode_nat *)
    intros G HG IHG; apply wf_Nat; exact IHG.
  - (* nfcode_empty.
       CONVERSION (A): "Empty" concludes at [info rel (iota L1)] but
       [NormalForms.v] pins the code to [sCode G irr L0 = info rel (next L0)].
       Bridge: [eq_next0], via [eq_sort_U_irr0]. *)
    intros G HG IHG.
    apply wft_U0irr_iota; [ exact IHG | apply wf_Empty; exact IHG ].
  - (* nfcode_pi_rel *)
    intros G rF lF lG F B HrF HlF HlG HF IHF HB IHB.
    apply wf_PiRel;
      [ eapply wft_exp_env; exact IHF
      | apply RelNf_wf; exact HrF
      | apply LvlNf_wf; exact HlF
      | apply LvlNf_wf; exact HlG
      | exact IHF
      | exact IHB ].
  - (* nfcode_pi_irr.
       TWO CONVERSIONS (A), both bridged by [eq_next0]:
       - the codomain premise: [NormalForms.v] gives [B] at [iCode L0] but the
         rule "Pi_irr" demands it at [info rel (iota L1)];
       - the conclusion: "Pi_irr" concludes at [info rel (iota L1)] but
         [NormalForms.v] wants [sCode G irr L0]. *)
    intros G rF lF F B HrF HlF HF IHF HB IHB.
    assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact IHF).
    assert (wft (oExtC G rF lF F) sEnv) as HXw
        by (eapply wft_exp_env; exact IHB).
    apply wft_U0irr_iota; [ exact HGw | ].
    apply wf_PiIrr;
      [ exact HGw
      | apply RelNf_wf; exact HrF
      | apply LvlNf_wf; exact HlF
      | exact IHF
      | apply wft_U0irr_next; [ exact HXw | exact IHB ] ].
  - (* nfcode_var *)
    intros G r l c Hc IHc; exact IHc.

  (* ---- VarT ---- *)
  - (* vart_hd.
       CONVERSION (B): [hd] is typed at [A[wkn]]; the clause supplies the
       normal representative [A'] and the equation identifying them. *)
    intros G i A A' HG IHG HA IHA HA' IHA' Heq.
    assert (wft i sInfo) as Hi by (eapply wft_ty_info; exact IHA).
    eapply wf_term_conv;
      [ apply wf_Hd; [ exact IHG | exact Hi | exact IHA ] | ].
    apply eq_sort_exp_ty; exact Heq.
  - (* vart_wkn.
       CONVERSION (B): [x[wkn]] is typed at [A[wkn]]; the clause supplies
       the normal representative [A'] and the equation. *)
    intros G i A x j B A' Hx IHx HB IHB HA' IHA' Heq.
    assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact IHx).
    assert (wft i sInfo) as Hi by (eapply wft_exp_info; exact IHx).
    assert (wft A (sTy G i)) as HAw by (eapply wft_exp_ty; exact IHx).
    assert (wft j sInfo) as Hj by (eapply wft_ty_info; exact IHB).
    assert (wft (oExt G j B) sEnv) as HEw
        by (apply wf_Ext; [ exact HGw | exact Hj | exact IHB ]).
    eapply wf_term_conv;
      [ apply wf_ExpSubst;
        [ exact HEw
        | exact HGw
        | apply wf_Wkn; [ exact HGw | exact Hj | exact IHB ]
        | exact Hi
        | exact HAw
        | exact IHx ]
      | ].
    apply eq_sort_exp_ty; exact Heq.

  (* ---- NeET ---- *)
  - (* neet_var *)
    intros G i A x Hx IHx; exact IHx.
  - (* neet_app_rel.
       CONVERSION (B): "app_rel" concludes at [(El B)[<id,a>]]; the clause
       supplies the normal representative [C] and the equation. *)
    intros G rF lF lG F B f a C Hf IHf Ha IHa HC IHC Heq.
    assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact IHf).
    assert (wft (iEl oRel lG) sInfo) as Hi by (eapply wft_exp_info; exact IHf).
    destruct (wft_El_args (wft_exp_ty IHf)) as [_ [Hrel [HlGw HPi]]].
    destruct (wft_PiRel_args HPi) as [_ [HrFw [HlFw [_ [HFw HBw]]]]].
    eapply wf_term_conv;
      [ apply wf_AppRel;
        [ exact HGw | exact HrFw | exact HlFw | exact HlGw
        | exact HFw | exact HBw | exact IHf | exact IHa ]
      | ].
    apply eq_sort_exp_ty; exact Heq.
  - (* neet_app_irr.
       TWO CONVERSIONS:
       (A) the codomain [B] recovered from the type of the head comes back
           at [info rel (iota L1)] (that is how "Pi_irr" stores it), but
           "app_irr" demands it at [sCode _ irr L0]; bridge [eq_next0].
       (B) "app_irr" concludes at [(El B)[<id,a>]]; the clause supplies the
           normal representative [C] and the equation. *)
    intros G rF lF F B f a C Hf IHf Ha IHa HC IHC Heq.
    assert (wft G sEnv) as HGw by (eapply wft_exp_env; exact IHf).
    assert (wft (iEl oIrr oL0) sInfo) as Hi by (eapply wft_exp_info; exact IHf).
    destruct (wft_El_args (wft_exp_ty IHf)) as [_ [_ [_ HPi]]].
    destruct (wft_PiIrr_args HPi) as [_ [HrFw [HlFw [HFw HBw]]]].
    assert (wft (oExtC G rF lF F) sEnv) as HXw
        by (apply wf_ExtC; [ exact HGw | exact HrFw | exact HlFw | exact HFw ]).
    eapply wf_term_conv;
      [ apply wf_AppIrr;
        [ exact HGw | exact HrFw | exact HlFw
        | exact HFw
        | apply wft_U0irr_iota; [ exact HXw | exact HBw ]
        | exact IHf | exact IHa ]
      | ].
    apply eq_sort_exp_ty; exact Heq.
  - (* neet_emptyrec *)
    intros G rA lA A e HA IHA He IHe.
    apply wf_Emptyrec;
      [ eapply wft_exp_env; exact IHA
      | apply RelNf_wf; eapply NfCode_RelNf; exact HA
      | apply LvlNf_wf; eapply NfCode_LvlNf; exact HA
      | exact IHA
      | exact IHe ].

  (* ---- NfET ---- *)
  - (* nfet_code *)
    intros G r l c Hc IHc; exact IHc.
  - (* nfet_zero *)
    intros G HG IHG; apply wf_Zero; exact IHG.
  - (* nfet_suc *)
    intros G n Hn IHn.
    apply wf_Suc; [ eapply wft_exp_env; exact IHn | exact IHn ].
  - (* nfet_ne_nat *)
    intros G e He IHe; exact IHe.
  - (* nfet_ne_empty *)
    intros G e He IHe; exact IHe.
  - (* nfet_ne_var *)
    intros G r l c e Hc IHc He IHe; exact IHe.
  - (* nfet_lam_rel *)
    intros G rF lF lG F B t HrF HlF HlG HF IHF HB IHB Ht IHt.
    apply wf_LamRel;
      [ eapply wft_exp_env; exact IHF
      | apply RelNf_wf; exact HrF
      | apply LvlNf_wf; exact HlF
      | apply LvlNf_wf; exact HlG
      | exact IHF | exact IHB | exact IHt ].
  - (* nfet_lam_irr.  No conversion: "lam_irr" already demands its codomain
       at [sCode _ irr L0], the spelling [NormalForms.v] uses. *)
    intros G rF lF F B t HrF HlF HF IHF HB IHB Ht IHt.
    apply wf_LamIrr;
      [ eapply wft_exp_env; exact IHF
      | apply RelNf_wf; exact HrF
      | apply LvlNf_wf; exact HlF
      | exact IHF | exact IHB | exact IHt ].
Qed.

Definition EnvOk_wf := proj1 Nf_wf.
Definition TyOk_wf := proj1 (proj2 Nf_wf).
Definition NfCode_wf := proj1 (proj2 (proj2 Nf_wf)).
Definition VarT_wf := proj1 (proj2 (proj2 (proj2 Nf_wf))).
Definition NeET_wf := proj1 (proj2 (proj2 (proj2 (proj2 Nf_wf)))).
Definition NfET_wf := proj2 (proj2 (proj2 (proj2 (proj2 Nf_wf)))).

(* ================================================================== *)
(* Weakenings                                                          *)
(* ================================================================== *)

Lemma Wk_dom D G w : Wk D G w -> EnvOk D.
Proof.
  induction 1; [ assumption | | | ]; apply envok_ext; assumption.
Qed.

Lemma Wk_cod D G w : Wk D G w -> EnvOk G.
Proof.
  induction 1;
    [ assumption | assumption | assumption | apply envok_ext; assumption ].
Qed.

(* The equation the [wk_lift] conversion needs:
     [A'[wkn]]  =  [A[wkn o w]]
   It is NOT supplied by the clause -- what the clause supplies is
   [A[w] = A'] -- so it is derived here: transport that equation under
   [wkn] with [TySubst_cong], then collapse the two substitutions with
   "ty_subst_cmp". *)
Lemma eq_wk_lift_ty D G i A A' w
  : wft D sEnv -> wft G sEnv -> wft i sInfo ->
    wft A (sTy G i) -> wft A' (sTy D i) -> wft w (sSub D G) ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    eqt (sTy (oExt D i A') i)
      (oTySubst (oExt D i A') D (oWkn D i A') i A')
      (oTySubst (oExt D i A') G (oCmp (oExt D i A') D G (oWkn D i A') w) i A).
Proof.
  intros HD HG Hi HA HA' Hw Heq.
  assert (wft (oExt D i A') sEnv) as HE
      by (apply wf_Ext; [ exact HD | exact Hi | exact HA' ]).
  assert (wft (oWkn D i A') (sSub (oExt D i A') D)) as HW
      by (apply wf_Wkn; [ exact HD | exact Hi | exact HA' ]).
  eapply eq_term_trans.
  - apply TySubst_cong with (A1 := A') (A2 := oTySubst D G w i A);
      [ apply eq_term_refl; exact HE
      | apply eq_term_refl; exact HD
      | apply eq_term_refl; exact HW
      | apply eq_term_refl; exact Hi
      | apply eq_term_sym; exact Heq ].
  - apply eq_ty_subst_cmp;
      [ exact HE | exact HD | exact HG | exact HW | exact Hw | exact Hi
      | exact HA ].
Qed.

Lemma Wk_wf D G w : Wk D G w -> wf_term ott_dtt [] w (sSub D G).
Proof.
  induction 1.
  - (* wk_id *)
    apply wf_Id; apply EnvOk_wf; assumption.
  - (* wk_wkn *)
    match goal with
    | [ HT : TyOk _ _ _ |- _ ] => pose proof (TyOk_wf HT) as HAw
    end.
    apply wf_Wkn;
      [ eapply wft_ty_env; exact HAw | eapply wft_ty_info; exact HAw
      | exact HAw ].
  - (* wk_ext *)
    match goal with
    | [ HT : TyOk _ _ _ |- _ ] =>
        pose proof (TyOk_wf HT) as HAw
    end.
    assert (wft D sEnv) as HDw by (eapply wft_ty_env; exact HAw).
    assert (wft i sInfo) as Hi by (eapply wft_ty_info; exact HAw).
    assert (wft G sEnv) as HGw by (eapply wft_sub_cod; exact IHWk).
    apply wf_Cmp;
      [ apply wf_Ext; [ exact HDw | exact Hi | exact HAw ]
      | exact HDw | exact HGw
      | apply wf_Wkn; [ exact HDw | exact Hi | exact HAw ]
      | exact IHWk ].
  - (* wk_lift.
       CONVERSION: the head variable [hd D i A'] is typed at [A'[wkn]],
       while [snoc] demands its value at [A[wkn o w]].  Bridge:
       [eq_wk_lift_ty] (the clause's equation [A[w] = A'] transported under
       [wkn] and collapsed by "ty_subst_cmp"). *)
    match goal with
    | [ HT : TyOk G _ _, HT' : TyOk D _ _ |- _ ] =>
        pose proof (TyOk_wf HT) as HAw; pose proof (TyOk_wf HT') as HA'w
    end.
    assert (wft G sEnv) as HGw by (eapply wft_ty_env; exact HAw).
    assert (wft D sEnv) as HDw by (eapply wft_ty_env; exact HA'w).
    assert (wft i sInfo) as Hi by (eapply wft_ty_info; exact HAw).
    assert (wft (oExt D i A') sEnv) as HEw
        by (apply wf_Ext; [ exact HDw | exact Hi | exact HA'w ]).
    assert (wft (oWkn D i A') (sSub (oExt D i A') D)) as HWw
        by (apply wf_Wkn; [ exact HDw | exact Hi | exact HA'w ]).
    apply wf_Snoc;
      [ exact HEw | exact HGw | exact Hi | exact HAw
      | apply wf_Cmp;
        [ exact HEw | exact HDw | exact HGw | exact HWw | exact IHWk ]
      | ].
    eapply wf_term_conv;
      [ apply wf_Hd; [ exact HDw | exact Hi | exact HA'w ] | ].
    apply eq_sort_exp_ty; apply eq_wk_lift_ty;
        [ exact HDw | exact HGw | exact Hi | exact HAw | exact HA'w
        | exact IHWk | assumption ].
Qed.

(* ------------------------------------------------------------------ *)
(* Hints                                                                *)
(* ------------------------------------------------------------------ *)

#[export] Hint Resolve
  RelNf_wf LvlNf_wf
  EnvOk_wf TyOk_wf NfCode_wf VarT_wf NeET_wf NfET_wf
  Wk_wf
  TyOk_EnvOk NfCode_EnvOk VarT_EnvOk NeET_EnvOk NfET_EnvOk
  VarT_TyOk NeET_TyOk NfET_TyOk
  Wk_dom Wk_cod
  wft_U0irr_next wft_U0irr_iota
  : dtt_wf.
