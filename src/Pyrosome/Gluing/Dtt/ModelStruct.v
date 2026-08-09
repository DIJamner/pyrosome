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
  Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelCand Pyrosome.Gluing.Dtt.RSub Pyrosome.Gluing.Dtt.Ceq.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4b: the STRUCTURAL and SORT obligations of
   [CutTModel_ok ott_dtt [] (CM := DttCM)].

   The analogue of Gluing/Stlc/ModelCong.v's first half.  Each field is a
   standalone top-level lemma so the record can be assembled elsewhere;
   [cterm_cong] and [cterm_by] are developed independently.

   Everything goes through src/Pyrosome/Gluing/Dtt/Ceq.v's constructors and clause lemmas
   ([ceq_relevance] .. [ceq_exp], [Ceq_relevance_e] .. [Ceq_exp_e]);
   [Ceq_term] is inverted by hand nowhere.

   RESULT.  All sixteen obligations covered here are proved outright and
   unconditionally: the seven structural/sort fields ([cterm_var],
   [csort_by], [cterm_conv], [csort_trans], [csort_sym], [cterm_trans],
   [cterm_sym]) and all nine cases of [csort_cong].  Only [cterm_cong] and
   [cterm_by] are developed elsewhere.

   THE SORT TRANSFERS ARE CHEAP -- BUT ONLY BECAUSE EVERY SORT INDEX IS
   QUANTIFIED UP TO [eq_term].  See the note at section 4's [ty] case: an
   earlier version of Layers 2/3 held the info index and the codomain
   environment FIXED, and the resulting [csort_cong] was refutable modulo
   consistency.  With [RTmN]/[RTyN] quantifying [i] and [RSubN] quantifying
   [G], each transfer direction is now a use of transitivity
   ([RTyN_eq_info] / [RTmN_eq_info] / [RSubN_env]) composed with the
   type/subject closure lemmas and one congruence from src/Pyrosome/Gluing/Dtt/Eqns.v.
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

(* The same for a substitution reducible only up to a provable equality of
   the codomain environment: transport the sort along [sSub_cong]. *)
Lemma RSubN_wf D G g : RSubN D G g -> wft g (sSub D G).
Proof.
  intros [G0 (HG0 & Heq & HR)].
  apply RSub_wf in HR.
  eapply wf_term_conv; [ exact HR | ].
  apply sSub_cong;
    [ apply eq_term_refl; eapply wft_sub_dom; exact HR
    | apply eq_term_sym; exact Heq ].
Qed.

(* [RTmN] is closed under provable equality of the TYPE, exactly as
   [RTyN_eq] is: the representative is quantified up to [eq_term] already,
   so this is one transitivity plus the sort conversion that [RTmN]'s
   quantified info index forces ([sTy_cong]).  The [subject] and [info]
   versions are [RTmN_eq] / [RTmN_eq_info] in Layers 2a/2b. *)
Lemma RTmN_eq_ty G i A A' e
  : RTmN G i A e -> eqt (sTy G i) A A' -> RTmN G i A' e.
Proof.
  intros He Heq i0 A0 Hi HT HA0.
  apply He; try assumption.
  eapply eq_term_trans; [ | exact HA0 ].
  destruct (wf_sort_ty_inv (eqt_wf_sort HA0)) as [HG _].
  eapply eq_term_conv; [ exact Heq | ].
  apply sTy_cong; [ apply eq_term_refl; exact HG | exact Hi ].
Qed.

(* ================================================================== *)
(* 1.  The vacuous / immediate obligations                             *)
(* ================================================================== *)

(* [cterm_var]: the ambient meta-context is empty (openness is
   object-level: object variables are [hd] and its [wkn]-shifts, see
   [VarT] in src/Pyrosome/Gluing/Dtt/NormalForms.v), so there are no meta-variables to relate. *)
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
   of src/Pyrosome/Gluing/Dtt/Eqns.v ([Cmp_cong] / [TySubst_cong] / [ExpSubst_cong]).  Note
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
    apply RSubN_eq with (g := oCmp D G G' h g1); [ apply Hb; assumption | ].
    apply Cmp_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact HwG
      | apply eq_term_refl; exact HwG'
      | apply eq_term_refl; apply RSubN_wf; exact Hh
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
      | apply eq_term_refl; apply RSubN_wf; exact Hg
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
      | apply eq_term_refl; apply RSubN_wf; exact Hg
      | apply eq_term_refl; exact Hwi
      | apply eq_term_refl; exact HwA
      | exact Ha ].
Qed.


(* ================================================================== *)
(* 4.  Sort congruence                                                 *)
(* ================================================================== *)

(* [ott_dtt] has nine sort rules, so computing the membership premise
   splits the obligation nine ways.  The goals come out in the language's
   own order:

     exp, ty, sub, env, tyinfo, tlvl, ltl, lvl, relevance.

   SIX are settled outright by [Ceq_sort_refl]:

     - [env], [tyinfo], [tlvl], [lvl], [relevance] are NULLARY sort rules,
       so [s1 = s2 = []] and the two sorts are syntactically identical;
     - [ltl]'s two arguments are at [lvl], where [Ceq_term] IS identity
       ([Ceq_lvl_e]), so again [s1 = s2].  (Proof irrelevance --
       [eq_ltl_irr] -- is not needed: it would be, if [Ceq_term] at [lvl]
       carried an equation rather than an identity.)

   The three substantive ones are the transfer lemmas below. *)

(* ---- the three transfers ---------------------------------------- *)

(* Each is stated in ONE direction only and applied twice, with the
   argument equations reversed, to give both halves of [Ceq_sort]. *)

Lemma ceq_sub_transfer G1 G2 G1' G2' g1 g2
  : eqt sEnv G1 G2 -> eqt sEnv G1' G2' ->
    Ceq_term (sSub G1 G1') g1 g2 -> Ceq_term (sSub G2 G2') g1 g2.
Proof.
  intros H12 H12' Hc.
  apply Ceq_sub_e in Hc as [Ha Hb].
  assert (eqt (sSub G2 G2') g1 g2) as Ha'
      by (eapply eq_term_conv; [ exact Ha | apply sSub_cong; assumption ]).
  apply ceq_sub; [ exact Ha' | ].
  intros D h HD Hh.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft h (sSub D G2)) as Hwh by (apply RSubN_wf; exact Hh).
  (* [RSubN] is stable under equality of the codomain environment in BOTH
     directions -- that is the whole point of the wrapper. *)
  apply RSubN_eq with (g := oCmp D G1 G1' h g1).
  - apply RSubN_env with (G := G1');
      [ apply Hb; [ exact HD | eapply RSubN_env;
                    [ exact Hh | apply eq_term_sym; exact H12 ] ]
      | exact H12' ].
  - apply Cmp_cong;
      [ apply eq_term_refl; exact HwD
      | exact H12
      | exact H12'
      | apply eq_term_refl; exact Hwh
      | apply eq_term_refl; eapply eqt_wf_l; exact Ha' ].
Qed.

(* THE [ty] CASE, AND THE BUG THAT IS NOT THERE ANY MORE.
   [RTyN D i X] asks for a normal representative [A0] with [TyOk D i0 A0]
   for SOME [i0] provably equal to [i].  An earlier version of src/Pyrosome/Gluing/Dtt/LogRel.v
   held [i0 := i] fixed, and this transfer was then REFUTABLE modulo
   consistency, not merely unproved.  The reason: [TyOk]'s info index is
   syntactic BY DESIGN (src/Pyrosome/Gluing/Dtt/NormalForms.v's header) -- a universe is pinned at
   [iCode l = info rel (next l)], an [El] at [iEl r l = info r (iota l)] --
   whereas "next0" makes [iCode L0] and [iEl rel L1] provably equal infos,
   and [Ceq_term] at [tyinfo] relates them (it only demands equal
   [ninfo]s).  So [ty G (iCode L0)] and [ty G (iEl rel L1)] are provably
   equal sorts whose sets of normal representatives are DISJOINT.  Taking
   [A1 := U emp irr L0], whose reducibility at [iCode L0] is immediate from
   "U subst" and [rty_U], the fixed-index transfer forced
   [RTyN emp (iEl rel L1) (U emp irr L0)]; the only [TyOk]s at that info
   are [El emp rel L1 c], and the only normal code there (no variables in
   [emp], [Nat] is at L0, [Empty]/[Pi_irr] are irrelevant) is a [Pi_rel] --
   i.e. the closed universe would have to be provably equal to the [El] of
   a closed relevant [Pi] code, which [ott_dtt] does not prove (there is no
   code for a universe: [U] is a sort former, see Lang/OTT/Base.v).
   Quantifying [i0] absorbs the aliasing here, leaving [TyOk]'s pinned
   infos alone, and the transfer becomes [RTyN_eq_info] -- transitivity. *)
Lemma ceq_ty_transfer G1 G2 i1 i2 A1 A2
  : eqt sEnv G1 G2 -> eqt sInfo i1 i2 ->
    Ceq_term (sTy G1 i1) A1 A2 -> Ceq_term (sTy G2 i2) A1 A2.
Proof.
  intros H12 Hi12 Hc.
  apply Ceq_ty_e in Hc as [Ha Hb].
  assert (eqt (sTy G2 i2) A1 A2) as Ha'
      by (eapply eq_term_conv; [ exact Ha | apply sTy_cong; assumption ]).
  apply ceq_ty; [ exact Ha' | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  apply RTyN_eq with (A := oTySubst D G1 g i1 A1).
  - apply RTyN_eq_info with (i := i1); [ | exact Hi12 ].
    apply Hb; [ exact HD | ].
    eapply RSubN_env; [ exact Hg | apply eq_term_sym; exact H12 ].
  - apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | exact H12
      | apply eq_term_refl; exact Hwg
      | exact Hi12
      | apply eq_term_refl; eapply eqt_wf_l; exact Ha' ].
Qed.

Lemma ceq_exp_transfer G1 G2 i1 i2 A1 A2 e1 e2
  : eqt sEnv G1 G2 -> eqt sInfo i1 i2 -> eqt (sTy G2 i2) A1 A2 ->
    Ceq_term (sExp G1 i1 A1) e1 e2 -> Ceq_term (sExp G2 i2 A2) e1 e2.
Proof.
  intros H12 Hi12 HA Hc.
  apply Ceq_exp_e in Hc as [Ha Hb].
  assert (eqt (sExp G2 i2 A2) e1 e2) as Ha'
      by (eapply eq_term_conv; [ exact Ha | apply sExp_cong; assumption ]).
  apply ceq_exp; [ exact Ha' | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G2)) as Hwg by (apply RSubN_wf; exact Hg).
  assert (eqt (sTy D i2)
              (oTySubst D G1 g i1 A1) (oTySubst D G2 g i2 A2)) as Hty.
  { apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | exact H12
      | apply eq_term_refl; exact Hwg
      | exact Hi12
      | exact HA ]. }
  (* three moves, each side-condition-free: the info, then the type, then
     the subject. *)
  apply RTmN_eq with (e := oExpSubst D G1 g i1 A1 e1).
  - apply RTmN_eq_ty with (A := oTySubst D G1 g i1 A1); [ | exact Hty ].
    apply RTmN_eq_info with (i := i1); [ | exact Hi12 ].
    apply Hb; [ exact HD | ].
    eapply RSubN_env; [ exact Hg | apply eq_term_sym; exact H12 ].
  - apply ExpSubst_cong;
      [ apply eq_term_refl; exact HwD
      | exact H12
      | apply eq_term_refl; exact Hwg
      | exact Hi12
      | exact HA
      | apply eq_term_refl; eapply eqt_wf_l; exact Ha' ].
Qed.

(* ---- packaged as [Ceq_sort] -------------------------------------- *)

(* Each transfer lemma is applied twice, with the argument equations
   reversed.  Only the [exp] case needs a conversion to do so: its type
   equation is stated at the RIGHT sort ([sTy G2 i2], as [ceq_args]
   delivers it), and the reversed direction wants it at the left one. *)

Lemma Ceq_sort_sub G1 G2 G1' G2'
  : eqt sEnv G1 G2 -> eqt sEnv G1' G2' ->
    Ceq_sort (sSub G1 G1') (sSub G2 G2').
Proof.
  intros H12 H12'; repeat split.
  - apply sSub_cong; assumption.
  - intros; eapply ceq_sub_transfer; eassumption.
  - intros; eapply ceq_sub_transfer;
      [ apply eq_term_sym; exact H12
      | apply eq_term_sym; exact H12'
      | eassumption ].
Qed.

Lemma Ceq_sort_ty G1 G2 i1 i2
  : eqt sEnv G1 G2 -> eqt sInfo i1 i2 -> Ceq_sort (sTy G1 i1) (sTy G2 i2).
Proof.
  intros H12 Hi12; repeat split.
  - apply sTy_cong; assumption.
  - intros; eapply ceq_ty_transfer; eassumption.
  - intros; eapply ceq_ty_transfer;
      [ apply eq_term_sym; exact H12
      | apply eq_term_sym; exact Hi12
      | eassumption ].
Qed.

Lemma Ceq_sort_exp G1 G2 i1 i2 A1 A2
  : eqt sEnv G1 G2 -> eqt sInfo i1 i2 -> eqt (sTy G2 i2) A1 A2 ->
    Ceq_sort (sExp G1 i1 A1) (sExp G2 i2 A2).
Proof.
  intros H12 Hi12 HA.
  assert (eqt (sTy G1 i1) A1 A2) as HA'
      by (eapply eq_term_conv;
          [ exact HA | apply eq_sort_sym; apply sTy_cong; assumption ]).
  repeat split.
  - apply sExp_cong; assumption.
  - intros; eapply ceq_exp_transfer; eassumption.
  - intros; eapply ceq_exp_transfer;
      [ apply eq_term_sym; exact H12
      | apply eq_term_sym; exact Hi12
      | apply eq_term_sym; exact HA'
      | eassumption ].
Qed.

(* ---- the obligation ---------------------------------------------- *)

Lemma sort_cong_obligation
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
  (* The sorts in [Hargs] are presented as [t[/with_names_from c' s2/]], so
     the clause readings are applied by unification, not by matching. *)
  all: repeat match goal with
              | [ H : Ceq_term _ _ _ |- _ ] =>
                  first [ apply Ceq_env_e in H
                        | apply Ceq_tyinfo_e in H
                        | apply Ceq_ty_e in H
                        | apply Ceq_lvl_e in H ];
                  destruct H as [H ?]
              end.
  - (* exp *) apply Ceq_sort_exp; assumption.
  - (* ty *) apply Ceq_sort_ty; assumption.
  - (* sub *) apply Ceq_sort_sub; assumption.
  - (* env *) apply Ceq_sort_refl, wf_sort_env.
  - (* tyinfo *) apply Ceq_sort_refl, wf_sort_info.
  - (* tlvl *) apply Ceq_sort_refl, wf_sort_tlvl.
  - (* ltl: both arguments are at [lvl], where [Ceq_term] is identity, so
       the two sorts are syntactically equal.  (Proof irrelevance --
       [eq_ltl_irr] -- is not needed here.) *)
    subst; apply Ceq_sort_refl, wf_sort_ltl; apply LvlNf_wf; assumption.
  - (* lvl *) apply Ceq_sort_refl, wf_sort_lvl.
  - (* relevance *) apply Ceq_sort_refl, wf_sort_relevance.
Qed.

(* ================================================================== *)
(* 5.  Assembly                                                        *)
(* ================================================================== *)

(* The two obligations developed elsewhere.  Naming them here is not idle:
   building the record below CHECKS that the sixteen statements above have
   exactly the shapes the class's fields demand (argument order, the
   [with_names_from c' s2] on the conclusion sort, the [ceq_term]/
   [ceq_sort] projections of [DttCM]).

   NB the record must be built with tactics: the [{| ... |}] literal makes
   elaboration diverge (stack overflow) on this class. *)

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

Definition DttCM_ok (Hcong : CongObligation) (Hby : ByObligation)
  : CutTModel_ok (V := string) ott_dtt [] (CM := DttCM).
Proof.
  constructor.
  - exact var_obligation.
  - exact Hcong.
  - exact Hby.
  - exact term_trans_obligation.
  - exact term_sym_obligation.
  - exact term_conv_obligation.
  - exact sort_cong_obligation.
  - exact sort_by_obligation.
  - exact sort_trans_obligation.
  - exact sort_sym_obligation.
Defined.
