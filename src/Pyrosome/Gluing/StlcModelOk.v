Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound
  StlcModel StlcNormalization StlcNormalForms StlcEqns StlcLogRel StlcRSub
  StlcCeq StlcModelCong StlcModelEq.
Import Core.Notations.

(* Layer 4c: assembly.

   The two halves of [CutTModel_ok] -- the 16 congruence + 5 sort obligations
   (StlcModelCong.v) and the 18 equation obligations (StlcModelEq.v) -- are
   plugged into the class, and the normalization theorem follows.

   [cterm_var] and [csort_by] are vacuous here: the meta-context is empty, and
   this language has no sort equations. *)

#[export] Instance StlcCM_ok : CutTModel_ok (CM := StlcCM) stlc_unit [].
Proof.
  constructor.
  - exact var_obligation.
  - exact cong_obligation.
  - exact by_obligation.
  - exact term_trans_obligation.
  - exact term_sym_obligation.
  - exact term_conv_obligation.
  - exact sort_cong_obligation.
  - exact sort_by_obligation.
  - exact sort_trans_obligation.
  - exact sort_sym_obligation.
Defined.

Lemma wf_ctx_nil_stlc : wf_ctx (Model := core_model stlc_unit) [].
Proof. constructor. Qed.

(* NORMALIZATION.

   Every well-typed expression of [stlc_unit] is provably equal to a canonical
   form.  Note this is genuinely about OPEN terms: openness is carried by the
   object-level environment [G], whose variables are [hd] and its [wkn]-shifts,
   so the meta-context can stay empty. *)
Theorem stlc_unit_normalization G A e
  : EnvOk G -> TyOk A ->
    wf_term stlc_unit [] e (Sexp G A) ->
    exists n, NfE n /\ eq_term stlc_unit [] (Sexp G A) e n.
Proof.
  intros HG HA Hwf.
  (* the model gives content at [e] from well-typedness alone *)
  destruct (normalization_from_model (CM := StlcCM) (CMok := StlcCM_ok)
              stlc_unit_wf wf_ctx_nil_stlc Hwf) as [Hceq].
  apply Ceq_exp_e in Hceq.
  destruct Hceq as [_ Hsem].
  (* instantiate the reducible-substitution quantifier at the identity *)
  specialize (Hsem G (Id G) HG (RSub_id HG)).
  assert (Heq : eq_term stlc_unit [] (Sexp G A) (ExpSubst G G (Id G) A e) e)
    by (apply eq_exp_subst_id; auto using EnvOk_wf, TyOk_wf).
  pose proof (RE_eq Hsem Heq) as Hre.
  destruct (CR_reify_E Hre) as [n [Hn Hen]].
  exists n; split.
  - eapply NfET_NfE; exact Hn.
  - exact Hen.
Qed.

(* The equational corollary: provably equal terms have a common canonical form. *)
Theorem stlc_unit_eq_normalization G A e1 e2
  : EnvOk G -> TyOk A ->
    eq_term stlc_unit [] (Sexp G A) e1 e2 ->
    exists n, NfE n
              /\ eq_term stlc_unit [] (Sexp G A) e1 n
              /\ eq_term stlc_unit [] (Sexp G A) e2 n.
Proof.
  intros HG HA Heq.
  destruct (eq_sound (CM := StlcCM) (CMok := StlcCM_ok)
              stlc_unit_wf wf_ctx_nil_stlc Heq) as [Hceq].
  apply Ceq_exp_e in Hceq.
  destruct Hceq as [Hq Hsem].
  specialize (Hsem G (Id G) HG (RSub_id HG)).
  assert (Hwf1 : wf_term stlc_unit [] e1 (Sexp G A)) by (eapply eqt_wf_l; exact Heq).
  assert (Hid : eq_term stlc_unit [] (Sexp G A) (ExpSubst G G (Id G) A e1) e1)
    by (apply eq_exp_subst_id; auto using EnvOk_wf, TyOk_wf).
  pose proof (RE_eq Hsem Hid) as Hre.
  destruct (CR_reify_E Hre) as [n [Hn Hen]].
  exists n; split; [ eapply NfET_NfE; exact Hn | split ].
  - exact Hen.
  - eapply eq_term_trans; [ apply eq_term_sym; exact Hq | exact Hen ].
Qed.
