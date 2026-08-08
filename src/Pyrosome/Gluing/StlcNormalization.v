Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC.
Import Core.Notations.

(* Normalization for call-by-value STLC with explicit substitutions, i.e. for
   [stlc ++ exp_subst ++ value_subst].

   This file fixes the language, discharges its well-formedness, and specializes
   the generic driver of Gluing/CutModelSound.v to it.  The resulting statement
   is the precise reduction of "normalization" to "a cut-free model": once a
   [CutTModel] for this language is built whose [ceq_term t e e] asserts that [e]
   has a normal form at [t], [stlc_normalization_from_model] delivers that for
   every well-typed [e]. *)

Definition stlc_full := stlc ++ exp_subst ++ value_subst.

Lemma stlc_full_wf : wf_lang stlc_full.
Proof.
  unfold stlc_full.
  apply wf_lang_concat.
  - apply wf_lang_concat.
    + exact value_subst_wf.
    + exact exp_subst_wf.
  - exact stlc_wf.
Qed.

Section WithCtx.
  Context (c : ctx)
    (wfc : wf_ctx (Model := core_model stlc_full) c).

  Context {CM : CutTModel}
    {CMok : CutTModel_ok stlc_full c}.

  (* Normalization, modulo the model.  [ceq_term t e e] is whatever content the
     model attaches to a term; for a normalization model that content is its
     normal form, so this says every well-typed term of the language has one. *)
  Theorem stlc_normalization_from_model t e
    : wf_term stlc_full c e t ->
      inhabited (ceq_term (CutTModel := CM) t e e).
  Proof.
    intro Hwf.
    (* [l] occurs only in the hypotheses of the driver, so it has to be given. *)
    eapply (cut_model_normalization stlc_full_wf wfc); eassumption.
  Qed.

  (* The equational form: provably-equal terms receive equal content. *)
  Theorem stlc_eq_sound t e1 e2
    : eq_term stlc_full c t e1 e2 ->
      inhabited (ceq_term (CutTModel := CM) t e1 e2).
  Proof.
    intro Heq.
    eapply (cut_model_inhabited stlc_full_wf wfc); eassumption.
  Qed.

End WithCtx.
