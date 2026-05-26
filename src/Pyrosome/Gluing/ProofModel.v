Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Proof Require Import TreeProofs.
From Pyrosome.Gluing Require Import TModel.
Import Core.Notations.

(* The initial Type-valued model: its judgments are *checkable proof terms*
   (TreeProofs.pf).  Because [pf] is cut-free (substitution is baked into [pcon]
   rule applications, not a separate constructor), a generic evaluation can
   recurse on a [pf] via [pf_rect] and only ever sees [pvar]/[pcon]/[ptrans]/
   [psym]/[pconv] — in particular [pconv] makes the otherwise Prop->Type-forbidden
   conversion case an explicit constructor.  Soundness of the checker bridges
   these Type-valued judgments back to Theory/Core.v's Prop judgments. *)
Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation lang := (@lang V).
  Notation pf := (@pf V).
  Notation wf_ctx l := (wf_ctx (Model := core_model l)).

  Definition ProofModel (l : lang) : TModel term sort :=
    {|
      tpremodel := @syntax_model V V_Eqb;
      teq_sort c t1 t2 := { p & check_sort_proof l c p = Some (t1, t2) };
      teq_term c t e1 e2 := { p & check_proof l c p = Some (e1, e2, t) };
      twf_sort c t := { p & check_sort_proof l c p = Some (t, t) };
      twf_term c e t := { p & check_proof l c p = Some (e, e, t) };
    |}.

  (* Bridge to the syntactic (Prop) model via the checker's soundness. *)
  Lemma proofmodel_eq_sort_sound (l : lang) c t1 t2
    : wf_lang l -> wf_ctx l c ->
      teq_sort (TModel := ProofModel l) c t1 t2 -> eq_sort l c t1 t2.
  Proof.
    intros wfl wfc H; cbn in H; destruct H as [p Hp].
    exact (proj1 (@pf_checker_sound V V_Eqb V_Eqb_ok l c wfl p) t1 t2 Hp).
  Qed.

  Lemma proofmodel_eq_term_sound (l : lang) c t e1 e2
    : wf_lang l -> wf_ctx l c ->
      teq_term (TModel := ProofModel l) c t e1 e2 -> eq_term l c t e1 e2.
  Proof.
    intros wfl wfc H; cbn in H; destruct H as [p Hp].
    exact (proj2 (@pf_checker_sound V V_Eqb V_Eqb_ok l c wfl p) t e1 e2 Hp).
  Qed.

  Lemma proofmodel_wf_term_sound (l : lang) c e t
    : wf_lang l -> wf_ctx l c ->
      twf_term (TModel := ProofModel l) c e t -> eq_term l c t e e.
  Proof.
    intros wfl wfc H; cbn in H; destruct H as [p Hp].
    exact (proj2 (@pf_checker_sound V V_Eqb V_Eqb_ok l c wfl p) t e e Hp).
  Qed.

  Lemma proofmodel_wf_sort_sound (l : lang) c t
    : wf_lang l -> wf_ctx l c ->
      twf_sort (TModel := ProofModel l) c t -> eq_sort l c t t.
  Proof.
    intros wfl wfc H; cbn in H; destruct H as [p Hp].
    exact (proj1 (@pf_checker_sound V V_Eqb V_Eqb_ok l c wfl p) t t Hp).
  Qed.

  (* Structural reflexivity proof term for a (directly-typed) term.  Its
     correctness (check_proof (reflect_tm e) = Some (e,e,t) for well-typed e with
     no conversions) is the Prop->Type bridge, established with the full checker in
     a later module (M6). *)
  Fixpoint reflect_tm (e : term) : pf :=
    match e with
    | var x => pvar x
    | con n s => pcon n (map reflect_tm s)
    end.

End WithVar.
