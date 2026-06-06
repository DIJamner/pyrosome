(* ====================================================================== *)
(* OTT pivot, file 1/5 (see WIP/NEXT_SESSION.md UPDATE-n / -o).            *)
(*                                                                        *)
(* Reduction over CLOSED Pyrosome terms (Pyrosome ctx = []; object        *)
(* open-ness lives in the `env` carried by the sort).  A reduction step is *)
(* the LHS of an (oriented) computation `term_eq_rule`, instantiated by a  *)
(* closed substitution.  Soundness (`step ⊆ eq_term`) is free via         *)
(* `eq_term_by` + `eq_term_subst`; subject reduction and the              *)
(* reflexive-transitive closure come from `Compilers/OperationalBridge.v`. *)
(*                                                                        *)
(* Everything here is GENERIC over an arbitrary `wf_lang l`; the OTT       *)
(* instantiation (`ott_full`) is a downstream corollary.  Weak-head        *)
(* evaluation-context congruence is deferred to Neutral.v, where the spine *)
(* structure of OTT eliminators is available.                             *)
(* ====================================================================== *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core ModelImpls.
(* NB: imported QUALIFIED (no `Import`) -- WfCutElim's `Import` shadows the
   bare `wf_term`/`wf_args` names this file relies on. *)
From Pyrosome.Theory Require WfCutElim.
From Pyrosome.Compilers Require Import OperationalBridge.
Import Core.Notations.

(* Functional update of a list at an index; identity if [i] is out of range.
   Used to express the result of a weak-head congruence step (reduce the
   principal argument of an eliminator spine). *)
Fixpoint set_nth {A} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, 0 => x :: t
  | h :: t, S i' => h :: set_nth t i' x
  end.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).

  Section WithLang.
    Context (l : lang) (wfl : wf_lang l).

    (* A redex is the LHS of a computation rule instantiated by a closed
       substitution; it rewrites to the (instantiated) RHS at the
       (instantiated) rule type. *)
    Inductive step : sort -> term -> term -> Prop :=
    | step_redex : forall name c e1 e2 t s,
        In (name, term_eq_rule c e1 e2 t) l ->
        wf_subst l [] s c ->
        step t[/s/] e1[/s/] e2[/s/].

    Lemma step_sound : rel_sound V l step.
    Proof.
      intros a b t Hwf Hstep.
      destruct Hstep as [name c e1 e2 t0 s Hin Hs].
      assert (wf_ctx l c) as Hc by with_rule_in_wf_crush.
      eapply eq_term_subst.
      - eapply eq_term_by; eauto.
      - eapply eq_subst_refl; eauto.
      - assumption.
    Qed.

    (* Subject reduction and the closure lemmas, specialised from
       OperationalBridge to this `step`. *)

    Lemma step_wf t a b
      : wf_term l [] a t -> step t a b -> wf_term l [] b t.
    Proof. eapply OperationalBridge.step_wf; eauto using step_sound. Qed.

    Lemma star_step_wf t a b
      : wf_term l [] a t -> star (step t) a b -> wf_term l [] b t.
    Proof. eapply OperationalBridge.star_step_wf; eauto using step_sound. Qed.

    Lemma star_step_sound : rel_sound V l (fun t => star (step t)).
    Proof. eapply OperationalBridge.star_step_sound; eauto using step_sound. Qed.

    (* ------------------------------------------------------------------ *)
    (* Sort-ERASED redex relation.  This is the substrate for the         *)
    (* weak-head reduction whose head-congruence cases reduce a sub-term   *)
    (* at a DIFFERENT sort than the whole term — so the relation cannot    *)
    (* carry the sort.  Soundness recovers it from `wf_term` via the       *)
    (* sort-uniqueness theorem `term_sorts_eq` (Dustin's call).           *)
    (* ------------------------------------------------------------------ *)
    Definition redex (a b : term) : Prop :=
      exists name c e1 e2 t s,
        In (name, term_eq_rule c e1 e2 t) l /\
        wf_subst l [] s c /\
        a = e1[/s/] /\ b = e2[/s/].

    Lemma redex_sound a b t
      : wf_term l [] a t -> redex a b -> eq_term l [] t a b.
    Proof.
      intros Hwf (name & c & e1 & e2 & t0 & s & Hin & Hs & -> & ->).
      assert (wf_ctx l c) as Hc by with_rule_in_wf_crush.
      assert (wf_term l c e1 t0) as He1 by with_rule_in_wf_crush.
      (* the equality at the rule's (instantiated) sort *)
      assert (eq_term l [] t0[/s/] e1[/s/] e2[/s/]) as Heq.
      {
        eapply eq_term_subst.
        - eapply eq_term_by; eauto.
        - eapply eq_subst_refl; eauto.
        - assumption.
      }
      (* realign to the sort `t` at which `e1[/s/]` is actually well-typed *)
      assert (wf_term l [] e1[/s/] t0[/s/]) as Hwf0
          by (eapply wf_term_subst_monotonicity; eauto).
      eapply eq_term_conv; [ exact Heq | ].
      eapply term_sorts_eq with (e := e1[/s/]); eauto with lang_core.
    Qed.

    (* ------------------------------------------------------------------ *)
    (* "One position steps, the rest are refl" for `eq_args`.              *)
    (*                                                                    *)
    (* The directive (NEXT_SESSION UPDATE-q) anticipated a non-occurrence  *)
    (* SIDE-CONDITION here (the changed argument must not appear in the     *)
    (* sorts of the later-bound siblings).  It turns out NOT to be needed:  *)
    (* the stepped argument `a` and its reduct `b` are CONVERTIBLE (the     *)
    (* sort-erased IH gives `eq_term [] _ a b`), so the sort of every       *)
    (* sibling whose type mentions the principal position is preserved UP   *)
    (* TO `eq_sort` — exactly the conversion `wf_term_conv` consumes.  So   *)
    (* this congruence is GENERIC, no non-occurrence gate.                 *)
    (* ------------------------------------------------------------------ *)
    Lemma eq_args_step_at c' args i a b
      : wf_ctx l c' ->
        wf_args l [] args c' ->
        nth_error args i = Some a ->
        (forall t, wf_term l [] a t -> eq_term l [] t a b) ->
        eq_args l [] c' args (set_nth args i b).
    Proof.
      intros Hctx Hwf Hnth Hstep.
      revert i Hnth Hctx.
      induction Hwf as [| s c' name e t Hhd Htl IH]; intros i Hnth Hctx.
      { destruct i; cbn in Hnth; discriminate. }
      safe_invert Hctx.
      destruct i; cbn in Hnth.
      {
        (* the principal argument is this head; tail is refl *)
        safe_invert Hnth.
        cbn; constructor.
        - apply (eq_args_refl (core_model_ok wfl)); exact Htl.
        - eapply Hstep; exact Hhd.
      }
      {
        (* recurse into the tail; this head is refl up to conversion *)
        assert (eq_args l [] c' s (set_nth s i b)) as Htail
            by (eapply IH; eassumption).
        cbn; constructor.
        - exact Htail.
        - (* head sort changed (tail stepped) but only up to eq_sort *)
          eapply eq_term_refl.
          eapply wf_term_conv; [ exact Hhd | ].
          eapply eq_sort_subst.
          + eapply eq_sort_refl; eassumption.
          + eapply eq_args_implies_eq_subst; exact Htail.
          + eassumption.
      }
    Qed.

    (* ------------------------------------------------------------------ *)
    (* Weak-head reduction = the redex relation extended by congruence at  *)
    (* the PRINCIPAL argument of an eliminator spine.  Generic over the    *)
    (* principal-argument selector `pa` (cf. Neutral.v); for OTT, `pa`     *)
    (* names the function/scrutinee position of each eliminator.           *)
    (* Sort-erased (the principal arg reduces at a DIFFERENT sort than the *)
    (* whole term); soundness recovers the sort via `redex_sound` /        *)
    (* `term_con_congruence`.                                              *)
    (* ------------------------------------------------------------------ *)
    Context (pa : V -> option nat).

    Inductive whstep : term -> term -> Prop :=
    | whstep_redex : forall a b, redex a b -> whstep a b
    | whstep_congr : forall name args i a b,
        pa name = Some i ->
        nth_error args i = Some a ->
        whstep a b ->
        whstep (con name args) (con name (set_nth args i b)).

    Lemma whstep_sound : rel_sound V l (fun _ => whstep).
    Proof.
      intros e1 e2 tt Hwf Hstep.
      revert tt Hwf.
      induction Hstep; intros tt Hwf.
      { eapply redex_sound; eauto. }
      (* congruence at the principal argument *)
      apply WfCutElim.invert_wf_term_con in Hwf as (c' & cargs & t' & Hin & Hwfargs & Hsort).
      assert (wf_ctx l c') as Hwfctx by with_rule_in_wf_crush.
      pose proof (eq_args_step_at _ _ _ _ _ Hwfctx Hwfargs H0 IHHstep) as Heqargs.
      (* the rule type, instantiated, changes only up to eq_sort *)
      assert (eq_sort l [] t'[/with_names_from c' args/]
                          t'[/with_names_from c' (set_nth args i b)/]) as Hconv.
      {
        eapply eq_sort_subst.
        - eapply eq_sort_refl. eapply term_rule_in_sort_wf; eauto.
        - eapply eq_args_implies_eq_subst; eauto.
        - assumption.
      }
      eapply term_con_congruence; [ exact Hin | | exact wfl | exact Heqargs ].
      left.
      destruct Hsort as [Hs | Hs].
      - eapply eq_sort_trans; [ eapply eq_sort_sym; exact Hs | exact Hconv ].
      - rewrite <- Hs; exact Hconv.
    Qed.

    Lemma whstep_wf t a b
      : wf_term l [] a t -> whstep a b -> wf_term l [] b t.
    Proof.
      intros Hwf Hs.
      pose proof (whstep_sound _ _ _ Hwf Hs) as Heq.
      eapply eq_term_wf_r; eauto with lang_core.
    Qed.

    Lemma star_whstep_wf t a b
      : wf_term l [] a t -> star whstep a b -> wf_term l [] b t.
    Proof.
      intros Hwf Hstar; revert Hwf.
      induction Hstar; intros; eauto using whstep_wf.
    Qed.

    Lemma star_whstep_sound : rel_sound V l (fun _ => star whstep).
    Proof.
      intros a b t Hwf Hstar; revert t Hwf.
      induction Hstar; intros t Hwf.
      - eapply eq_term_refl; eassumption.
      - eapply eq_term_trans.
        + eapply IHHstar; eassumption.
        + eapply whstep_sound; [ eapply star_whstep_wf; eassumption | eassumption ].
    Qed.

  End WithLang.

End WithVar.
