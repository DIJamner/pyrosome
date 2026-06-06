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
From Pyrosome.Theory Require Import Core.
From Pyrosome.Compilers Require Import OperationalBridge.
Import Core.Notations.

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

  End WithLang.

End WithVar.
