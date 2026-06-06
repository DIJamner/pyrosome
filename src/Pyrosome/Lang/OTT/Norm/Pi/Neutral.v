(* ====================================================================== *)
(* OTT pivot, file 2/5 (see WIP/NEXT_SESSION.md UPDATE-n / -o / -p).       *)
(*                                                                        *)
(* Neutral and weak-head-normal-form predicates on CLOSED Pyrosome terms.  *)
(*                                                                        *)
(* These are GENERIC over a "principal-argument selector" `pa : V ->        *)
(* option nat`: for each ELIMINATOR head `name`, `pa name = Some i` names   *)
(* the index of its principal (head) argument; for every other head        *)
(* `pa name = None`.                                                       *)
(*                                                                        *)
(*   neutral := variable | eliminator whose principal argument is neutral. *)
(*   whnf    := neutral  | a `con` whose head is NOT an eliminator.        *)
(*                                                                        *)
(* CAVEAT for OTT (UPDATE-p): this encoding has EXPLICIT SUBSTITUTIONS      *)
(* (`exp_subst`/`ty_subst`) that always reduce via the subst-commuting      *)
(* computation rules.  They are therefore NOT inert formers — when `pa`    *)
(* is instantiated for OTT it must map them to `Some i` (or they must be    *)
(* arranged never to be head-exposed at a whnf), otherwise `whnf` would     *)
(* wrongly accept an un-pushed substitution.  The generic development here  *)
(* is agnostic; the discipline is enforced by the chosen `pa`.            *)
(* ====================================================================== *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation sort := (@sort V).

  (* For each eliminator head `name`, `pa name = Some i` is the index of the
     principal argument (the sub-term that must be reduced to expose a redex);
     for non-eliminators it is `None`. *)
  Context (pa : V -> option nat).

  Inductive neutral : term -> Prop :=
  | neutral_var : forall x, neutral (var x)
  | neutral_elim : forall name args i a,
      pa name = Some i ->
      nth_error args i = Some a ->
      neutral a ->
      neutral (con name args).

  (* A weak-head normal form: a neutral, or a head that is not an eliminator
     (a canonical former). *)
  Definition whnf (e : term) : Prop :=
    neutral e \/ (exists name args, e = con name args /\ pa name = None).

  Lemma neutral_whnf e : neutral e -> whnf e.
  Proof. intro; left; assumption. Qed.

  (* A variable is the canonical neutral. *)
  Lemma var_neutral x : neutral (var x).
  Proof. constructor. Qed.

  Lemma var_whnf x : whnf (var x).
  Proof. apply neutral_whnf, var_neutral. Qed.

  (* Inversion: a neutral is never a non-eliminator former. *)
  Lemma neutral_inv name args
    : neutral (con name args) ->
      exists i a, pa name = Some i /\ nth_error args i = Some a /\ neutral a.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  (* The two whnf cases are mutually exclusive on `con`: an eliminator-headed
     whnf is necessarily neutral. *)
  Lemma whnf_elim_neutral name args i
    : pa name = Some i ->
      whnf (con name args) ->
      neutral (con name args).
  Proof.
    intros Hpa [Hn | (name' & args' & Heq & Hnone)]; eauto.
    safe_invert Heq.
    rewrite Hpa in Hnone; congruence.
  Qed.

End WithVar.

Arguments neutral {V}%_type_scope pa%_function_scope _.
Arguments whnf {V}%_type_scope pa%_function_scope _.
