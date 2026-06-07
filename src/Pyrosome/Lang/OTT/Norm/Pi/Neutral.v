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

  (* The head constructor of the CwF/explicit-substitution bound VARIABLE (the
     "last variable" projection).  For OTT this is instantiated with `"hd"`.  It
     is recognized STRUCTURALLY by `neutral` (NOT via `pa` — it is not an
     eliminator: `pa hd_name = None`). *)
  Context (hd_name : V).

  Inductive neutral : term -> Prop :=
  | neutral_var : forall x, neutral (var x)
  (* The CwF/explicit-substitution bound VARIABLE is the projection
     `hd = con hd_name [A; i; G]`, NOT a meta `var x`.  It is whnf (its head is
     not an eliminator: `pa hd_name = None`) but it is the canonical neutral
     that NbE reflects (the zero variable).  In the metamltt-style direct syntax
     the variable rule is `neutral_var`; in OTT's categorical syntax the
     variable IS this projection, so it gets its own neutral base case.
     See WIP/NEXT_SESSION.md z18/z19. *)
  | neutral_hd : forall A i G, neutral (con hd_name [A; i; G])
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

  (* Inversion: a neutral `con` is either the bound-variable projection
     `hd_name` (the `neutral_hd` base case), or an eliminator whose principal
     argument is itself neutral.  (Pre-`neutral_hd` this returned only the
     eliminator disjunct; the variable-projection clause adds the left case.) *)
  Lemma neutral_inv name args
    : neutral (con name args) ->
      (exists A i G, name = hd_name /\ args = [A; i; G]) \/
      (exists i a, pa name = Some i /\ nth_error args i = Some a /\ neutral a).
  Proof.
    inversion 1; subst; eauto 10.
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

Arguments neutral {V}%_type_scope pa%_function_scope hd_name _.
Arguments whnf {V}%_type_scope pa%_function_scope _.
