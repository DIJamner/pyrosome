Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping Pyrosome.Gluing.Dtt.LogRel
  Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelFun Pyrosome.Gluing.Dtt.LogRelCore.
Import Core.Notations.

(* =====================================================================
   THE MISSING HALF OF THE [RTmN] INTERFACE.

   src/Pyrosome/Gluing/Dtt/LogRelFun.v supplies [RTmN_intro]: build the
   forall-over-all-representatives relation from ONE representative, which
   is what rigidity bought.  Writing the Layer-4b congruences showed the
   other half is wanted just as often -- every congruence with a
   non-index argument has to READ a normal form back out of a hypothesis's
   [RTmN] -- and that it was being open-coded each time as [RTm_elim]
   composed with a clause introduction and a hand-supplied instantiation
   of [RTmN]'s three arguments.  Packaging it here.

   [RTmN] is universally quantified, so elimination is the easy direction:
   nothing below needs rigidity.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* The general form: instantiate at any representative and read off the
   candidate. *)
Lemma RTmN_elim G i A e i0 A0 P
  : RTmN G i A e ->
    eqt sInfo i i0 -> TyOk G i0 A0 -> eqt (sTy G i0) A A0 ->
    RTy G i0 A0 P -> P e.
Proof.
  intros He Hi HT HA HR; eapply RTm_elim; [ exact HR | apply He; assumption ].
Qed.

(* The form the congruences actually use: at a representative the type is
   already syntactically equal to, so the two equations are reflexivity.
   The [wf_term] side conditions come from [RTy_TyOk] and the sort of the
   subject, so callers supply nothing. *)
Lemma RTmN_elim_refl G i A e P
  : RTmN G i A e -> TyOk G i A -> RTy G i A P ->
    wf_term ott_dtt [] i sInfo -> wf_term ott_dtt [] A (sTy G i) -> P e.
Proof.
  intros He HT HR Hi HA.
  eapply RTmN_elim; try eassumption; apply eq_term_refl; assumption.
Qed.

(* Reducibility of a term always yields a normal form -- the composite of
   elimination with escape, which is what every "read a normal form out of
   the hypothesis" step in Layer 4b wants. *)
Lemma RTmN_HasNf G i A e i0 A0 P
  : RTmN G i A e ->
    eqt sInfo i i0 -> TyOk G i0 A0 -> eqt (sTy G i0) A A0 ->
    RTy G i0 A0 P -> HasNf G i0 A0 e.
Proof.
  intros He Hi HT HA HR.
  eapply RTy_escape; [ exact HR | eapply RTmN_elim; eassumption ].
Qed.

(* ... and its two specializations, since a type that is [TyOk] always has
   a candidate ([RTyEx_of_TyOk]), so the caller need not produce one. *)
Lemma RTmN_HasNf' G i A e i0 A0
  : RTmN G i A e ->
    eqt sInfo i i0 -> TyOk G i0 A0 -> eqt (sTy G i0) A A0 ->
    HasNf G i0 A0 e.
Proof.
  intros He Hi HT HA.
  destruct (RTyEx_of_TyOk HT) as [P HP].
  eapply RTmN_HasNf; eassumption.
Qed.

(* At a universe the candidate IS [HasNfCode], so this is the reading every
   code-valued argument of a congruence wants. *)
Lemma RTmN_HasNfCode G r l c i
  : RTmN G i (oU G r l) c -> eqt sInfo i (iCode l) ->
    EnvOk G -> RelNf r -> LvlNf l -> HasNfCode G r l c.
Proof.
  intros Hc Hi HG Hr Hl.
  eapply RTmN_elim with (i0 := iCode l) (A0 := oU G r l) (P := HasNfCode G r l).
  - exact Hc.
  - exact Hi.
  - apply tyok_U; assumption.
  - apply eq_term_refl.
    apply wf_U; [ apply EnvOk_wf | apply RelNf_wf | apply LvlNf_wf ]; assumption.
  - apply RTy_U_i; assumption.
Qed.
