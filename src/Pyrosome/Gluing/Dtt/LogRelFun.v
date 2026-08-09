Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelCand Pyrosome.Gluing.Dtt.Erase Pyrosome.Gluing.Dtt.Rigid
  Pyrosome.Gluing.Dtt.RigidOk Pyrosome.Gluing.Dtt.Inj.
Import Core.Notations.

(* =====================================================================
   CASHING IN LAYER 0.5.

   src/Pyrosome/Gluing/Dtt/LogRelBasics.v proves functionality of [RTy] only in the form
   [RTy_fun_of_inj], parameterised by the two rigidity statements, because
   the Pi clauses name their domain and codomain candidates at a CHOSEN
   representative and record only that it is PROVABLY equal to the raw
   instance -- so two derivations at the same syntactic type may choose
   different representatives, and the induction hypothesis (which compares
   candidates at the same type) does not apply until those are identified.

   src/Pyrosome/Gluing/Dtt/Inj.v now identifies them.  This file discharges the parameters
   and exports the unconditional forms, which is what every later layer
   consumes.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* Functionality, unconditionally                                       *)
(* ------------------------------------------------------------------ *)

Theorem RTy_fun
  : forall G i A P, RTy G i A P -> forall Q, RTy G i A Q -> forall e, P e <-> Q e.
Proof. apply RTy_fun_of_inj; [ exact @NfCode_inj | exact @TyOk_inj ]. Qed.

Theorem RTm_intro G i A P e : RTy G i A P -> P e -> RTm G i A e.
Proof. apply (RTm_intro_of_inj (@NfCode_inj) (@TyOk_inj)). Qed.

(* [RTm_elim] is already unconditional (src/Pyrosome/Gluing/Dtt/LogRelBasics.v); with
   [RTm_intro] the universal and existential readings of [RTm] finally
   coincide. *)
Lemma RTm_iff G i A P e
  : RTy G i A P -> (RTm G i A e <-> P e).
Proof.
  intro HR; split.
  - intro H; eapply RTm_elim; eassumption.
  - intro H; eapply RTm_intro; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Functionality ACROSS a type equation -- the statement section 3 of    *)
(* the design identified as the hole in the original plan               *)
(* ------------------------------------------------------------------ *)

Theorem RTy_fun_eq G i A B P Q
  : RTy G i A P -> RTy G i B Q -> eqt (sTy G i) A B -> forall e, P e <-> Q e.
Proof.
  intros HA HB Heq.
  assert (A = B) as ->
    by (eapply TyOk_inj; [ eapply RTy_TyOk | eapply RTy_TyOk | ]; eassumption).
  eapply RTy_fun; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Introducing [RTmN] from a SINGLE representative                      *)
(* ------------------------------------------------------------------ *)

(* [RTmN] quantifies over every normal representative of the type (and of
   the info); building it from one representative is exactly what rigidity
   buys, and is the form every congruence case will use. *)

(* First, the info-agnostic form of [TyOk_inj].  src/Pyrosome/Gluing/Dtt/Inj.v states it at
   a fixed info because that is what its own composition needed, but the
   proof does not use the info at all -- [rceq_term] at a [ty] sort is
   [Req_ty G A1 A2], which does not mention it -- and the erasure pins the
   info anyway.  So the general form is the same proof. *)
Theorem TyOk_inj_gen G j i1 A1 i2 A2
  : TyOk G i1 A1 -> TyOk G i2 A2 -> eqt (sTy G j) A1 A2 -> i1 = i2 /\ A1 = A2.
Proof.
  intros Ht1 Ht2 Heq.
  destruct (rigid_ty Heq) as [E [T [HIG [HI1 HI2]]]].
  destruct (EnvOk_ErI (TyOk_EnvOk Ht1)) as [E0 [HEr0 HI0]].
  pose proof (IEnv_fun HI0 HIG) as ?; subst E0.
  destruct (TyOk_ErI Ht1 HEr0 HI0) as [T1 [HT1r HT1i]].
  destruct (TyOk_ErI Ht2 HEr0 HI0) as [T2 [HT2r HT2i]].
  destruct (ITy_fun HT1i HI1) as [_ ?]; subst T1.
  destruct (ITy_fun HT2i HI2) as [_ ?]; subst T2.
  exact (TyOk_erase_inj_u Ht1 Ht2 HT1r HT2r).
Qed.

Lemma RTmN_intro G i A i0 A0 P e
  : eqt sInfo i i0 -> TyOk G i0 A0 -> eqt (sTy G i0) A A0 ->
    RTy G i0 A0 P -> P e -> RTmN G i A e.
Proof.
  intros Hi HT HA HR HP i1 A1 Hi1 HT1 HA1.
  assert (wf_term ott_dtt [] G sEnv) as HG
    by (eapply wft_ty_env; eapply eqt_wf_l; exact HA).
  (* move the second representative's equation to the first one's sort, so
     the two can be chained; the sorts are equal because both infos are
     provably equal to [i]. *)
  assert (eqt (sTy G i0) A A1) as HA1'.
  { eapply eq_term_conv; [ exact HA1 | ].
    apply eq_sort_ty_cong; [ apply eq_term_refl; exact HG | ].
    eapply eq_term_trans; [ apply eq_term_sym; exact Hi1 | exact Hi ]. }
  destruct (TyOk_inj_gen (j := i0) HT HT1
              (eq_term_trans (eq_term_sym HA) HA1')) as [-> ->].
  eapply RTm_intro; eassumption.
Qed.
