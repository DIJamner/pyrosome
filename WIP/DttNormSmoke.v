Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttModel WIP.DttNormalForms WIP.DttLogRel WIP.DttRSub
  WIP.DttCeq WIP.DttModelOk.
Import Core.Notations.

(* =====================================================================
   NON-VACUITY.

   The STLC proof had to add [unit_lang] because over bare [stlc] the sort
   [ty] has no closed inhabitant, so [TyOk] is empty and the theorem is
   vacuous.  The analogous question here is sharper, because OTT's types
   are DECODED CODES: [El G r L0 e] is a type only when [e] is a code, i.e.
   a term of [U G r L0].  The closed codes of [ott_dtt] are exactly

     Nat G          : U G rel L0        (from ott_nat)
     Empty G        : U G irr L0        (from ott_nat)
     Pi_rel/Pi_irr  : built from codes   (from ott_pi)

   [Pi] alone has no base case, so WITHOUT [ott_nat] every [U _ L0] is
   empty, every [El _ _ _ e] is uninhabited, [TyOk] is empty and the
   theorem is vacuous.  [Nat] plays exactly the role [unit] plays in the
   STLC proof, and that is why [ott_nat] is in the target language.

   (Note that [ott_base] alone does NOT rescue this: [U G r L0] is a TYPE,
   but the sort of codes [exp G iU (U G r L0)] has no closed inhabitant
   without a base code.  Conversely [U] itself IS a non-vacuous type at the
   level above: [Nat oEmp] inhabits it, which is what [wit_Nat_code] below
   records.)

   The witnesses below are closed and are genuinely at the interesting
   sorts.  [G1] is an OPEN environment (its variable is the object-level
   [hd]), so the theorem applied to it is a statement about open terms.
   ===================================================================== *)

(* ---- the base type Nat, in the empty environment ---- *)
Definition natC (G : term) : term := oNat G.
Definition natT (G : term) : term := tEl G oRel (oNat G).

(* ---- G1 = (x : Nat) ---- *)
Definition G1 : term := oExtC0 oEmp oRel (oNat oEmp).

(* ---- the code Nat -> Nat, and the identity function on it ---- *)
Definition piNN : term := oPiRel oEmp oRel oL0 oL0 (oNat oEmp) (oNat G1).
Definition hdNat : term := oHd oEmp (iE oRel) (tEl oEmp oRel (oNat oEmp)).
Definition idNat : term :=
  oLamRel oEmp oRel oL0 oL0 (oNat oEmp) (oNat G1) hdNat.

(* ---- a closed redex: (fun x => x) 0 ---- *)
Definition appIdZero : term :=
  oAppRel oEmp oRel oL0 oL0 (oNat oEmp) (oNat G1) idNat (oZero oEmp).

(* ---- an OPEN term: suc x, in G1 ---- *)
Definition sucVar : term := oSuc G1 hdNat.

(* ================================================================== *)
(* The fragment predicates hold -- these are real proofs, by pure       *)
(* inductive construction (no object-theory reasoning).                 *)
(* ================================================================== *)

Lemma EnvOk_emp : EnvOk oEmp.
Proof. apply envok_emp. Qed.

Lemma NfCode_Nat_emp : NfCode oEmp oRel (oNat oEmp).
Proof. apply nfcode_nat, envok_emp. Qed.

Lemma TyOk_Nat_emp : TyOk oEmp (iE oRel) (natT oEmp).
Proof. apply tyok_El, NfCode_Nat_emp. Qed.

Lemma EnvOk_G1 : EnvOk G1.
Proof. apply envok_ext; [ apply envok_emp | apply TyOk_Nat_emp ]. Qed.

Lemma NfCode_Nat_G1 : NfCode G1 oRel (oNat G1).
Proof. apply nfcode_nat, EnvOk_G1. Qed.

Lemma TyOk_Nat_G1 : TyOk G1 (iE oRel) (natT G1).
Proof. apply tyok_El, NfCode_Nat_G1. Qed.

(* the universe is inhabited: [Nat] is a normal code, hence a normal term
   of the type [U emp rel L0] *)
Lemma wit_Nat_code : NfET oEmp iU (tU oEmp oRel) (oNat oEmp).
Proof. apply nfet_code, NfCode_Nat_emp. Qed.

Lemma TyOk_U_emp : TyOk oEmp iU (tU oEmp oRel).
Proof. apply tyok_U; [ apply envok_emp | apply relnf_rel ]. Qed.

(* the function type is a normal code, so [El (Pi Nat Nat)] is a normal
   type -- the first genuinely DEPENDENT-SHAPED witness (its codomain code
   lives in the extended environment [G1]) *)
Lemma NfCode_piNN : NfCode oEmp oRel piNN.
Proof.
  apply nfcode_pi_rel; [ apply NfCode_Nat_emp | apply NfCode_Nat_G1 ].
Qed.

Lemma TyOk_piNN : TyOk oEmp (iE oRel) (tEl oEmp oRel piNN).
Proof. apply tyok_El, NfCode_piNN. Qed.

(* ================================================================== *)
(* STATEMENTS ONLY: the object-theory typings and the payoff.           *)
(*                                                                      *)
(* These need [wf_term_conv]: [hd]'s type is                            *)
(*   [ty_subst G1 emp (wkn ...) (iE rel) (El emp rel L0 (Nat emp))],     *)
(* which is the type [El G1 rel L0 (Nat G1)] only via the "El subst" and *)
(* "Nat subst" equations.  That single conversion is a fair miniature of *)
(* what the whole [cterm_cong] half of Layer 4b consists of.            *)
(* ================================================================== *)

Lemma wf_hdNat : wf_term ott_dtt [] hdNat (sExp G1 (iE oRel) (natT G1)).
Admitted.

Lemma NfET_hdNat : NfET G1 (iE oRel) (natT G1) hdNat.
Admitted.

Lemma wf_idNat : wf_term ott_dtt [] idNat (sExp oEmp (iE oRel) (tEl oEmp oRel piNN)).
Admitted.

Lemma wf_appIdZero
  : wf_term ott_dtt [] appIdZero (sExp oEmp (iE oRel) (natT oEmp)).
Admitted.

(* THE PAYOFF, on a closed beta-redex.  The expected normal form is
   [zero], via "Pi_rel beta" plus [exp_subst] on [hd] and the [snoc_hd]
   equation. *)
Theorem appIdZero_has_normal_form
  : exists n, NfET oEmp (iE oRel) (natT oEmp) n
              /\ eq_term ott_dtt [] (sExp oEmp (iE oRel) (natT oEmp)) appIdZero n.
Proof.
  apply ott_dtt_normalization;
    [ apply envok_emp | apply TyOk_Nat_emp | apply wf_appIdZero ].
Qed.

(* THE PAYOFF, on an OPEN term.  [G1] contains a variable, so this is a
   statement about an open term whose normal form contains a neutral. *)
Theorem sucVar_has_normal_form
  : wf_term ott_dtt [] sucVar (sExp G1 (iE oRel) (natT G1)) ->
    exists n, NfET G1 (iE oRel) (natT G1) n
              /\ eq_term ott_dtt [] (sExp G1 (iE oRel) (natT G1)) sucVar n.
Proof.
  intro H; apply ott_dtt_normalization;
    [ apply EnvOk_G1 | apply TyOk_Nat_G1 | exact H ].
Qed.
