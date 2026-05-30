Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply Reflect.
Import Core.Notations.

(* Smoke tests validating that beta (semantic application) and eta
   (type-directed reflection) compute correctly on concrete values. *)
Section Smoke.

  (* BETA: the identity function [\x. x] applied to [vZero] yields [vZero].
     [Vapp 0 (vLam (vNe (nVar 0))) vZero vZero] reduces via [vapp_lam] to
     [Apply_val 0 [vZero] (vNe (nVar 0)) vZero] (id_list 0 = []). *)
  Example beta_id_applied_zero :
    Vapp 0 (vLam (vNe (nVar 0))) vZero vZero.
  Proof.
    apply vapp_lam. apply ap_ne.
    change vZero with (nth_default (vNe (nVar 0)) (vZero :: id_list 0) 0) at 2.
    apply ap_var.
  Qed.

  (* BETA, dependent-ish: [\x. suc x] applied to [vZero] yields [vSuc vZero]. *)
  Example beta_suc_applied_zero :
    Vapp 0 (vLam (vSuc (vNe (nVar 0)))) vZero (vSuc vZero).
  Proof.
    apply vapp_lam. apply ap_suc, ap_ne.
    change vZero with (nth_default (vNe (nVar 0)) (vZero :: id_list 0) 0) at 2.
    apply ap_var.
  Qed.

  (* ETA: reflecting a variable [nVar 0] at the function type [Nat -> Nat]
     (= El (vPi vNat vNat)) eta-expands it to [\x. (var 1) x], i.e.
     [vLam (vNe (nApp (nVar 1) (vNe (nVar 0))))].  The bound variable becomes
     index 0; the reflected head is weakened from index 0 to index 1. *)
  Example eta_var_at_Nat_to_Nat : forall m,
    Reflect m (dEl (vPi vNat vNat)) (nVar 0)
            (vLam (vNe (nApp (nVar 1) (vNe (nVar 0))))).
  Proof.
    intro m.
    eapply refl_Pi.
    - (* reflected argument: nVar 0 at El Nat stays neutral *) apply refl_Nat.
    - (* codomain B[arg] : Nat substituted = Nat *) apply ap_nat.
    - (* body: (nVar 1) applied to the bound var, at El Nat, stays neutral *)
      apply refl_Nat.
  Qed.

  (* ETA at a BASE type does NOT expand: a variable at El Nat reflects to itself. *)
  Example eta_var_at_Nat : forall m,
    Reflect m (dEl vNat) (nVar 0) (vNe (nVar 0)).
  Proof. intro m. apply refl_Nat. Qed.

  (* ETA does NOT fire for a proof-IRRELEVANT function type. *)
  Example no_eta_at_PiI : forall m,
    Reflect m (dEl (vPiI vNat vNat)) (nVar 0) (vNe (nVar 0)).
  Proof. intro m. apply refl_PiI. Qed.

End Smoke.
