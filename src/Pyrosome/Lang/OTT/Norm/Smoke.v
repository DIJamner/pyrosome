Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Reify.
Import Core.Notations.

(* Smoke tests for the environment-free evaluator + readback: values compute and
   read back to normal-form terms (the point of the NbE approach). *)
Section Smoke.
  Notation term := (@term string).
  Let a : term := con "_ann" [].   (* the annotation placeholder used by Reify *)

  (* readback of closed numerals / codes / a reflected variable *)
  Example nf_zero : reify_val vZero = con "zero" [a]. Proof. reflexivity. Qed.
  Example nf_two  : reify_val (vSuc (vSuc vZero)) = con "suc" [con "suc" [con "zero" [a]; a]; a].
  Proof. reflexivity. Qed.
  Example nf_Nat  : reify_val vNat = con "Nat" [a]. Proof. reflexivity. Qed.
  Example nf_NatTy : reify_ty (dEl vNat) = con "El" [con "Nat" [a]; a; a; a].
  Proof. reflexivity. Qed.
  Example nf_var0 : reify_val (vNe (nVar 0)) = con "hd" [a; a; a]. Proof. reflexivity. Qed.

  (* the substitution acts on values: [snoc id zero] applied to variable 0 is zero *)
  Example apply_redex : apply_val (vZero :: id_list 0) (vNe (nVar 0)) = vZero.
  Proof. reflexivity. Qed.

  (* the TYPED evaluator (EvalRel.v) computes closed numerals in the empty
     context [[]], tracking the semantic type [dEl vNat].  (The old env-free
     [exp_subst]/[hd] redexes used placeholder [_ann] contexts, which the typed
     evaluator rejects: [ev_hd]/[ev_zero] require a real [emp]/[ext] context.) *)
  Example eval_zero :
    eval_rel [] (con "zero" [con "emp" []]) (dEl vNat) vZero.
  Proof. apply ev_zero, ev_env_emp. Qed.

  Example eval_suc :
    eval_rel [] (con "suc" [con "zero" [con "emp" []]; con "emp" []])
             (dEl vNat) (vSuc vZero).
  Proof. apply ev_suc, ev_zero, ev_env_emp. Qed.

End Smoke.
