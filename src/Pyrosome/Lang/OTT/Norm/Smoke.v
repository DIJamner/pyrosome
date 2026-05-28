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

  (* and the corresponding object-level redex evaluates to the value [vZero]:
        (hd)[snoc id zero]  ==>  vZero
     The exp_subst value is [apply_val sg ve], so we pin it by [change] first. *)
  Definition redex1 : term :=
    con "exp_subst"
        [con "hd" [a; a; a];
         a; a;
         con "snoc" [con "zero" [a]; con "id" [con "emp" []]; a; a; a; a];
         a; a].

  Example eval_redex1 : eval_rel redex1 vZero.
  Proof.
    unfold redex1.
    change vZero with (apply_val (vZero :: id_list (ctx_len (con "emp" []))) (vNe (nVar 0))).
    eapply ev_exp_subst.
    - eapply ev_snoc; econstructor.
    - econstructor.
  Qed.

  (* deeper: (hd)[snoc id (suc zero)] evaluates to (suc vZero) *)
  Definition redex2 : term :=
    con "exp_subst"
        [con "hd" [a; a; a];
         a; a;
         con "snoc" [con "suc" [con "zero" [a]; a]; con "id" [con "emp" []]; a; a; a; a];
         a; a].

  Example eval_redex2 : eval_rel redex2 (vSuc vZero).
  Proof.
    unfold redex2.
    change (vSuc vZero)
      with (apply_val (vSuc vZero :: id_list (ctx_len (con "emp" []))) (vNe (nVar 0))).
    eapply ev_exp_subst.
    - eapply ev_snoc; [ econstructor | econstructor; econstructor ].
    - econstructor.
  Qed.

End Smoke.
