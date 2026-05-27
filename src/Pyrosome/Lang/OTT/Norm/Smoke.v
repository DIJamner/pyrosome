Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Reify Env.
Import Core.Notations.

(* Smoke tests: the relational evaluator + readback actually *compute* normal
   forms (the point of the gluing/NbE approach). Annotation slots irrelevant to
   evaluation use the dummy [d]. *)
Section Smoke.
  Notation term := (@term string).
  Let d : term := con "emp" [].
  Let emp : term := con "emp" [].

  (* the substitution redex  (hd)[snoc id zero]  evaluates to the value zero. *)
  Definition redex1 : term :=
    con "exp_subst"
        [d; d;
         con "snoc" [d; d; d; d; con "id" [d]; con "zero" [d]];
         d; d;
         con "hd" [d; d; d]].

  Example eval_redex1 : eval_rel [] redex1 vZero.
  Proof. unfold redex1. repeat econstructor. Qed.

  (* and its normal form reads back to the literal [zero] over the empty env. *)
  Example nf_redex1 : reify_val emp vZero = con "zero" [emp].
  Proof. reflexivity. Qed.

  (* deeper: (hd)[snoc id (suc zero)] evaluates to (suc zero) and reifies to it. *)
  Definition redex2 : term :=
    con "exp_subst"
        [d; d;
         con "snoc" [d; d; d; d; con "id" [d]; con "suc" [d; con "zero" [d]]];
         d; d;
         con "hd" [d; d; d]].

  Example eval_redex2 : eval_rel [] redex2 (vSuc vZero).
  Proof. unfold redex2. repeat econstructor. Qed.

  Example nf_redex2 : reify_val emp (vSuc vZero) = con "suc" [emp; con "zero" [emp]].
  Proof. reflexivity. Qed.

  (* OPEN terms: normalizing the env [ext emp Nat] gives a one-slot reflecting
     environment, and the variable [hd] reflects to a neutral that reads back to
     itself (the variable is its own normal form). *)
  Definition ctx1 : term := con "ext" [emp; d; con "Nat" [emp]].

  Example eval_env_ctx1 :
    eval_env ctx1 = [ vNe (con "hd" [emp; d; con "Nat" [emp]]) ].
  Proof. reflexivity. Qed.

  Example eval_open_var :
    eval_rel (eval_env ctx1) (con "hd" [emp; d; con "Nat" [emp]])
             (vNe (con "hd" [emp; d; con "Nat" [emp]])).
  Proof. econstructor. Qed.

  Example nf_open_var :
    reify_val ctx1 (vNe (con "hd" [emp; d; con "Nat" [emp]]))
      = con "hd" [emp; d; con "Nat" [emp]].
  Proof. reflexivity. Qed.

End Smoke.
