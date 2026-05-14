From Utils Require Import Utils Monad.
Import StateMonad.

(* Verification conditions for the state monad: a [vc c P] holds when
   [P] holds of every input state and the resulting (output, post-state)
   pair.  Compared to a Hoare triple, the precondition is folded into
   [P] as an implication, removing the need for a separate slot. *)
Definition vc {S A} (c : state S A) (P : S -> A * S -> Prop) :=
  forall e, P e (c e).

Lemma vc_bind {S A B} (c : state S A) (f : A -> state S B)
  (P1 : S -> A * S -> Prop) (P2 : S -> B * S -> Prop)
  : vc c P1 ->
    (forall s0 a, vc (f a) (fun s1 res => P1 s0 (a,s1) -> P2 s0 res)) ->
    vc (Mbind f c) P2.
Proof.
  unfold vc; intros Hc Hf e; cbn.
  specialize (Hc e).
  destruct (c e) as [a e1] eqn:Hce.
  apply Hf. exact Hc.
Qed.

Lemma vc_consequence {S A} (c : state S A)
  (P P' : S -> A * S -> Prop)
  : (forall s1 res, P s1 res -> P' s1 res) ->
    vc c P ->
    vc c P'.
Proof.
  unfold vc; intuition.
Qed.

Ltac vc_apply lem :=
  first [ simple eapply lem
        | simple eapply vc_consequence;
          [ | simple eapply lem];
          [eauto 2; cbn beta; intros | ..] ].

Ltac vc_bind lem :=
  eapply vc_bind;
  [ vc_apply lem; intuition eauto | intros ? ?].
