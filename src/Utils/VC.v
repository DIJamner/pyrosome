From Stdlib Require Import Lists.List.
Import ListNotations.
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

(* List-induction principle for [vc] over [list_Mmap]: given a list-
   indexed precondition [P] that the per-element step [f a] preserves
   (advancing from [a :: l_rest] to [l_rest]) along a transitive
   step-relation [R], the whole [list_Mmap f l] establishes [P []] on
   the post-state and connects pre- and post-states by [R]. *)
Lemma vc_list_Mmap_inv {S A B}
  (f : A -> state S B)
  (P : list A -> S -> Prop)
  (R : S -> S -> Prop)
  : (forall s, P [] s -> R s s) ->
    (forall s s' s'', R s s' -> R s' s'' -> R s s'') ->
    (forall a l_rest,
       vc (f a)
          (fun s p => P (a :: l_rest) s -> P l_rest (snd p) /\ R s (snd p))) ->
    forall l,
      vc (list_Mmap f l)
        (fun s p => P l s -> P [] (snd p) /\ R s (snd p)).
Proof.
  intros Hrefl_base Htrans Hstep l.
  induction l as [| a l' IH].
  - unfold vc; cbn; intros e HP; split; auto.
  - unfold vc in *; intros e HP.
    cbn [list_Mmap Mbind StateMonad.state_monad].
    pose proof (Hstep a l' e HP) as Hae.
    destruct (f a e) as [b s1] eqn:Hfa.
    cbn [fst snd] in Hae. destruct Hae as [HPl' Hmono1].
    pose proof (IH s1) as IH1.
    specialize (IH1 HPl').
    destruct (list_Mmap f l' s1) as [bl' s2] eqn:Hmap.
    cbn [fst snd] in IH1. destruct IH1 as [HPnil Hmono2].
    cbn [Mret StateMonad.state_monad fst snd].
    split; eauto.
Qed.
