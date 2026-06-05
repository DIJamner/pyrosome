(* Phase-2 PER infrastructure for the two-sided [LR] (LogRel2.v):
   - typing of the base PERs ([RedNatEq]/[RedNeutralEq]);
   - ESCAPE: a reducible type-conversion entails both sides well-formed, and a
     reducible term-conversion entails both terms well-typed;
   - the base-case PER laws (symmetry / transitivity of [NeConv], [RedNatEq],
     [RedNeutralEq]).
   These hold on the PROVISIONAL [NeConv] of Phase 1 (which is already a PER)
   and do NOT touch [Domain.v], so the build stays green ahead of Phase 0. *)
Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Typing Preservation LogRel2.
Import Core.Notations.

(* A dummy universe level, used only to witness [has_svalty _ vNat (dU _ _)]
   etc. in escape (the typing rules [t_Nat]/[t_Empty] hold at every level). *)
Local Notation L0 := (con "L0" nil).

(* ===================================================================== *)
(* Typing of the base PERs.                                               *)
(* ===================================================================== *)

Lemma RedNatEq_wf : forall Ge a b,
    RedNatEq Ge a b -> (has_svalty Ge a (dEl vNat) * has_svalty Ge b (dEl vNat))%type.
Proof.
  intros Ge a b H; induction H.
  - split; apply t_zero.
  - destruct IHRedNatEq as [Ha Hb]; split; apply t_suc; assumption.
  - destruct n0 as [[wn wm] _]; split; apply t_ne; assumption.
Qed.

Lemma RedNeutralEq_wf : forall Ge T a b,
    RedNeutralEq Ge T a b -> (has_svalty Ge a T * has_svalty Ge b T)%type.
Proof.
  intros Ge T a b H; destruct H as [n m [[wn wm] _]].
  split; apply t_ne; assumption.
Qed.

(* ===================================================================== *)
(* ESCAPE.                                                                *)
(* ===================================================================== *)

Lemma RedTyEq_wf : forall Ge A B,
    RedTyEq Ge A B -> (wf_svalty Ge A * wf_svalty Ge B)%type.
Proof.
  intros Ge A B [P H]; destruct H.
  - (* LRnat *)   split; apply (wf_dEl (r:=L0) (l:=L0)); apply t_Nat.
  - (* LRempty *) split; apply (wf_dEl (r:=L0) (l:=L0)); apply t_Empty.
  - (* LRne *)    destruct n0 as [[wn wm] _];
                  split; apply (wf_dEl (r:=r) (l:=l)); apply t_ne; assumption.
  - (* LRpiI *)   split; assumption.
  - (* LRpi *)    split; assumption.
  - (* LRU *)     split; apply wf_dU.
Qed.

Lemma RedTmEq_wf : forall Ge A B a b,
    RedTmEq Ge A B a b -> (has_svalty Ge a A * has_svalty Ge b B)%type.
Proof.
  intros Ge A B a b [P [H Pab]]; destruct H.
  - (* LRnat *)   exact (RedNatEq_wf Pab).
  - (* LRempty *) exact (RedNeutralEq_wf Pab).
  - (* LRne *)    destruct n0 as [[wn wm] eqnm]; subst m.
                  exact (RedNeutralEq_wf Pab).
  - (* LRpiI *)   destruct Pab as [Hf Hg]; split; assumption.
  - (* LRpi *)    destruct Pab as [[Hf Hg] _]; split; assumption.
  - (* LRU *)     destruct Pab as [[Hc Hd] _]; split; assumption.
Qed.

(* ===================================================================== *)
(* Base-case PER laws (provisional [NeConv] is already a PER).            *)
(* ===================================================================== *)

Lemma NeConv_sym : forall Ge T n m, NeConv Ge T n m -> NeConv Ge T m n.
Proof. intros Ge T n m [[wn wm] e]; repeat split; [exact wm | exact wn | exact (eq_sym e)]. Qed.

Lemma NeConv_trans : forall Ge T n m p,
    NeConv Ge T n m -> NeConv Ge T m p -> NeConv Ge T n p.
Proof.
  intros Ge T n m p [[wn wm] e1] [[wm' wp] e2];
    repeat split; [exact wn | exact wp | exact (eq_trans e1 e2)].
Qed.

Lemma RedNatEq_sym : forall Ge a b, RedNatEq Ge a b -> RedNatEq Ge b a.
Proof.
  intros Ge a b H; induction H.
  - apply rne_zero.
  - apply rne_suc; assumption.
  - apply rne_ne; apply NeConv_sym; assumption.
Qed.

Lemma RedNatEq_trans : forall Ge a b c,
    RedNatEq Ge a b -> RedNatEq Ge b c -> RedNatEq Ge a c.
Proof.
  intros Ge a b c H; revert c; induction H; intros c Hbc.
  - exact Hbc.
  - inversion Hbc; subst. apply rne_suc; apply IHRedNatEq; assumption.
  - inversion Hbc; subst. apply rne_ne; eapply NeConv_trans; eassumption.
Qed.

Lemma RedNeutralEq_sym : forall Ge T a b,
    RedNeutralEq Ge T a b -> RedNeutralEq Ge T b a.
Proof. intros Ge T a b [n m c]; apply rneT; apply NeConv_sym; assumption. Qed.

Lemma RedNeutralEq_trans : forall Ge T a b c,
    RedNeutralEq Ge T a b -> RedNeutralEq Ge T b c -> RedNeutralEq Ge T a c.
Proof.
  intros Ge T a b c Hab Hbc; destruct Hab as [n m cab]; inversion Hbc; subst.
  apply rneT; eapply NeConv_trans; eassumption.
Qed.
