Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

From Utils Require Import Utils.

Section Closure.
  Context {A : Type}
    (R : A -> A -> Prop).
  Inductive equivalence_closure : A -> A -> Prop :=
  | eq_clo_base a b : R a b -> equivalence_closure a b
  | eq_clo_refl a : equivalence_closure a a
  | eq_clo_trans a b c : equivalence_closure a b -> equivalence_closure b c -> equivalence_closure a c
  | eq_clo_sym a b : equivalence_closure a b -> equivalence_closure b a.
  Hint Constructors equivalence_closure : utils.
  
  Inductive PER_closure : A -> A -> Prop :=
  | PER_clo_base a b : R a b -> PER_closure a b
  | PER_clo_trans a b c : PER_closure a b -> PER_closure b c -> PER_closure a c
  | PER_clo_sym a b : PER_closure a b -> PER_closure b a.
  Hint Constructors PER_closure : utils.

  Inductive transitive_closure : _ -> _ -> Prop :=
  | trans_clo_base a b : R a b -> transitive_closure a b
  | trans_clo_step a b c : R a b -> transitive_closure b c -> transitive_closure a c.
  Hint Constructors transitive_closure : utils.

  Lemma transitive_closure_transitive : Transitive transitive_closure.
  Proof.
    intros a b c H.
    revert c; induction H;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  (*TODO: rename to supremum?*)
  Definition limit a x :=
    R a x /\ forall b, R a b -> b = x \/ R b x.

  Inductive count_step_closure : nat -> A -> A -> Prop :=
  | count_clo_base : forall a b : A, R a b -> count_step_closure 0 a b
  | count_clo_step : forall n (a b c : A),
      R a b ->
      count_step_closure n b c ->
      count_step_closure (S n) a c.
  Hint Constructors count_step_closure : utils.

  Lemma count_step_implies_transitive n b c
    : count_step_closure n b c -> transitive_closure b c.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma transitive_iff_count_step b c
    : transitive_closure b c <-> exists n, count_step_closure n b c.
  Proof.
    split; basic_goal_prep; eauto using count_step_implies_transitive.
    induction H;
      basic_goal_prep; eexists;
      basic_utils_crush.
  Qed.
  

  Lemma transitive_closure_leftmost (x z : A)
    : transitive_closure x z ->
      exists y, R x y.
  Proof. inversion 1; eauto. Qed.

  Definition dom (a:A) : Prop :=
    exists b:A, R a b.
  
  Definition codom (b:A) : Prop :=
    exists a:A, R a b.

    
  Lemma PER_trans_equiv b c
    : equivalence_closure b c ->
      (forall a, PER_closure a b -> PER_closure a c)
      /\ (forall d, PER_closure c d -> PER_closure b d).
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma PER_step a c
    : PER_closure a c <->
        (exists b, (R a b \/ R b a) /\ equivalence_closure b c)
        /\ (exists b, (R c b \/ R b c) /\ equivalence_closure a b).
  Proof.
    split; basic_goal_prep.
    {
      induction H; basic_goal_prep.
      { basic_utils_crush. }
      { split; eexists; basic_utils_crush. }
      { split; eexists; basic_utils_crush. }
    }
    {
      basic_utils_crush.
      all: eapply PER_trans_equiv; basic_utils_crush.
    }
  Qed.
  
End Closure.
#[export] Hint Constructors equivalence_closure transitive_closure
  PER_closure count_step_closure : utils.

Add Parametric Relation {A : Type} (R : A -> A -> Prop) : A (transitive_closure R)
    transitivity proved by (transitive_closure_transitive _)
    as transitive_closure_rel.

Definition iff2 {A B} R1 R2 := forall (a:A) (b:B), R1 a b <-> R2 a b.

Lemma iff2_refl A B (R : A -> B -> Prop) : iff2 R R.
Proof. unfold iff2; firstorder fail. Qed.
Hint Resolve iff2_refl : utils.

Lemma iff2_trans A B (R1 R2 R3 : A -> B -> Prop) : iff2 R1 R2 -> iff2 R2 R3 -> iff2 R1 R3.
Proof.
  unfold iff2.
  intros.
  rewrite H.
  eauto.
Qed.
(*Hint Resolve iff2_trans : utils.*)


Instance equivalence_closure_proper A
  : Proper (iff2 ==> iff2) (@equivalence_closure A).
Proof.
  cbv.
  (*Enough to prove one side *)
  enough (forall x y : A -> A -> Prop,
             (forall a b : A, (x a b -> y a b)) ->
             forall a b : A,
               (equivalence_closure x a b -> equivalence_closure y a b)).
  { intros; break; split; eapply H; eapply H0. }
  {
    intros.
    induction H0; basic_goal_prep;
      basic_utils_crush.
  }
Qed.


    
Instance transitive_closure_subrelation A (R R' : A -> A -> Prop) `{subrelation _ R R'}
  : subrelation (transitive_closure R) (transitive_closure R').
Proof.
  unfold subrelation; intros.
  induction H0;
    basic_goal_prep;
    basic_utils_crush.
Qed.

Definition disjoint {A} P1 P2 : Prop :=
  forall a:A, ~ (P1 a /\ P2 a).

Definition or1 {A} (R1 R2 : A -> Prop) a := R1 a \/ R2 a.
Definition or2 {A B} (R1 R2 : A -> B -> Prop) a b := R1 a b \/ R2 a b.


Lemma transitive_disjoint_closure A (R1 R2 : A -> _)
  : disjoint (dom R1) (codom R2) ->
    disjoint (dom R2) (codom R1) ->          
    iff2 (transitive_closure (or2 R1 R2))
      (or2 (transitive_closure R1) (transitive_closure R2)).
Proof.
  split.
  {
    unfold or2 in *;
      induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      specialize (H0 b);
        unfold dom, codom in H0.
      exfalso.
      intuition eauto.
      eapply H4; eauto.
      inversion H1; eexists; eauto.
    }
    {
      specialize (H b);
        unfold dom, codom in H.
      exfalso.
      intuition eauto.
      eapply H4; eauto.
      inversion H1; eexists; eauto.
    }
  }
  {
    unfold or2 in *;
      intro H'; destruct H' as [H' | H'];
      induction H';
      basic_goal_prep;
      basic_utils_crush.
  }        
Qed.

Lemma transitive_closure_iff2_impl A x y (a b : A)
  : iff2 x y -> transitive_closure x a b -> transitive_closure y a b.
Proof.
  intro H.
  induction 1;
    basic_goal_prep;
    basic_utils_crush.
  { apply H in H0; basic_utils_crush. }
  { apply H in H0; basic_utils_crush. }
Qed.

Lemma iff2_sym A B (R1 R2 : A -> B -> Prop) : iff2 R1 R2 -> iff2 R2 R1.
Proof using.
  unfold iff2; intuition; eapply H; eauto.
Qed.

Add Parametric Relation A B : (A -> B -> Prop) (@iff2 A B)
    reflexivity proved by ltac:(intros a b; intuition)
    symmetry proved by (@iff2_sym A B)
    transitivity proved by (@iff2_trans A B)
    as iff2_rel.

Instance transitive_closure_Proper A : Proper (iff2 ==> iff2) (transitive_closure (A:=A)).
Proof.
  intros ? ? ? ? ?.
  split; eapply transitive_closure_iff2_impl; eauto; symmetry; eauto.
Qed.

Definition union_closure {A : Type} (R1 R2 : A -> A -> Prop) :=
  equivalence_closure (fun a b => R1 a b \/ R2 a b).

Definition singleton_rel {A : Type} (x y : A) a b : Prop := a = x /\ b = y.

Definition impl2 {A} (R1 R2 : _ -> _ -> Prop) : Prop := forall a b : A, R1 a b -> R2 a b.

Instance equivalence_closure_impl_proper A
  : Proper (@impl2 A ==> impl2) equivalence_closure.
Proof.
  unfold Proper, respectful, impl2.
  intros.
  induction H0; basic_goal_prep;
    basic_utils_crush.
Qed.

Lemma union_clo_equiv_l A (R1 R2 : A -> _)
  : iff2 (union_closure (equivalence_closure R1) R2)
      (union_closure R1 R2).
Proof.
  unfold union_closure.
  split.
  {
    induction 1; basic_goal_prep;
      basic_utils_crush.
    eapply equivalence_closure_impl_proper; eauto.
    unfold impl2; intuition eauto.
  }
  {
    induction 1; basic_goal_prep;
      basic_utils_crush.
  }
Qed.

Lemma union_closure_subrel A (R1 R2 : A -> A -> Prop)
  : (forall a b, R2 a b -> (equivalence_closure R1) a b) ->
    iff2 (union_closure (equivalence_closure R1) R2) (equivalence_closure R1).
Proof.
  intros.
  split.
  2:{
    intros; eapply union_clo_equiv_l.
    unfold union_closure.
    eapply equivalence_closure_impl_proper; eauto.
    intros a' b' H'; intuition.
  }
  {
    induction 1; basic_goal_prep;
      basic_utils_crush.
  }
Qed.

Lemma union_closure_singleton_transport A (R : _ -> _ -> Prop) (x y z : A)
  : R y z ->
    iff2 (union_closure R (singleton_rel x y))
      (union_closure R (singleton_rel x z)).
Proof.
  unfold singleton_rel, union_closure.
  split.
  all: induction 1;
    basic_goal_prep;
    subst;
    intuition (subst; eauto using eq_clo_base, eq_clo_refl, eq_clo_trans,eq_clo_sym).
  {
    eapply eq_clo_trans;[| eauto using eq_clo_base,eq_clo_sym].
    eapply eq_clo_base; intuition eauto.
  }
  {
    eapply eq_clo_trans;[| eauto using eq_clo_base,eq_clo_sym].
    eapply eq_clo_base; intuition eauto.
  }
Qed.

Lemma union_closure_singleton_sym A (R : _ -> _ -> Prop) (x y : A)
  : iff2 (union_closure R (singleton_rel x y))
      (union_closure R (singleton_rel y x)).
Proof.
  unfold singleton_rel, union_closure.
  split.
  all: induction 1;
    basic_goal_prep;
    subst;
    intuition (subst; eauto using eq_clo_base, eq_clo_refl, eq_clo_trans,eq_clo_sym).
Qed.


Lemma closure_left A (R1 R2 : A -> A -> Prop) a b
  : R1 a b -> union_closure R1 R2 a b.
Proof.
  intros; eapply eq_clo_base; eauto.
Qed.
#[export] Hint Resolve closure_left : utils.

Lemma closure_right A (R1 R2 : A -> A -> Prop) a b
  : R2 a b -> union_closure R1 R2 a b.
Proof.
  intros; eapply eq_clo_base; eauto.
Qed.
#[export] Hint Resolve closure_right : utils.

Lemma singleton_applies A (a b : A)
  : singleton_rel a b a b.
Proof.
  unfold singleton_rel; intuition eauto.
Qed.
#[export] Hint Resolve singleton_applies: utils.

#[export] Instance union_closure_proper A : Proper (iff2 ==> iff2 ==> iff2) (union_closure (A:=A)).
Proof.
  intros R1 R1' HeqR1 R2 R2' HeqR2.
  eapply equivalence_closure_proper.
  unfold iff2 in *; cbn; intros.
  rewrite !HeqR1, !HeqR2.
  reflexivity.
Qed.

Add Parametric Relation A (R : A -> A -> Prop) : A (PER_closure R)
    symmetry proved by (PER_clo_sym _)
    transitivity proved by (PER_clo_trans _)
    as PER_rel.


#[export] Instance trans_PER_subrel {A} {R : A -> A -> Prop}
  : subrelation (transitive_closure R) (PER_closure R).
Proof.
  intros ? ? H; induction H;
    basic_goal_prep;
    basic_utils_crush.
Qed.

#[export] Instance PER_equiv_subrel {A} {R : A -> A -> Prop}
  : subrelation (PER_closure R) (equivalence_closure R).
Proof.
  intros ? ? H; induction H;
    basic_goal_prep;
    basic_utils_crush.
Qed.

Definition union_closure_PER {A : Type} (R1 R2 : A -> A -> Prop) :=
  PER_closure (fun a b => R1 a b \/ R2 a b).


#[export] Instance PER_closure_impl_proper {A : Type}
  : Proper (impl2 ==> (impl2 (A:=A))) PER_closure.
Proof.
  unfold impl2;
    repeat intro.
  induction H0; basic_goal_prep;
    basic_utils_crush.
Qed.

Lemma union_clo_PER_l A (R1 R2 : A -> _)
  : iff2 (union_closure_PER (PER_closure R1) R2)
      (union_closure_PER R1 R2).
Proof.
  unfold union_closure_PER.
  split.
  {
    induction 1; basic_goal_prep;
      basic_utils_crush.
    eapply PER_closure_impl_proper; eauto.
    unfold impl2; intuition eauto.
  }
  {
    induction 1; basic_goal_prep;
      basic_utils_crush.
  }
Qed.

Lemma PER_closure_left A (R1 R2 : A -> A -> Prop) a b
  : R1 a b -> union_closure_PER R1 R2 a b.
Proof.
  intros; eapply PER_clo_base; eauto.
Qed.
Hint Resolve PER_closure_left : utils.


Lemma union_closure_PER_subrel A (R1 R2 : A -> A -> Prop)
  : (forall a b, R2 a b -> (PER_closure R1) a b) ->
    iff2 (union_closure_PER (PER_closure R1) R2) (PER_closure R1).
Proof.
  intros.
  split.
  2:{
    intros; eapply union_clo_PER_l.
    unfold union_closure.
    eapply PER_closure_impl_proper; eauto.
    intros a' b' H'; intuition.
  }
  {
    induction 1; basic_goal_prep;
      basic_utils_crush.
  }
Qed.


Lemma or_comm_iff2 A (R1 R2 : A -> A -> Prop) : iff2 (or2 R1 R2) (or2 R2 R1).
Proof. unfold iff2, or2; cbn; intros; intuition auto. Qed.

#[export] Instance PER_closure_Proper {A} : Proper (iff2 ==> iff2) (PER_closure (A:=A)).
Proof.
  repeat intro; split; eapply PER_closure_impl_proper;
    unfold iff2, impl2 in *; firstorder eauto.
Qed.      

Lemma union_closure_PER_sym A (R1 R2 : A -> A -> Prop)
  : iff2 (union_closure_PER R1 R2) (union_closure_PER R2 R1).
Proof.
  unfold union_closure_PER.
  change (fun a b : A => R1 a b \/ R2 a b) with (or2 R1 R2).
  rewrite or_comm_iff2.
  reflexivity.
Qed.


Lemma PER_bind A (R1 R2 : A -> A -> Prop)
  : impl2 R1 (PER_closure R2) ->
    impl2 (PER_closure R1) (PER_closure R2).
Proof.
  intros ? ? ? H.
  induction H; basic_goal_prep;
    basic_utils_crush.
Qed.

Lemma trans_bind A (R1 R2 : A -> A -> Prop)
  : impl2 R1 (transitive_closure R2) ->
    impl2 (transitive_closure R1) (transitive_closure R2).
Proof.
  intros ? ? ? H.
  induction H; basic_goal_prep;
    basic_utils_crush.
  etransitivity; try eassumption.
  eapply H0; eauto.
Qed.



Lemma union_closure_PER_singleton_transport1 A (R : _ -> _ -> Prop) (x y z : A)
  : R y z ->
    iff2 (union_closure_PER R (singleton_rel x y))
      (union_closure_PER R (singleton_rel x z)).
Proof.
  unfold singleton_rel, union_closure_PER.
  split.
  all: induction 1;
    basic_goal_prep;
    subst;
    intuition (subst; eauto using PER_clo_base, PER_clo_trans,PER_clo_sym).
  {
    eapply PER_clo_trans;[| eauto using PER_clo_base,PER_clo_sym].
    eapply PER_clo_base; intuition eauto.
  }
  {
    eapply PER_clo_trans;[| eauto using PER_clo_base,PER_clo_sym].
    eapply PER_clo_base; intuition eauto.
  }
Qed.

Lemma union_closure_PER_singleton_transport A (R : _ -> _ -> Prop) (x y z : A)
  : transitive_closure R y z ->
    iff2 (union_closure_PER R (singleton_rel x y))
      (union_closure_PER R (singleton_rel x z)).
Proof.
  induction 1;
    basic_goal_prep;
    rewrite union_closure_PER_singleton_transport1; eauto.
  reflexivity.
Qed.


Lemma union_closure_PER_singleton_sym A (R : _ -> _ -> Prop) (x y : A)
  : iff2 (union_closure_PER R (singleton_rel x y))
      (union_closure_PER R (singleton_rel y x)).
Proof.
  unfold singleton_rel, union_closure_PER.
  split.
  all: induction 1;
    basic_goal_prep;
    subst;
    intuition (subst; eauto using PER_clo_base,PER_clo_trans,PER_clo_sym).
Qed.


#[export] Instance union_closure_PER_Proper A
  : Proper (iff2 ==> iff2 ==> iff2) (union_closure_PER (A:=A)).
Proof.
  repeat intro.
  eapply PER_closure_Proper.
  repeat intro.
  unfold iff2 in *.
  rewrite H, H0.
  reflexivity.
Qed.
