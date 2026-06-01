(* ============================================================================
   Depth-restricted map laws for pos_trie  (the CORRECT replacement for the
   false [pos_trie_map_ok]; see WIP/PosTrieMapOk_false.v).

   [forall A, map.ok (@pos_trie_map A)] is FALSE because map.ok quantifies over
   ill-formed mixed-depth tries.  The lawful object is depth-RESTRICTED: the
   get/put laws hold for keys of a fixed length n under the uniform-depth
   predicate [depth' _ n] / [depth _ n] (PosListMap.v:904-915) -- in real
   e-graph use every key of a per-symbol db table has the same length (the
   symbol's arity), so the relevant tries are uniform-depth.

   All 11 lemmas Qed, 0 axioms ("Closed under the global context").  Destined
   for src/Utils/PosListMap.v (inside Section __, Context {A:Type}); kept here
   in WIP for now.  The core laws are the depth-restricted forms of:
     get_put_same  -> pt_get_put_same  / pt_get'_put'_same
     get_put_diff  -> pt_get_put_diff  / pt_get'_put'_diff
   plus put-preserves-depth (pt_put_depth) and the foundational PTree gss'/gso'
   and singleton lemmas.  DEFERRED (pending scoping of which fields the generic
   soundness lemma needs): map_ext / remove laws / fold_spec / fold_parametricity.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List Lia.
Import ListNotations.
From Tries Require Import Canonical.
From Utils Require Import PosListMap.

Set Implicit Arguments.

(* Lemma 1: get'(set' i x m) i = Some x *)
Lemma gss' : forall (A:Type) (i:positive) (x:A) (m: PTree.tree' A),
    PTree.get' i (PTree.set' i x m) = Some x.
Proof.
  induction i; destruct m; simpl; intros; auto using PTree.gss0.
Qed.

(* Lemma 2: i<>j -> get'(set' j x m) i = get' i m *)
Lemma gso' : forall (A:Type) (i j:positive) (x:A) (m: PTree.tree' A),
    i <> j -> PTree.get' i (PTree.set' j x m) = PTree.get' i m.
Proof.
  intros A i j x m H.
  revert j H m; induction i; destruct j, m; simpl; intros; auto;
    solve [apply IHi; congruence | apply PTree.gso0; congruence | congruence].
Qed.

(* Lemma 3: pt_get'(pt_singleton k v) k = Some v *)
Lemma pt_get'_singleton_same : forall (A:Type) (k: list positive) (v:A),
    pt_get' (pt_singleton k v) k = Some v.
Proof.
  induction k; simpl; auto.
  intro v. rewrite PTree.gss0. apply IHk.
Qed.

(* Lemma 4: length k = length k' -> k<>k' -> pt_get'(pt_singleton k' v) k = None *)
Lemma pt_get'_singleton_diff : forall (A:Type) (k k': list positive) (v:A),
    length k = length k' -> k <> k' -> pt_get' (pt_singleton k' v) k = None.
Proof.
  induction k; destruct k'; simpl; intros; try discriminate; try congruence.
  destruct (Pos.eq_dec a p) as [Heq | Hne].
  - subst p.
    rewrite PTree.gss0.
    apply IHk.
    + lia.
    + intro Heq. apply H0. rewrite Heq. reflexivity.
  - rewrite PTree.gso0 by auto. reflexivity.
Qed.

(* Lemma 5: depth'(pt_singleton k v) (length k) *)
Lemma pt_singleton_depth' : forall (A:Type) (k: list positive) (v:A),
    depth' (pt_singleton k v) (length k).
Proof.
  induction k; simpl.
  - constructor.
  - constructor. intros j w Hget.
    destruct (Pos.eq_dec j a) as [Heq | Hne].
    + subst a. rewrite PTree.gss0 in Hget. injection Hget. intro; subst w. apply IHk.
    + rewrite PTree.gso0 in Hget by auto. discriminate.
Qed.

(* Lemma 6: depth'(pt_put' t k v) (length k) given depth' t (length k) *)
Lemma pt_put'_depth' : forall (A:Type) (k: list positive) (v:A) t,
    depth' t (length k) -> depth' (pt_put' t k v) (length k).
Proof.
  induction k; intros.
  - inversion H; subst.
    simpl. constructor.
  - inversion H; subst.
    simpl.
    case_eq (PTree.get' a m); intros.
    + constructor. intros j w Hget.
      destruct (Pos.eq_dec j a) as [Heq | Hne].
      * subst a. rewrite gss' in Hget. injection Hget. intro; subst w.
        apply IHk. exact (H2 j p H0).
      * rewrite gso' in Hget by auto.
        exact (H2 _ _ Hget).
    + constructor. intros j w Hget.
      destruct (Pos.eq_dec j a) as [Heq | Hne].
      * subst a. rewrite gss' in Hget. injection Hget. intro; subst w.
        apply pt_singleton_depth'.
      * rewrite gso' in Hget by auto.
        exact (H2 _ _ Hget).
Qed.

(* Lemma 7: depth(pt_put m k v) (length k) given depth m (length k) *)
Lemma pt_put_depth : forall (A:Type) (k: list positive) (v:A) m,
    depth m (length k) -> depth (pt_put m k v) (length k).
Proof.
  intros A k v m H.
  destruct m; simpl.
  - apply pt_put'_depth'. exact H.
  - apply pt_singleton_depth'.
Qed.

(* Lemma 8: pt_get'(pt_put' t k v) k = Some v given depth' t (length k) *)
Lemma pt_get'_put'_same : forall (A:Type) (k: list positive) (v:A) t,
    depth' t (length k) -> pt_get' (pt_put' t k v) k = Some v.
Proof.
  induction k; intros.
  - inversion H; subst. simpl. reflexivity.
  - inversion H; subst.
    simpl.
    case_eq (PTree.get' a m); intros.
    + rewrite gss'. apply IHk. exact (H2 a p H0).
    + rewrite gss'. apply pt_get'_singleton_same.
Qed.

(* Lemma 9: pt_get(pt_put m k v) k = Some v given depth m (length k) *)
Lemma pt_get_put_same : forall (A:Type) (k: list positive) (v:A) m,
    depth m (length k) -> pt_get (pt_put m k v) k = Some v.
Proof.
  intros A k v m H.
  destruct m; simpl.
  - apply pt_get'_put'_same. exact H.
  - apply pt_get'_singleton_same.
Qed.

(* Lemma 10: length k = length k' -> k<>k' -> depth' t (length k') ->
             pt_get'(pt_put' t k' v) k = pt_get' t k *)
Lemma pt_get'_put'_diff : forall (A:Type) (k k': list positive) (v:A) t,
    length k = length k' -> k <> k' -> depth' t (length k') ->
    pt_get' (pt_put' t k' v) k = pt_get' t k.
Proof.
  induction k; destruct k'; intros; try discriminate.
  - simpl. congruence.
  - simpl. inversion H1; subst.
    destruct (PTree.get' p m) eqn:Hgetp.
    + destruct (Pos.eq_dec a p) as [Heq | Hne2].
      * subst p. rewrite gss'. rewrite Hgetp.
        apply IHk.
        -- simpl in H. lia.
        -- intro Heq. apply H0. rewrite Heq. reflexivity.
        -- exact (H4 a p0 Hgetp).
      * rewrite gso' by auto. reflexivity.
    + destruct (Pos.eq_dec a p) as [Heq | Hne2].
      * subst p. rewrite gss'. rewrite Hgetp.
        apply pt_get'_singleton_diff.
        -- simpl in H. lia.
        -- intro Heq. apply H0. rewrite Heq. reflexivity.
      * rewrite gso' by auto. reflexivity.
Qed.

(* Lemma 11: length k = length k' -> k<>k' -> depth m (length k') ->
             pt_get(pt_put m k' v) k = pt_get m k *)
Lemma pt_get_put_diff : forall (A:Type) (k k': list positive) (v:A) m,
    length k = length k' -> k <> k' -> depth m (length k') ->
    pt_get (pt_put m k' v) k = pt_get m k.
Proof.
  intros A k k' v m Hlen Hne Hdepth.
  destruct m; simpl.
  - apply pt_get'_put'_diff; auto.
  - simpl. apply pt_get'_singleton_diff; auto.
Qed.
