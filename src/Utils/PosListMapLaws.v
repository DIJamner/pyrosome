(* ============================================================================
   Depth-restricted map laws for pos_trie (the db-trie interface):
   get_empty, get_put_same/diff, get_remove_same/diff, fold_spec.
   Consolidated from the WIP development; destined to back the depth-indexed
   e-graph db-trie interface that replaces the (false) map.ok obligation.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List Lia.
Import ListNotations.
From Tries Require Import Canonical.
From Utils Require Import PosListMap TrieMapFold.

Set Implicit Arguments.

(* ============================================================================ *)
(* Part I: get/put laws (from WIP/PosTrieDepthLaws.v)                          *)
(* ============================================================================ *)

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

(* ============================================================================ *)
(* Part II: remove laws + get_empty (from WIP/PosTrieRemoveLaws.v)             *)
(* ============================================================================ *)

(* remove' is option-level: PTree.remove' : positive -> tree' A -> tree A, and
   PTree.remove p (PTree.Nodes m) = PTree.remove' p m definitionally, so the
   option-level grs/gro instantiate to tree'-level facts. *)
(* descending one level into [of_ptree T] *)
(* get_empty (trivial) *)
Lemma pt_get_empty : forall (A:Type) (k:list positive), @pt_get A None k = None.
Proof. reflexivity. Qed.

(* M1: pt_remove preserves uniform depth. *)
(* M2: get_remove_same (UNCONDITIONAL). *)
(* M3: get_remove_diff (depth-restricted, equal length). *)
(* ============================================================================ *)
(* Part III: fold_spec (from WIP/PosTrieFoldSpec.v)                            *)
(* ============================================================================ *)

Section FoldSpec.
  Context {A : Type}.

  (* ===== A. non-emptiness =================================================== *)
  Lemma pos_trie'_nonempty : forall n (t:@pos_trie' A),
      depth' t n -> exists k, length k = n /\ pt_get' t k <> None.
  Proof.
    induction n; intros t Hd.
    - inversion Hd; subst. exists []. split; [reflexivity| cbn; congruence].
    - inversion Hd as [| m n0 Hforall Hm Hn]; subst.
      destruct (PTree.tree'_not_empty m) as [p Hp].
      destruct (PTree.get' p m) as [c|] eqn:Hgp; [|congruence].
      destruct (IHn c (Hforall p c Hgp)) as [k' [Hlen Hget]].
      exists (p::k'). split; [cbn; lia|].
      cbn. rewrite Hgp. exact Hget.
  Qed.

  (* ===== B. extensionality (depth-restricted) ============================== *)
  Lemma pos_trie'_ext : forall n (t1 t2:@pos_trie' A),
      depth' t1 n -> depth' t2 n ->
      (forall k, length k = n -> pt_get' t1 k = pt_get' t2 k) ->
      t1 = t2.
  Proof.
    induction n; intros t1 t2 Hd1 Hd2 Hk.
    - inversion Hd1; inversion Hd2; subst.
      specialize (Hk [] eq_refl).
      cbn in Hk. injection Hk as ->. reflexivity.
    - inversion Hd1 as [|m1 n1 Hf1 Ht1 Hn1]; inversion Hd2 as [|m2 n2 Hf2 Ht2 Hn2]; subst.
      f_equal.
      assert (HNodes : PTree.Nodes m1 = PTree.Nodes m2).
      {
        apply PTree.extensionality.
        intro i. cbn [PTree.get].
        destruct (PTree.get' i m1) as [c1|] eqn:H1;
        destruct (PTree.get' i m2) as [c2|] eqn:H2.
        - f_equal.
          apply (IHn c1 c2 (Hf1 i c1 H1) (Hf2 i c2 H2)).
          intros suf Hlen.
          specialize (Hk (i :: suf) ltac:(cbn; lia)).
          cbn in Hk. rewrite H1, H2 in Hk. exact Hk.
        - exfalso.
          destruct (pos_trie'_nonempty (Hf1 i c1 H1)) as [suf [Hlen Hne]].
          specialize (Hk (i :: suf) ltac:(cbn; lia)).
          cbn in Hk. rewrite H1, H2 in Hk. apply Hne. exact Hk.
        - exfalso.
          destruct (pos_trie'_nonempty (Hf2 i c2 H2)) as [suf [Hlen Hne]].
          specialize (Hk (i :: suf) ltac:(cbn; lia)).
          cbn in Hk. rewrite H1, H2 in Hk. apply Hne. symmetry. exact Hk.
        - reflexivity.
      }
      injection HNodes as ->. reflexivity.
  Qed.

  Lemma pos_trie_ext : forall n (m1 m2:@pos_trie A),
      depth m1 n -> depth m2 n ->
      (forall k, length k = n -> pt_get m1 k = pt_get m2 k) ->
      m1 = m2.
  Proof.
    intros n m1 m2 Hd1 Hd2 Hk.
    destruct m1 as [t1|]; destruct m2 as [t2|].
    { cbn in Hd1, Hd2.
      f_equal.
      apply (pos_trie'_ext Hd1 Hd2).
      intros k Hlen. exact (Hk k Hlen). }
    { exfalso.
      cbn in Hd1.
      destruct (pos_trie'_nonempty Hd1) as [k [Hlen Hne]].
      specialize (Hk k Hlen).
      cbn in Hk. apply Hne. exact Hk. }
    { exfalso.
      cbn in Hd2.
      destruct (pos_trie'_nonempty Hd2) as [k [Hlen Hne]].
      specialize (Hk k Hlen).
      cbn in Hk. apply Hne. symmetry. exact Hk. }
    { reflexivity. }
  Qed.

  (* ===== C. elements ======================================================= *)

  (* Fuel-based auxiliary.  Terminates on n (the first argument).
     For depth'-n tries all cases are covered; the (O, node) branch is
     dead code (unreachable for well-formed inputs). *)
  Fixpoint pt_elements'_aux (n:nat) (t:@pos_trie' A) (stack:list positive)
    : list (list positive * A) :=
    match n, t with
    | _, pos_trie_leaf a => [(rev stack, a)]
    | O, pos_trie_node _ => []          (* unreachable for depth'-0 nodes *)
    | S n', pos_trie_node m =>
        flat_map (fun pc => pt_elements'_aux n' (snd pc) (fst pc :: stack))
                 (trie_elements (PTree.Nodes m))
    end.

  (* Top-level function: use the depth n as fuel. *)
  Definition pt_elements_n (n:nat) (m:@pos_trie A) : list (list positive * A) :=
    match m with
    | None => []
    | Some t => pt_elements'_aux n t []
    end.

  (* ===== Helper: map fst distributes over flat_map ======================== *)
  Lemma map_fst_flat_map_aux : forall (C D E : Type) (f : C -> list (D * E)) (l : list C),
      map fst (flat_map f l) = flat_map (fun x => map fst (f x)) l.
  Proof.
    intros. induction l; cbn; [reflexivity|].
    rewrite map_app. f_equal. exact IHl.
  Qed.

  (* ===== Spec of pt_elements'_aux ========================================= *)
  Lemma pt_elements'_aux_spec : forall n (t:@pos_trie' A) stack k v,
      depth' t n ->
      (In (k,v) (pt_elements'_aux n t stack) <->
       exists suf, k = rev stack ++ suf /\ length suf = n /\ pt_get' t suf = Some v).
  Proof.
    induction n; intros t stack k v Hd; split; intro Hin.
    - inversion Hd; subst.
      cbn [pt_elements'_aux] in Hin.
      destruct Hin as [Heq|[]]; injection Heq; intros; subst.
      exists []. cbn. rewrite app_nil_r. repeat split; reflexivity.
    - destruct Hin as [suf [Hk [Hlen Hget]]]. inversion Hd; subst.
      destruct suf; [|cbn in Hlen; discriminate].
      cbn [pt_elements'_aux]. left.
      rewrite app_nil_r. cbn [pt_get'] in Hget. injection Hget; intros; subst.
      reflexivity.
    - inversion Hd as [|m n_inner Hinv Hm Hn]; subst.
      cbn [pt_elements'_aux] in Hin.
      rewrite in_flat_map in Hin.
      destruct Hin as [[p c] [Hpc Hin']].
      fold (trie_elements (PTree.Nodes m)) in Hpc.
      apply trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
      cbn [fst snd] in Hin'.
      assert (Hdc : depth' c n) by exact (Hinv p c Hpc).
      apply (IHn c (p::stack) k v Hdc) in Hin'.
      destruct Hin' as [suf' [Hk' [Hlen' Hget']]].
      exists (p::suf'). split.
      + rewrite Hk'. cbn [rev]. rewrite <- app_assoc. reflexivity.
      + split; [cbn; lia|]. cbn [pt_get']. rewrite Hpc. exact Hget'.
    - destruct Hin as [suf [Hk [Hlen Hget]]].
      inversion Hd as [|m n_inner Hinv Hm Hn]; subst.
      destruct suf as [|p suf']; [cbn in Hlen; discriminate|].
      cbn [pt_get'] in Hget.
      destruct (PTree.get' p m) as [c|] eqn:Hpm; [|discriminate].
      assert (Hdc : depth' c n) by exact (Hinv p c Hpm).
      cbn [pt_elements'_aux].
      rewrite in_flat_map. exists (p,c). split.
      + apply trie_tuples_spec. cbn [PTree.get]. exact Hpm.
      + cbn [fst snd].
        apply (proj2 (IHn c (p::stack) (rev stack ++ p :: suf') v Hdc)).
        exists suf'. split; [|split].
        * cbn [rev]. rewrite <- app_assoc. reflexivity.
        * cbn in Hlen. lia.
        * exact Hget.
  Qed.

  (* ===== NoDup of pt_elements'_aux ======================================== *)

  (* Key prefix: every entry (k,v) in pt_elements'_aux n c (p::stack) has
     k = rev stack ++ p :: suf for some suf. *)
  Lemma key_in_block_prefix : forall n (c:@pos_trie' A) p stack k v,
      depth' c n ->
      In (k,v) (pt_elements'_aux n c (p :: stack)) ->
      exists suf, k = rev stack ++ p :: suf.
  Proof.
    intros n c p stack k v Hd Hin.
    apply (pt_elements'_aux_spec (p::stack) k v Hd) in Hin.
    destruct Hin as [suf [Hk _]].
    exists suf. rewrite Hk. cbn [rev]. rewrite <- app_assoc. reflexivity.
  Qed.

  (* Pairwise disjointness of blocks: if l has NoDup first-components,
     then the blocks of pt_elements'_aux keys are pairwise disjoint. *)
  Lemma blocks_forall_disjoint : forall n (l : list (positive * @pos_trie' A)) stack,
      NoDup (map fst l) ->
      (forall p c, In (p,c) l -> depth' c n) ->
      ForallOrdPairs
        (fun l1 l2 => forall k, In k l1 -> ~ In k l2)
        (map (fun pc => map fst (pt_elements'_aux n (snd pc) (fst pc :: stack))) l).
  Proof.
    induction l as [|[p1 c1] l IHl]; intros stack Hnd Hall.
    - constructor.
    - cbn [map fst].
      apply FOP_cons.
      + rewrite Forall_forall.
        intros bl Hbl.
        rewrite in_map_iff in Hbl.
        destruct Hbl as [[p2 c2] [Hbl_eq Hpc2_in]].
        subst bl. cbn [fst snd].
        assert (Hp1_notin : ~ In p1 (map fst l)).
        { inversion Hnd as [|x xs H1 H2 Heq]; subst. exact H1. }
        assert (Hp1_ne_p2 : p1 <> p2).
        { intro Heq. subst. apply Hp1_notin.
          apply in_map_iff. exists (p2, c2). split; [reflexivity | exact Hpc2_in]. }
        assert (Hdc1 : depth' c1 n) by (apply (Hall p1 c1); left; reflexivity).
        assert (Hdc2 : depth' c2 n) by (apply (Hall p2 c2); right; exact Hpc2_in).
        intros k Hk1 Hk2.
        apply in_map_iff in Hk1. destruct Hk1 as [[k1 v1] [Hfst1 Hin1]].
        cbn [fst] in Hfst1. subst k.
        apply in_map_iff in Hk2. destruct Hk2 as [[k2 v2] [Hfst2 Hin2]].
        cbn [fst] in Hfst2.
        destruct (key_in_block_prefix p1 stack k1 v1 Hdc1 Hin1) as [suf1 Hksuf1].
        subst k2.
        destruct (key_in_block_prefix p2 stack k1 v2 Hdc2 Hin2) as [suf2 Hksuf2].
        rewrite Hksuf2 in Hksuf1.
        apply app_inv_head in Hksuf1.
        injection Hksuf1. intros _. intro Heq. exact (Hp1_ne_p2 (eq_sym Heq)).
      + apply IHl.
        * inversion Hnd as [|x xs H1 H2 Heq]; subst. exact H2.
        * intros p c Hin. exact (Hall p c (or_intror Hin)).
  Qed.

  Lemma pt_elements'_aux_nodup : forall n (t:@pos_trie' A) stack,
      depth' t n ->
      NoDup (map fst (pt_elements'_aux n t stack)).
  Proof.
    induction n; intros t stack Hd.
    - inversion Hd; subst.
      cbn [pt_elements'_aux map fst].
      apply NoDup_cons; [simpl; tauto | constructor].
    - inversion Hd as [|m n_inner Hinv Hm Hn]; subst.
      cbn [pt_elements'_aux].
      rewrite map_fst_flat_map_aux.
      rewrite flat_map_concat_map.
      apply NoDup_concat.
      + rewrite Forall_map. rewrite Forall_forall.
        intros [p c] Hpc. cbn [fst snd].
        fold (trie_elements (PTree.Nodes m)) in Hpc.
        apply trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
        exact (IHn c (p :: stack) (Hinv p c Hpc)).
      + fold (trie_elements (PTree.Nodes m)).
        apply (blocks_forall_disjoint (trie_elements (PTree.Nodes m)) stack).
        * exact (trie_elements_nodup _).
        * intros p c Hpc.
          apply trie_tuples_spec in Hpc.
          cbn [PTree.get] in Hpc.
          exact (Hinv p c Hpc).
  Qed.

  (* ===== TARGET LEMMAS ==================================================== *)

  (* In/get correspondence for the top level (depth-n m): keys all have length n. *)
  Lemma pt_elements_spec : forall n (m:@pos_trie A) k v,
      depth m n ->
      (In (k,v) (pt_elements_n n m) <-> (pt_get m k = Some v /\ length k = n)).
  Proof.
    intros n m k v Hd.
    destruct m as [t|]; cbn [pt_elements_n pt_get].
    - rewrite (pt_elements'_aux_spec [] k v Hd).
      cbn [rev app].
      split.
      + intros [suf [Hk [Hlen Hget]]]. subst k. split; [exact Hget | exact Hlen].
      + intros [Hget Hlen]. exists k. split; [reflexivity | split; [exact Hlen | exact Hget]].
    - cbn [depth] in Hd.
      split; [intros [] | intros [H _]; discriminate].
  Qed.

  (* NoDup of keys in pt_elements_n n m, given depth m n. *)
  Lemma pt_elements_nodup : forall n (m:@pos_trie A),
      depth m n ->
      NoDup (map fst (pt_elements_n n m)).
  Proof.
    intros n m Hd.
    destruct m as [t|].
    - cbn [pt_elements_n].
      exact (pt_elements'_aux_nodup [] Hd).
    - cbn [pt_elements_n]. constructor.
  Qed.

  (* ===== D. fold = fold_left over elements ================================ *)
  Lemma fold_left_flat_map_het :
    forall (X Z Y : Type) (g : Y -> Z -> Y) (h : X -> list Z) (l : list X) (a0 : Y),
      fold_left g (flat_map h l) a0 =
      fold_left (fun a x => fold_left g (h x) a) l a0.
  Proof.
    intros X Z Y g h l. induction l as [|x xs IH]; intro a0.
    - reflexivity.
    - cbn [flat_map fold_left].
      rewrite fold_left_app.
      exact (IH _).
  Qed.

  Lemma fold_left_ext_in :
    forall (X Y : Type) (s1 s2 : Y -> X -> Y) (l : list X) (a0 : Y),
      (forall a x, In x l -> s1 a x = s2 a x) ->
      fold_left s1 l a0 = fold_left s2 l a0.
  Proof.
    intros X Y s1 s2 l. induction l as [|x xs IH]; intros a0 Hext.
    - reflexivity.
    - cbn [fold_left].
      rewrite (Hext a0 x (or_introl eq_refl)).
      apply IH.
      intros a y Hy. apply Hext. right. exact Hy.
  Qed.

  Lemma pt_fold'_elements : forall n (R:Type) (f : R -> list positive -> A -> R)
                                   (acc : R) (t : @pos_trie' A) (stack : list positive),
      depth' t n ->
      pt_fold' f acc t stack =
      fold_left (fun a p => f a (fst p) (snd p)) (pt_elements'_aux n t stack) acc.
  Proof.
    induction n; intros R f acc t stack Hd.
    - inversion Hd; subst.
      cbn [pt_fold' pt_elements'_aux fold_left].
      reflexivity.
    - inversion Hd as [|m n0 Hinv Hm Hn]; subst.
      cbn [pt_fold'].
      change (TrieMap.trie_fold' (fun (acc0 : R) (p : positive) (pt0 : @pos_trie' A) =>
                                    pt_fold' f acc0 pt0 (p :: stack)) acc m 1)
        with (TrieMap.trie_fold (fun (acc0 : R) (p : positive) (pt0 : @pos_trie' A) =>
                                   pt_fold' f acc0 pt0 (p :: stack)) acc (PTree.Nodes m)).
      rewrite trie_fold_elements.
      cbn [pt_elements'_aux].
      set (L := trie_elements (PTree.Nodes m)).
      set (g := fun (a : R) (p : list positive * A) => f a (fst p) (snd p)).
      set (h := fun (pc : positive * @pos_trie' A) =>
                  pt_elements'_aux n (snd pc) (fst pc :: stack)).
      symmetry.
      rewrite (@fold_left_flat_map_het (positive * @pos_trie' A) (list positive * A) R g h L acc).
      apply fold_left_ext_in.
      intros a pc Hpc_in.
      subst g h L.
      destruct pc as [p child].
      cbn [fst snd].
      apply trie_tuples_spec in Hpc_in.
      cbn [PTree.get] in Hpc_in.
      symmetry.
      exact (IHn R f a child (p :: stack) (Hinv p child Hpc_in)).
  Qed.

  Lemma pt_fold_elements : forall n (R:Type) (f : R -> list positive -> A -> R) r0 (m:@pos_trie A),
      depth m n ->
      pt_fold f r0 m
      = fold_left (fun a p => f a (fst p) (snd p)) (pt_elements_n n m) r0.
  Proof.
    intros n R f r0 m Hd.
    destruct m as [t|].
    - cbn [pt_fold pt_elements_n].
      cbn [depth] in Hd.
      exact (pt_fold'_elements f r0 [] Hd).
    - cbn [pt_fold pt_elements_n fold_left].
      reflexivity.
  Qed.

  (* ===== E. fold_spec ====================================================== *)
  Section EAssembly.
    (* These four hypotheses are proved 0-axiom in the top-level lemmas above
       (pt_get_put_same, pt_get_put_diff, pt_put_depth, pt_get_empty).
       They are discharged in pt_fold_spec' below the section. *)
    Context (pt_get_empty_h : forall (k : list positive), @pt_get A None k = None).
    Context (pt_get_put_same_h : forall (k : list positive) (v : A) (m : @pos_trie A),
                depth m (length k) -> pt_get (pt_put m k v) k = Some v).
    Context (pt_get_put_diff_h : forall (k k' : list positive) (v : A) (m : @pos_trie A),
                length k = length k' -> k <> k' -> depth m (length k') ->
                pt_get (pt_put m k' v) k = pt_get m k).
    Context (pt_put_depth_h : forall (k : list positive) (v : A) (m : @pos_trie A),
                depth m (length k) -> depth (pt_put m k v) (length k)).

    (* Auxiliary: depth None n for any n *)
    (* Auxiliary: all keys in pt_elements_n n m have length n *)
    Lemma pt_elements_length_keys : forall n (m : @pos_trie A),
        depth m n ->
        forall kv, In kv (pt_elements_n n m) -> length (fst kv) = n.
    Proof.
      intros n m Hd kv Hin.
      apply (pt_elements_spec n m (fst kv) (snd kv) Hd).
      rewrite <- surjective_pairing. exact Hin.
    Qed.

    (* Auxiliary: pt_of_list over a uniform-length-n list has depth n *)
    (* Auxiliary: pt_get (pt_of_list l) k = Some v when (k,v) in l,
       given uniform key length n, NoDup, and length k = n *)
    (* Auxiliary: pt_get (pt_of_list l) k = None when k not in map fst l,
       given uniform key length n and length k = n *)
    Lemma pt_fold_spec : forall n (R : Type) (P : @pos_trie A -> R -> Prop)
                                (f : R -> list positive -> A -> R) r0,
        P None r0 ->
        (forall k v (m : @pos_trie A) r,
            length k = n -> depth m n -> pt_get m k = None -> P m r ->
            P (pt_put m k v) (f r k v)) ->
        forall m, depth m n -> P m (pt_fold f r0 m).
    Proof.
      intros n R P f r0 Hbase Hstep m Hd.
      rewrite (pt_fold_elements n f r0 m Hd).
      set (l := pt_elements_n n m).
      set (g := fun (acc : R) (p : list positive * A) => f acc (fst p) (snd p)).
      assert (depth_none_n : @depth A None n) by (destruct n; exact I).
      assert (depth_fold_left : forall (l' : list (list positive * A)) mm,
          (forall kv, In kv l' -> length (fst kv) = n) ->
          depth mm n ->
          depth (fold_left (fun acc p => pt_put acc (fst p) (snd p)) l' mm) n).
      { induction l' as [|[k v] tl IH]; intros mm Hlens Hdmm.
        - exact Hdmm.
        - cbn [fold_left fst snd].
          apply IH.
          + intros kv Hkv. apply Hlens. right. exact Hkv.
          + assert (Hkn : length k = n) by (apply (Hlens (k,v)); left; exact eq_refl).
            rewrite <- Hkn. apply pt_put_depth_h. rewrite Hkn. exact Hdmm. }
      assert (get_fold_same : forall (l' : list (list positive * A)) k0 mm,
          (forall kv, In kv l' -> length (fst kv) = n) ->
          depth mm n ->
          ~ In k0 (map fst l') ->
          length k0 = n ->
          pt_get (fold_left (fun acc p => pt_put acc (fst p) (snd p)) l' mm) k0 = pt_get mm k0).
      { induction l' as [|[k1 v1] tl1 IHgs]; intros k0 mm Hlens1 Hdmm1 Hnotin1 Hk0n1.
        - reflexivity.
        - cbn [fold_left fst snd].
          assert (Hk1n : length k1 = n) by (apply (Hlens1 (k1,v1)); left; exact eq_refl).
          assert (Hk0_ne_k1 : k0 <> k1) by (intro Heq; subst k1; apply Hnotin1; left; reflexivity).
          assert (Hdput1 : depth (pt_put mm k1 v1) n)
            by (rewrite <- Hk1n; apply pt_put_depth_h; rewrite Hk1n; exact Hdmm1).
          rewrite IHgs.
          + rewrite pt_get_put_diff_h.
            * reflexivity.
            * rewrite Hk0n1, Hk1n. reflexivity.
            * exact Hk0_ne_k1.
            * rewrite Hk1n. exact Hdmm1.
          + intros kv Hkv. apply Hlens1. right. exact Hkv.
          + exact Hdput1.
          + intros Hink1. apply Hnotin1. right. exact Hink1.
          + exact Hk0n1. }
      assert (get_fold_in2 : forall (l' : list (list positive * A)) k0 v0 mm,
          NoDup (map fst l') ->
          (forall kv, In kv l' -> length (fst kv) = n) ->
          depth mm n ->
          (forall k'', In k'' (map fst l') -> pt_get mm k'' = None) ->
          In (k0, v0) l' ->
          length k0 = n ->
          pt_get (fold_left (fun acc p => pt_put acc (fst p) (snd p)) l' mm) k0 = Some v0).
      { induction l' as [|[k1 v1] tl1 IHgi]; intros k0 v0 mm Hnd1 Hlens1 Hdmm1 Hfresh1 Hin1 Hk0n1.
        - inversion Hin1.
        - cbn [fold_left fst snd].
          apply NoDup_cons_iff in Hnd1. destruct Hnd1 as [Hnotin1 Hndtl1].
          assert (Hk1n : length k1 = n) by (apply (Hlens1 (k1,v1)); left; exact eq_refl).
          assert (Hdput1 : depth (pt_put mm k1 v1) n)
            by (rewrite <- Hk1n; apply pt_put_depth_h; rewrite Hk1n; exact Hdmm1).
          destruct Hin1 as [Heq1 | Hin1'].
          + injection Heq1 as Hk01 Hv01. subst k1 v1.
            rewrite get_fold_same.
            * apply pt_get_put_same_h. rewrite Hk0n1. exact Hdmm1.
            * intros kv Hkv. apply Hlens1. right. exact Hkv.
            * exact Hdput1.
            * exact Hnotin1.
            * exact Hk0n1.
          + assert (Hk0ne : k0 <> k1)
              by (intro Heq2; subst k1; apply Hnotin1;
                  apply in_map_iff; exists (k0, v0); split; [cbn; reflexivity | exact Hin1']).
            apply IHgi.
            * exact Hndtl1.
            * intros kv Hkv. apply Hlens1. right. exact Hkv.
            * exact Hdput1.
            * intros k'' Hk''in.
              assert (Hk''n : length k'' = n).
              { rewrite in_map_iff in Hk''in.
                destruct Hk''in as [[k3 v3] [Hfst3 Hin3]].
                cbn [fst] in Hfst3. subst k3.
                apply (Hlens1 (k'', v3)); right. exact Hin3. }
              assert (Hne3 : k'' <> k1) by (intro Heq2; subst k''; apply Hnotin1; exact Hk''in).
              rewrite pt_get_put_diff_h.
              -- apply Hfresh1. right. exact Hk''in.
              -- rewrite Hk''n, Hk1n. reflexivity.
              -- exact Hne3.
              -- rewrite Hk1n. exact Hdmm1.
            * exact Hin1'.
            * exact Hk0n1. }
      assert (Heq : fold_left (fun acc p => pt_put acc (fst p) (snd p)) l (None : @pos_trie A) = m).
      { apply (pos_trie_ext (n:=n)).
        - apply depth_fold_left.
          + apply pt_elements_length_keys. exact Hd.
          + exact depth_none_n.
        - exact Hd.
        - intros k Hkn.
          destruct (pt_get m k) eqn:Hgetmk.
          + rewrite get_fold_in2 with (v0 := a).
            * reflexivity.
            * apply pt_elements_nodup. exact Hd.
            * apply pt_elements_length_keys. exact Hd.
            * exact depth_none_n.
            * intros k'' _. apply pt_get_empty_h.
            * apply (pt_elements_spec n m k a Hd). split; [exact Hgetmk | exact Hkn].
            * exact Hkn.
          + assert (Hknotinl : ~ In k (map fst l)).
            { intros Hkin.
              rewrite in_map_iff in Hkin.
              destruct Hkin as [[k' v'] [Hfst' Hin']].
              cbn [fst] in Hfst'. subst k'.
              apply (pt_elements_spec n m k v' Hd) in Hin'.
              destruct Hin' as [Hget' _].
              rewrite Hgetmk in Hget'. discriminate. }
            rewrite get_fold_same.
            * apply pt_get_empty_h.
            * apply pt_elements_length_keys. exact Hd.
            * exact depth_none_n.
            * exact Hknotinl.
            * exact Hkn. }
      assert (gen : forall (l' : list (list positive * A)),
          NoDup (map fst l') ->
          (forall kv, In kv l' -> length (fst kv) = n) ->
          forall (mm : @pos_trie A) (r : R),
            depth mm n ->
            P mm r ->
            (forall k, In k (map fst l') -> pt_get mm k = None) ->
            P (fold_left (fun acc p => pt_put acc (fst p) (snd p)) l' mm)
              (fold_left g l' r)).
      { induction l' as [|[k v] tl IHl']; intros Hnd Hlens mm r Hdmm HP Hfresh.
        - exact HP.
        - cbn [fold_left fst snd].
          apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hndtl].
          assert (Hkn : length k = n) by (apply (Hlens (k,v)); left; exact eq_refl).
          assert (Hgetk : pt_get mm k = None) by (apply Hfresh; left; reflexivity).
          assert (Hdput : depth (pt_put mm k v) n)
            by (rewrite <- Hkn; apply pt_put_depth_h; rewrite Hkn; exact Hdmm).
          apply IHl'.
          + exact Hndtl.
          + intros kv Hkv. apply Hlens. right. exact Hkv.
          + exact Hdput.
          + unfold g at 1. cbn [fst snd].
            apply Hstep; [exact Hkn | exact Hdmm | exact Hgetk | exact HP].
          + intros k' Hk'in.
            assert (Hk'n : length k' = n).
            { rewrite in_map_iff in Hk'in.
              destruct Hk'in as [[k2 v2] [Hfst2 Hin2]].
              cbn [fst] in Hfst2. subst k2.
              apply (Hlens (k', v2)); right. exact Hin2. }
            assert (Hne : k' <> k) by (intro Heqk; subst k'; apply Hnotin; exact Hk'in).
            rewrite pt_get_put_diff_h.
            * apply Hfresh. right. exact Hk'in.
            * rewrite Hk'n, Hkn. reflexivity.
            * exact Hne.
            * rewrite Hkn. exact Hdmm. }
      rewrite <- Heq.
      apply gen.
      - apply pt_elements_nodup. exact Hd.
      - apply pt_elements_length_keys. exact Hd.
      - exact depth_none_n.
      - exact Hbase.
      - intros k _. apply pt_get_empty_h.
    Qed.

  End EAssembly.

End FoldSpec.

(* ============================================================================ *)
(* Part IV: discharged fold_spec wrapper                                        *)
(* ============================================================================ *)

Lemma pt_fold_spec' : forall {A} n (R:Type) (P : @pos_trie A -> R -> Prop)
                             (f : R -> list positive -> A -> R) r0,
    P None r0 ->
    (forall k v (m:@pos_trie A) r,
        length k = n -> depth m n -> pt_get m k = None -> P m r -> P (pt_put m k v) (f r k v)) ->
    forall m, depth m n -> P m (pt_fold f r0 m).
Proof.
  intros A.
  apply (@pt_fold_spec A (@pt_get_empty A) (@pt_get_put_same A) (@pt_get_put_diff A) (@pt_put_depth A)).
Qed.

