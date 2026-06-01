(* ============================================================================
   Depth-restricted fold_spec for pos_trie (the last db-trie law).
   Ladder: A non-emptiness, B extensionality, C elements+spec+nodup (DONE),
   D fold=fold_left over elements, E generic induction => fold_spec.

   Key design choice: pt_elements'_aux is defined as a fuel-based fixpoint
   pt_elements'_aux n t stack (fuel = depth), since a plain structural
   Fixpoint on pos_trie' does not pass Coq's termination checker (the
   recursive call in the node case descends through trie_elements, which
   is opaque).  All helper lemmas are proved by induction on the fuel n.

   Signature changes from PosTrieFoldSpec.v skeleton:
     - We define pt_elements_n n m instead of pt_elements m, taking an
       explicit depth n as a parameter.  Consequently:
     - pt_elements_spec has signature:
         forall n m k v, depth m n -> (In (k,v) (pt_elements_n n m) <->
                                        (pt_get m k = Some v /\ length k = n))
     - pt_elements_nodup has signature:
         forall n m, depth m n -> NoDup (map fst (pt_elements_n n m))
       Both added a leading  n : nat  and a  depth m n  hypothesis.

   Admitted lemmas (intentionally left for other sessions):
     pos_trie'_ext, pos_trie_ext, pt_fold_elements,
     pt_of_list_elements, pt_fold_spec.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List Lia.
Import ListNotations.
From Tries Require Import Canonical.
From Utils Require Import PosListMap TrieMapFold.

Set Implicit Arguments.

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

  (* ===== B. extensionality (depth-restricted) — ADMITTED =================== *)
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

  (* ===== D. fold = fold_left over elements — ADMITTED ===================== *)
  Lemma pt_fold_elements : forall n (R:Type) (f : R -> list positive -> A -> R) r0 (m:@pos_trie A),
      depth m n ->
      pt_fold f r0 m
      = fold_left (fun a p => f a (fst p) (snd p)) (pt_elements_n n m) r0.
  Proof.
  Admitted.

  (* ===== E. fold_spec — ADMITTED ========================================== *)
  Definition pt_of_list (l : list (list positive * A)) : @pos_trie A :=
    fold_right (fun p acc => pt_put acc (fst p) (snd p)) None l.

  Lemma pt_of_list_elements : forall n (m:@pos_trie A),
      depth m n -> pt_of_list (pt_elements_n n m) = m.
  Proof.
  Admitted.

  Lemma pt_fold_spec : forall n (R:Type) (P : @pos_trie A -> R -> Prop)
                              (f : R -> list positive -> A -> R) r0,
      P None r0 ->
      (forall k v (m:@pos_trie A) r,
          length k = n -> depth m n -> pt_get m k = None -> P m r ->
          P (pt_put m k v) (f r k v)) ->
      forall m, depth m n -> P m (pt_fold f r0 m).
  Proof.
  Admitted.

End FoldSpec.
