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

   ALL lemmas proven (Qed, 0 axioms).  pt_fold_spec is the depth-restricted
   fold_spec.  Phase E (pt_of_list_elements, pt_fold_spec) lives in inner
   Section EAssembly and is parameterized by the four depth-restricted get/put
   laws (pt_get_empty / pt_get_put_same / pt_get_put_diff / pt_put_depth, proven
   0-axiom in PosTrieDepthLaws.v + PosTrieRemoveLaws.v) as section hypotheses;
   after discharge pt_fold_spec carries them as explicit premises.  They get
   instantiated when this ladder is merged into src/Utils/PosListMap.v, where
   the real lemmas are in scope.

   NOTE: rocq_assumptions on the EAssembly-internal pt_of_list_ lemmas lists
   sibling opaque section-constants as "axioms" -- an interactive-session
   artifact (they are Qed, and pt_fold_spec itself is "Closed under the global
   context").
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
  Definition pt_of_list (l : list (list positive * A)) : @pos_trie A :=
    fold_right (fun p acc => pt_put acc (fst p) (snd p)) None l.

  Section EAssembly.
    (* These four hypotheses are proved 0-axiom in WIP/PosTrieDepthLaws.v
       (pt_get_put_same, pt_get_put_diff, pt_put_depth) and
       WIP/PosTrieRemoveLaws.v (pt_get_empty).  They will be discharged
       when everything is merged into src/Utils/PosListMap.v. *)
    Context (pt_get_empty_h : forall (k : list positive), @pt_get A None k = None).
    Context (pt_get_put_same_h : forall (k : list positive) (v : A) (m : @pos_trie A),
                depth m (length k) -> pt_get (pt_put m k v) k = Some v).
    Context (pt_get_put_diff_h : forall (k k' : list positive) (v : A) (m : @pos_trie A),
                length k = length k' -> k <> k' -> depth m (length k') ->
                pt_get (pt_put m k' v) k = pt_get m k).
    Context (pt_put_depth_h : forall (k : list positive) (v : A) (m : @pos_trie A),
                depth m (length k) -> depth (pt_put m k v) (length k)).

    (* Auxiliary: depth None n for any n *)
    Lemma depth_none : forall n, depth (@None (pos_trie' A)) n.
    Proof. intro n. destruct n; exact I. Qed.

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
    Lemma pt_of_list_depth : forall n (l : list (list positive * A)),
        (forall kv, In kv l -> length (fst kv) = n) ->
        depth (pt_of_list l) n.
    Proof.
      intros n l Hlen.
      induction l as [|[k v] tl IH].
      - cbn. apply depth_none.
      - cbn [pt_of_list fold_right fst snd].
        assert (Hkn : length k = n) by (apply (Hlen (k, v)); left; reflexivity).
        assert (IHd : depth (pt_of_list tl) n).
        { apply IH. intros kv Hin. apply Hlen. right. exact Hin. }
        rewrite <- Hkn.
        apply pt_put_depth_h.
        rewrite Hkn. exact IHd.
    Qed.

    (* Auxiliary: pt_get (pt_of_list l) k = Some v when (k,v) in l,
       given uniform key length n, NoDup, and length k = n *)
    Lemma pt_get_of_list_in : forall n (l : list (list positive * A)) k v,
        (forall kv, In kv l -> length (fst kv) = n) ->
        NoDup (map fst l) ->
        length k = n ->
        In (k, v) l ->
        pt_get (pt_of_list l) k = Some v.
    Proof.
      intros n l k v Hlen Hnd Hkn Hin.
      induction l as [|[k0 v0] tl IH].
      - inversion Hin.
      - cbn [pt_of_list fold_right fst snd].
        assert (Hk0n : length k0 = n) by (apply (Hlen (k0, v0)); left; reflexivity).
        assert (IHd : depth (pt_of_list tl) n).
        { apply pt_of_list_depth. intros kv Hkv. apply Hlen. right. exact Hkv. }
        inversion Hnd as [|? ? Hnotin Hndtl Heqx]. subst.
        destruct Hin as [Heq | Hin'].
        + (* k = k0, v = v0 *)
          injection Heq as Hkk Hvv. subst k0 v0.
          apply pt_get_put_same_h.
          rewrite Hkn. exact IHd.
        + (* k in tail *)
          assert (Hne : k <> k0).
          { intro Heq. subst k. apply Hnotin.
            apply in_map_iff. exists (k0, v). split; [reflexivity | exact Hin']. }
          rewrite pt_get_put_diff_h.
          * apply IH.
            -- intros kv Hkv. apply Hlen. right. exact Hkv.
            -- exact Hndtl.
            -- exact Hin'.
          * rewrite Hkn, Hk0n. reflexivity.
          * exact Hne.
          * rewrite Hk0n. exact IHd.
    Qed.

    (* Auxiliary: pt_get (pt_of_list l) k = None when k not in map fst l,
       given uniform key length n and length k = n *)
    Lemma pt_get_of_list_notin : forall n (l : list (list positive * A)) k,
        (forall kv, In kv l -> length (fst kv) = n) ->
        length k = n ->
        ~ In k (map fst l) ->
        pt_get (pt_of_list l) k = None.
    Proof.
      intros n l k Hlen Hkn Hnotin.
      induction l as [|[k0 v0] tl IH].
      - cbn. apply pt_get_empty_h.
      - cbn [pt_of_list fold_right fst snd].
        assert (Hk0n : length k0 = n) by (apply (Hlen (k0, v0)); left; reflexivity).
        assert (IHd : depth (pt_of_list tl) n).
        { apply pt_of_list_depth. intros kv Hkv. apply Hlen. right. exact Hkv. }
        assert (Hne : k <> k0).
        { intro Heq. apply Hnotin. left. symmetry. exact Heq. }
        rewrite pt_get_put_diff_h.
        + apply IH.
          * intros kv Hkv. apply Hlen. right. exact Hkv.
          * intros Hin. apply Hnotin. right. exact Hin.
        + rewrite Hkn, Hk0n. reflexivity.
        + exact Hne.
        + rewrite Hk0n. exact IHd.
    Qed.

    Lemma pt_of_list_elements : forall n (m : @pos_trie A),
        depth m n -> pt_of_list (pt_elements_n n m) = m.
    Proof.
      intros n m Hd.
      apply (pos_trie_ext (n:=n)).
      - apply pt_of_list_depth.
        apply pt_elements_length_keys. exact Hd.
      - exact Hd.
      - intros k Hkn.
        destruct (pt_get m k) eqn:Hget.
        + apply (pt_get_of_list_in (n:=n)).
          * apply pt_elements_length_keys. exact Hd.
          * apply pt_elements_nodup. exact Hd.
          * exact Hkn.
          * apply (pt_elements_spec n m k a Hd).
            split; [exact Hget | exact Hkn].
        + apply (pt_get_of_list_notin (n:=n)).
          * apply pt_elements_length_keys. exact Hd.
          * exact Hkn.
          * intros Hkin.
            rewrite in_map_iff in Hkin.
            destruct Hkin as [[k' v] [Hfst Hkvin]].
            cbn [fst] in Hfst. subst k'.
            apply (pt_elements_spec n m k v Hd) in Hkvin.
            destruct Hkvin as [Hget' _].
            rewrite Hget in Hget'. discriminate.
    Qed.

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
