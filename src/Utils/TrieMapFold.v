(* trie_map_ok : the coqutil map.ok instance for TrieMap.trie_map.

   Establishes fold_spec / fold_parametricity for trie_fold (the two laws the
   Aborted instance at TrieMap.v:374 was missing), plus the 6 basic laws,
   yielding `map.ok (trie_map value)`.  This is one half of the "trie-lawfulness"
   obligation that gates the positive instantiation of the e-graph soundness
   lemmas (the other half is pos_trie_map_ok).

   The fold is correct because trie_fold' reconstructs each binding's key as
   [pos_rev revnum] from the reversed path prefix [revnum], which matches the
   canonical PTree.get' descent (xO -> left, xI -> right) exactly. *)
Set Implicit Arguments.
From Stdlib Require Import ZArith Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Tries Require Import Canonical.
Import PTree.
From Utils Require Import Booleans Base Lists ExtraMaps Monad TrieMap.

Section Spec.
  Context {B : Type}.

  (* ---- glob: global key of local position q under path-prefix revnum ---- *)
  (* mirrors trie_fold' descent: xO -> left (xO revnum), xI -> right (xI revnum),
     value at xH -> key (pos_rev revnum). *)
  Fixpoint glob (revnum q : positive) : positive :=
    match q with
    | xH => pos_rev revnum
    | xO q => glob (xO revnum) q
    | xI q => glob (xI revnum) q
    end.

  (* ======================= PROVEN FOUNDATION ======================= *)

  Lemma pos_rev'_invol_gen : forall p acc, pos_rev' (pos_rev' p acc) xH = pos_rev' acc p.
  Proof. induction p; intros; simpl; try rewrite IHp; reflexivity. Qed.

  Lemma pos_rev_involutive : forall p, pos_rev (pos_rev p) = p.
  Proof. intro p; unfold pos_rev; rewrite pos_rev'_invol_gen; reflexivity. Qed.

  Lemma glob_closed : forall q revnum, glob revnum q = pos_rev (pos_rev' q revnum).
  Proof. induction q; intros; simpl; try rewrite IHq; reflexivity. Qed.

  Lemma glob_xH : forall q, glob xH q = q.
  Proof.
    intro q; rewrite glob_closed; unfold pos_rev; rewrite pos_rev'_invol_gen; reflexivity.
  Qed.

  Lemma pos_rev'_inj_r : forall acc a b, pos_rev' acc a = pos_rev' acc b -> a = b.
  Proof.
    induction acc; intros a b H; simpl in *;
      [ apply IHacc in H; congruence
      | apply IHacc in H; congruence
      | exact H ].
  Qed.

  Lemma glob_inj : forall q1 q2 revnum, glob revnum q1 = glob revnum q2 -> q1 = q2.
  Proof.
    intros q1 q2 revnum Hg. rewrite !glob_closed in Hg.
    assert (Hpr : pos_rev' q1 revnum = pos_rev' q2 revnum).
    { rewrite <- (pos_rev_involutive (pos_rev' q1 revnum)),
              <- (pos_rev_involutive (pos_rev' q2 revnum)), Hg; reflexivity. }
    assert (Hg2 : pos_rev' revnum q1 = pos_rev' revnum q2).
    { rewrite <- (pos_rev'_invol_gen q1 revnum), <- (pos_rev'_invol_gen q2 revnum), Hpr;
        reflexivity. }
    apply pos_rev'_inj_r in Hg2; exact Hg2.
  Qed.

  (* Disjointness corollary used for NoDup: a left-subtree key (prefix [xO revnum])
     can never equal a right-subtree key (prefix [xI revnum]) or the current key
     (prefix [revnum] at position xH).  Same Hgen/inj_r machinery. *)
  (* glob (xO revnum) q is DEFINITIONALLY glob revnum (xO q), so [change] exposes a
     common prefix and glob_inj + discriminate closes each disjointness goal. *)
  Lemma glob_prefix_OI : forall revnum q1 q2,
      glob (xO revnum) q1 = glob (xI revnum) q2 -> False.
  Proof.
    intros revnum q1 q2 Hg.
    change (glob revnum (xO q1) = glob revnum (xI q2)) in Hg.
    apply glob_inj in Hg. discriminate.
  Qed.

  (* current-node key (xH) vs any subtree key (prefix xO/xI) *)
  Lemma glob_prefix_H_O : forall revnum q,
      glob revnum xH = glob (xO revnum) q -> False.
  Proof.
    intros revnum q Hg.
    change (glob revnum xH = glob revnum (xO q)) in Hg.
    apply glob_inj in Hg. discriminate.
  Qed.

  Lemma glob_prefix_H_I : forall revnum q,
      glob revnum xH = glob (xI revnum) q -> False.
  Proof.
    intros revnum q Hg.
    change (glob revnum xH = glob revnum (xI q)) in Hg.
    apply glob_inj in Hg. discriminate.
  Qed.

  (* ======================= REMAINING LADDER (delegate) ======================= *)

  (* P1. elements list, mirroring trie_fold' order EXACTLY (current; right; left). *)
  Fixpoint trie_elements' (m : tree' B) (revnum : positive) : list (positive * B) :=
    match m with
    | Node001 r => trie_elements' r (xI revnum)
    | Node010 y => [(pos_rev revnum, y)]
    | Node011 y r => (pos_rev revnum, y) :: trie_elements' r (xI revnum)
    | Node100 l => trie_elements' l (xO revnum)
    | Node101 l r => trie_elements' r (xI revnum) ++ trie_elements' l (xO revnum)
    | Node110 l y => (pos_rev revnum, y) :: trie_elements' l (xO revnum)
    | Node111 l y r => (pos_rev revnum, y) :: (trie_elements' r (xI revnum) ++ trie_elements' l (xO revnum))
    end.

  Definition trie_elements (m : tree B) : list (positive * B) :=
    match m with Empty => [] | Nodes m' => trie_elements' m' xH end.

  (* P1-spec. structural induction on m', using glob at xO/xI revnum (clean, like glob_closed). *)
  Lemma trie_elements'_spec : forall m revnum k v,
      In (k,v) (trie_elements' m revnum) <->
      (exists q, get' q m = Some v /\ glob revnum q = k).
  Proof.
    induction m; intros revnum k v; simpl; split; intro H.
    - (* Node001 forward *)
      apply IHm in H. destruct H as [q [Hg Hk]]. exists (xI q). split; [exact Hg | exact Hk].
    - (* Node001 backward *)
      destruct H as [q [Hg Hk]]. destruct q; simpl in Hg; try discriminate.
      apply IHm. exists q. split; [exact Hg | exact Hk].
    - (* Node010 forward *)
      destruct H as [H | H]; [|contradiction].
      injection H; intros; subst. exists xH. split; [reflexivity | reflexivity].
    - (* Node010 backward *)
      destruct H as [q [Hg Hk]]. destruct q; simpl in Hg; try discriminate.
      injection Hg; intros; subst. left. simpl. reflexivity.
    - (* Node011 forward *)
      destruct H as [H | H].
      + injection H; intros; subst. exists xH. split; [reflexivity | reflexivity].
      + apply IHm in H. destruct H as [q [Hg Hk]]. exists (xI q). split; [exact Hg | exact Hk].
    - (* Node011 backward *)
      destruct H as [q [Hg Hk]]. destruct q; simpl in Hg; try discriminate.
      + right. apply IHm. exists q. split; [exact Hg | exact Hk].
      + injection Hg; intros; subst. left. simpl. reflexivity.
    - (* Node100 forward *)
      apply IHm in H. destruct H as [q [Hg Hk]]. exists (xO q). split; [exact Hg | exact Hk].
    - (* Node100 backward *)
      destruct H as [q [Hg Hk]]. destruct q; simpl in Hg; try discriminate.
      apply IHm. exists q. split; [exact Hg | exact Hk].
    - (* Node101 forward *)
      rewrite in_app_iff in H. destruct H as [H | H].
      + apply IHm2 in H. destruct H as [q [Hg Hk]]. exists (xI q). split; [exact Hg | exact Hk].
      + apply IHm1 in H. destruct H as [q [Hg Hk]]. exists (xO q). split; [exact Hg | exact Hk].
    - (* Node101 backward: xI->left(m2), xO->right(m1) *)
      destruct H as [q [Hg Hk]]. rewrite in_app_iff. destruct q; simpl in Hg; try discriminate.
      + left. apply IHm2. exists q. split; [exact Hg | exact Hk].
      + right. apply IHm1. exists q. split; [exact Hg | exact Hk].
    - (* Node110 forward *)
      destruct H as [H | H].
      + injection H; intros; subst. exists xH. split; [reflexivity | reflexivity].
      + apply IHm in H. destruct H as [q [Hg Hk]]. exists (xO q). split; [exact Hg | exact Hk].
    - (* Node110 backward *)
      destruct H as [q [Hg Hk]]. destruct q; simpl in Hg; try discriminate.
      + right. apply IHm. exists q. split; [exact Hg | exact Hk].
      + injection Hg; intros; subst. left. simpl. reflexivity.
    - (* Node111 forward *)
      destruct H as [H | H].
      + injection H; intros; subst. exists xH. split; [reflexivity | reflexivity].
      + rewrite in_app_iff in H. destruct H as [H | H].
        * apply IHm2 in H. destruct H as [q [Hg Hk]]. exists (xI q). split; [exact Hg | exact Hk].
        * apply IHm1 in H. destruct H as [q [Hg Hk]]. exists (xO q). split; [exact Hg | exact Hk].
    - (* Node111 backward *)
      destruct H as [q [Hg Hk]]. destruct q; simpl in Hg; try discriminate.
      + right. rewrite in_app_iff. left. apply IHm2. exists q. split; [exact Hg | exact Hk].
      + right. rewrite in_app_iff. right. apply IHm1. exists q. split; [exact Hg | exact Hk].
      + injection Hg; intros; subst. left. simpl. reflexivity.
  Qed.

  (* top-level tuples_spec via glob_xH (k = q at top). *)
  Lemma trie_tuples_spec : forall m k v,
      In (k,v) (trie_elements m) <-> get k m = Some v.
  Proof.
    intros m k v. destruct m as [|m'].
    - simpl. split; [contradiction | discriminate].
    - unfold trie_elements. rewrite trie_elements'_spec.
      split.
      + intros [q [Hg Hgk]]. rewrite glob_xH in Hgk. subst. simpl. exact Hg.
      + intros Hg. simpl in Hg. exists k. split; [exact Hg | apply glob_xH].
  Qed.

  (* P2. NoDup of keys.  induction on m'; the three sublists are pairwise key-disjoint
     by glob_prefix_OI / _H_O / _H_I and intra-list NoDup by IH; cross-membership uses
     trie_elements'_spec + glob_inj. *)
  Lemma trie_elements'_nodup : forall m revnum, NoDup (map fst (trie_elements' m revnum)).
  Proof.
    assert (key_shape : forall m' revnum k,
      In k (map fst (trie_elements' m' revnum)) ->
      exists q v, get' q m' = Some v /\ glob revnum q = k).
    { intros m' revnum k Hin.
      rewrite in_map_iff in Hin. destruct Hin as [[k' v] [Hfst Hin]].
      simpl in Hfst. subst k'.
      rewrite trie_elements'_spec in Hin.
      destruct Hin as [q [Hg Hk]].
      exists q, v. split; assumption. }
    induction m; intros revnum; simpl.
    - (* Node001 *) apply IHm.
    - (* Node010 *) apply NoDup_cons; [simpl; tauto | apply NoDup_nil].
    - (* Node011 *)
      apply NoDup_cons.
      + intros Hin. apply key_shape in Hin.
        destruct Hin as [q [v [_ Hk]]].
        exact (glob_prefix_H_I revnum q (eq_sym Hk)).
      + apply IHm.
    - (* Node100 *) apply IHm.
    - (* Node101 *)
      rewrite map_app. apply NoDup_app.
      + apply IHm2.
      + apply IHm1.
      + intros k Hin1 Hin2.
        apply key_shape in Hin1. destruct Hin1 as [q1 [v1 [_ Hk1]]].
        apply key_shape in Hin2. destruct Hin2 as [q2 [v2 [_ Hk2]]].
        subst k.
        exact (glob_prefix_OI revnum q2 q1 Hk2).
    - (* Node110 *)
      apply NoDup_cons.
      + intros Hin. apply key_shape in Hin.
        destruct Hin as [q [v [_ Hk]]].
        exact (glob_prefix_H_O revnum q (eq_sym Hk)).
      + apply IHm.
    - (* Node111 *)
      rewrite map_app. apply NoDup_cons.
      + rewrite in_app_iff. intros [Hin | Hin].
        * apply key_shape in Hin. destruct Hin as [q [v [_ Hk]]].
          exact (glob_prefix_H_I revnum q (eq_sym Hk)).
        * apply key_shape in Hin. destruct Hin as [q [v [_ Hk]]].
          exact (glob_prefix_H_O revnum q (eq_sym Hk)).
      + apply NoDup_app.
        * apply IHm2.
        * apply IHm1.
        * intros k Hin1 Hin2.
          apply key_shape in Hin1. destruct Hin1 as [q1 [v1 [_ Hk1]]].
          apply key_shape in Hin2. destruct Hin2 as [q2 [v2 [_ Hk2]]].
          subst k.
          exact (glob_prefix_OI revnum q2 q1 Hk2).
  Qed.

  Lemma trie_elements_nodup : forall m, NoDup (map fst (trie_elements m)).
  Proof.
    intros m. destruct m as [|m'].
    - simpl. apply NoDup_nil.
    - simpl. apply trie_elements'_nodup.
  Qed.

  (* P3. trie_fold = fold_left over the elements (structural induction; fold_left_app). *)
  Lemma trie_fold_elements : forall (A:Type) (f : A -> positive -> B -> A) (acc:A) (m : tree B),
      trie_fold f acc m
      = fold_left (fun a p => f a (fst p) (snd p)) (trie_elements m) acc.
  Proof.
    intros A f acc m.
    assert (helper : forall (m' : tree' B) revnum acc',
      trie_fold' f acc' m' revnum =
      fold_left (fun a p => f a (fst p) (snd p)) (trie_elements' m' revnum) acc').
    { induction m'; intros revnum acc'; simpl.
      - apply IHm'.
      - reflexivity.
      - apply IHm'.
      - apply IHm'.
      - rewrite fold_left_app. rewrite <- IHm'2. rewrite <- IHm'1. reflexivity.
      - apply IHm'.
      - rewrite fold_left_app. rewrite <- IHm'2. rewrite <- IHm'1. reflexivity. }
    destruct m as [|m'].
    - simpl. reflexivity.
    - simpl. apply helper.
  Qed.

  (* P4. GENERIC list -> fold_spec.  Map-agnostic; uses only the 6 basic laws + map_ext.
     of_list := fold_right put empty.  Needs: get_of_list_not_in, of_list_elements = m
     (via map_ext + trie_tuples_spec + NoDup), then a fold_left induction tracking the
     partial map of_list(processed-prefix) with the fresh-key property from NoDup. *)
  Lemma trie_fold_spec :
    forall (R:Type) (P : @map.rep _ _ (trie_map B) -> R -> Prop)
           (f : R -> positive -> B -> R) (r0 : R),
      P map.empty r0 ->
      (forall k v m r, map.get m k = None -> P m r -> P (map.put m k v) (f r k v)) ->
      forall m, P m (map.fold f r0 m).
  Proof.
    intros R P f r0 Hempty Hstep m.
    unfold map.fold. simpl. rewrite trie_fold_elements.
    set (g := fun (acc : tree B) p => set (fst p) (snd p) acc).
    set (elems := trie_elements m).
    assert (get_fold_notin : forall l mm k,
        ~In k (map fst l) ->
        get k (fold_left g l mm) = get k mm).
    { induction l as [|a l IHl]; intros mm k Hnotin; simpl.
      - reflexivity.
      - rewrite IHl by (intros H; apply Hnotin; right; exact H).
        unfold g. simpl. apply gso. intros Heq. apply Hnotin. left. symmetry. exact Heq. }
    assert (get_fold_in : forall l mm k v,
        NoDup (map fst l) ->
        In (k, v) l ->
        get k (fold_left g l mm) = Some v).
    { induction l as [|a l IHl]; intros mm k v Hnd Hin; simpl.
      - contradiction.
      - inversion Hnd as [|x xs Hnotin Hndl Heqx]. subst.
        destruct Hin as [Heq | Hin].
        + subst a. simpl.
          rewrite get_fold_notin by (simpl in Hnotin; exact Hnotin).
          unfold g. simpl. apply gss.
        + apply IHl; [exact Hndl | exact Hin]. }
    assert (Heq : fold_left g elems (empty B) = m).
    { apply extensionality. intros k.
      destruct (get k m) eqn:Hgetm.
      - apply get_fold_in.
        + apply trie_elements_nodup.
        + apply trie_tuples_spec. exact Hgetm.
      - rewrite get_fold_notin.
        + apply gempty.
        + intros Hkin.
          rewrite in_map_iff in Hkin. destruct Hkin as [[k' v] [Hfst Hin]].
          simpl in Hfst. subst k'.
          unfold elems in Hin. rewrite trie_tuples_spec in Hin. congruence. }
    assert (gen : forall l, NoDup (map fst l) ->
        forall mm r,
          P mm r ->
          (forall k, In k (map fst l) -> get k mm = None) ->
          P (fold_left g l mm) (fold_left (fun a p => f a (fst p) (snd p)) l r)).
    { induction l as [| a l IHl]; intros Hnd mm r HP Hfresh; simpl.
      - exact HP.
      - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hndl].
        apply IHl.
        + exact Hndl.
        + unfold g at 1. simpl. apply Hstep.
          * unfold map.get. simpl. apply Hfresh. simpl. left. reflexivity.
          * exact HP.
        + intros k Hink.
          unfold g at 1. simpl.
          destruct (Pos.eq_dec k (fst a)) as [Heqk | Hneq].
          { exfalso. apply Hnotin. rewrite <- Heqk. exact Hink. }
          { rewrite gso; [| exact Hneq].
            apply Hfresh. simpl. right. exact Hink. } }
    rewrite <- Heq.
    apply gen.
    - apply trie_elements_nodup.
    - exact Hempty.
    - intros k _. apply gempty.
  Qed.

  (* P5. fold_parametricity.  DIRECT structural induction on the tree threading the
     relation through the sequential sub-folds (do NOT go through elements). Generalize
     over revnum + both accumulators. *)
  Lemma trie_fold_parametricity :
    forall (A1 A2 : Type) (Rrel : A1 -> A2 -> Prop)
           (f1 : A1 -> positive -> B -> A1) (f2 : A2 -> positive -> B -> A2),
      (forall a1 a2 k v, Rrel a1 a2 -> Rrel (f1 a1 k v) (f2 a2 k v)) ->
      forall a1 a2, Rrel a1 a2 -> forall m, Rrel (trie_fold f1 a1 m) (trie_fold f2 a2 m).
  Proof.
    intros A1 A2 Rrel f1 f2 Hstep a1 a2 Hrel m.
    destruct m as [|m'].
    - simpl. exact Hrel.
    - simpl.
      assert (helper : forall (m'' : tree' B) revnum a1' a2',
          Rrel a1' a2' -> Rrel (trie_fold' f1 a1' m'' revnum) (trie_fold' f2 a2' m'' revnum)).
      { induction m''; intros revnum a1' a2' Hrel'; simpl.
        - apply IHm''. exact Hrel'.
        - apply Hstep. exact Hrel'.
        - apply IHm''. apply Hstep. exact Hrel'.
        - apply IHm''. exact Hrel'.
        - apply IHm''1. apply IHm''2. exact Hrel'.
        - apply IHm''. apply Hstep. exact Hrel'.
        - apply IHm''1. apply IHm''2. apply Hstep. exact Hrel'. }
      apply helper. exact Hrel.
  Qed.

End Spec.

#[export] Instance trie_map_ok (value : Type) : map.ok (trie_map value).
Proof.
  constructor.
  { intros m1 m2 H. apply extensionality. exact H. }
  { intros k. apply gempty. }
  { intros m k v. apply gss. }
  { intros m k v k' Hne. apply gso. exact Hne. }
  { intros m k. apply grs. }
  { intros m k k' Hne. apply gro. exact Hne. }
  { intros R P f r0 Hbase Hstep m. exact (@trie_fold_spec value R P f r0 Hbase Hstep m). }
  { intros A C Rrel fa fb Hpres a0 b0 Hr m.
    exact (@trie_fold_parametricity value A C Rrel fa fb Hpres a0 b0 Hr m). }
Qed.
