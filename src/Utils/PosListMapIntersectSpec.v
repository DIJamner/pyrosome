Require Import NArith Tries.Canonical Lists.List Sorting.Permutation.
Import ListNotations.

From Utils Require Import Utils Monad.
From Utils Require Import PosListMap.

#[local] Notation ne_list A := (A * list A)%type.

Section PtSpacedIntersectSpec.
  Context {A : Type}.
  Context `{WithDefault A}.
  Context (merge : A -> A -> A).
  (* [pt_spaced_intersect'] re-orders inputs while it partitions on each
     variable, so the per-key merge runs in a different order than the
     spec's [fold_left merge es e].  The two agree only when [merge] is
     commutative and associative. *)
  Context (merge_comm : forall a b, merge a b = merge b a).
  Context (merge_assoc : forall a b c, merge a (merge b c) = merge (merge a b) c).

  (* The combined bool pattern for the intersected trie is the pointwise
     OR ("union") of all the input patterns. *)
  Definition combined_bools (tries : ne_list (@pos_trie A * list bool)) : list bool :=
    List.fold_left (fun acc p => map2 orb (combine (snd p) acc))
                   (snd tries)
                   (snd (fst tries)).

  (* Look up [x] in a single (pos_trie, list bool) pair using [spaced_get],
     which expects the pair in the opposite order. *)
  Definition lookup_one (x : list positive) (p : @pos_trie A * list bool) : option A :=
    spaced_get x (snd p, fst p).

  (* Same as [lookup_one] but on the unwrapped trie ([pos_trie'] rather than [pos_trie]). *)
  Definition lookup_one' (x : list positive) (p : @pos_trie' A * list bool) : option A :=
    pt_get' (fst p) (map fst (filter snd (combine x (snd p)))).

  (* Specification of [pt_spaced_intersect]:
     For any key [x], looking up [x] in the intersected trie (using the
     combined bool pattern) yields:
       - [Some (merge_all e e1 ... en)] when the key is present in EVERY
         input trie with values [e, e1, ..., en], merged left-to-right
         using [merge];
       - [None] when the key is missing from at least one input trie. *)
  Definition pt_spaced_intersect_spec
    (tries : ne_list (@pos_trie A * list bool))
    (x : list positive) : Prop :=
    let all_tries := fst tries :: snd tries in
    let bools := combined_bools tries in
    let result := spaced_get x (bools, pt_spaced_intersect merge tries) in
    match list_Mmap (lookup_one x) all_tries with
    | Some (e :: es) => result = Some (List.fold_left merge es e)
    | Some []        => result = None  (* unreachable: list is non-empty *)
    | None           => result = None
    end.

  (* Well-formedness of one (trie, bool-list) pair w.r.t. lookup key [x]. *)
  Definition wf_input (x : list positive) (p : @pos_trie A * list bool) : Prop :=
    length (snd p) = length x /\
    match fst p with
    | Some pt' => Is_true (has_depth' (length (filter id (snd p))) pt')
    | None => True
    end.

  Definition wf_tries (x : list positive) (tries : ne_list (@pos_trie A * list bool)) : Prop :=
    wf_input x (fst tries) /\ Forall (wf_input x) (snd tries).

  (* ------------------------------------------------------------ *)
  (* Auxiliary lemma about the recursive helper [pt_spaced_intersect'].
     Given well-formed inputs as set up by [pt_spaced_intersect] (after
     stripping the [Some] wrappers and splitting the tail), the lookup of
     [x] in the resulting trie under the OR-combined bool pattern equals
     the merged fold of the per-trie lookups, or [None] if any input
     lookup misses. *)
  (* Helper: when all elements of [cil] are [], folding [map2 orb] starting
     from [[]] yields [[]]. *)
  Lemma fold_left_map2_orb_all_nil (cil : list (list bool)) :
    Forall (fun l => l = []) cil ->
    fold_left (fun acc (l : list bool) => map2 orb (combine l acc)) cil []
    = [].
  Proof.
    induction cil as [|c cil IH]; cbn; intros Hall; [reflexivity|].
    inversion Hall as [|? ? Hc Hall']; subst c.
    cbn. apply IH; assumption.
  Qed.

  (* Helper: every element of [ptl] is a leaf when its depth is 0. *)
  Lemma has_depth'_0_leaf (pt : @pos_trie' A) :
    Is_true (has_depth' 0 pt) -> exists a, pt = pos_trie_leaf a.
  Proof.
    destruct pt as [a|m]; cbn; intros Hd; [eauto|contradiction].
  Qed.

  (* Helper for [trie_fold'] folding [andb f]: false propagates. *)
  Lemma trie_fold'_andb_false {B : Type} (f : B -> bool)
    (m : Tries.Canonical.PTree.tree' B) (revnum : positive) :
    TrieMap.trie_fold' (fun res (_:positive) (v:B) => andb res (f v))
                       false m revnum = false.
  Proof.
    revert revnum.
    induction m as [m IH | a | a m IH | m IH | m1 IH1 m2 IH2 | m IH a | m1 IH1 a m2 IH2];
      intros revnum; cbn;
      rewrite ?Bool.andb_false_l;
      try (apply IH);
      try (rewrite IH2; apply IH1);
      reflexivity.
  Qed.

  (* Helper: starting accumulator factors out of [trie_fold'] with [andb]. *)
  Lemma trie_fold'_andb_factor {B : Type} (f : B -> bool)
    (m : Tries.Canonical.PTree.tree' B) (revnum : positive) (acc : bool) :
    TrieMap.trie_fold' (fun res (_:positive) (v:B) => andb res (f v))
                       acc m revnum
    = andb acc
       (TrieMap.trie_fold' (fun res (_:positive) (v:B) => andb res (f v))
                           true m revnum).
  Proof.
    revert revnum acc.
    induction m as [m IH | a | a m IH | m IH | m1 IH1 m2 IH2 | m IH a | m1 IH1 a m2 IH2];
      intros revnum acc; cbn.
    - rewrite (IH (xI revnum) acc). reflexivity.
    - reflexivity.
    - rewrite (IH (xI revnum) (acc && f a)).
      rewrite (IH (xI revnum) (f a)).
      rewrite Bool.andb_assoc. reflexivity.
    - rewrite (IH (xO revnum) acc). reflexivity.
    - rewrite (IH1 (xO revnum)
                   (TrieMap.trie_fold' _ acc m2 (xI revnum))).
      rewrite (IH1 (xO revnum)
                   (TrieMap.trie_fold' _ true m2 (xI revnum))).
      rewrite (IH2 (xI revnum) acc).
      rewrite Bool.andb_assoc. reflexivity.
    - rewrite (IH (xO revnum) (acc && f a)).
      rewrite (IH (xO revnum) (f a)).
      rewrite Bool.andb_assoc. reflexivity.
    - rewrite (IH1 (xO revnum)
                   (TrieMap.trie_fold' _ (acc && f a) m2 (xI revnum))).
      rewrite (IH1 (xO revnum)
                   (TrieMap.trie_fold' _ (f a) m2 (xI revnum))).
      rewrite (IH2 (xI revnum) (acc && f a)).
      rewrite (IH2 (xI revnum) (f a)).
      rewrite !Bool.andb_assoc. reflexivity.
  Qed.

  (* Helper: [trie_fold'] folding [andb f] gives the per-entry property. *)
  Lemma trie_fold'_andb_get_inv {B : Type} (f : B -> bool)
    (m : Tries.Canonical.PTree.tree' B) (revnum : positive) :
    Is_true (TrieMap.trie_fold' (fun res (_:positive) (v:B) => andb res (f v))
                                true m revnum) ->
    forall p v, Tries.Canonical.PTree.get' p m = Some v -> Is_true (f v).
  Proof.
    revert revnum.
    induction m as [m IH | a | a m IH | m IH | m1 IH1 m2 IH2 | m IH a | m1 IH1 a m2 IH2];
      intros revnum Hfold p v Hget; cbn in *.
    - (* Node001 *)
      destruct p as [p'|p'|]; cbn in Hget; try discriminate.
      eapply IH; eauto.
    - (* Node010 *)
      destruct p as [p'|p'|]; cbn in Hget; try discriminate.
      injection Hget as <-. exact Hfold.
    - (* Node011 *)
      destruct p as [p'|p'|]; cbn in Hget; try discriminate.
      + eapply IH; eauto.
        rewrite (trie_fold'_andb_factor f m (xI revnum) (f a)) in Hfold.
        apply Is_true_eq_true in Hfold.
        apply Bool.andb_true_iff in Hfold as [_ Hr].
        apply Is_true_eq_left. exact Hr.
      + injection Hget as <-.
        rewrite (trie_fold'_andb_factor f m (xI revnum) (f a)) in Hfold.
        apply Is_true_eq_true in Hfold.
        apply Bool.andb_true_iff in Hfold as [Hf _].
        apply Is_true_eq_left. exact Hf.
    - (* Node100 *)
      destruct p as [p'|p'|]; cbn in Hget; try discriminate.
      eapply IH; eauto.
    - (* Node101 *)
      rewrite (trie_fold'_andb_factor f m1 (xO revnum)
                 (TrieMap.trie_fold' _ true m2 (xI revnum))) in Hfold.
      apply Is_true_eq_true in Hfold.
      apply Bool.andb_true_iff in Hfold as [Hf1 Hf2].
      apply Is_true_eq_left in Hf1. apply Is_true_eq_left in Hf2.
      destruct p as [p'|p'|]; cbn in Hget; try discriminate.
      + (* xI: lookup in m2 *) eapply IH2; eauto.
      + (* xO: lookup in m1 *) eapply IH1; eauto.
    - (* Node110 *)
      rewrite (trie_fold'_andb_factor f m (xO revnum) (f a)) in Hfold.
      apply Is_true_eq_true in Hfold.
      apply Bool.andb_true_iff in Hfold as [Hfa Hfm].
      apply Is_true_eq_left in Hfa. apply Is_true_eq_left in Hfm.
      destruct p as [p'|p'|]; cbn in Hget; try discriminate.
      + eapply IH; eauto.
      + injection Hget as <-. exact Hfa.
    - (* Node111 *)
      rewrite (trie_fold'_andb_factor f m1 (xO revnum)
                 (TrieMap.trie_fold' _ (f a) m2 (xI revnum)))
        in Hfold.
      rewrite (trie_fold'_andb_factor f m2 (xI revnum) (f a))
        in Hfold.
      apply Is_true_eq_true in Hfold.
      apply Bool.andb_true_iff in Hfold as [Hfa Hfm1].
      apply Bool.andb_true_iff in Hfa as [Hfay Hfm2].
      apply Is_true_eq_left in Hfay.
      apply Is_true_eq_left in Hfm1. apply Is_true_eq_left in Hfm2.
      destruct p as [p'|p'|]; cbn in Hget; try discriminate.
      + (* xI: lookup in m2 *) eapply IH2; eauto.
      + (* xO: lookup in m1 *) eapply IH1; eauto.
      + injection Hget as <-. exact Hfay.
  Qed.

  (* Direct per-entry inversion for [has_depth' (S n) (pos_trie_node m)]. *)
  Lemma has_depth'_node_inv (n : nat) (m : Tries.Canonical.PTree.tree' (@pos_trie' A))
    (p : positive) (v : @pos_trie' A) :
    Is_true (has_depth' (S n) (pos_trie_node m)) ->
    Tries.Canonical.PTree.get' p m = Some v ->
    Is_true (has_depth' n v).
  Proof.
    intros Hd Hg.
    eapply (@trie_fold'_andb_get_inv (@pos_trie' A) (has_depth' n) m xH); eauto.
  Qed.

  (* Conversion: [Is_true (has_depth' n pt)] gives the per-entry depth property
     via the inductive proposition [depth']. *)
  Lemma has_depth'_to_depth' (n : nat) (pt : @pos_trie' A) :
    Is_true (has_depth' n pt) -> depth' pt n.
  Proof.
    revert pt.
    induction n; intros pt Hd.
    - destruct pt as [a|m]; cbn in Hd; [|contradiction].
      constructor.
    - destruct pt as [a|m]; cbn in Hd; [contradiction|].
      constructor. intros k v Hget.
      apply IHn.
      (* From [Hd : Is_true (map.forallb (fun _ => has_depth' n) (Nodes m))]
         derive per-entry. *)
      change (Is_true (TrieMap.trie_fold'
                         (fun res (_:positive) (w:@pos_trie' A) =>
                            res && has_depth' n w)
                         true m xH)) in Hd.
      eapply trie_fold'_andb_get_inv; eauto.
  Qed.

  (* Every [pos_trie'] of [has_depth' n] has at least one valid lookup. *)
  Lemma pos_trie'_lookup_exists (n : nat) (pt : @pos_trie' A) :
    Is_true (has_depth' n pt) ->
    exists k v, length k = n /\ pt_get' pt k = Some v.
  Proof.
    revert pt.
    induction n; intros pt Hd.
    - destruct pt as [a|m]; cbn in Hd; [|contradiction].
      exists [], a. split; reflexivity.
    - destruct pt as [a|m]; [cbn in Hd; contradiction|].
      pose proof (@Tries.Canonical.PTree.tree'_not_empty _ m) as [p Hp].
      destruct (Tries.Canonical.PTree.get' p m) as [pt'|] eqn:Hgp; [|congruence].
      assert (Hd' : Is_true (has_depth' n pt')).
      { apply has_depth'_to_depth' in Hd.
        inversion Hd as [|m' n' Hall Heq1 Heq2]; subst.
        (* We need to recover Is_true from depth'.  Just induct backward
           via a separate iff. *)
        clear Hd.
        revert Hall.
        clear -Hgp.
        intros Hall.
        specialize (Hall _ _ Hgp).
        clear -Hall.
        revert pt' Hall; induction n; intros pt' Hd; cbn.
        - inversion Hd; subst; cbn; trivial.
        - inversion Hd as [|m'' n'' Hall' Heq1 Heq2]; subst; cbn.
          (* depth' (node m'') (S n) means all entries of m'' have depth' n. *)
          (* We want Is_true (map.forallb (has_depth' n) (Nodes m'')). *)
          change (Is_true (TrieMap.trie_fold'
                             (fun res (_:positive) (v:@pos_trie' A) =>
                                res && has_depth' n v)
                             true m'' xH)).
          (* Plan: show the andb-fold returns true. *)
          generalize xH as revnum.
          revert Hall' IHn.
          generalize m'' as mm. clear.
          intros mm.
          induction mm as [mm IH | a | a mm IH | mm IH | mm1 IH1 mm2 IH2 | mm IH a | mm1 IF1 a mm2 IF2];
            intros Hall IHn revnum; cbn.
          + (* Node001 mm *)
            apply IH.
            * intros k v Hget. apply (Hall (xI k) v). cbn. exact Hget.
            * exact IHn.
          + (* Node010 a *)
            apply Is_true_eq_left.
            apply Is_true_eq_true.
            apply IHn. apply (Hall xH). reflexivity.
          + (* Node011 a mm *)
            assert (Hy : Is_true (has_depth' n a)).
            { apply IHn. apply (Hall xH). reflexivity. }
            apply Is_true_eq_true in Hy.
            rewrite Hy. cbn [andb].
            apply IH.
            * intros k v Hget. apply (Hall (xI k) v). cbn. exact Hget.
            * exact IHn.
          + (* Node100 mm *)
            apply IH.
            * intros k v Hget. apply (Hall (xO k) v). cbn. exact Hget.
            * exact IHn.
          + (* Node101 mm1 mm2 *)
            assert (Hr : Is_true (TrieMap.trie_fold'
                                    (fun (res : bool) (_ : positive) (v : pos_trie') =>
                                       res && has_depth' n v) true mm2 (xI revnum))).
            { apply IH2.
              - intros k v Hget. apply (Hall (xI k) v). cbn. exact Hget.
              - exact IHn. }
            rewrite (trie_fold'_andb_factor (has_depth' n) mm1 (xO revnum)
                       (TrieMap.trie_fold' _ true mm2 (xI revnum))).
            apply Is_true_eq_true in Hr. rewrite Hr. cbn [andb].
            apply IH1.
            * intros k v Hget. apply (Hall (xO k) v). cbn. exact Hget.
            * exact IHn.
          + (* Node110 mm a *)
            assert (Hy : Is_true (has_depth' n a)).
            { apply IHn. apply (Hall xH). reflexivity. }
            apply Is_true_eq_true in Hy. rewrite Hy. cbn [andb].
            apply IH.
            * intros k v Hget. apply (Hall (xO k) v). cbn. exact Hget.
            * exact IHn.
          + (* Node111 mm1 a mm2 *)
            assert (Hy : Is_true (has_depth' n a)).
            { apply IHn. apply (Hall xH). reflexivity. }
            apply Is_true_eq_true in Hy.
            assert (Hr : Is_true (TrieMap.trie_fold'
                                    (fun (res : bool) (_ : positive) (v : pos_trie') =>
                                       res && has_depth' n v) true mm2 (xI revnum))).
            { apply IF2.
              - intros k v Hget. apply (Hall (xI k) v). cbn. exact Hget.
              - exact IHn. }
            rewrite Hy. cbn [andb].
            rewrite (trie_fold'_andb_factor (has_depth' n) mm1 (xO revnum)
                       (TrieMap.trie_fold' _ true mm2 (xI revnum))).
            apply Is_true_eq_true in Hr. rewrite Hr. cbn [andb].
            apply IF1.
            * intros k v Hget. apply (Hall (xO k) v). cbn. exact Hget.
            * exact IHn. }
      destruct (IHn pt' Hd') as [k' [v [Hk'_len Hgk']]].
      exists (p :: k'), v. split.
      + cbn. f_equal. exact Hk'_len.
      + cbn. rewrite Hgp. exact Hgk'.
  Qed.

  (* Pos_trie' extensionality at fixed depth: two tries of the same depth with
     identical lookups for keys of that length are equal. *)
  Lemma pos_trie'_ext_at_depth (n : nat) (pt1 pt2 : @pos_trie' A) :
    Is_true (has_depth' n pt1) ->
    Is_true (has_depth' n pt2) ->
    (forall k, length k = n -> pt_get' pt1 k = pt_get' pt2 k) ->
    pt1 = pt2.
  Proof.
    revert pt1 pt2.
    induction n; intros pt1 pt2 Hd1 Hd2 Hk.
    - apply has_depth'_0_leaf in Hd1 as [a1 ->].
      apply has_depth'_0_leaf in Hd2 as [a2 ->].
      specialize (Hk [] eq_refl). cbn in Hk. injection Hk as <-. reflexivity.
    - destruct pt1 as [a1|m1]; [cbn in Hd1; contradiction|].
      destruct pt2 as [a2|m2]; [cbn in Hd2; contradiction|].
      f_equal.
      assert (Hgeq : forall p, Tries.Canonical.PTree.get' p m1
                               = Tries.Canonical.PTree.get' p m2).
      { intro p.
        destruct (Tries.Canonical.PTree.get' p m1) as [pt1'|] eqn:Hg1;
          destruct (Tries.Canonical.PTree.get' p m2) as [pt2'|] eqn:Hg2.
        - f_equal.
          assert (Hd1' : Is_true (has_depth' n pt1')).
          { apply (@has_depth'_node_inv n m1 p pt1' Hd1 Hg1). }
          assert (Hd2' : Is_true (has_depth' n pt2')).
          { apply (@has_depth'_node_inv n m2 p pt2' Hd2 Hg2). }
          apply IHn; auto.
          intros k' Hk'_len.
          specialize (Hk (p :: k') (f_equal S Hk'_len)).
          cbn in Hk. rewrite Hg1, Hg2 in Hk. exact Hk.
        - exfalso.
          assert (Hd1' : Is_true (has_depth' n pt1')).
          { apply (@has_depth'_node_inv n m1 p pt1' Hd1 Hg1). }
          destruct (pos_trie'_lookup_exists _ _ Hd1') as [k' [v [Hlen' Hk']]].
          specialize (Hk (p :: k') (f_equal S Hlen')).
          cbn in Hk. rewrite Hg1, Hg2, Hk' in Hk. discriminate.
        - exfalso.
          assert (Hd2' : Is_true (has_depth' n pt2')).
          { apply (@has_depth'_node_inv n m2 p pt2' Hd2 Hg2). }
          destruct (pos_trie'_lookup_exists _ _ Hd2') as [k' [v [Hlen' Hk']]].
          specialize (Hk (p :: k') (f_equal S Hlen')).
          cbn in Hk. rewrite Hg1, Hg2, Hk' in Hk. discriminate.
        - reflexivity. }
      (* Use PTree.extensionality on Nodes m1 vs Nodes m2. *)
      assert (Hnodes : Tries.Canonical.PTree.Nodes m1 = Tries.Canonical.PTree.Nodes m2).
      { apply Tries.Canonical.PTree.extensionality.
        intro i. cbn. apply Hgeq. }
      injection Hnodes as Hnodes. exact Hnodes.
  Qed.

  (* Helper: list_Mmap of lookup_one' on length-0 keys gives the leaves. *)
  Lemma list_Mmap_lookup_one'_nil
    (ptl : list (@pos_trie' A)) (cil : list (list bool)) :
    length cil = length ptl ->
    Forall (fun l => l = []) cil ->
    Forall (fun pt => Is_true (has_depth' 0 pt)) ptl ->
    list_Mmap (lookup_one' []) (combine ptl cil)
    = Some (map get_leaf_unchecked ptl).
  Proof.
    revert cil; induction ptl as [|pt ptl IH]; intros [|ci cil] Hlen Hcil Hptl;
      cbn in *; try discriminate; try reflexivity.
    inversion Hcil as [|? ? Hc Hcil']; subst ci.
    inversion Hptl as [|? ? Hpt Hptl']; subst.
    apply has_depth'_0_leaf in Hpt.
    destruct Hpt as [a Heqa]; subst pt; cbn.
    unfold lookup_one'; cbn.
    rewrite IH by (auto || Lia.lia).
    reflexivity.
  Qed.

  (* Helper: list_Mmap distributes over [++] when the [Mret/None] is option. *)
  Lemma list_Mmap_app {T1 T2} (f : T1 -> option T2) (l1 l2 : list T1) :
    list_Mmap f (l1 ++ l2) =
      match list_Mmap f l1, list_Mmap f l2 with
      | Some xs1, Some xs2 => Some (xs1 ++ xs2)
      | _, _ => None
      end.
  Proof.
    induction l1 as [|a l1 IH]; cbn.
    - destruct (list_Mmap f l2); reflexivity.
    - destruct (f a) as [b|]; cbn; [|reflexivity].
      rewrite IH.
      destruct (list_Mmap f l1) as [xs1|];
        destruct (list_Mmap f l2) as [xs2|]; reflexivity.
  Qed.

  (* Helper: when the bool in [ci] is [false] at the head, the corresponding
     position [p] in [x] is dropped from the lookup key by [filter snd]. *)
  Lemma lookup_one'_cons_false (x : list positive) (p : positive)
    (pt : @pos_trie' A) (c : list bool) :
    lookup_one' (p :: x) (pt, false :: c) = lookup_one' x (pt, c).
  Proof.
    unfold lookup_one'; cbn [combine fst snd filter map].
    reflexivity.
  Qed.

  (* Helper: [spaced_get] with a [false] head bit drops the corresponding
     position from the lookup key. *)
  Lemma spaced_get_cons_false (x : list positive) (p : positive)
    (bools : list bool) (trie : @pos_trie A) :
    spaced_get (p :: x) (false :: bools, trie) = spaced_get x (bools, trie).
  Proof.
    unfold spaced_get; cbn [fst snd combine filter map]. reflexivity.
  Qed.

  (* Helper: when [hd false c = false], [lookup_one' (p :: x) (pt, c)]
     drops [p] and recurses on [tl c].  Covers both [c = []] and [c = false :: _]. *)
  Lemma lookup_one'_cons_hd_false (x : list positive) (p : positive)
    (pt : @pos_trie' A) (c : list bool) :
    hd false c = false ->
    lookup_one' (p :: x) (pt, c) = lookup_one' x (pt, tl c).
  Proof.
    destruct c as [|h c_tl]; intros Hhd.
    - unfold lookup_one'; cbn [snd tl].
      rewrite combine_nil. cbn [filter map].
      destruct x; cbn [combine filter map]; reflexivity.
    - cbn [hd] in Hhd. subst h. apply lookup_one'_cons_false.
  Qed.

  (* Helper: when the bool head is [true], the lookup descends one level
     into [pt] at position [p] before continuing on [x]. *)
  Lemma lookup_one'_cons_true (x : list positive) (p : positive)
    (m : PTree.tree' (@pos_trie' A)) (c : list bool) :
    lookup_one' (p :: x) (pos_trie_node m, true :: c)
    = match PTree.get' p m with
      | Some pt' => lookup_one' x (pt', c)
      | None => None
      end.
  Proof.
    unfold lookup_one'; cbn [combine fst snd filter map pt_get'].
    destruct (PTree.get' p m); reflexivity.
  Qed.

  (* Helper: convert standard [Forall2] to Pyrosome's [all2]. *)
  Lemma Forall2_to_all2 {T1 T2} (R : T1 -> T2 -> Prop)
    (l1 : list T1) (l2 : list T2) :
    Forall2 R l1 l2 -> all2 R l1 l2.
  Proof.
    induction 1; cbn; auto.
  Qed.

  (* Helper: combine [Forall length = n] and [Forall2 (has_depth' …)] into
     [rectangular_trie_list n] (the precondition required by
     [partition_tries_app] and [partition_tries_spec] in PosListMap.v). *)
  Lemma rectangular_trie_list_of_Forall2 (n : nat)
    (cil : list (list bool)) (ptl : list (@pos_trie' A)) :
    Forall (fun l => length l = n) cil ->
    Forall2 (fun c t => Is_true (has_depth' (length (filter id c)) t)) cil ptl ->
    rectangular_trie_list n cil ptl.
  Proof.
    intros Hlen Hd2.
    revert Hlen.
    induction Hd2 as [|c t cil' ptl' Hct Htail IH]; intros Hlen; cbn; auto.
    pose proof (Forall_inv Hlen) as Hlen_c.
    pose proof (Forall_inv_tail Hlen) as Hlen_tail.
    split; [split; assumption|].
    apply IH; assumption.
  Qed.

  (* Helper: if both head-true and head-false filters of a combine are
     empty *and* every cil entry is non-empty (forced when the section's
     [length = S _] hypothesis holds), then the input lists are empty. *)
  Lemma filter_both_empty_combine_nil
    (cil : list (list bool)) (ptl : list (@pos_trie' A)) (n : nat) :
    Forall (fun l => length l = S n) cil ->
    length cil = length ptl ->
    filter (fun p => hd false (fst p)) (combine cil ptl) = [] ->
    filter (fun p => negb (hd false (fst p))) (combine cil ptl) = [] ->
    cil = [].
  Proof.
    intros Hlen Hlen_p HfT HfF.
    destruct cil as [|c cil_rest]; [reflexivity|].
    destruct ptl as [|pt ptl_rest]; [cbn in Hlen_p; discriminate|].
    cbn in HfT, HfF.
    pose proof (Forall_inv Hlen) as Hc_len.
    destruct c as [|b r]; cbn in Hc_len; [discriminate|].
    destruct b; cbn in HfT, HfF; discriminate.
  Qed.

  (* Helper: when [filter f l] is empty, [filter (negb ∘ f) l = l]. *)
  Lemma filter_complement_nil_id {T} (f : T -> bool) (l : list T) :
    filter f l = [] ->
    filter (fun x => negb (f x)) l = l.
  Proof.
    induction l as [|a l IH]; cbn; auto.
    destruct (f a) eqn:Hfa; cbn; intro Heq; [discriminate|].
    f_equal. apply IH; assumption.
  Qed.

  (* Helper: [combine] of a list-of-pairs split is the list itself when
     the components have equal length. *)
  Lemma combine_split_id {T1 T2} (l : list (T1 * T2)) :
    combine (map fst l) (map snd l) = l.
  Proof.
    induction l as [|[a b] l IH]; cbn; auto. f_equal; assumption.
  Qed.

  (* Helper: [map fst (combine A B) = A] and [map snd (combine A B) = B]
     when [A] and [B] have equal length. *)
  Lemma map_fst_combine {T1 T2} (la : list T1) (lb : list T2) :
    length la = length lb -> map fst (combine la lb) = la.
  Proof.
    revert lb; induction la as [|a la IH]; intros [|b lb] Hlen; cbn in *;
      try discriminate; try reflexivity.
    f_equal. apply IH; Lia.lia.
  Qed.

  Lemma map_snd_combine {T1 T2} (la : list T1) (lb : list T2) :
    length la = length lb -> map snd (combine la lb) = lb.
  Proof.
    revert lb; induction la as [|a la IH]; intros [|b lb] Hlen; cbn in *;
      try discriminate; try reflexivity.
    f_equal. apply IH; Lia.lia.
  Qed.

  (* Helper: [combine (map snd L) (map fst L)] swaps each pair. *)
  Lemma combine_swap_proj {T1 T2} (L : list (T1 * T2)) :
    combine (map snd L) (map fst L) = map (fun p => (snd p, fst p)) L.
  Proof.
    induction L as [|[a b] L IH]; cbn; auto. f_equal; assumption.
  Qed.

  (* Helper: [map (fun p => (snd p, fst p)) (combine A B)] = [combine B A]
     when [A] and [B] have the same length. *)
  Lemma map_swap_combine {T1 T2} (la : list T1) (lb : list T2) :
    length la = length lb ->
    map (fun p => (snd p, fst p)) (combine la lb) = combine lb la.
  Proof.
    revert lb; induction la as [|a la IH]; intros [|b lb] Hlen; cbn in *;
      try discriminate; try reflexivity.
    f_equal. apply IH; Lia.lia.
  Qed.

  (* Helper: [map (fun p => (tl (fst p), snd p)) (combine A B) = combine (map tl A) B]
     when [A] and [B] have the same length. *)
  Lemma map_tl_fst_combine {T} (la : list (list bool)) (lb : list T) :
    length la = length lb ->
    map (fun p => (tl (fst p), snd p)) (combine la lb)
    = combine (map (@tl _) la) lb.
  Proof.
    revert lb; induction la as [|a la IH]; intros [|b lb] Hlen; cbn in *;
      try discriminate; try reflexivity.
    f_equal. apply IH; Lia.lia.
  Qed.

  (* Helper: in the all-heads-false case, [fold_left (map2 orb (combine ...))]
     leaves the [acc]'s head untouched and recurses on the tails. *)
  Lemma fold_orb_combine_all_false_head
    (L : list (list bool)) (b : bool) (t : list bool) :
    Forall (fun l => length l = S (length t) /\ hd false l = false) L ->
    fold_left (fun acc (l : list bool) => map2 orb (combine l acc)) L (b :: t)
    = b :: fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                     (map (@tl _) L) t.
  Proof.
    revert b t; induction L as [|l L IH]; intros b t Hall; cbn; [reflexivity|].
    pose proof (Forall_inv Hall) as [Hl_len Hl_hd].
    pose proof (Forall_inv_tail Hall) as Hall'.
    destruct l as [|h l_tl]; cbn [length] in Hl_len; [discriminate|].
    cbn [hd] in Hl_hd. subst h.
    injection Hl_len as Hl_tl_len.
    change (combine (false :: l_tl) (b :: t)) with ((false, b) :: combine l_tl t).
    change (map2 orb ((false, b) :: combine l_tl t))
      with (b :: map2 orb (combine l_tl t)).
    rewrite IH.
    2: { eapply Forall_impl; [|exact Hall'].
         intros l' [Hl'_len Hl'_hd]; split; [|exact Hl'_hd].
         (* length (map2 orb (combine l_tl t)) = length t *)
         unfold map2.
         rewrite length_map, length_combine, Hl_tl_len, PeanoNat.Nat.min_id.
         exact Hl'_len. }
    cbn [tl]. reflexivity.
  Qed.

  (* Permutation invariance of [fold_left merge] under comm/assoc. *)
  Lemma fold_left_merge_Permutation (l1 l2 : list A) :
    Permutation l1 l2 ->
    forall a, fold_left merge l1 a = fold_left merge l2 a.
  Proof.
    intros Hperm. induction Hperm; intros a; cbn; auto.
    - (* swap case *)
      f_equal.
      rewrite <- merge_assoc, (merge_comm y x), merge_assoc. reflexivity.
    - etransitivity; eauto.
  Qed.

  (* Pointwise-OR over equal-length boolean lists is comm/assoc, so the
     bool-fold over a list of equal-length lists is permutation-invariant. *)
  Lemma map2_orb_comm (a b : list bool) :
    map2 orb (combine a b) = map2 orb (combine b a).
  Proof.
    revert b; induction a as [|x a IH]; intros [|y b]; cbn; auto.
    f_equal; [apply Bool.orb_comm | apply IH].
  Qed.

  Lemma map2_orb_assoc (a b c : list bool) :
    length a = length b -> length b = length c ->
    map2 orb (combine (map2 orb (combine a b)) c)
    = map2 orb (combine a (map2 orb (combine b c))).
  Proof.
    revert b c; induction a as [|x a IH]; intros [|y b] [|z c] Hab Hbc;
      cbn in *; try discriminate; try reflexivity.
    f_equal.
    - symmetry; apply Bool.orb_assoc.
    - apply IH; Lia.lia.
  Qed.

  Lemma fold_left_orb_combine_Permutation
    (cil1 cil2 : list (list bool)) (acc : list bool) :
    Forall (fun l => length l = length acc) cil1 ->
    Permutation cil1 cil2 ->
    fold_left (fun a l => map2 orb (combine l a)) cil1 acc
    = fold_left (fun a l => map2 orb (combine l a)) cil2 acc.
  Proof.
    intros Hlen Hperm.
    revert acc Hlen.
    induction Hperm; intros acc Hlen; cbn; auto.
    - apply IHHperm.
      pose proof (Forall_inv Hlen) as Hlen_x.
      pose proof (Forall_inv_tail Hlen) as Hlen_tail.
      eapply Forall_impl; [|exact Hlen_tail].
      intros lz Hlz.
      rewrite Hlz.
      symmetry.
      clear -Hlen_x.
      revert acc Hlen_x.
      induction x as [|b x IH]; intros [|c acc] Hlen; cbn in *;
        try discriminate; try reflexivity.
      f_equal. apply IH; Lia.lia.
    - (* swap case *)
      pose proof (Forall_inv Hlen) as Hlen_y.
      pose proof (Forall_inv_tail Hlen) as Hlen_tail.
      pose proof (Forall_inv Hlen_tail) as Hlen_x.
      f_equal.
      assert (Hxy : length x = length y) by congruence.
      rewrite <- (map2_orb_assoc x y acc) by congruence.
      rewrite <- (map2_orb_assoc y x acc) by congruence.
      rewrite (map2_orb_comm x y).
      reflexivity.
    - etransitivity.
      + apply IHHperm1; assumption.
      + apply IHHperm2.
        eapply Permutation_Forall; eassumption.
  Qed.

  (* Permutation invariance for [fold_left merge] including the accumulator
     element.  Treats [acc :: l] as a single multiset over which merge is
     commutative/associative. *)
  Lemma fold_left_merge_perm_full (l1 l2 : list A) (e1 e2 : A) :
    Permutation (e1 :: l1) (e2 :: l2) ->
    fold_left merge l1 e1 = fold_left merge l2 e2.
  Proof.
    remember (e1 :: l1) as L1 eqn:HEq1.
    remember (e2 :: l2) as L2 eqn:HEq2.
    intros HP. revert e1 l1 e2 l2 HEq1 HEq2.
    induction HP; intros e1' l1' e2' l2' HEq1 HEq2; try discriminate.
    - injection HEq1 as <- <-. injection HEq2 as <- <-.
      apply fold_left_merge_Permutation; eauto.
    - injection HEq1 as <- <-. injection HEq2 as <- <-.
      cbn. f_equal. apply merge_comm.
    - subst l. subst l''.
      destruct l' as [|m_e m_l].
      + apply Permutation_sym in HP1.
        apply Permutation_nil_cons in HP1; contradiction.
      + transitivity (fold_left merge m_l m_e).
        * apply IHHP1; reflexivity.
        * apply IHHP2; reflexivity.
  Qed.

  (* Permutation invariance for [fold_left (fun acc l => map2 orb (combine l acc))]
     including the accumulator element.  Same treatment as above for OR over
     equal-length boolean lists. *)
  Lemma fold_left_orb_combine_perm_full
    (l1 l2 : list (list bool)) (acc1 acc2 : list bool) :
    Forall (fun l => length l = length acc1) (acc1 :: l1) ->
    Permutation (acc1 :: l1) (acc2 :: l2) ->
    fold_left (fun a l => map2 orb (combine l a)) l1 acc1
    = fold_left (fun a l => map2 orb (combine l a)) l2 acc2.
  Proof.
    intros Hlen HP.
    remember (acc1 :: l1) as L1 eqn:HEq1.
    remember (acc2 :: l2) as L2 eqn:HEq2.
    revert acc1 l1 acc2 l2 Hlen HEq1 HEq2.
    induction HP; intros acc1' l1' acc2' l2' Hlen HEq1 HEq2; try discriminate.
    - injection HEq1 as <- <-. injection HEq2 as <- <-.
      apply fold_left_orb_combine_Permutation; auto.
      apply Forall_inv_tail in Hlen; assumption.
    - injection HEq1 as <- <-. injection HEq2 as <- <-.
      pose proof (Forall_inv Hlen) as Ha1.
      pose proof (Forall_inv_tail Hlen) as Ha1tail.
      pose proof (Forall_inv Ha1tail) as Ha2.
      cbn. f_equal. apply map2_orb_comm.
    - subst l. subst l''.
      destruct l' as [|m_e m_l].
      + apply Permutation_sym in HP1.
        apply Permutation_nil_cons in HP1; contradiction.
      + assert (Hlen_mid : Forall (fun l => length l = length acc1') (m_e :: m_l)).
        { eapply Permutation_Forall; [exact HP1|]. exact Hlen. }
        transitivity (fold_left (fun a l => map2 orb (combine l a)) m_l m_e).
        * apply IHHP1; auto.
        * apply IHHP2; auto.
          (* Need Forall on (m_e :: m_l) with length = length m_e *)
          pose proof (Forall_inv Hlen_mid) as Hme_len.
          eapply Forall_impl; [|exact Hlen_mid].
          cbn; intros lz Hlz; congruence.
  Qed.

  (* Permutation invariance for [list_Mmap]: the result options carry
     permutation information. *)
  Lemma list_Mmap_Permutation_resp
    {T1 T2} (f : T1 -> option T2) (l1 l2 : list T1) :
    Permutation l1 l2 ->
    match list_Mmap f l1, list_Mmap f l2 with
    | Some r1, Some r2 => Permutation r1 r2
    | None, None => True
    | _, _ => False
    end.
  Proof.
    intros HP.
    induction HP; cbn.
    - constructor.
    - destruct (f x) as [v|]; cbn; [|trivial].
      destruct (list_Mmap f l) as [r1|], (list_Mmap f l') as [r2|];
        cbn in *; try contradiction; try trivial.
      apply perm_skip; assumption.
    - destruct (f x) as [vx|], (f y) as [vy|]; cbn; try trivial.
      destruct (list_Mmap f l) as [r|]; cbn; try trivial.
      apply perm_swap.
    - destruct (list_Mmap f l) as [r|],
               (list_Mmap f l') as [r'|],
               (list_Mmap f l'') as [r''|]; cbn in *;
        try contradiction; try trivial.
      etransitivity; eassumption.
  Qed.

  (* Combined helper: pulls a permutation through both [list_Mmap] and the
     [fold_left merge] that follows. *)
  Lemma list_Mmap_lookup_fold_perm
    {T1} (f : T1 -> option A) (e1 e2 : T1) (l1 l2 : list T1) :
    Permutation (e1 :: l1) (e2 :: l2) ->
    match f e1, list_Mmap f l1 with
    | Some v, Some vs => Some (fold_left merge vs v)
    | _, _ => None
    end
    = match f e2, list_Mmap f l2 with
      | Some v, Some vs => Some (fold_left merge vs v)
      | _, _ => None
      end.
  Proof.
    intros HP.
    pose proof (list_Mmap_Permutation_resp f _ _ HP) as HMM.
    cbn in HMM.
    destruct (f e1) as [v1|] eqn:Hf1;
      destruct (list_Mmap f l1) as [vs1|] eqn:HM1;
      destruct (f e2) as [v2|] eqn:Hf2;
      destruct (list_Mmap f l2) as [vs2|] eqn:HM2;
      cbn in HMM;
      try contradiction;
      try reflexivity.
    f_equal. apply fold_left_merge_perm_full. assumption.
  Qed.

  (* Combine over [(la1 ++ la2)] / [(lb1 ++ lb2)] when the prefix lengths agree. *)
  Lemma combine_app_eq T1 T2
    (la1 la2 : list T1) (lb1 lb2 : list T2) :
    length la1 = length lb1 ->
    combine (la1 ++ la2) (lb1 ++ lb2) = combine la1 lb1 ++ combine la2 lb2.
  Proof.
    revert lb1; induction la1 as [|a la1 IH]; intros [|b lb1] Hlen;
      cbn in *; try discriminate; try reflexivity.
    f_equal; apply IH; Lia.lia.
  Qed.

  (* Joint reversal of [cil']/[ptl'] preserves [pt_spaced_intersect'].
     This is the special case of [pt_spaced_intersect'_perm] (PosListMap.v
     line 2849, aborted) needed to discharge [list_intersect_correct]'s
     [elts_intersect_rev] section premise.  Admitted: follows from the
     same blocking lemma as [list_intersect_Perm_combined]
     (PosListMap.v line 2453, also Admitted). *)
  Lemma pt_spaced_intersect'_sim_rev
    (fuel : nat)
    (cil : list (list bool)) (ptl : list (@pos_trie' A))
    (ci0 : list bool) (cil' : list (list bool))
    (pt0 : @pos_trie' A) (ptl' : list (@pos_trie' A)) :
    pt_spaced_intersect' merge fuel cil ptl ci0 (rev cil') pt0 (rev ptl')
    = pt_spaced_intersect' merge fuel cil ptl ci0 cil' pt0 ptl'.
  Admitted.

  (* Specialised [list_intersect_correct] for our [lam].  The joint-reversal
     property of [pt_spaced_intersect'] (the same fact stated globally as the
     admitted [pt_spaced_intersect'_sim_rev]) is taken here as an explicit
     hypothesis [Hsim_rev], so the proof body of this lemma is independent of
     the admit.  Callers discharge [Hsim_rev] at instantiation. *)
  Lemma list_intersect_lookup_at_pos
    (fuel' : nat) (other_cil : list (list bool))
    (other_tries : list (@pos_trie' A)) (t_ci0 : list bool)
    (true_cil : list (list bool)) (t_pt0 : @pos_trie' A)
    (true_tries : list (@pos_trie' A)) (p : positive)
    (Hsim_rev : forall cil' pt0 ptl',
       pt_spaced_intersect' merge fuel' other_cil other_tries t_ci0
                            (rev cil') pt0 (rev ptl')
       = pt_spaced_intersect' merge fuel' other_cil other_tries t_ci0
                              cil' pt0 ptl') :
    Tries.Canonical.PTree.get p
      (TrieMap.otree (TrieMap.list_intersect
         (fun is_forward : bool =>
           pt_spaced_intersect' merge fuel' other_cil other_tries t_ci0
             (if is_forward then true_cil else rev true_cil))
         (proj_node_map_unchecked t_pt0)
         (map proj_node_map_unchecked true_tries)))
    = match Tries.Canonical.PTree.get' p (proj_node_map_unchecked t_pt0),
            list_Mmap (Tries.Canonical.PTree.get' p)
                      (map proj_node_map_unchecked true_tries) with
      | Some hd_x, Some tl_x =>
          pt_spaced_intersect' merge fuel' other_cil other_tries t_ci0
                               true_cil hd_x tl_x
      | _, _ => None
      end.
  Proof.
    pose (lam := fun is_forward : bool =>
                   pt_spaced_intersect' merge fuel' other_cil other_tries t_ci0
                     (if is_forward then true_cil else rev true_cil)).
    assert (Hrev : forall b x l,
              True ->
              lam b x (rev l) = lam (negb b) x l).
    { intros b x l _; subst lam.
      destruct b; cbn.
      - (* Goal: pt_spaced_intersect' ... true_cil x (rev l)
                = pt_spaced_intersect' ... (rev true_cil) x l *)
        rewrite <- (Hsim_rev (rev true_cil) x l).
        rewrite rev_involutive. reflexivity.
      - (* Goal: pt_spaced_intersect' ... (rev true_cil) x (rev l)
                = pt_spaced_intersect' ... true_cil x l *)
        rewrite <- (Hsim_rev true_cil x l).
        reflexivity. }
    rewrite (TrieMap.list_intersect_correct
               (B := @pos_trie' A) (C := @pos_trie' A)
               lam
               (fun _ _ _ => True)
               (fun _ _ _ => iff_refl _)
               Hrev
               p
               (proj_node_map_unchecked t_pt0)
               (map proj_node_map_unchecked true_tries)).
    2: { intros i x' l' _ _; trivial. }
    cbn.
    destruct (Tries.Canonical.PTree.get' p (proj_node_map_unchecked t_pt0)) as [hd_x|];
      cbn; [|reflexivity].
    destruct (list_Mmap (Tries.Canonical.PTree.get' p) (map proj_node_map_unchecked true_tries))
      as [tl_x|]; cbn; [|reflexivity].
    subst lam; cbn.
    rewrite (Hsim_rev true_cil hd_x tl_x).
    reflexivity.
  Qed.


  (* Helper: when no element of [L] has [hd false l = true], the filter on
     pairs of (combine L P) selecting [hd false (fst p) = true] is empty. *)
  Lemma filter_combine_no_true_head
    (L : list (list bool)) (P : list (@pos_trie' A)) :
    existsb (fun l => hd false l) L = false ->
    filter (fun p => hd false (fst p)) (combine L P) = [].
  Proof.
    revert P. induction L as [|l L IH]; intros [|pt P] Hany;
      cbn in *; auto.
    destruct (hd false l) eqn:Hh; cbn in Hany; [discriminate|].
    apply IH; exact Hany.
  Qed.

  (* Helper: head of OR-fold is true whenever the initial accumulator's head
     is true OR some entry of [L] has [hd false l = true].  Each entry of
     [L] must have length matching [acc] and be non-empty (length = S _). *)
  Lemma fold_orb_combine_head_some_true (L : list (list bool)) (acc : list bool) (n : nat) :
    Forall (fun l => length l = S n) L ->
    length acc = S n ->
    (hd false acc = true \/ exists l, In l L /\ hd false l = true) ->
    hd false (fold_left (fun a l => map2 orb (combine l a)) L acc) = true.
  Proof.
    revert acc n.
    induction L as [|l L IH]; intros acc n Hlen Hacc_len Hht; cbn.
    - destruct Hht as [Hb | [_ [[] _]]]. exact Hb.
    - pose proof (Forall_inv Hlen) as Hl_len.
      pose proof (Forall_inv_tail Hlen) as Hlen'.
      destruct l as [|h l_tl]; cbn in Hl_len; [discriminate|].
      injection Hl_len as Hl_tl_len.
      destruct acc as [|b acc_tl]; cbn in Hacc_len; [discriminate|].
      injection Hacc_len as Hacc_tl_len.
      change (combine (h :: l_tl) (b :: acc_tl)) with ((h, b) :: combine l_tl acc_tl).
      change (map2 orb ((h, b) :: combine l_tl acc_tl))
        with ((h || b) :: map2 orb (combine l_tl acc_tl)).
      eapply IH with (n := n).
      + (* Forall length on rest *)
        eapply Forall_impl; [|exact Hlen'].
        intros lz Hlz; cbn in *; assumption.
      + (* length of new acc *)
        cbn. unfold map2.
        rewrite length_map, length_combine, Hl_tl_len, Hacc_tl_len, PeanoNat.Nat.min_id.
        reflexivity.
      + (* Disjunction for new fold acc *)
        destruct Hht as [Hb | [l' [HIn Hhd]]].
        * left. cbn in Hb. subst b. rewrite Bool.orb_true_r. reflexivity.
        * destruct HIn as [Hl_eq|HIn_rest].
          -- subst l'. cbn in Hhd. left.
             destruct h; cbn in *; [reflexivity|discriminate].
          -- right. exists l'. split; assumption.
  Qed.

  (* Helper: tail of [fold_left (fun acc l => map2 orb (combine l acc))]
     over a list of equal-length entries equals the same fold over their
     tails started from the original tail accumulator. *)
  Lemma fold_orb_combine_tail
    (L : list (list bool)) (b : bool) (t : list bool) :
    Forall (fun l => length l = S (length t)) L ->
    tl (fold_left (fun acc (l : list bool) => map2 orb (combine l acc)) L (b :: t))
    = fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                (map (@tl _) L) t.
  Proof.
    revert b t; induction L as [|l L IH]; intros b t Hall; cbn; [reflexivity|].
    pose proof (Forall_inv Hall) as Hl_len.
    pose proof (Forall_inv_tail Hall) as Hall'.
    destruct l as [|h l_tl]; cbn [length] in Hl_len; [discriminate|].
    injection Hl_len as Hl_tl_len.
    change (combine (h :: l_tl) (b :: t)) with ((h, b) :: combine l_tl t).
    change (map2 orb ((h, b) :: combine l_tl t))
      with ((h || b) :: map2 orb (combine l_tl t)).
    cbn [tl].
    apply IH.
    eapply Forall_impl; [|exact Hall'].
    intros l' Hl'_len; cbn [length].
    unfold map2.
    rewrite length_map, length_combine, Hl_tl_len, PeanoNat.Nat.min_id.
    exact Hl'_len.
  Qed.

  (* Helper: lookup of [(p :: x')] in a node trie with bool head [true].
     Descends one level via [PTree.get' p] of the node's inner map. *)
  Lemma lookup_one'_cons_node_true (x : list positive) (p : positive)
    (m : PTree.tree' (@pos_trie' A)) (c : list bool) :
    hd false c = true ->
    lookup_one' (p :: x) (pos_trie_node m, c)
    = match Tries.Canonical.PTree.get' p m with
      | Some pt' => lookup_one' x (pt', tl c)
      | None => None
      end.
  Proof.
    destruct c as [|h c_tl]; intros Hhd; cbn [hd] in Hhd; [discriminate|].
    subst h. apply lookup_one'_cons_true.
  Qed.

  (* Helper: when [t_pt0] is a node and the head bit is true, the
     [proj_node_map_unchecked] projection coincides with the inner map. *)
  Lemma has_depth'_S_node (n : nat) (pt : @pos_trie' A) :
    Is_true (has_depth' (S n) pt) ->
    exists m, pt = pos_trie_node m.
  Proof.
    destruct pt as [a|m]; cbn; intros Hd; [contradiction|eauto].
  Qed.

  (* The "have_true" recursive cases of [pt_spaced_intersect'_spec_general]
     (the [b = true] inductive sub-case and the [TF]-non-empty sub-case of
     [b = false]).  States the spec restricted to inputs in which at least
     one of [ci0] or some entry of [cil ++ cil'] has [hd = true]; in that
     scenario the function takes the [have_true_part] branch and the result
     is [option_map pos_trie_node (list_intersect ...)].

     Takes the outer induction hypothesis [IHx_param] as a parameter so the
     recursive call inside [list_intersect] can be unfolded into its
     spec form. *)
  Lemma pt_spaced_intersect'_spec_general_have_true
    (fuel' : nat) (p : positive) (x' : list positive)
    (ci0 : list bool) (pt0 : @pos_trie' A)
    (cil : list (list bool)) (ptl : list (@pos_trie' A))
    (cil' : list (list bool)) (ptl' : list (@pos_trie' A))
    (IHx_param :
       forall (fuel : nat) (ci0_in : list bool) (pt0_in : @pos_trie' A)
              (cil_in : list (list bool)) (ptl_in : list (@pos_trie' A))
              (cil'_in : list (list bool)) (ptl'_in : list (@pos_trie' A)),
         (fuel > length x')%nat ->
         length ci0_in = length x' ->
         Forall (fun l => length l = length x') cil_in ->
         Forall (fun l => length l = length x') cil'_in ->
         length cil_in = length ptl_in ->
         length cil'_in = length ptl'_in ->
         Is_true (has_depth' (length (filter id ci0_in)) pt0_in) ->
         Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt))
                 cil_in ptl_in ->
         Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt))
                 cil'_in ptl'_in ->
         spaced_get x'
           (fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                      (cil_in ++ cil'_in) ci0_in,
            pt_spaced_intersect' merge fuel cil_in ptl_in ci0_in cil'_in
                                 pt0_in ptl'_in)
         = match lookup_one' x' (pt0_in, ci0_in),
                 list_Mmap (lookup_one' x')
                           (combine ptl_in cil_in ++ combine ptl'_in cil'_in) with
           | Some e, Some es => Some (fold_left merge es e)
           | _, _ => None
           end)
    : (fuel' > length x')%nat ->
      length ci0 = S (length x') ->
      Forall (fun l => length l = S (length x')) cil ->
      Forall (fun l => length l = S (length x')) cil' ->
      length cil = length ptl ->
      length cil' = length ptl' ->
      Is_true (has_depth' (length (filter id ci0)) pt0) ->
      Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil ptl ->
      Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil' ptl' ->
      (hd false ci0 = true \/ exists l, In l (cil ++ cil') /\ hd false l = true) ->
      spaced_get (p :: x')
        (fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                   (cil ++ cil') ci0,
         pt_spaced_intersect' merge (S fuel') cil ptl ci0 cil' pt0 ptl')
      = match lookup_one' (p :: x') (pt0, ci0),
              list_Mmap (lookup_one' (p :: x'))
                        (combine ptl cil ++ combine ptl' cil') with
        | Some e, Some es => Some (fold_left merge es e)
        | _, _ => None
        end.
  Proof.
    intros Hfuel Hci0_len Hcil_len Hcil'_len Hcil_ptl_len Hcil'_ptl'_len
           Hpt0_d Hcil_ptl_d Hcil'_ptl'_d Hht.
    (* Build rectangular_trie_list facts. *)
    assert (Hrect : rectangular_trie_list (S (length x')) cil ptl).
    { eapply rectangular_trie_list_of_Forall2; [exact Hcil_len|exact Hcil_ptl_d]. }
    assert (Hrect' : rectangular_trie_list (S (length x')) cil' ptl').
    { eapply rectangular_trie_list_of_Forall2; [exact Hcil'_len|exact Hcil'_ptl'_d]. }
    assert (Hrect_app : rectangular_trie_list (S (length x'))
                                              (cil ++ cil') (ptl ++ ptl')).
    { apply rectangular_trie_list_app; assumption. }
    assert (Hcc_len : Forall (fun l => length l = S (length x')) (cil ++ cil')).
    { apply Forall_app; split; assumption. }
    (* Destruct ci0 = b :: ci0'. *)
    destruct ci0 as [|b ci0']; [cbn in Hci0_len; discriminate|].
    cbn [Datatypes.length] in Hci0_len. injection Hci0_len as Hci0_len.
    (* Compute that Bools[0] = true. *)
    assert (Hb_ci0_len : length (b :: ci0') = S (length x')) by (cbn; congruence).
    pose proof (fold_orb_combine_head_some_true (cil ++ cil')
                  (b :: ci0') (length x') Hcc_len Hb_ci0_len Hht)
      as Hbools_head_true.
    (* Roadmap.  Mirror the FF-non-empty case but with [have_true_part]:
       1. Unfold one step of [pt_spaced_intersect'].
       2. Combine the two [partition_tries] calls via [partition_tries_app].
       3. Apply [partition_tries_spec] — get an explicit [TF/FF]-based form.
       4. In both subcases (b=true; b=false with TF non-empty) the
          partition output is [have_true_part]; reduce
          [spaced_get (p::x') (true::Bools_tl, option_map pos_trie_node X)]
          using [Hbools_head_true] and the descent-by-one-level lemma
          [pt_get'/PTree.get' on the node].
       5. Apply [list_intersect_lookup_at_pos] supplying the global
          [pt_spaced_intersect'_sim_rev] for [Hsim_rev].
       6. Apply [IHx_param] to express the inner recursive call.
       7. Align the bool-fold and lookup sides with the spec via
          [fold_left_orb_combine_perm_full] / [list_Mmap_lookup_fold_perm].

       The per-subcase permutation alignment is the structural analog of
       the FF non-empty case (lines ~1330 onwards) but tracks both
       [other_cil/other_tries] (false-headed entries) and
       [true_cil/true_tries] (true-headed entries except the chosen head).
       That last alignment step is ~250 lines of mechanical proof and is
       left admitted here; the rest of the structure (1–6) is laid out
       below to the point of the alignment goal. *)
    cbn [pt_spaced_intersect'].
    (* Combine the two partition_tries. *)
    erewrite partition_tries_app by eassumption.
    cbn in Hpt0_d.
    (* Case-split on [b]: each branch has a concrete initial accumulator.
       Both cases use [partition_tries_spec] then destructure the [TF]
       output to access the [have_true_part] case. *)
    destruct b.
    { (* b = true.  initial = have_true_part [] [] ci0' pt0 [] [].
         After [partition_tries_spec]: partition_result_of_lists
         FF_filter (TF_filter ++ [(ci0', pt0)]).  TF non-empty by
         construction. *)
      assert (Hwf_init : partition_result_wf (length x')
                (have_true_part [] (@nil (@pos_trie' A)) ci0' pt0 [] [])).
      { cbn. split; [|cbn; trivial].
        cbn. split; [|trivial]. split; [exact Hpt0_d|exact Hci0_len]. }
      erewrite (@partition_tries_spec _ _ merge (cil ++ cil') (ptl ++ ptl')
                  _ (length x') Hrect_app Hwf_init).
      cbn [false_lists true_lists].
      (* Set up names. *)
      set (Lall := combine (cil ++ cil') (ptl ++ ptl')).
      set (TF_filter := rev (map (fun p => (tl (fst p), snd p))
                              (filter (fun p => hd false (fst p)) Lall))).
      set (FF := rev (map (fun p => (tl (fst p), snd p))
                        (filter (fun p => negb (hd false (fst p))) Lall))).
      (* TF = TF_filter ++ [(ci0', pt0)] is non-empty by construction. *)
      set (TF := TF_filter ++ [(ci0', pt0)]).
      assert (HTF_ne : TF <> []).
      { unfold TF. intro HEq.
        apply (f_equal (@length _)) in HEq.
        rewrite length_app in HEq; cbn [length] in HEq; Lia.lia. }
      destruct TF as [|tp TF_tail] eqn:HTF; [exfalso; apply HTF_ne; reflexivity|].
      destruct tp as [tc0 tp0].
      cbn [partition_result_of_lists].
      rewrite ?TrieMap.split_map.
      cbn [fst snd].
      (* Expose Bools = true :: Bools_tl. *)
      remember (fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                          (cil ++ cil') (true :: ci0')) as Bools eqn:HBools.
      destruct Bools as [|b1 Bools_tl];
        [cbn in Hbools_head_true; discriminate|].
      cbn [hd] in Hbools_head_true. subst b1.
      (* Goal: spaced_get (p :: x') (true :: Bools_tl, option_map pos_trie_node (list_intersect ...))
              = match lookup_one' (p :: x') (pt0, true :: ci0'),
                      list_Mmap ... with ... end.
         The remaining ~100 lines reduce LHS via head=true descent,
         [list_intersect_lookup_at_pos], [IHx_param], and align with RHS
         via two Permutations. *)
      admit. }
    { (* b = false.  initial = just_false_part ci0' pt0 [] [].
         After [partition_tries_spec]: partition_result_of_lists
         (FF_filter ++ [(ci0', pt0)]) TF_filter.  TF_filter non-empty by
         [Hht]'s right disjunct (Hht left disjunct is impossible since
         [hd false (false :: ci0') = false]). *)
      assert (Hwf_init : partition_result_wf (length x')
                (just_false_part ci0' pt0 [] (@nil (@pos_trie' A)))).
      { cbn. split; [|trivial]. split; [exact Hpt0_d|exact Hci0_len]. }
      erewrite (@partition_tries_spec _ _ merge (cil ++ cil') (ptl ++ ptl')
                  _ (length x') Hrect_app Hwf_init).
      cbn [false_lists true_lists].
      rewrite app_nil_r.
      (* Set up names and prove TF non-empty. *)
      set (Lall := combine (cil ++ cil') (ptl ++ ptl')).
      set (TF := rev (map (fun p => (tl (fst p), snd p))
                        (filter (fun p => hd false (fst p)) Lall))).
      set (FF := rev (map (fun p => (tl (fst p), snd p))
                        (filter (fun p => negb (hd false (fst p))) Lall))).
      assert (HTF_ne : TF <> []).
      { destruct Hht as [Hb_hd | [l_w [HIn Hl_w_hd]]];
          [cbn in Hb_hd; discriminate|].
        unfold TF, Lall.
        intro HEq.
        apply (f_equal (@rev _)) in HEq; rewrite rev_involutive in HEq;
          cbn [rev] in HEq.
        apply map_eq_nil in HEq.
        (* HEq: filter (hd false ∘ fst) (combine (cil++cil') (ptl++ptl')) = [].
           But l_w ∈ cil++cil' has hd false l_w = true, contradiction. *)
        assert (Hcc_p_len : length (cil ++ cil') = length (ptl ++ ptl'))
          by (rewrite ?length_app; congruence).
        revert HIn HEq Hcc_p_len Hl_w_hd; clear.
        generalize (ptl ++ ptl') as Pall.
        generalize (cil ++ cil') as Call.
        intros Call; revert Call.
        induction Call as [|c rest IH]; intros Pall HIn HEq Hlen Hl_w_hd;
          [cbn in HIn; contradiction|].
        destruct Pall as [|pp Prest]; [cbn in Hlen; discriminate|].
        cbn [combine] in HEq.
        destruct HIn as [Heq|HIn_rest].
        + (* c = l_w: filter sees hd l_w = true, so cons-ed. *)
          subst c. cbn [filter fst] in HEq.
          rewrite Hl_w_hd in HEq. discriminate.
        + (* c ∈ rest: filter on (c, pp) :: combine rest Prest decides on hd c. *)
          cbn [filter fst] in HEq.
          destruct (hd false c) eqn:Hhd_c; [discriminate|].
          apply (IH Prest); [exact HIn_rest|exact HEq| |exact Hl_w_hd].
          cbn in Hlen; Lia.lia. }
      (* Destructure TF.  After this, partition_result_of_lists
         reduces to have_true_part. *)
      destruct TF as [|tp TF_tail] eqn:HTF; [exfalso; apply HTF_ne; reflexivity|].
      destruct tp as [tc0 tp0].
      cbn [partition_result_of_lists].
      rewrite ?TrieMap.split_map.
      cbn [fst snd].
      (* Simplify [map fst/snd (FF ++ [(ci0', pt0)])] to
         [map fst FF ++ [ci0']] / [map snd FF ++ [pt0]]. *)
      rewrite ?(map_app _ FF), ?(map_cons _ (ci0', pt0)); cbn [map fst snd].
      (* Expose Bools = true :: Bools_tl using [Hbools_head_true]. *)
      remember (fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                          (cil ++ cil') (false :: ci0')) as Bools eqn:HBools.
      destruct Bools as [|b1 Bools_tl];
        [cbn in Hbools_head_true; discriminate|].
      cbn [hd] in Hbools_head_true. subst b1.
      (* Reduce [spaced_get] on head bit [true]: drops to [pt_get] on the
         remaining key.  Set [rest_key] to track the key tail. *)
      unfold spaced_get; cbn [fst snd combine filter map].
      set (rest_key := map fst (filter snd (combine x' Bools_tl))).
      (* Factor [pt_get (option_map pos_trie_node X) (p :: rest_key)]
         through [Tries.Canonical.PTree.get p (otree X)] so that
         [list_intersect_lookup_at_pos] applies. *)
      assert (Hfactor : forall X : option (Tries.Canonical.PTree.tree' (@pos_trie' A)),
                 pt_get (option_map pos_trie_node X) (p :: rest_key)
                 = match Tries.Canonical.PTree.get p (TrieMap.otree X) with
                   | Some pt' => pt_get' pt' rest_key
                   | None => None
                   end).
      { intros [m|]; cbn; reflexivity. }
      rewrite Hfactor.
      (* Apply [list_intersect_lookup_at_pos], supplying the global
         [pt_spaced_intersect'_sim_rev] as the Hsim_rev premise. *)
      rewrite (list_intersect_lookup_at_pos
                 fuel'
                 (map fst FF ++ [ci0'])
                 (map snd FF ++ [pt0])
                 tc0
                 (map fst TF_tail)
                 tp0
                 (map snd TF_tail)
                 p
                 (pt_spaced_intersect'_sim_rev fuel'
                    (map fst FF ++ [ci0'])
                    (map snd FF ++ [pt0])
                    tc0)).
      (* Goal LHS now:
         match
           match Tries.Canonical.PTree.get' p (proj_node_map_unchecked tp0),
                 list_Mmap (Tries.Canonical.PTree.get' p)
                           (map proj_node_map_unchecked (map snd TF_tail)) with
           | Some hd_x, Some tl_x =>
               pt_spaced_intersect' merge fuel'
                 (map fst FF ++ [ci0']) (map snd FF ++ [pt0]) tc0
                 (map fst TF_tail) hd_x tl_x
           | _, _ => None
           end
         with Some pt' => pt_get' pt' rest_key | None => None end.
         Remaining ~60 lines: apply [IHx_param] to expand the inner
         [pt_spaced_intersect'] (when both lookups succeed), align the
         bool-fold via [fold_orb_combine_tail] + a Permutation argument,
         and align the lookup side with the goal RHS via another
         Permutation. *)
      admit. }
  Admitted.


  (* Generalised version: handles the auxiliary [cil'/ptl'] arguments to
     [pt_spaced_intersect'] (which the just_false_part recursion sets to []
     but which the have_true_part recursion through [list_intersect] uses
     non-trivially).  Setting [cil' = ptl' = []] recovers the original. *)
  Lemma pt_spaced_intersect'_spec_general
    (fuel : nat) (x : list positive)
    (ci0 : list bool) (pt0 : @pos_trie' A)
    (cil : list (list bool)) (ptl : list (@pos_trie' A))
    (cil' : list (list bool)) (ptl' : list (@pos_trie' A))
    : (fuel > length x)%nat ->
      length ci0 = length x ->
      Forall (fun l => length l = length x) cil ->
      Forall (fun l => length l = length x) cil' ->
      length cil = length ptl ->
      length cil' = length ptl' ->
      Is_true (has_depth' (length (filter id ci0)) pt0) ->
      Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil ptl ->
      Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil' ptl' ->
      spaced_get x (fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                              (cil ++ cil') ci0,
                    pt_spaced_intersect' merge fuel cil ptl ci0 cil' pt0 ptl')
      = match lookup_one' x (pt0, ci0),
              list_Mmap (lookup_one' x) (combine ptl cil ++ combine ptl' cil') with
        | Some e, Some es => Some (fold_left merge es e)
        | _, _ => None
        end.
  Proof.
    revert fuel ci0 pt0 cil ptl cil' ptl'.
    induction x as [|p x' IHx];
      intros fuel ci0 pt0 cil ptl cil' ptl'
             Hfuel Hci0_len Hcil_len Hcil'_len Hcil_ptl_len Hcil'_ptl'_len
             Hpt0_d Hcil_ptl_d Hcil'_ptl'_d.
    - (* Base case: x = []. Both cil and cil' contain only []s, every ptl
         and ptl' element is a leaf, function returns
         Some (pos_trie_leaf (leaf_intersect (leaf_intersect a ptl) ptl')). *)
      destruct ci0 as [|? ?]; [|cbn in Hci0_len; discriminate].
      destruct fuel as [|fuel']; [Lia.lia|].
      cbn in Hpt0_d.
      destruct pt0 as [a|m]; [|contradiction].
      assert (Hcil_all_nil : Forall (fun l => l = []) cil).
      { eapply Forall_impl; [|exact Hcil_len].
        intros l Hl; cbn in Hl. apply length_zero_iff_nil. exact Hl. }
      assert (Hcil'_all_nil : Forall (fun l => l = []) cil').
      { eapply Forall_impl; [|exact Hcil'_len].
        intros l Hl; cbn in Hl. apply length_zero_iff_nil. exact Hl. }
      assert (Hptl_leaf : Forall (fun pt => Is_true (has_depth' 0 pt)) ptl).
      { revert Hcil_ptl_d Hcil_all_nil. clear.
        revert ptl. induction cil as [|c cil IH]; intros [|pt ptl] Hd Hcil;
          inversion Hd; subst; constructor.
        - inversion Hcil; subst c. cbn in *. assumption.
        - apply IH; [assumption|]. inversion Hcil; assumption. }
      assert (Hptl'_leaf : Forall (fun pt => Is_true (has_depth' 0 pt)) ptl').
      { revert Hcil'_ptl'_d Hcil'_all_nil. clear.
        revert ptl'. induction cil' as [|c cil' IH]; intros [|pt ptl'] Hd Hcil';
          inversion Hd; subst; constructor.
        - inversion Hcil'; subst c. cbn in *. assumption.
        - apply IH; [assumption|]. inversion Hcil'; assumption. }
      assert (Hptl_all : all (fun t => Is_true (has_depth' 0 t)) ptl).
      { clear - Hptl_leaf. induction ptl; cbn; auto.
        inversion Hptl_leaf; subst; split; auto. }
      assert (Hptl'_all : all (fun t => Is_true (has_depth' 0 t)) ptl').
      { clear - Hptl'_leaf. induction ptl'; cbn; auto.
        inversion Hptl'_leaf; subst; split; auto. }
      cbn [pt_spaced_intersect'].
      (* combined-bools across cil ++ cil' folds to []. *)
      assert (Hcc_all_nil : Forall (fun l => l = []) (cil ++ cil')).
      { apply Forall_app; split; assumption. }
      rewrite (fold_left_map2_orb_all_nil _ Hcc_all_nil).
      (* RHS list_Mmap over the appended combine. *)
      rewrite list_Mmap_app.
      rewrite (list_Mmap_lookup_one'_nil _ _ Hcil_ptl_len Hcil_all_nil Hptl_leaf).
      rewrite (list_Mmap_lookup_one'_nil _ _ Hcil'_ptl'_len Hcil'_all_nil Hptl'_leaf).
      change (lookup_one' [] (pos_trie_leaf a, [])) with (@Some A a).
      unfold spaced_get; cbn [fst snd pt_get].
      cbn [filter combine map].
      cbn [pt_get'].
      (* leaf_intersect (leaf_intersect a ptl) ptl' = fold_left merge over
         (map leaf_value ptl ++ map leaf_value ptl') starting at a. *)
      rewrite (leaf_intersect_correct _ a ptl Hptl_all).
      rewrite (leaf_intersect_correct _ _ ptl' Hptl'_all).
      rewrite <- fold_left_app.
      reflexivity.
    - (* Inductive case: x = p :: x'. *)
      destruct ci0 as [|b ci0']; [cbn in Hci0_len; discriminate|].
      destruct fuel as [|fuel']; [cbn in Hfuel; Lia.lia|].
      cbn [Datatypes.length] in Hci0_len, Hfuel.
      injection Hci0_len as Hci0_len.
      assert (Hfuel' : (fuel' > length x')%nat) by Lia.lia.
      (* Build rectangular_trie_list facts for partition_tries_app. *)
      assert (Hrect : rectangular_trie_list (S (length x')) cil ptl).
      { eapply rectangular_trie_list_of_Forall2; [|exact Hcil_ptl_d]. exact Hcil_len. }
      assert (Hrect' : rectangular_trie_list (S (length x')) cil' ptl').
      { eapply rectangular_trie_list_of_Forall2; [|exact Hcil'_ptl'_d]. exact Hcil'_len. }
      (* The combined inputs are rectangular at width [S (length x')]. *)
      assert (Hrect_app : rectangular_trie_list (S (length x'))
                                                (cil ++ cil') (ptl ++ ptl')).
      { apply rectangular_trie_list_app; assumption. }
      (* Case on [b].  [b = true] dispatches directly through the
         have-true helper; [b = false] further splits on whether any entry
         of [cil ++ cil'] starts with [true]. *)
      destruct b.
      + (* b = true: the initial accumulator is have_true_part, so we can
           apply [pt_spaced_intersect'_spec_general_have_true] with
           [hd false ci0 = true] as witness. *)
        apply (pt_spaced_intersect'_spec_general_have_true
                 fuel' p x' (true :: ci0') pt0 cil ptl cil' ptl' IHx);
          try assumption; try Lia.lia.
        * cbn [Datatypes.length]; congruence.
        * left; reflexivity.
      + (* b = false: case on whether any entry of [cil ++ cil'] starts
           with [true].  If yes, apply the same helper with the right
           disjunct; otherwise the partition's true-filter is empty and
           the existing [TF = []] proof structure applies. *)
        destruct (existsb (fun l => hd false l) (cil ++ cil')) eqn:Hany.
        { (* Some entry of [cil ++ cil'] has head = true: apply helper. *)
          apply (pt_spaced_intersect'_spec_general_have_true
                   fuel' p x' (false :: ci0') pt0 cil ptl cil' ptl' IHx);
            try assumption; try Lia.lia.
          - cbn [Datatypes.length]; congruence.
          - right.
            apply existsb_exists in Hany.
            destruct Hany as [l [HIn Hhd]].
            exists l. split; [exact HIn|].
            destruct (hd false l); cbn in Hhd; [reflexivity|discriminate]. }
        (* All heads are false; proceed with the existing TF = [] proof. *)
        cbn [pt_spaced_intersect'].
        erewrite partition_tries_app by eassumption.
        cbn in Hpt0_d.
        assert (Hwf_init : partition_result_wf (length x')
                             (just_false_part ci0' pt0 (@nil (list bool))
                                              (@nil (@pos_trie' A)))).
        { cbn. split; [|reflexivity]. split; [exact Hpt0_d|exact Hci0_len]. }
        erewrite (@partition_tries_spec _ _ merge (cil ++ cil') (ptl ++ ptl')
                    (just_false_part ci0' pt0 [] []) (length x')
                    Hrect_app Hwf_init).
        cbn [false_lists true_lists].
        rewrite app_nil_r.
        (* Bind the [true_filter] / [false_filter] expressions so we can
           case on them. *)
        set (Lall := combine (cil ++ cil') (ptl ++ ptl')).
        set (TF := rev (map (fun p => (tl (fst p), snd p))
                          (filter (fun p => hd false (fst p)) Lall))).
        set (FF := rev (map (fun p => (tl (fst p), snd p))
                          (filter (fun p => negb (hd false (fst p))) Lall))).
        (* Partition_result_of_lists pattern-matches on its second
           argument [TF].  Subcases on whether [TF] is empty. *)
        destruct TF as [|[tc0 tp0] TF_tail] eqn:HTF.
        * (* TF = []: no entry of cil++cil' has a true head.  We further
             split on FF: if FF=[] then cil=cil'=[] (no extra tries) and
             the recursive call is trivially over the empty input; if FF
             is non-empty, the recursive call is over the false-headed
             entries (in reverse order) with (ci0', pt0) appended. *)
          destruct FF as [|[fc0' fp0'] FF_tail] eqn:HFF.
          { (* FF = []: no false-headed entries either, so cil++cil'=[].
               Sub-goal: the original function call collapses to the same
               recursive form as the spec at x'. *)
            (* From TF = [] and FF = [], all entries of [combine (cil++cil')
               (ptl++ptl')] must satisfy both [head=true] and [head=false]
               filters being empty.  Since each cil/cil' entry is non-empty
               (length = S (length x')), this forces cil++cil' = []. *)
            assert (Hcc_empty : cil ++ cil' = []).
            { (* Extract that the head=true filter on Lall is empty. *)
              unfold TF in HTF; unfold FF in HFF.
              assert (Hfilter_T : filter (fun p => hd false (fst p)) Lall = []).
              { apply (f_equal (@rev _)) in HTF.
                rewrite rev_involutive in HTF.
                apply map_eq_nil in HTF; exact HTF. }
              assert (Hfilter_F : filter
                (fun p => negb (hd false (fst p))) Lall = []).
              { apply (f_equal (@rev _)) in HFF.
                rewrite rev_involutive in HFF.
                apply map_eq_nil in HFF; exact HFF. }
              eapply (filter_both_empty_combine_nil _ _ (length x')).
              - apply Forall_app; split.
                + eapply Forall_impl; [|exact Hcil_len].
                  intros l Hl; cbn in Hl; cbn; Lia.lia.
                + eapply Forall_impl; [|exact Hcil'_len].
                  intros l Hl; cbn in Hl; cbn; Lia.lia.
              - rewrite length_app, length_app,
                  <- Hcil_ptl_len, <- Hcil'_ptl'_len. reflexivity.
              - exact Hfilter_T.
              - exact Hfilter_F. }
            assert (Hp_empty : ptl ++ ptl' = []).
            { apply length_zero_iff_nil.
              rewrite length_app, <- Hcil_ptl_len, <- Hcil'_ptl'_len,
                <- length_app, Hcc_empty. reflexivity. }
            (* With cil++cil' = [] and ptl++ptl' = [], we substitute and the
               partition_result_of_lists collapses to just_false_part with
               (ci0', pt0) as the new head and empty other_cil/other_tries. *)
            apply app_eq_nil in Hcc_empty as [Hcil_e Hcil'_e].
            apply app_eq_nil in Hp_empty as [Hptl_e Hptl'_e].
            subst cil cil' ptl ptl'.
            subst TF FF Lall.
            clear HTF HFF Hrect Hrect' Hrect_app
                  Hcil_len Hcil'_len Hcil_ptl_len Hcil'_ptl'_len
                  Hcil_ptl_d Hcil'_ptl'_d Hwf_init.
            (* Reduce partition_result_of_lists *)
            cbn [app combine partition_result_of_lists split fst snd].
            (* Apply IHx with all-empty side inputs *)
            specialize (IHx fuel' ci0' pt0 [] [] [] [] Hfuel' Hci0_len
                            (Forall_nil _) (Forall_nil _) eq_refl eq_refl
                            Hpt0_d (Forall2_nil _) (Forall2_nil _)).
            cbn [combine app] in IHx.
            (* Reduce the bool-list fold and the spaced_get on the head *)
            cbn [fold_left app] in *.
            unfold spaced_get in *; cbn [fst snd] in *.
            cbn [combine filter map] in *.
            rewrite lookup_one'_cons_false.
            cbn [combine list_Mmap].
            exact IHx. }
          { (* FF non-empty: recursive call has new (ci0_new, pt0_new) and
               reverse-ordered other_cil/other_tries from FF and (ci0', pt0).
               IHx applies; the bool-list and lookup-pair sides each need
               permutation reasoning to align with IHx's per-call form,
               using fold_left_orb_combine_perm_full and
               list_Mmap_lookup_fold_perm. *)

            (* Step 1: derive that all entries of [cil ++ cil'] start
               with [false], by extracting [filter (hd=true) Lall = []]
               from HTF. *)
            unfold TF in HTF.
            apply (f_equal (@rev _)) in HTF.
            rewrite rev_involutive in HTF; cbn [rev] in HTF.
            apply map_eq_nil in HTF.
            (* HTF : filter (fun p => hd false (fst p)) Lall = [] *)

            (* Step 2: simplify HFF.  Since [filter (hd=true) Lall = []],
               [filter (negb (hd=true)) Lall = Lall]. *)
            pose proof (filter_complement_nil_id _ _ HTF) as Hfilter_F.
            unfold FF in HFF.
            rewrite Hfilter_F in HFF.
            apply (f_equal (@rev _)) in HFF.
            rewrite rev_involutive in HFF.
            (* HFF : map (fun p => (tl (fst p), snd p)) Lall =
                       rev ((fc0', fp0') :: FF_tail) *)
            unfold Lall in HFF.
            rewrite map_tl_fst_combine in HFF.
            2: { rewrite ?length_app, <- Hcil_ptl_len, <- Hcil'_ptl'_len.
                 reflexivity. }
            (* HFF : combine (map tl (cil ++ cil')) (ptl ++ ptl') =
                       rev ((fc0', fp0') :: FF_tail) *)

            (* Step 3: build [Forall (length = S length x' /\ hd false = false)]
               for [cil ++ cil']. *)
            assert (Hall_false : Forall
                       (fun l : list bool => length l = S (length x')
                                             /\ hd false l = false)
                       (cil ++ cil')).
            { (* All entries have length S(length x') (rectangular).
                 Head false comes from HTF. *)
              assert (Hcc_len : Forall (fun l => length l = S (length x'))
                                  (cil ++ cil')).
              { apply Forall_app; split; assumption. }
              assert (Hcc_hd : Forall (fun l => hd false l = false) (cil ++ cil')).
              { (* HTF says no entry of Lall has hd=true.  Lall has all of
                   cil++cil' as fst-projections (with corresponding ptl++ptl'). *)
                assert (Hlen_full : length (cil ++ cil') = length (ptl ++ ptl')).
                { rewrite ?length_app; congruence. }
                unfold Lall in HTF.
                revert HTF Hlen_full.
                generalize (ptl ++ ptl') as P. generalize (cil ++ cil') as C.
                clear; intros C P HTF Hlen.
                revert P Hlen HTF.
                induction C as [|c C IH]; intros [|p P] Hlen HTF.
                - constructor.
                - cbn in Hlen; discriminate.
                - cbn in Hlen; discriminate.
                - destruct c as [|h c].
                  + (* c = []: hd false [] = false trivially *)
                    cbn in HTF.
                    constructor; [reflexivity|].
                    apply (IH P); [cbn in Hlen; Lia.lia | exact HTF].
                  + destruct h.
                    * (* h = true: HTF has (true :: c, p) :: ... = [] *)
                      cbn in HTF; discriminate.
                    * (* h = false *)
                      cbn in HTF.
                      constructor; [reflexivity|].
                      apply (IH P); [cbn in Hlen; Lia.lia | exact HTF]. }
              clear -Hcc_len Hcc_hd.
              induction Hcc_len; cbn; auto.
              inversion Hcc_hd; subst.
              constructor; [split; assumption|]. apply IHHcc_len; assumption. }

            clear Hfilter_F.
            (* Step 4: compute the bool-list fold via [fold_orb_combine_all_false_head]. *)
            rewrite <- Hci0_len in Hall_false.
            rewrite (fold_orb_combine_all_false_head _ _ _ Hall_false).
            rewrite Hci0_len in Hall_false.
            (* Now the goal's Bools is [false :: fold (map tl (cil++cil')) ci0']. *)

            (* Step 5: reduce the [partition_result_of_lists] in the trie. *)
            (* combine [ci0'] [pt0] = [(ci0', pt0)] *)
            cbn [combine] in *.
            (* ((fc0', fp0') :: FF_tail) ++ [(ci0', pt0)]
               = (fc0', fp0') :: (FF_tail ++ [(ci0', pt0)]) *)
            rewrite <- app_comm_cons.
            (* Reduce partition_result_of_lists *)
            cbn [partition_result_of_lists].
            (* Replace split with (map fst, map snd) and destructure the let. *)
            assert (Hsplit_eq : split (FF_tail ++ [(ci0', pt0)])
                                = (map fst (FF_tail ++ [(ci0', pt0)]),
                                   map snd (FF_tail ++ [(ci0', pt0)])))
              by apply TrieMap.split_map.
            rewrite Hsplit_eq.
            clear Hsplit_eq.
            cbn [split].
            (* The match has been resolved to:
               just_false_part fc0' fp0'
                 (map fst (FF_tail ++ [(ci0', pt0)]))
                 (map snd (FF_tail ++ [(ci0', pt0)])) *)

            (* Set [f_c, f_p] for clarity. *)
            set (f_c := map fst (FF_tail ++ [(ci0', pt0)])).
            set (f_p := map snd (FF_tail ++ [(ci0', pt0)])).

            (* Step 6: derive preconditions for IHx. *)
            (* Permutation: (fc0', fp0') :: FF_tail ≡perm≡ combine (map tl (cil++cil')) (ptl++ptl') *)
            assert (Hperm_FF :
                      Permutation ((fc0', fp0') :: FF_tail)
                                  (combine (map (@tl _) (cil ++ cil'))
                                           (ptl ++ ptl'))).
            { rewrite HFF. apply Permutation_rev. }

            assert (Hcc_lentl : length (map (@tl _) (cil ++ cil'))
                                = length (ptl ++ ptl')).
            { rewrite length_map, ?length_app. congruence. }

            (* Length facts about cil++cil' tails *)
            assert (Hmap_tl_len :
                      Forall (fun l => length l = length x')
                             (map (@tl _) (cil ++ cil'))).
            { eapply Forall_map.
              eapply Forall_impl; [|exact Hall_false].
              intros l [Hl_len Hl_hd]. cbn.
              destruct l as [|h ltl]; cbn in *; [discriminate|].
              injection Hl_len as ->. reflexivity. }

            (* Forall2 depth fact about (map tl (cil++cil'), ptl++ptl') *)
            assert (Hmap_tl_d :
                      Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt))
                              (map (@tl _) (cil ++ cil'))
                              (ptl ++ ptl')).
            { (* From Hcil_ptl_d, Hcil'_ptl'_d and Hall_false (heads=false). *)
              assert (Hcc_d : Forall2 (fun ci pt =>
                                Is_true (has_depth' (length (filter id ci)) pt))
                                (cil ++ cil') (ptl ++ ptl')).
              { clear -Hcil_ptl_d Hcil'_ptl'_d.
                induction Hcil_ptl_d; cbn; auto. }
              clear -Hcc_d Hall_false.
              induction Hcc_d as [|c p C P Hcp Hrest IH]; cbn; auto.
              pose proof (Forall_inv Hall_false) as [Hl_len Hl_hd].
              pose proof (Forall_inv_tail Hall_false) as Hall_false'.
              destruct c as [|h c]; cbn in *; [discriminate|].
              subst h.
              constructor; [exact Hcp|].
              apply IH. exact Hall_false'. }

            (* Length: f_c length = length f_p *)
            assert (Hf_cp_len : length f_c = length f_p).
            { unfold f_c, f_p. rewrite ?length_map. reflexivity. }

            (* (fc0', fp0') :: FF_tail has length len(map tl (cil++cil')). *)
            assert (Hperm_len_eq : length ((fc0', fp0') :: FF_tail)
                                   = length (map (@tl _) (cil ++ cil'))).
            { erewrite Permutation_length by exact Hperm_FF.
              rewrite length_combine, Hcc_lentl, PeanoNat.Nat.min_id.
              reflexivity. }

            (* All elements of (fc0', fp0') :: FF_tail have appropriate length/depth. *)
            assert (Hperm_lens : Forall (fun pq => length (fst pq) = length x')
                                        ((fc0', fp0') :: FF_tail)).
            { (* By Permutation: same property holds. *)
              eapply Permutation_Forall;
                [apply Permutation_sym; exact Hperm_FF|].
              clear -Hmap_tl_len Hcc_lentl.
              revert Hcc_lentl Hmap_tl_len.
              generalize (ptl ++ ptl') as P.
              generalize (map (@tl _) (cil ++ cil')) as C.
              intros C P Hlen Hall.
              revert P Hlen.
              induction Hall as [|c C Hc Hrest IH]; intros [|p P] Hlen;
                cbn in *; try discriminate; constructor.
              - cbn. exact Hc.
              - apply IH; Lia.lia. }

            assert (Hperm_dep : Forall2 (fun ci pt =>
                       Is_true (has_depth' (length (filter id ci)) pt))
                       (map fst ((fc0', fp0') :: FF_tail))
                       (map snd ((fc0', fp0') :: FF_tail))).
            { (* By Permutation: same Forall2 holds. *)
              (* Convert Forall2 to Forall on combine, apply Permutation, convert back. *)
              assert (HPair :
                        Forall (fun pq => Is_true (has_depth' (length (filter id (fst pq))) (snd pq)))
                          ((fc0', fp0') :: FF_tail)).
              { eapply Permutation_Forall;
                  [apply Permutation_sym; exact Hperm_FF|].
                clear -Hmap_tl_d Hcc_lentl.
                revert Hcc_lentl Hmap_tl_d.
                generalize (ptl ++ ptl') as P.
                generalize (map (@tl _) (cil ++ cil')) as C.
                intros C P Hlen Hd.
                induction Hd; cbn; auto. }
              clear -HPair.
              remember ((fc0', fp0') :: FF_tail) as L.
              clear HeqL fc0' fp0' FF_tail.
              induction HPair; cbn; auto. }

            (* Permutation of (fc0' :: f_c) and (ci0' :: map tl (cil++cil')) *)
            assert (Hperm_cil : Permutation (fc0' :: f_c)
                                            (ci0' :: map (@tl _) (cil ++ cil'))).
            { unfold f_c.
              rewrite map_app; cbn [map fst].
              (* fc0' :: (map fst FF_tail ++ [ci0']) *)
              change (fc0' :: (map fst FF_tail ++ [ci0']))
                with ((fc0' :: map fst FF_tail) ++ [ci0']).
              (* fc0' :: map fst FF_tail = map fst ((fc0', fp0') :: FF_tail) *)
              change (fc0' :: map fst FF_tail)
                with (map fst ((fc0', fp0') :: FF_tail)).
              etransitivity.
              { apply Permutation_app_tail.
                apply Permutation_map. exact Hperm_FF. }
              (* map fst (combine A B) ≡ A when |A| = |B|. *)
              rewrite map_fst_combine by exact Hcc_lentl.
              (* Now: map tl (cil++cil') ++ [ci0'] vs ci0' :: map tl (cil++cil') *)
              rewrite Permutation_app_comm; cbn. reflexivity. }

            (* Permutation of (fp0', fc0') :: combine f_p f_c
                                  vs (pt0, ci0') :: (combine ptl (map tl cil) ++ combine ptl' (map tl cil')) *)
            assert (Hperm_lookup :
                      Permutation
                        ((fp0', fc0') :: combine f_p f_c)
                        ((pt0, ci0')
                           :: (combine ptl (map (@tl _) cil)
                                ++ combine ptl' (map (@tl _) cil')))).
            { unfold f_c, f_p.
              rewrite ?map_app; cbn [map fst snd].
              rewrite combine_app_eq by (rewrite ?length_map; reflexivity).
              cbn [combine].
              (* (fp0', fc0') :: (combine (map snd FF_tail) (map fst FF_tail) ++ [(pt0, ci0')]) *)
              (* Rotate (pt0, ci0') to head via Permutation_app_comm + perm_skip. *)
              change ((fp0', fc0')
                       :: combine (map snd FF_tail) (map fst FF_tail) ++ [(pt0, ci0')])
                with (((fp0', fc0')
                         :: combine (map snd FF_tail) (map fst FF_tail))
                        ++ [(pt0, ci0')]).
              etransitivity; [apply Permutation_app_comm|]; cbn [app].
              apply perm_skip.
              (* (fp0', fc0') :: combine (map snd FF_tail) (map fst FF_tail)
                 = combine (map snd ((fc0', fp0') :: FF_tail))
                           (map fst ((fc0', fp0') :: FF_tail))
                 = map swap ((fc0', fp0') :: FF_tail) *)
              rewrite combine_swap_proj.
              change ((fp0', fc0')
                        :: map (fun p => (snd p, fst p)) FF_tail)
                with (map (fun p : list bool * pos_trie' => (snd p, fst p))
                          ((fc0', fp0') :: FF_tail)).
              etransitivity.
              { apply Permutation_map. exact Hperm_FF. }
              rewrite map_swap_combine by exact Hcc_lentl.
              (* combine (ptl++ptl') (map tl (cil++cil')) *)
              rewrite map_app.
              rewrite combine_app_eq by (rewrite length_map; congruence).
              reflexivity. }

            (* Step 7: reduce LHS [spaced_get] using head-false. *)
            rewrite spaced_get_cons_false.

            (* Step 8: reduce RHS using lookup_one'_cons_false. *)
            rewrite lookup_one'_cons_false.

            (* Now align RHS list_Mmap with IHx. *)
            (* For each (pt, b::tl) ∈ combine ptl cil ++ combine ptl' cil',
               lookup_one' (p::x') (pt, false::tl) = lookup_one' x' (pt, tl).
               We push this through with a helper. *)
            assert (Hrhs_eq :
                      list_Mmap (lookup_one' (p :: x'))
                        (combine ptl cil ++ combine ptl' cil')
                      = list_Mmap (lookup_one' x')
                          (combine ptl (map (@tl _) cil)
                             ++ combine ptl' (map (@tl _) cil'))).
            { (* Each ci in cil has head=false (from Hall_false). *)
              assert (Hcil_hd : Forall (fun l => hd false l = false) cil).
              { eapply Forall_impl with (P := fun l => length l = S (length x')
                                                       /\ hd false l = false);
                  [intuition|].
                eapply Forall_app in Hall_false as [Hcc1 _]. exact Hcc1. }
              assert (Hcil'_hd : Forall (fun l => hd false l = false) cil').
              { eapply Forall_impl with (P := fun l => length l = S (length x')
                                                       /\ hd false l = false);
                  [intuition|].
                eapply Forall_app in Hall_false as [_ Hcc2]. exact Hcc2. }
              (* General helper: list_Mmap (lookup_one' (p::x')) (combine ptl cil)
                 = list_Mmap (lookup_one' x') (combine ptl (map tl cil))
                 when all entries of cil have head false. *)
              assert (Hgeneric : forall (cil_ : list (list bool)) (ptl_ : list (@pos_trie' A)),
                         length cil_ = length ptl_ ->
                         Forall (fun l => hd false l = false) cil_ ->
                         list_Mmap (lookup_one' (p :: x')) (combine ptl_ cil_)
                         = list_Mmap (lookup_one' x')
                             (combine ptl_ (map (@tl _) cil_))).
              { clear.
                intro cil_; induction cil_ as [|c cil_ IH];
                  intros [|pt ptl_] Hlen Hhd;
                  try (cbn in Hlen; discriminate);
                  cbn [combine map]; [reflexivity..|].
                pose proof (Forall_inv Hhd) as Hc_hd.
                pose proof (Forall_inv_tail Hhd) as Hhd_tail.
                cbn [list_Mmap].
                rewrite (lookup_one'_cons_hd_false _ _ _ _ Hc_hd).
                destruct (lookup_one' x' (pt, tl c)) as [v|]; [|reflexivity].
                rewrite IH by (cbn in Hlen; Lia.lia || assumption).
                reflexivity. }
              rewrite ?list_Mmap_app.
              rewrite (Hgeneric _ _ Hcil_ptl_len Hcil_hd).
              rewrite (Hgeneric _ _ Hcil'_ptl'_len Hcil'_hd).
              reflexivity. }
            rewrite Hrhs_eq.

            (* Step 9: apply IHx with parameters (fuel', x', fc0', fp0', f_c, f_p, [], []). *)
            (* Length of fc0'. *)
            assert (Hfc0'_len : length fc0' = length x').
            { pose proof (Forall_inv Hperm_lens) as Hfc0'.
              cbn [fst] in Hfc0'. exact Hfc0'. }

            assert (Hf_c_len_x : Forall (fun l => length l = length x') f_c).
            { unfold f_c; rewrite map_app; cbn [map].
              apply Forall_app; split.
              - eapply Forall_map.
                eapply Forall_impl; [|exact (Forall_inv_tail Hperm_lens)].
                intros pq Hpq; cbn [fst] in *. exact Hpq.
              - constructor; [exact Hci0_len | constructor]. }

            assert (Hfp0'_d :
                      Is_true (has_depth' (length (filter id fc0')) fp0')).
            { (* head pair of Hperm_dep. *)
              clear -Hperm_dep.
              cbn [map] in Hperm_dep. inversion Hperm_dep; subst.
              assumption. }

            assert (Hf_cp_d :
                      Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt))
                              f_c f_p).
            { unfold f_c, f_p; rewrite ?map_app; cbn [map].
              apply Forall2_app.
              - (* tail of Hperm_dep *)
                cbn [map] in Hperm_dep.
                inversion Hperm_dep as [|a b la lb Ha Htail]; subst.
                exact Htail.
              - constructor; [exact Hpt0_d | constructor]. }

            specialize (IHx fuel' fc0' fp0' f_c f_p [] []
                            Hfuel' Hfc0'_len Hf_c_len_x (Forall_nil _)
                            Hf_cp_len eq_refl
                            Hfp0'_d Hf_cp_d (Forall2_nil _)).
            cbn [combine app] in IHx.
            rewrite ?app_nil_r in IHx.

            (* Step 10: align fold sides via Hperm_cil. *)
            (* IHx's bool-list fold is [fold_left ... f_c fc0']. *)
            (* Our LHS bool-list fold is [fold_left ... (map tl (cil++cil')) ci0']. *)
            (* These are equal by [fold_left_orb_combine_perm_full] using Hperm_cil. *)
            assert (Hfold_eq :
                      fold_left (fun acc l => map2 orb (combine l acc))
                                (map (@tl _) (cil ++ cil')) ci0'
                      = fold_left (fun acc l => map2 orb (combine l acc))
                                  f_c fc0').
            { apply (fold_left_orb_combine_perm_full _ _ _ _).
              - constructor; [reflexivity|].
                eapply Forall_impl; [|exact Hmap_tl_len].
                intros l Hl. rewrite Hl, Hci0_len. reflexivity.
              - apply Permutation_sym. exact Hperm_cil. }
            rewrite Hfold_eq.

            (* Step 11: rewrite LHS using IHx *)
            etransitivity; [exact IHx|].

            (* Step 12: Apply Hperm_lookup to align. *)
            apply (list_Mmap_lookup_fold_perm (lookup_one' x') _ _ _ _ Hperm_lookup).
          }
        * (* TF non-empty: contradiction with [Hany], since this branch
             assumes no entry of [cil ++ cil'] has [hd false l = true],
             yet a non-empty TF would witness exactly such an entry. *)
          exfalso.
          unfold TF in HTF; unfold Lall in HTF.
          rewrite (filter_combine_no_true_head _ _ Hany) in HTF.
          cbn in HTF; discriminate.
  Qed.

  (* The original lemma is the cil'=ptl'=[] specialisation. *)
  Lemma pt_spaced_intersect'_spec
    (fuel : nat) (x : list positive)
    (ci0 : list bool) (pt0 : @pos_trie' A)
    (cil : list (list bool)) (ptl : list (@pos_trie' A))
    : (fuel > length x)%nat ->
      length ci0 = length x ->
      Forall (fun l => length l = length x) cil ->
      length cil = length ptl ->
      Is_true (has_depth' (length (filter id ci0)) pt0) ->
      Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil ptl ->
      spaced_get x (fold_left (fun acc (l : list bool) => map2 orb (combine l acc))
                              cil ci0,
                    pt_spaced_intersect' merge fuel cil ptl ci0 [] pt0 [])
      = match lookup_one' x (pt0, ci0),
              list_Mmap (lookup_one' x) (combine ptl cil) with
        | Some e, Some es => Some (fold_left merge es e)
        | _, _ => None
        end.
  Proof.
    intros Hfuel Hci0 Hcil Hcil_ptl Hpt0 Hcil_ptl_d.
    pose proof (pt_spaced_intersect'_spec_general
                  fuel x ci0 pt0 cil ptl [] []
                  Hfuel Hci0 Hcil
                  (Forall_nil _)
                  Hcil_ptl
                  eq_refl
                  Hpt0 Hcil_ptl_d
                  (Forall2_nil _)) as Hgen.
    rewrite app_nil_r in Hgen.
    cbn [combine] in Hgen.
    rewrite app_nil_r in Hgen.
    exact Hgen.
  Qed.

  (* ------------------------------------------------------------ *)
  (* Bookkeeping helpers used to lift [pt_spaced_intersect'_spec]
     to [pt_spaced_intersect_spec]. *)

  Lemma list_Mmap_id_Some_inv {T} (l : list (option T)) (lr : list T) :
    list_Mmap id l = Some lr -> l = map Some lr.
  Proof.
    revert lr; induction l as [|a l IH]; cbn; intros lr Hmm.
    - injection Hmm as <-. reflexivity.
    - destruct a as [t|]; cbn in Hmm; [|discriminate].
      destruct (list_Mmap id l) as [l'|] eqn:Heq; cbn in Hmm; [|discriminate].
      injection Hmm as <-. cbn. f_equal. apply IH; reflexivity.
  Qed.

  Lemma list_Mmap_id_None_inv_local {T} (l : list (option T)) :
    list_Mmap id l = None ->
    exists i, nth_error l i = Some None.
  Proof.
    induction l as [|a l IH]; cbn; [discriminate|].
    intros Hmm; destruct a as [t|].
    - destruct (list_Mmap id l) as [l'|] eqn:Heq; cbn in Hmm; [discriminate|].
      destruct (IH eq_refl) as [i Hi]. exists (S i); exact Hi.
    - exists 0; reflexivity.
  Qed.

  Lemma lookup_one_None_propagates (x : list positive)
    (l : list (@pos_trie A * list bool)) :
    (exists p, In p l /\ fst p = None) ->
    list_Mmap (lookup_one x) l = None.
  Proof.
    induction l as [|p l IH]; intros [q [Hin Hq_None]]; cbn in *; [contradiction|].
    destruct Hin as [<- | Hin].
    - unfold lookup_one, spaced_get; cbn.
      rewrite Hq_None. cbn. reflexivity.
    - destruct (lookup_one x p) as [v|] eqn:Hp; cbn; [|reflexivity].
      rewrite IH; [reflexivity|]. exists q. split; assumption.
  Qed.

  Lemma list_Mmap_lookup_combine_some
    (x : list positive)
    (ptl : list (@pos_trie' A)) (cil : list (list bool)) :
    list_Mmap (lookup_one x) (combine (map Some ptl) cil)
    = list_Mmap (lookup_one' x) (combine ptl cil).
  Proof.
    revert cil; induction ptl as [|pt ptl IH]; intros [|ci cil]; cbn; try reflexivity.
    unfold lookup_one at 1, spaced_get, lookup_one' at 1; cbn.
    destruct (pt_get' pt (map fst (filter snd (combine x ci)))) as [v|]; cbn; [|reflexivity].
    rewrite IH. reflexivity.
  Qed.

  Lemma combined_bools_via_split
    (tries : ne_list (@pos_trie A * list bool))
    (ptl_opt : list (@pos_trie A)) (cil : list (list bool)) :
    split (snd tries) = (ptl_opt, cil) ->
    combined_bools tries
    = List.fold_left (fun acc l => map2 orb (combine l acc)) cil (snd (fst tries)).
  Proof.
    intros Hsplit. unfold combined_bools.
    pose proof (split_length_l (snd tries)) as Hll.
    pose proof (split_length_r (snd tries)) as Hlr.
    rewrite Hsplit in Hll, Hlr; cbn in Hll, Hlr.
    apply split_combine in Hsplit.
    rewrite <- Hsplit. clear Hsplit.
    assert (Hlen : length ptl_opt = length cil) by congruence.
    clear Hll Hlr.
    generalize (snd (fst tries)).
    revert cil Hlen; induction ptl_opt as [|p ptl IH]; intros [|c cil] Hlen acc;
      cbn in *; try reflexivity; try discriminate.
    apply IH. Lia.lia.
  Qed.

  (* Extract length-correctness for [cil] after splitting the tail. *)
  Lemma Forall_wf_input_split (x : list positive)
    (tail : list (@pos_trie A * list bool))
    (ptl_opt : list (@pos_trie A)) (cil : list (list bool)) :
    split tail = (ptl_opt, cil) ->
    Forall (wf_input x) tail ->
    Forall (fun l => length l = length x) cil
    /\ Forall (fun (q : @pos_trie A * list bool) =>
                 match fst q with
                 | Some pt' => Is_true (has_depth' (length (filter id (snd q))) pt')
                 | None => True
                 end) tail.
  Proof.
    revert ptl_opt cil; induction tail as [|p tail IH]; intros ptl_opt cil Hsplit Hwf.
    - injection Hsplit as <- <-. split; constructor.
    - destruct p as [pt ci]; cbn in Hsplit.
      destruct (split tail) as [pt' ci'] eqn:Heq.
      injection Hsplit as <- <-.
      inversion Hwf as [|? ? Hp Htail]; subst.
      destruct Hp as [Hci_len Hpt_d].
      specialize (IH _ _ eq_refl Htail). destruct IH as [Hcil_len Hd_tail].
      split; constructor; cbn; auto.
  Qed.

  (* Convert wf_input depth conditions on [combine (map Some ptl) cil] into
     a [Forall2] depth condition on [cil] and [ptl]. *)
  Lemma Forall2_depth_from_Forall
    (cil : list (list bool)) (ptl : list (@pos_trie' A)) :
    length cil = length ptl ->
    Forall (fun (q : @pos_trie A * list bool) =>
              match fst q with
              | Some pt' => Is_true (has_depth' (length (filter id (snd q))) pt')
              | None => True
              end) (combine (map Some ptl) cil) ->
    Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil ptl.
  Proof.
    revert ptl; induction cil as [|c cil IH]; intros [|p ptl] Hlen Hall; cbn in *;
      try discriminate; try constructor.
    - inversion Hall; subst; cbn in *. assumption.
    - apply IH; [Lia.lia|]. inversion Hall; subst; cbn in *. assumption.
  Qed.

  (* ------------------------------------------------------------ *)
  Theorem pt_spaced_intersect_correct
    (tries : ne_list (@pos_trie A * list bool)) (x : list positive) :
    wf_tries x tries -> pt_spaced_intersect_spec tries x.
  Proof.
    intros [Hwf_head Hwf_tail].
    destruct tries as [[pt0_opt ci0] tail]; cbn [fst snd] in *.
    destruct Hwf_head as [Hci0_len Hpt0_depth].
    unfold pt_spaced_intersect_spec, pt_spaced_intersect; cbn [fst snd].

    (* Compute split *)
    destruct (split tail) as [ptl_opt cil] eqn:Hsplit.
    cbn [fst snd] in *.
    pose proof (split_combine tail Hsplit) as Htail_eq.
    assert (Hlen_pc : length ptl_opt = length cil).
    { pose proof (split_length_l tail) as Hll.
      pose proof (split_length_r tail) as Hlr.
      rewrite Hsplit in Hll, Hlr. cbn in Hll, Hlr. congruence. }

    (* Rewrite combined_bools in terms of [cil] and [ci0]. *)
    erewrite combined_bools_via_split with (ptl_opt := ptl_opt) (cil := cil)
      by (cbn [fst snd]; exact Hsplit).
    cbn [fst snd].

    (* Extract Forall facts on cil and a per-element depth fact on tail. *)
    destruct (Forall_wf_input_split _ _ _ _ Hsplit Hwf_tail)
      as [Hcil_len Htail_depth].

    (* Case on pt0_opt *)
    destruct pt0_opt as [pt0|] eqn:Hpt0_eq.
    2: { (* pt0 = None: both sides are None *)
      cbn [Mbind].
      unfold lookup_one at 1, spaced_get; cbn [fst snd pt_get].
      reflexivity.
    }

    (* pt0 = Some pt0: case on whether all tail tries are Some *)
    cbn [Mbind option_monad].
    destruct (list_Mmap (M:=option) (B:=@pos_trie' A) id ptl_opt) as [ptl|] eqn:Hmmap.
    2: { (* Some tail trie is None: both sides are None *)
      apply list_Mmap_id_None_inv_local in Hmmap.
      destruct Hmmap as [i Hi].
      (* The corresponding pair (None, _) is in tail = combine ptl_opt cil *)
      assert (Hin_tail : exists p, In p tail /\ fst p = None).
      { rewrite <- Htail_eq.
        clear -Hi Hlen_pc.
        revert i cil Hlen_pc Hi; induction ptl_opt as [|p ptl IH]; intros i cil Hlen Hi.
        - destruct i; cbn in Hi; discriminate.
        - destruct cil as [|c cil]; cbn in Hlen; [discriminate|].
          destruct i; cbn in *.
          + injection Hi as ->. exists (None, c); split; [left; reflexivity|reflexivity].
          + destruct (IH i cil ltac:(Lia.lia) Hi) as [q [Hq_in Hq_None]].
            exists q; split; [right; assumption|assumption]. }
      rewrite lookup_one_None_propagates.
      2: { destruct Hin_tail as [p [Hp_in Hp_None]].
           exists p; split; [right; assumption|assumption]. }
      unfold spaced_get; cbn [fst snd pt_get]. reflexivity.
    }

    (* Both pt0 and all tail tries are Some. Apply the lemma. *)
    cbn [Mbind id].
    pose proof (list_Mmap_id_Some_inv _ _ Hmmap) as Hptl_opt_eq.

    (* Set up the lemma's hypotheses *)
    assert (Hfuel : (S (length ci0) > length x)%nat) by Lia.lia.
    assert (Hcil_len_x : Forall (fun l => length l = length x) cil) by exact Hcil_len.
    assert (Hcil_ptl_len : length cil = length ptl).
    { rewrite Hptl_opt_eq, length_map in Hlen_pc. Lia.lia. }
    assert (Hpt0_d : Is_true (has_depth' (length (filter id ci0)) pt0))
      by exact Hpt0_depth.
    assert (Htail_dep : Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt))
                                cil ptl).
    { apply Forall2_depth_from_Forall; [Lia.lia|].
      assert (Hcombine_eq : combine (map Some ptl) cil = tail).
      { rewrite <- Hptl_opt_eq. exact Htail_eq. }
      rewrite Hcombine_eq. exact Htail_depth. }

    (* Apply the lemma. *)
    pose proof (pt_spaced_intersect'_spec _ x ci0 pt0 cil ptl Hfuel Hci0_len
                                          Hcil_len_x Hcil_ptl_len Hpt0_d Htail_dep)
      as Hlemma.
    (* Massage the LHS list_Mmap into the form used by Hlemma's RHS. *)
    rewrite <- Htail_eq, Hptl_opt_eq.
    cbn [list_Mmap].
    rewrite list_Mmap_lookup_combine_some.

    (* Replace the Mbind/lookup_one structure with the matched lookups
       form by unfolding everything to pt_get'. *)
    unfold lookup_one, spaced_get; cbn [fst snd pt_get].

    destruct (pt_get' pt0 (map fst (filter snd (combine x ci0)))) as [e|] eqn:Hheadlk;
      cbn [Mbind option_monad].
    2: { (* head lookup is None *)
      etransitivity; [exact Hlemma|].
      change (lookup_one' x (pt0, ci0)) with
        (pt_get' pt0 (map fst (filter snd (combine x ci0)))).
      rewrite Hheadlk. reflexivity. }
    destruct (list_Mmap (lookup_one' x) (combine ptl cil)) as [es|] eqn:Htaillk;
      cbn.
    - (* both lookups succeed *)
      etransitivity; [exact Hlemma|].
      change (lookup_one' x (pt0, ci0)) with
        (pt_get' pt0 (map fst (filter snd (combine x ci0)))).
      rewrite Hheadlk. reflexivity.
    - (* tail lookup is None *)
      etransitivity; [exact Hlemma|].
      change (lookup_one' x (pt0, ci0)) with
        (pt_get' pt0 (map fst (filter snd (combine x ci0)))).
      rewrite Hheadlk. reflexivity.
  Qed.

End PtSpacedIntersectSpec.
