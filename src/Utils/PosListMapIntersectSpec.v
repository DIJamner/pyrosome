Require Import NArith Tries.Canonical Lists.List.
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
    revert fuel ci0 pt0 cil ptl.
    induction x as [|p x' IHx];
      intros fuel ci0 pt0 cil ptl
             Hfuel Hci0_len Hcil_len Hcil_ptl_len Hpt0_d Hcil_ptl_d.
    - (* Base case: x = [] *)
      destruct ci0 as [|? ?]; [|cbn in Hci0_len; discriminate].
      destruct fuel as [|fuel']; [Lia.lia|].
      cbn in Hpt0_d.
      destruct pt0 as [a|m]; [|contradiction].
      assert (Hcil_all_nil : Forall (fun l => l = []) cil).
      { eapply Forall_impl; [|exact Hcil_len].
        intros l Hl; cbn in Hl. apply length_zero_iff_nil. exact Hl. }
      assert (Hptl_leaf : Forall (fun pt => Is_true (has_depth' 0 pt)) ptl).
      { revert Hcil_ptl_d Hcil_all_nil. clear.
        revert ptl. induction cil as [|c cil IH]; intros [|pt ptl] Hd Hcil;
          inversion Hd; subst; constructor.
        - inversion Hcil; subst c. cbn in *. assumption.
        - apply IH; [assumption|]. inversion Hcil; assumption. }
      assert (Hptl_all : all (fun t => Is_true (has_depth' 0 t)) ptl).
      { clear - Hptl_leaf. induction ptl; cbn; auto.
        inversion Hptl_leaf; subst; split; auto. }
      cbn [pt_spaced_intersect'].
      rewrite (fold_left_map2_orb_all_nil _ Hcil_all_nil).
      rewrite (list_Mmap_lookup_one'_nil _ _ Hcil_ptl_len Hcil_all_nil Hptl_leaf).
      change (lookup_one' [] (pos_trie_leaf a, []))
        with (@Some A a).
      unfold spaced_get; cbn [fst snd pt_get].
      cbn [filter combine map].
      cbn [pt_get'].
      rewrite (leaf_intersect_correct _ a ptl Hptl_all).
      cbn [map fold_left].
      reflexivity.
    - (* Inductive case: x = p :: x'.  Still admitted; below is what
         finishing it actually entails.

         Setup:
           destruct ci0 = b :: ci0' (Hci0_len),
           destruct fuel = S fuel' (Hfuel).
         The inner [partition_tries [] [] _] is the identity, so the
         function's internal partition is just [partition_tries cil ptl
         initial] with [initial] determined by [b].  Use
         [PosListMap.partition_tries_spec] (proven, [Qed]) to rewrite
         that into [partition_result_of_lists (false_filter ++ false_lists
         initial) (true_filter ++ true_lists initial)] where false/true
         filters are [rev (map (tl, snd) (filter (head=…) (combine cil
         ptl)))].

         Two subcases, on the partition result:

         (A) [just_false_part]: occurs iff [b = false] AND no entry of
             [cil] has a true head.  Then the recursive call is
             [pt_spaced_intersect' fuel' f_c f_p fc0 [] fp0 []] —
             cil' = ptl' = [], so IHx applies directly at x'.  But the
             new (fc0, fp0) is the LAST false-headed entry and (f_c, f_p)
             holds the rest in REVERSE order with the original (ci0', pt0)
             appended at the end.  Reconciling LHS and IH-RHS requires:
               (i)  [lookup_one' (p::x') (pt, false :: ci) = lookup_one' x'
                    (pt, ci)] (since [filter snd] drops the false slot);
               (ii) [fold_left orb_combine] is permutation-invariant
                    (fold of OR is comm/assoc), so the combined-bools on
                    x' agree across the reordering;
               (iii) [fold_left merge] is permutation-invariant given
                     [merge_comm]/[merge_assoc] above, so the reordered
                     left-fold equals the original.

         (B) [have_true_part]: occurs iff [b = true] OR some [cil] entry
             has a true head.  The recursive call goes through
             [list_intersect (fun fwd => pt_spaced_intersect' fuel' other_cil
             other_tries t_ci0 (true_cil/rev)) (proj t_pt0) (map proj
             true_tries)].  Use [TrieMap.list_intersect_correct] to push
             [PTree.get' p _] through the [list_intersect].  THE OBSTACLE:
             that recursive call passes [cil' = true_cil] and [ptl' =]
             children-of-true-tries — both NON-EMPTY in general — so this
             very lemma's IH (which fixes [cil' = ptl' = []]) does not
             apply.  Finishing (B) requires a stronger variant of this
             lemma whose conclusion is over [combine ptl cil ++ combine
             ptl' cil'] (i.e. the "extra" arguments behave as additional
             input tries).  The leaf base case extends cleanly because
             [leaf_intersect (leaf_intersect a ptl) ptl' = fold_left merge
             (leaf_values (ptl ++ ptl')) a]; the inductive case follows
             the same partition structure but with [partition_tries] applied
             twice.  That generalised lemma — call it
             [pt_spaced_intersect'_spec_general] — should be proven first,
             with the present statement an immediate corollary
             ([cil' = ptl' = []]).

         Note: as documented in the section's [merge_comm]/[merge_assoc]
         hypotheses, the lemma is FALSE without those — the partition step
         in subcase (A) literally swaps the head and last input. *)
  Admitted.

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
