Require Import NArith Tries.Canonical Lists.List.
Import ListNotations.

From Utils Require Import Utils Monad.
From Utils Require Import PosListMap.

#[local] Notation ne_list A := (A * list A)%type.

Section PtSpacedIntersectSpec.
  Context {A : Type}.
  Context `{WithDefault A}.
  Context (merge : A -> A -> A).

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
    snd tries <> [] /\ wf_input x (fst tries) /\ Forall (wf_input x) (snd tries).

  (* ------------------------------------------------------------ *)
  (* Auxiliary lemma about the recursive helper [pt_spaced_intersect'].
     Given well-formed inputs as set up by [pt_spaced_intersect] (after
     stripping the [Some] wrappers and splitting the tail), the lookup of
     [x] in the resulting trie under the OR-combined bool pattern equals
     the merged fold of the per-trie lookups, or [None] if any input
     lookup misses. *)
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
    intros [Htail_ne [Hwf_head Hwf_tail]].
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
    assert (Hfuel : (S (length (hd [] cil)) > length x)%nat).
    { destruct cil as [|c cil']; cbn.
      - (* cil = [], so tail = [], contradicting Htail_ne *)
        exfalso. apply Htail_ne. rewrite <- Htail_eq.
        cbn in Hlen_pc. destruct ptl_opt; [reflexivity|cbn in Hlen_pc; discriminate].
      - inversion Hcil_len; subst. Lia.lia. }
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
