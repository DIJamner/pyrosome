(* Scratch development for the pt_spaced_intersect result-depth obligation.
   Imports the built .vo so all existing helpers are in scope; lemmas proved
   here get transplanted into PosListMap.v / PosListMapIntersectSpec.v. *)

From Stdlib Require Import NArith Lists.List.
Import ListNotations.
From Stdlib Require Import Permutation.
From Tries Require Import Canonical.
From Utils Require Import Utils Monad PosListMap PosListMapIntersectSpec.

Set Implicit Arguments.

#[local] Notation ne_list A := (A * list A)%type.

Section Depth.
  Context {A : Type} `{WithDefault A}.
  Context (merge : A -> A -> A).

  Notation pos_trie' := (@pos_trie' A).
  Notation has_depth' := (@has_depth' A).

  (* ---- L1: introduction direction for [has_depth' (S n) (pos_trie_node m)]. *)
  Lemma has_depth'_node_intro (n : nat) (m : PTree.tree' pos_trie') :
    (forall p v, PTree.get' p m = Some v -> Is_true (has_depth' n v)) ->
    Is_true (has_depth' (S n) (pos_trie_node m)).
  Proof.
    intros Hentry. cbn [has_depth'].
    change (Is_true (TrieMap.trie_fold' (fun res (_:positive) (v:pos_trie') => res && has_depth' n v) true m xH)).
    assert (Hgen : forall (mm : PTree.tree' pos_trie') (revnum : positive),
      (forall p v, PTree.get' p mm = Some v -> Is_true (has_depth' n v)) ->
      Is_true (TrieMap.trie_fold' (fun res (_:positive) (v:pos_trie') => res && has_depth' n v) true mm revnum)).
    { intros mm.
      induction mm as [mm IH | a | a mm IH | mm IH | mm1 IH1 mm2 IH2 | mm IH a | mm1 IF1 a mm2 IF2];
        intros revnum Hentry'; cbn.
      - apply IH. intros p v Hg. apply (Hentry' (xI p) v). cbn. exact Hg.
      - apply (Hentry' xH a). reflexivity.
      - rewrite trie_fold'_andb_factor. apply andb_prop_intro. split.
        + apply (Hentry' xH a). reflexivity.
        + apply IH. intros p v Hg. apply (Hentry' (xI p) v). cbn. exact Hg.
      - apply IH. intros p v Hg. apply (Hentry' (xO p) v). cbn. exact Hg.
      - rewrite trie_fold'_andb_factor. apply andb_prop_intro. split.
        + apply IH2. intros p v Hg. apply (Hentry' (xI p) v). cbn. exact Hg.
        + apply IH1. intros p v Hg. apply (Hentry' (xO p) v). cbn. exact Hg.
      - rewrite trie_fold'_andb_factor. apply andb_prop_intro. split.
        + apply (Hentry' xH a). reflexivity.
        + apply IH. intros p v Hg. apply (Hentry' (xO p) v). cbn. exact Hg.
      - rewrite trie_fold'_andb_factor. rewrite trie_fold'_andb_factor.
        apply andb_prop_intro. split.
        + apply andb_prop_intro. split.
          * apply (Hentry' xH a). reflexivity.
          * apply IF2. intros p v Hg. apply (Hentry' (xI p) v). cbn. exact Hg.
        + apply IF1. intros p v Hg. apply (Hentry' (xO p) v). cbn. exact Hg. }
    apply Hgen. exact Hentry.
  Qed.

  (* ---- L2a: folding a list into a zero accumulator absorbs the head acc. *)
  Definition comb (L : list (list bool)) (acc : list bool) : list bool :=
    fold_left (fun a (l : list bool) => map2 orb (combine l a)) L acc.

  Lemma comb_cons_zero (L : list (list bool)) (acc : list bool) :
    comb L acc = comb (acc :: L) (repeat false (length acc)).
  Proof.
    unfold comb. cbn [fold_left].
    replace (map2 orb (combine acc (repeat false (length acc)))) with acc; [reflexivity|].
    clear. induction acc as [|b acc IH]; cbn; [reflexivity|].
    unfold map2 in *. cbn. rewrite Bool.orb_false_r. f_equal. exact IH.
  Qed.

  (* ---- L2: permutation invariance over the full (acc::L) collection. *)
  Lemma comb_perm (L1 L2 : list (list bool)) (acc1 acc2 : list bool) :
    Forall (fun l => length l = length acc1) (acc1 :: L1) ->
    Permutation (acc1 :: L1) (acc2 :: L2) ->
    comb L1 acc1 = comb L2 acc2.
  Proof.
    intros Hlen Hperm.
    assert (Hlen2 : length acc2 = length acc1).
    { assert (Hin : In acc2 (acc1 :: L1)).
      { apply (Permutation_in acc2 (Permutation_sym Hperm)). left. reflexivity. }
      rewrite Forall_forall in Hlen. apply Hlen. exact Hin. }
    rewrite (comb_cons_zero L1 acc1).
    rewrite (comb_cons_zero L2 acc2).
    rewrite Hlen2.
    apply fold_left_orb_combine_Permutation; [|exact Hperm].
    rewrite repeat_length. exact Hlen.
  Qed.

  Context (merge_comm : forall a b, merge a b = merge b a).
  Context (merge_assoc : forall a b c, merge a (merge b c) = merge (merge a b) c).

  (* ---- inversion of rectangular_trie_list into the IHx-shaped hyps. *)
  Lemma rectangular_trie_list_inv (n : nat) (cs : list (list bool)) (ts : list pos_trie') :
    rectangular_trie_list n cs ts ->
    Forall (fun l => length l = n) cs
    /\ Forall2 (fun c t => Is_true (has_depth' (length (filter id c)) t)) cs ts
    /\ length cs = length ts.
  Proof.
    intro Hr0. revert ts Hr0; induction cs as [|c cs IH]; intros [|t ts] Hr;
      cbn in Hr; try contradiction.
    - repeat split; constructor.
    - destruct Hr as [ [Hd Hlen] Hrest ].
      specialize (IH ts Hrest). destruct IH as [HF [HF2 Hl]].
      repeat split; try constructor; auto.
      cbn; rewrite Hl; reflexivity.
  Qed.

  (* ---- L2.5 (crux): the bool-lists of a partition output are a permutation of
     the original tails plus the single accumulator bool-list [ci0'].

     This is what makes both recursion-combined-bools equal to
     [comb (map tl cc) ci0'] (via [comb_perm]).  The hypothesis
       [map fst (true_lists init) ++ map fst (false_lists init) = [ci0']]
     holds for both partition initial accumulators we use:
       - have_true_part [] [] ci0' pt0 [] []  (true_lists = [(ci0',pt0)], false=[])
       - just_false_part ci0' pt0 [] []        (false_lists = [(ci0',pt0)], true=[])

     PROOF: rewrite [true_lists]/[false_lists] of the partition output via
     [partition_tries_true_lists]/[partition_tries_false_lists] (width = length x',
     i.e. cc all length [S (length x')]); then it is pure list/Permutation algebra:
       map fst (true_filter ++ true_lists init) ++ map fst (false_filter ++ false_lists init)
     where map fst true_filter  = rev (map tl (filter (hd false) cc))  and
           map fst false_filter = rev (map tl (filter (negb∘hd false) cc)).
     [filter P cc ++ filter (negb∘P) cc] is a permutation of cc (filter-complement),
     [map tl] distributes, [rev] is a permutation, and the [init] piece contributes
     exactly [ci0'].  Helpers likely needed (search/derive):
       - map fst (filter (fun p => hd false (fst p)) (combine cc pp)) = filter (hd false) cc
         (length cc = length pp); map fst (combine cc pp) = cc.
       - filter_complement_permutation (used in the commented partition_tries_ptl_perm). *)
  Lemma part_bool_lists_perm (width : nat)
    (cc : list (list bool)) (pp : list pos_trie')
    (init : partition_result) (ci0' : list bool) :
    length cc = length pp ->
    all (fun l => length l = S width) cc ->
    map fst (true_lists init) ++ map fst (false_lists init) = [ci0'] ->
    Permutation
      (map fst (true_lists (partition_tries cc pp init))
         ++ map fst (false_lists (partition_tries cc pp init)))
      (ci0' :: map (@tl _) cc).
  Proof.
    intros Hlen Hall Hinit.
    rewrite (partition_tries_true_lists merge width cc pp init Hall Hlen).
    rewrite (partition_tries_false_lists merge width cc pp init Hall Hlen).
    cbv zeta.
    rewrite !map_app.
    rewrite !map_rev.
    rewrite !map_map.
    cbn [fst].
    assert (Hgen : forall (P : list bool -> bool) (cc0 : list (list bool)) (pp0 : list pos_trie'),
      length cc0 = length pp0 ->
      map (fun x : list bool * pos_trie' => tl (fst x)) (filter (fun p => P (fst p)) (combine cc0 pp0))
      = map (tl (A:=bool)) (filter P cc0))
      by (intros P cc0; induction cc0 as [|c cc0 IHcc]; intros [|p pp0] Hl; cbn in *; try discriminate; try reflexivity;
          injection Hl as Hl; case_match; cbn; rewrite IHcc by assumption; reflexivity).
    rewrite !Hgen by assumption.
    rewrite (Hgen (fun c => negb (hd false c)) cc pp Hlen).
    assert (Hrearr : forall {T} (a b c d : list T), Permutation ((a ++ b) ++ c ++ d) ((b ++ d) ++ (a ++ c)))
      by (intros T a b c d;
          rewrite <- (app_assoc a b (c ++ d));
          rewrite <- (app_assoc b d (a ++ c));
          rewrite (Permutation_app_swap_app a b (c++d));
          apply Permutation_app_head;
          rewrite (Permutation_app_comm a (c ++ d));
          rewrite <- (app_assoc c d a);
          apply (Permutation_app_rot c d a)).
    eapply Permutation_trans.
    - apply (Hrearr _ (rev (map (tl (A:=bool)) (filter (hd false) cc)))
                      (map fst (true_lists init))
                      (rev (map (tl (A:=bool)) (filter (fun c : list bool => negb (hd false c)) cc)))
                      (map fst (false_lists init))).
    - rewrite Hinit. cbn [app]. apply perm_skip.
      rewrite <- !map_rev.
      rewrite <- map_app.
      apply Permutation_map.
      eapply Permutation_trans; [ apply Permutation_app; apply Permutation_rev | ].
      rewrite !rev_involutive.
      apply filter_complement_permutation.
  Qed.

  (* ---- L3: the main structural depth lemma (mirrors
     pt_spaced_intersect'_spec_general, tracking has_depth' only).

     VALIDATED PREFIX (already machine-checked in dev, keep verbatim):
       revert fuel ci0 pt0 cil ptl cil' ptl'.
       induction x as [|p x' IHx]; intros ... .
       - (* base x=[] : result is a leaf, combined-bools = [], depth 0 *)
         destruct ci0 as [|? ?]; [|cbn in Hci0_len; discriminate].
         destruct fuel as [|fuel']; [Lia.lia|].
         cbn in Hpt0_d. destruct pt0 as [a|m]; [|contradiction].
         cbn [pt_spaced_intersect'].
         assert (Hcomb_nil : comb (cil ++ cil') [] = []).
         { unfold comb. generalize (cil ++ cil') as LL. clear.
           induction LL as [|l LL IH]; cbn; [reflexivity|].
           rewrite <- IH at 2. f_equal. destruct l; reflexivity. }
         rewrite Hcomb_nil. cbn [filter length has_depth']. exact I.
       - (* inductive x=p::x' *)
         destruct ci0 as [|b ci0']; [cbn in Hci0_len; discriminate|].
         destruct fuel as [|fuel']; [cbn in Hfuel; Lia.lia|].
         cbn [Datatypes.length] in Hci0_len, Hfuel. injection Hci0_len as Hci0_len.
         assert (Hfuel' : (fuel' > length x')%nat) by Lia.lia.
         assert (Hrect : rectangular_trie_list (S (length x')) cil ptl)
           by (eapply rectangular_trie_list_of_Forall2; [exact Hcil_len|exact Hcil_ptl_d]).
         assert (Hrect' : rectangular_trie_list (S (length x')) cil' ptl')
           by (eapply rectangular_trie_list_of_Forall2; [exact Hcil'_len|exact Hcil'_ptl'_d]).
         cbn [pt_spaced_intersect'].
       (* GOAL NOW (state 11334):
            match (match partition_tries cil' ptl'
                       (partition_tries cil ptl (if b then have_true_part [] [] ci0' pt0 [] []
                                                       else just_false_part ci0' pt0 [] []))
                   with just_false_part jci0 jpt0 joc jot =>
                          pt_spaced_intersect' merge fuel' joc jot jci0 [] jpt0 []
                      | have_true_part foc fot tci0 tpt0 tcil tptl =>
                          option_map pos_trie_node (list_intersect (callback) (proj tpt0) (map proj tptl))
                   end)
            with Some r => Is_true (has_depth' (length (filter id (comb (cil++cil') (b::ci0')))) r)
               | None => True end *)

     REMAINING PLAN:
       Let cc := cil++cil', pp := ptl++ptl', init := (if b then have_true_part [] [] ci0' pt0 [] []
                                                      else just_false_part ci0' pt0 [] []).
       (1) assert Hrect_app : rectangular_trie_list (S (length x')) cc pp
             by (apply rectangular_trie_list_app; assumption).
       (2) rewrite (partition_tries_app (S (length x')) cil cil' ptl ptl' init Hrect Hrect')
           to collapse the double partition into [partition_tries cc pp init].  Set part := that.
       (3) assert Hinit_wf : partition_result_wf (length x') init   (destruct b; cbn; use Hpt0_d
             with [filter id (true::ci0') = true::filter id ci0'] / [filter id (false::ci0')=filter id ci0'],
             and Hci0_len for [length ci0' = length x']).
       (4) assert Hpart_wf : partition_result_wf (length x') part
             by (apply partition_tries_wf; [exact Hrect_app|exact Hinit_wf]).
       (5) assert Hbl : map fst (true_lists init) ++ map fst (false_lists init) = [ci0']
             by (destruct b; reflexivity).
       (6) pose proof (part_bool_lists_perm (length x') cc pp init ci0' Hcc_pp_len Hcc_all Hbl) as Hperm.
           [Hcc_all : all (length = S (length x')) cc — from Hcil_len/Hcil'_len via Forall->all + app.]
       (7) destruct part as [jci0 jpt0 joc jot | foc fot tci0 tpt0 tcil tptl] eqn:Hpart.

       === just_false case ===
       Here true_lists part = [], so Hperm : map fst (false_lists part) = jci0::joc ~perm~ ci0'::map tl cc.
       Also Hpart_wf : rectangular_trie_list (length x') (jci0::joc) (jpt0::jot) — gives lengths AND
         per-entry has_depth'(length(filter id ·)).  Convert to the Forall2 + Forall + length hyps for IHx.
       The function = pt_spaced_intersect' merge fuel' joc jot jci0 [] jpt0 [].
       Apply IHx fuel' jci0 jpt0 joc jot [] []  (cil'0=[], ptl'0=[]).  Hyps:
         fuel'>length x' ✓; length jci0 = length x' (from rect, length jci0 = length x'); Forall(len=len x') joc;
         Forall _ []; length joc = length jot; length []=length[]; has_depth'(len filter jci0) jpt0;
         Forall2 ... joc jot; Forall2 ... [] [].
       IHx conclusion: match ... with Some r => Is_true(has_depth'(len(filter id (comb (joc++[]) jci0))) r).
       Need to rewrite the goal's [comb (cil++cil') (b::ci0')] depth to equal [comb (joc++[]) jci0]:
         comb (joc++[]) jci0 = comb joc jci0 = comb (map tl cc) ci0'  (comb_perm with jci0::joc ~perm~ ci0'::map tl cc).
         comb cc (b::ci0') : b=false here (just_false ⟹ init was just_false ⟹ b=false; and all heads false ⟹
           true_filter empty).  By fold_orb_combine_all_false_head (needs: all cc have length S(len x') and
           hd false = false), comb cc (false::ci0') = false :: comb (map tl cc) ci0'.  So
           filter id (comb cc (false::ci0')) = filter id (comb (map tl cc) ci0') ⟹ equal lengths.
         (The "all heads false" fact: in just_false case, true_lists part = [] forces every cc entry to have
          hd false = false — derive from partition_tries_true_lists giving true_filter = [], i.e. filter (hd) = [].)
       Then the goal's depth = IHx's depth ⟹ conclude by IHx (destruct the inner match Some/None; None case trivial).

       === have_true case ===
       Hpart_wf : offset_rectangular_trie_list (length x') (tci0::tcil) (tpt0::tptl)
                  /\ rectangular_trie_list (length x') foc fot.
       The function = option_map pos_trie_node (list_intersect (fun is_fwd =>
            pt_spaced_intersect' merge fuel' foc fot tci0 (if is_fwd then tcil else rev tcil))
            (proj_node_map_unchecked tpt0) (map proj_node_map_unchecked tptl)).
       Destruct (list_intersect ...) as [m_res|]; [|exact I (None case)].
       Goal: Is_true (has_depth' (length (filter id (comb cc (b::ci0')))) (pos_trie_node m_res)).
       Head of (comb cc (b::ci0')) is true (have_true ⟹ b=true OR some cc head true; use
         fold_orb_combine_head_some_true with the disjunction).  So
         length (filter id (comb cc (b::ci0'))) = S (length (filter id (tl (comb cc (b::ci0')))))
         and tl (comb cc (b::ci0')) = comb (map tl cc) ci0'  (fold_orb_combine_tail).
       Let D := length (filter id (comb (map tl cc) ci0')).  Goal becomes has_depth' (S D) (pos_trie_node m_res).
       Apply has_depth'_node_intro: forall q v, PTree.get' q m_res = Some v -> Is_true (has_depth' D v).
       For such q,v: relate to the recursion via list_intersect_lookup_at_pos:
         PTree.get q (otree (list_intersect ...)) = match get' q (proj tpt0), Mmap (get' q) (map proj tptl) with
           Some hd_x, Some tl_x => pt_spaced_intersect' merge fuel' foc fot tci0 tcil hd_x tl_x | _ => None end.
         (Supply its hyps: Ht_ci0_len (length tci0 = length x' from offset_rect), Ht_pt0_d
          (has_depth'(S(len filter tci0)) tpt0 from offset_rect), Hrect_true_offset (the offset all2),
          Hsim_rev := pt_spaced_intersect'_sim_rev fuel' (length x') ... — see IntersectSpec:1407,2067 usage.)
         Since m_res = the otree's tree' and get' q m_res = Some v, the above is Some v, so the match is the
         Some/Some branch and v = pt_spaced_intersect' merge fuel' foc fot tci0 tcil hd_x tl_x (Some v).
         hd_x is a child of tpt0 (depth (len filter tci0)); tl_x are children of tptl (offset) ⟹ depth (len filter tcil_i).
       Apply IHx fuel' tci0 hd_x foc fot tcil tl_x.  Hyps from offset/rect + has_depth'_node_inv for hd_x/tl_x.
       IHx gives: Is_true (has_depth' (length (filter id (comb (foc++tcil) tci0))) v).
       Finally comb (foc++tcil) tci0 = comb (map tl cc) ci0'  (comb_perm: tci0::(foc++tcil) ~perm~ ci0'::map tl cc,
         from Hperm which says (tci0::tcil)++foc ~perm~ ci0'::map tl cc).  So depth = D. Done. *)
  Lemma pt_spaced_intersect'_depth_general
    (fuel : nat) (x : list positive)
    (ci0 : list bool) (pt0 : pos_trie')
    (cil : list (list bool)) (ptl : list pos_trie')
    (cil' : list (list bool)) (ptl' : list pos_trie') :
    (fuel > length x)%nat ->
    length ci0 = length x ->
    Forall (fun l => length l = length x) cil ->
    Forall (fun l => length l = length x) cil' ->
    length cil = length ptl ->
    length cil' = length ptl' ->
    Is_true (has_depth' (length (filter id ci0)) pt0) ->
    Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil ptl ->
    Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil' ptl' ->
    match pt_spaced_intersect' merge fuel cil ptl ci0 cil' pt0 ptl' with
    | Some r => Is_true (has_depth' (length (filter id (comb (cil ++ cil') ci0))) r)
    | None => True
    end.
  Proof.
    revert fuel ci0 pt0 cil ptl cil' ptl'.
    induction x as [|p x' IHx];
      intros fuel ci0 pt0 cil ptl cil' ptl'
             Hfuel Hci0_len Hcil_len Hcil'_len Hcil_ptl_len Hcil'_ptl'_len
             Hpt0_d Hcil_ptl_d Hcil'_ptl'_d.
    - destruct ci0 as [|? ?]; [|cbn in Hci0_len; discriminate].
      destruct fuel as [|fuel']; [Lia.lia|].
      cbn in Hpt0_d. destruct pt0 as [a|m]; [|contradiction].
      cbn [pt_spaced_intersect'].
      assert (Hcomb_nil : comb (cil ++ cil') [] = [])
        by (unfold comb; generalize (cil ++ cil') as LL; clear;
            induction LL as [|l LL IH]; cbn; [reflexivity| rewrite <- IH at 2; f_equal; destruct l; reflexivity]).
      rewrite Hcomb_nil. cbn [filter length has_depth']. exact I.
    - destruct ci0 as [|b ci0']; [cbn in Hci0_len; discriminate|].
      destruct fuel as [|fuel']; [cbn in Hfuel; Lia.lia|].
      cbn [Datatypes.length] in Hci0_len, Hfuel. injection Hci0_len as Hci0_len.
      assert (Hfuel' : (fuel' > length x')%nat) by Lia.lia.
      assert (Hrect : rectangular_trie_list (S (length x')) cil ptl)
        by (eapply rectangular_trie_list_of_Forall2; [exact Hcil_len|exact Hcil_ptl_d]).
      assert (Hrect' : rectangular_trie_list (S (length x')) cil' ptl')
        by (eapply rectangular_trie_list_of_Forall2; [exact Hcil'_len|exact Hcil'_ptl'_d]).
      assert (Hrect_app : rectangular_trie_list (S (length x')) (cil ++ cil') (ptl ++ ptl'))
        by (apply rectangular_trie_list_app; assumption).
      cbn [pt_spaced_intersect'].
      rewrite (partition_tries_app merge (S (length x')) cil cil' ptl ptl' _ Hrect Hrect').
      set (init := if b then have_true_part [] [] ci0' pt0 [] [] else just_false_part ci0' pt0 [] []) in *.
      set (part := partition_tries (cil ++ cil') (ptl ++ ptl') init) in *.
      assert (Hcc_pp_len : length (cil ++ cil') = length (ptl ++ ptl'))
        by (rewrite !length_app; congruence).
      assert (Hbl : map fst (true_lists init) ++ map fst (false_lists init) = [ci0'])
        by (unfold init; destruct b; cbn; reflexivity).
      assert (Hcc_all : all (fun l => length l = S (length x')) (cil ++ cil'))
        by (apply all_app; split;
            [ clear -Hcil_len; induction Hcil_len; cbn in *; auto
            | clear -Hcil'_len; induction Hcil'_len; cbn in *; auto ]).
      assert (Hinit_wf : partition_result_wf (length x') init)
        by (unfold init; destruct b; cbn in Hpt0_d |- *;
            [ split; [|exact I]; split; [split; [exact Hpt0_d | exact Hci0_len] | exact I]
            | split; [|exact I]; split; [exact Hpt0_d | exact Hci0_len] ]).
      assert (Hpart_wf : partition_result_wf (length x') part)
        by (unfold part; apply (partition_tries_wf merge); [exact Hrect_app | exact Hinit_wf]).
      pose proof (@part_bool_lists_perm (length x') (cil ++ cil') (ptl ++ ptl') init ci0' Hcc_pp_len Hcc_all Hbl) as Hperm.
      fold part in Hperm.
      destruct part as [jci0 jpt0 joc jot | foc fot tci0 tpt0 tcil tptl] eqn:Hpart.
      + (* just_false *)
        cbn [true_lists false_lists app] in Hperm.
        pose proof (rectangular_trie_list_inv _ _ _ Hpart_wf) as [HFjc [HF2jc Hlenjc]].
        pose proof (Forall_inv HFjc) as Hjci0_len.
        pose proof (Forall_inv_tail HFjc) as Hjoc_len.
        inversion HF2jc as [|c0 t0 cs0 ts0 Hjpt0_d Hjoc_d Heqc Heqt]; subst.
        cbn [Datatypes.length] in Hlenjc. injection Hlenjc as Hjoc_jot_len.
        assert (Hmapfst : map fst (combine (jci0 :: joc) (jpt0 :: jot)) = jci0 :: joc)
          by (rewrite map_fst_combine; [reflexivity| cbn; congruence]).
        rewrite Hmapfst in Hperm.
        cbn [map app] in Hperm.
        pose proof (partition_tries_true_lists merge (length x') (cil ++ cil') (ptl ++ ptl') init Hcc_all Hcc_pp_len) as Htl.
        fold part in Htl. rewrite Hpart in Htl. cbn [true_lists] in Htl.
        symmetry in Htl. apply app_eq_nil in Htl. destruct Htl as [Htf Hti].
        assert (Hbfalse : b = false) by (unfold init in Hti; destruct b; [cbn in Hti; discriminate | reflexivity]).
        subst b.
        apply rev_eq_nil in Htf. rewrite rev_involutive in Htf. apply map_eq_nil in Htf.
        assert (Hhd : forall (cc0:list (list bool)) (pp0:list pos_trie'),
                  length cc0 = length pp0 ->
                  filter (fun q => hd false (fst q)) (combine cc0 pp0) = [] ->
                  Forall (fun l => hd false l = false) cc0).
        { clear. intros cc0; induction cc0 as [|c cc0 IH]; intros [|q pp0] Hlen Hf;
            cbn in *; try discriminate; [constructor|].
          destruct (hd false c) eqn:Hhc; cbn in Hf; [discriminate Hf|].
          constructor; [exact Hhc | apply (IH pp0); [congruence | exact Hf]]. }
        pose proof (Hhd (cil ++ cil') (ptl ++ ptl') Hcc_pp_len Htf) as Hheads.
        assert (Hjci0' : length jci0 = length x') by exact Hjci0_len.
        assert (Hcomb_eq : comb (cil ++ cil') (false :: ci0')
                           = false :: comb (map (tl (A:=bool)) (cil ++ cil')) ci0').
        { unfold comb. apply fold_orb_combine_all_false_head.
          apply Forall_forall. intros l Hl. split.
          - rewrite Hci0_len. apply in_app_or in Hl; rewrite Forall_forall in Hcil_len, Hcil'_len;
              destruct Hl as [Hl|Hl]; [apply Hcil_len in Hl | apply Hcil'_len in Hl]; cbn in Hl; exact Hl.
          - rewrite Forall_forall in Hheads. apply Hheads. exact Hl. }
        assert (HF' : Forall (fun l => length l = length jci0) (jci0 :: joc))
          by (eapply Forall_impl; [|exact HFjc]; cbn; intros a Ha; rewrite Ha; symmetry; exact Hjci0').
        assert (Hcomb_rec : comb joc jci0 = comb (map (tl (A:=bool)) (cil ++ cil')) ci0')
          by (apply comb_perm; [exact HF' | exact Hperm]).
        pose proof (IHx fuel' jci0 jpt0 joc jot [] [] Hfuel' Hjci0' Hjoc_len (Forall_nil _) Hjoc_jot_len eq_refl Hjpt0_d Hjoc_d (Forall2_nil _)) as IHapp.
        rewrite app_nil_r, Hcomb_rec in IHapp.
        rewrite Hcomb_eq. cbn [filter id].
        exact IHapp.
      + (* have_true *)
        cbn [true_lists false_lists] in Hperm.
        destruct Hpart_wf as [Hoffset Hrect_f].
        pose proof (rectangular_trie_list_inv _ _ _ Hrect_f) as [HFf [HF2f Hlenf]].
        pose proof (all2_len _ _ _ _ _ Hoffset) as Htct_len.
        rewrite (map_fst_combine (tci0 :: tcil) (tpt0 :: tptl) Htct_len) in Hperm.
        rewrite (map_fst_combine foc fot Hlenf) in Hperm.
        cbn [offset_rectangular_trie_list all2] in Hoffset.
        destruct Hoffset as [ [Htpt0_d Htci0_len] Htcil_off ].
        assert (Hoff_inv : Forall (fun l => length l = length x') tcil
                           /\ Forall2 (fun c t => Is_true (has_depth' (S (length (filter id c))) t)) tcil tptl
                           /\ length tcil = length tptl).
        { clear -Htcil_off. revert tptl Htcil_off; induction tcil as [|c cs IH]; intros [|t ts] Hr;
            cbn in Hr; try contradiction.
          - repeat split; constructor.
          - destruct Hr as [ [Hd Hlen] Hrest ]. specialize (IH ts Hrest). destruct IH as [HF [HF2 Hl]].
            repeat split; try constructor; auto. cbn; rewrite Hl; reflexivity. }
        destruct Hoff_inv as [Htcil_lenF [Htcil_d Htcil_tptl_len]].
        assert (HccF : Forall (fun l => length l = S (length ci0')) (cil ++ cil')).
        { rewrite Hci0_len. apply Forall_app; split;
            (eapply Forall_impl; [|eassumption]); cbn; intros a Ha; exact Ha. }
        assert (Htl_comb : tl (comb (cil ++ cil') (b :: ci0')) = comb (map (tl (A:=bool)) (cil ++ cil')) ci0')
          by (unfold comb; apply fold_orb_combine_tail; exact HccF).
        assert (Hhead_true : hd false (comb (cil ++ cil') (b :: ci0')) = true).
        { unfold comb. apply (fold_orb_combine_head_some_true (cil ++ cil') (b :: ci0') (length ci0')).
          - exact HccF.
          - cbn; reflexivity.
          - destruct b; [left; reflexivity|].
            right.
            pose proof (partition_tries_true_lists merge (length x') (cil ++ cil') (ptl ++ ptl') init Hcc_all Hcc_pp_len) as Htl2.
            fold part in Htl2. rewrite Hpart in Htl2. cbn [true_lists] in Htl2.
            unfold init in Htl2. cbn [true_lists] in Htl2. rewrite app_nil_r in Htl2.
            destruct (filter (fun q => hd false (fst q)) (combine (cil ++ cil') (ptl ++ ptl'))) as [|h0 ftl] eqn:Hfeq.
            + cbn in Htl2. discriminate Htl2.
            + assert (Hin_h0 : In h0 (filter (fun q => hd false (fst q)) (combine (cil ++ cil') (ptl ++ ptl'))))
                by (rewrite Hfeq; left; reflexivity).
              apply filter_In in Hin_h0. destruct Hin_h0 as [Hin_comb Hhdh0].
              destruct h0 as [h0a h0b]; cbn in *.
              exists h0a. split; [apply in_combine_l in Hin_comb; exact Hin_comb | exact Hhdh0]. }
        assert (HpermFT : Permutation (tci0 :: (foc ++ tcil)) (ci0' :: map (tl (A:=bool)) (cil ++ cil')))
          by (eapply Permutation_trans; [apply perm_skip; apply Permutation_app_comm | exact Hperm]).
        assert (HFFT : Forall (fun l => length l = length tci0) (tci0 :: (foc ++ tcil))).
        { constructor; [reflexivity|]. apply Forall_app; split.
          - eapply Forall_impl; [|exact HFf]; cbn; intros a Ha; rewrite Ha; symmetry; exact Htci0_len.
          - eapply Forall_impl; [|exact Htcil_lenF]; cbn; intros a Ha; rewrite Ha; symmetry; exact Htci0_len. }
        assert (Hcomb_rec2 : comb (foc ++ tcil) tci0 = comb (map (tl (A:=bool)) (cil ++ cil')) ci0')
          by (apply comb_perm; [exact HFFT | exact HpermFT]).
        assert (Hcc_form : comb (cil ++ cil') (b :: ci0') = true :: comb (map (tl (A:=bool)) (cil ++ cil')) ci0').
        { pose proof Hhead_true as Hht. pose proof Htl_comb as Htc.
          destruct (comb (cil ++ cil') (b :: ci0')) as [|h t].
          - cbn in Hht; discriminate.
          - cbn in Hht, Htc. subst. reflexivity. }
        assert (Hidx : length (filter id (comb (cil ++ cil') (b :: ci0')))
                       = S (length (filter id (comb (map (tl (A:=bool)) (cil ++ cil')) ci0'))))
          by (rewrite Hcc_form; cbn [filter id]; reflexivity).
        destruct (TrieMap.list_intersect
               (fun is_forward : bool =>
                pt_spaced_intersect' merge fuel' foc fot tci0
                  (if is_forward then tcil else rev tcil))
               (proj_node_map_unchecked tpt0) (map proj_node_map_unchecked tptl)) as [m_res|] eqn:Hli;
          cbn [option_map]; [|exact I].
        rewrite Hidx. apply has_depth'_node_intro. intros q v Hqv.
        assert (Hsim_rev : forall (xx : pos_trie') (ll : list pos_trie'),
                  rectangular_trie_list (length x') (tci0 :: tcil) (xx :: ll) ->
                  pt_spaced_intersect' merge fuel' foc fot tci0 (rev tcil) xx (rev ll)
                  = pt_spaced_intersect' merge fuel' foc fot tci0 tcil xx ll).
        { intros xx ll Hrectxl.
          apply (pt_spaced_intersect'_sim_rev merge merge_comm merge_assoc fuel' (length x') foc fot tci0 tcil xx ll).
          - cbn in Hrectxl. destruct Hrectxl as [Hhd Htl]. split; [exact Hhd | exact Hrect_f].
          - cbn in Hrectxl. destruct Hrectxl as [_ Htl]. exact Htl. }
        pose proof (@list_intersect_lookup_at_pos A H merge fuel' (length x') foc fot tci0 tcil tpt0 tptl q
                      Htci0_len Htpt0_d Htcil_off Hsim_rev) as Hlip.
        rewrite Hli in Hlip. cbn [TrieMap.otree Tries.Canonical.PTree.get] in Hlip.
        rewrite Hqv in Hlip.
        destruct (PTree.get' q (proj_node_map_unchecked tpt0)) as [hd_x|] eqn:Hgq; [|discriminate Hlip].
        destruct (list_Mmap (PTree.get' q) (map proj_node_map_unchecked tptl)) as [tl_x|] eqn:Hmm; [|discriminate Hlip].
        assert (Hmmd : forall (cs:list (list bool)) (ts ts':list pos_trie'),
                  Forall2 (fun c t => Is_true (has_depth' (S (length (filter id c))) t)) cs ts ->
                  list_Mmap (PTree.get' q) (map proj_node_map_unchecked ts) = Some ts' ->
                  Forall2 (fun c t => Is_true (has_depth' (length (filter id c)) t)) cs ts'
                  /\ length cs = length ts').
        { clear. intros cs; induction cs as [|c cs IH]; intros ts ts' Hd Hmm0.
          - inversion Hd; subst. cbn in Hmm0. injection Hmm0 as <-. split; [constructor|reflexivity].
          - inversion Hd as [|c0 t0 cs0 ts0 Hct Hrest Heq1 Heq2]; subst.
            cbn in Hmm0.
            destruct (PTree.get' q (proj_node_map_unchecked t0)) as [vt|] eqn:Hgt; [|discriminate].
            destruct (list_Mmap (PTree.get' q) (map proj_node_map_unchecked ts0)) as [vts|] eqn:Hmms; [|discriminate].
            injection Hmm0 as <-.
            destruct (IH ts0 vts Hrest Hmms) as [HF2' Hl'].
            destruct (has_depth'_S_node _ _ Hct) as [m0 Hm0]. rewrite Hm0 in Hct, Hgt.
            cbn [proj_node_map_unchecked] in Hgt.
            pose proof (has_depth'_node_inv _ _ q vt Hct Hgt) as Hvt.
            split; [constructor; assumption | cbn; rewrite Hl'; reflexivity]. }
        destruct (Hmmd tcil tptl tl_x Htcil_d Hmm) as [HF2_tx Hlen_tx].
        destruct (has_depth'_S_node _ _ Htpt0_d) as [mtp Hmtp]. rewrite Hmtp in Htpt0_d, Hgq.
        cbn [proj_node_map_unchecked] in Hgq.
        pose proof (has_depth'_node_inv _ _ q hd_x Htpt0_d Hgq) as Hhd_x_d.
        specialize (IHx fuel' tci0 hd_x foc fot tcil tl_x Hfuel' Htci0_len HFf Htcil_lenF Hlenf Hlen_tx Hhd_x_d HF2f HF2_tx).
        rewrite <- Hlip in IHx. cbn in IHx. rewrite Hcomb_rec2 in IHx. exact IHx.
  Qed.

  (* ---- wrapper: the ne_list form used by the inheritance bridge.
     [depth t n = match t with Some t' => depth' t' n | None => True].
     PROOF mirrors pt_spaced_intersect_correct's preamble (IntersectSpec:3352):
       intros [Hwf_head Hwf_tail]; destruct tries as [[pt0_opt ci0] tail];
       destruct Hwf_head as [Hci0_len Hpt0_depth].
       unfold pt_spaced_intersect, depth; cbn [fst snd].
       destruct (split tail) as [ptl_opt cil] eqn:Hsplit; cbn [fst snd] in *.
       erewrite combined_bools_via_split by (cbn; exact Hsplit).  (* combined_bools = fold cil ci0 *)
       destruct (Forall_wf_input_split _ _ _ _ Hsplit Hwf_tail) as [Hcil_len Htail_depth].
       destruct pt0_opt as [pt0|]; [|cbn; exact I].              (* None head -> depth None = True *)
       cbn [Mbind option_monad].
       destruct (list_Mmap id ptl_opt) as [ptl|] eqn:Hmmap; [|cbn; exact I].  (* None tail -> True *)
       cbn [Mbind id].
       (* goal: depth (pt_spaced_intersect' merge (S (length ci0)) cil ptl ci0 [] pt0 [])
                      (length (filter id (fold_left ... cil ci0)))  *)
       pose proof (list_Mmap_id_Some_inv _ _ Hmmap) as Hptl_eq.   (* ptl_opt = map Some ptl *)
       pose proof (pt_spaced_intersect'_depth_general (S (length ci0)) x ci0 pt0 cil ptl [] []
                     <fuel> Hci0_len <Hcil_len_x> <Forall []> <len cil=len ptl> <len []=len []>
                     Hpt0_depth <Forall2 cil ptl> <Forall2 [] []>) as Hgen.
         (hyps: same massaging as pt_spaced_intersect_correct lines 3415-3426 — Hcil_ptl_len from
          Hptl_eq+length_map+Hlen_pc; Htail_dep via Forall2_depth_from_Forall on combine (map Some ptl) cil = tail.)
       (* Hgen : match pt_spaced_intersect' ... ci0 [] pt0 [] with
                   Some r => Is_true (has_depth' (length (filter id (comb (cil++[]) ci0))) r) | None => True *)
       rewrite app_nil_r in Hgen.   (* cil ++ [] = cil ; comb cil ci0 = fold_left ... cil ci0 (defeq) *)
       destruct (pt_spaced_intersect' merge (S (length ci0)) cil ptl ci0 [] pt0 []) as [r|];
         [ apply has_depth'_to_depth'; exact Hgen | exact I ]. *)
  Lemma pt_spaced_intersect_depth
    (tries : ne_list (@pos_trie A * list bool)) (x : list positive) :
    wf_tries x tries ->
    depth (pt_spaced_intersect merge tries)
          (length (filter id (combined_bools tries))).
  Proof.
    intros [Hwf_head Hwf_tail].
    destruct tries as [[pt0_opt ci0] tail].
    destruct Hwf_head as [Hci0_len Hpt0_depth].
    unfold pt_spaced_intersect, depth; cbn [fst snd].
    destruct (split tail) as [ptl_opt cil] eqn:Hsplit; cbn [fst snd] in *.
    erewrite combined_bools_via_split by (cbn; exact Hsplit).
    destruct (Forall_wf_input_split _ _ _ _ Hsplit Hwf_tail) as [Hcil_len Htail_depth].
    cbn [fst snd].
    destruct pt0_opt as [pt0|]; [|cbn; exact I].
    cbn [Mbind option_monad].
    destruct (list_Mmap (M:=option) (B:=pos_trie') id ptl_opt) as [ptl|] eqn:Hmmap; [|exact I].
    assert (Hlen_pc : length ptl_opt = length cil)
      by (pose proof (length_fst_split tail) as Hll;
          pose proof (length_snd_split tail) as Hlr;
          rewrite Hsplit in Hll, Hlr; cbn in Hll, Hlr; congruence).
    pose proof (list_Mmap_id_Some_inv _ _ Hmmap) as Hptl_opt_eq.
    assert (Hcil_ptl_len : length cil = length ptl)
      by (rewrite Hptl_opt_eq, length_map in Hlen_pc; Lia.lia).
    pose proof (split_combine tail Hsplit) as Htail_eq.
    assert (Htail_dep : Forall2 (fun ci pt => Is_true (has_depth' (length (filter id ci)) pt)) cil ptl);
      [ apply Forall2_depth_from_Forall;
        [ Lia.lia
        | assert (Hcombine_eq : combine (map Some ptl) cil = tail)
            by (rewrite <- Hptl_opt_eq; exact Htail_eq);
          rewrite Hcombine_eq; exact Htail_depth ]
      | ].
    pose proof (@pt_spaced_intersect'_depth_general (S (length ci0)) x ci0 pt0 cil ptl [] []
                  ltac:(Lia.lia) Hci0_len Hcil_len (Forall_nil _) Hcil_ptl_len eq_refl
                  Hpt0_depth Htail_dep (Forall2_nil _)) as Hgen.
    rewrite app_nil_r in Hgen.
    unfold comb in Hgen.
    destruct (pt_spaced_intersect' merge (S (length ci0)) cil ptl ci0 [] pt0 []) as [r|];
      [ apply has_depth'_to_depth'; exact Hgen | exact I ].
  Qed.

End Depth.
