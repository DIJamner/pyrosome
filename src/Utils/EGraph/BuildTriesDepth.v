(* ============================================================================
   Cluster II of trie #4: depth-uniformity of the [build_tries] output and the
   [variable_flags] bookkeeping facts.

   These discharge the [Hfd]/[H9] obligations of
   [FullPosTrieConv.fpt_spaced_intersect_inputs_hit] for the positive
   e-graph instantiation, so that H9/H10 at Automation.v can be closed and
   [egraph_sound] becomes axiom-free.  See WIP/trie4_P2_build_tries_depth_design.md.
   ============================================================================ *)
From Stdlib Require Import Lists.List Uint63 BinNums PArith.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils Monad Default ExtraMaps.
From Utils Require Import FullPosTrie FullPosTrieConv PosListMap.
From Utils Require Import EGraph.Defs.

Section VariableFlags.
  Context {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}.

  (* [variable_flags] returns one flag per query variable. *)
  Lemma variable_flags_length (qvs cvs : list idx) :
    length (variable_flags idx Eqb_idx qvs cvs) = length qvs.
  Proof.
    revert cvs. induction qvs as [|qx qvs' IH]; intros cvs; cbn [variable_flags length].
    - reflexivity.
    - destruct cvs as [|cx cvs'].
      + cbn [length]. rewrite IH. reflexivity.
      + destruct (eqb qx cx); cbn [length]; rewrite IH; reflexivity.
  Qed.

  (* The number of selected (true) flags equals the number of clause variables,
     when the clause variables are exactly a value-predicate filtering of the
     query variables -- which is how [compile_query_clause] builds
     [clause_vars := sort_by_position_in (out::args) qvs = filter _ qvs]. *)
  Lemma variable_flags_filter_id_len (p : idx -> bool) (qv : list idx) :
    length (filter id (variable_flags idx Eqb_idx qv (filter p qv))) = length (filter p qv).
  Proof.
    induction qv as [|qx qv' IH]; cbn [filter variable_flags].
    - reflexivity.
    - destruct (p qx) eqn:Hpqx.
      + cbn [variable_flags]. rewrite eqb_refl_true by exact Eqb_idx_ok.
        cbn [filter id length]. rewrite IH. reflexivity.
      + destruct (filter p qv') as [|cx cv''] eqn:Hcv'.
        * cbn [variable_flags filter id]. rewrite IH. reflexivity.
        * assert (Hpcx : p cx = true).
          { assert (Hin : In cx (filter p qv')) by (rewrite Hcv'; left; reflexivity).
            apply filter_In in Hin. apply Hin. }
          cbn [variable_flags].
          replace (eqb qx cx) with false.
          2:{ symmetry. apply eqb_ineq_false;
                [ exact Eqb_idx_ok
                | left; intros ->; rewrite Hpcx in Hpqx; discriminate ]. }
          cbn [filter id]. exact IH.
  Qed.

End VariableFlags.

(* ============================================================================
   (A) [match_clause] produces fixed-length assignments: the length depends
   only on the clause [(cargs,cv)], never on the DB row [(args,v)].  This is
   what makes each clause's [build_tries] trie uniform-depth.
   ============================================================================ *)
Section MatchClauseLength.
  Context {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}.

  Lemma insert_length (acc : list (option idx)) (n : nat) (x : idx) (acc' : list (option idx)) :
    insert idx Eqb_idx acc n x = Some acc' ->
    length acc' = Nat.max (length acc) (S n).
  Proof.
    revert acc acc'. induction n as [|n0 IH]; intros acc acc' Hins.
    - destruct acc as [|[y|] acc0]; cbn [insert] in Hins.
      + injection Hins as <-. reflexivity.
      + destruct (eqb x y); [injection Hins as <-|discriminate].
        cbn [length]. Lia.lia.
      + injection Hins as <-. cbn [length]. Lia.lia.
    - destruct acc as [|my acc0]; cbn [insert] in Hins.
      + destruct (insert idx Eqb_idx [] n0 x) as [t|] eqn:Ht; cbn [option_map] in Hins; [|discriminate].
        injection Hins as <-. cbn [length]. rewrite (IH _ _ Ht). cbn [length]. Lia.lia.
      + destruct (insert idx Eqb_idx acc0 n0 x) as [t|] eqn:Ht; cbn [option_map] in Hins; [|discriminate].
        injection Hins as <-. cbn [length]. rewrite (IH _ _ Ht). cbn [length]. Lia.lia.
  Qed.

  Lemma match_clause'_length (cargs : list nat) (cv : nat) (args : list idx) (v : idx)
    (acc acc' : list (option idx)) :
    match_clause' idx Eqb_idx cargs cv args v acc = Some acc' ->
    length acc' = Nat.max (length acc) (S (fold_right Nat.max cv cargs)).
  Proof.
    revert args acc acc'. induction cargs as [|x cargs' IH]; intros args acc acc' Hmc.
    - destruct args as [|y args']; cbn [match_clause'] in Hmc; [|discriminate].
      apply insert_length in Hmc. cbn [fold_right]. exact Hmc.
    - destruct args as [|y args']; cbn [match_clause'] in Hmc; [discriminate|].
      unfold Mbind, option_monad in Hmc.
      destruct (insert idx Eqb_idx acc x y) as [acc1|] eqn:Hins; [|discriminate].
      apply insert_length in Hins.
      apply IH in Hmc. rewrite Hmc, Hins.
      cbn [fold_right]. Lia.lia.
  Qed.

  (* The uniform width of clause [(cargs,cv)]'s assignment trie. *)
  Definition clen (clause : list nat * nat) : nat :=
    let '(cargs, cv) := clause in S (fold_right Nat.max cv cargs).

  Lemma match_clause_length (cargs : list nat) (cv : nat) (args : list idx) (v : idx)
    (a : list idx) :
    match_clause idx Eqb_idx (cargs, cv) args v = Some a ->
    length a = clen (cargs, cv).
  Proof.
    unfold match_clause, clen. unfold Mbind, option_monad.
    destruct (match_clause' idx Eqb_idx cargs cv args v []) as [acc'|] eqn:Hmc; [|discriminate].
    intros Hoa. apply length_option_all in Hoa. rewrite Hoa.
    apply match_clause'_length in Hmc. rewrite Hmc. cbn [length]. Lia.lia.
  Qed.

End MatchClauseLength.

(* ============================================================================
   (B) [build_tries_for_symbol] produces depth-uniform tries: for the positive
   e-graph instantiation (db trie = full_pos_trie_map), each clause [n]'s
   [(full,frontier)] pair has both tries at [fpt_depth] = [clen] of the clause.
   ============================================================================ *)
Section BuildTries.
  Context {idx_map : forall A, map.map positive A} {idx_map_plus : map_plus idx_map}
          {idx_map_plus_ok : @map_plus_ok positive idx_map idx_map_plus}.
  Context {analysis_result : Type}.

  Notation fptm := (@FullPosTrie.full_pos_trie_map).

  (* The fold invariant: every clause key's trie pair is depth-[clen]. *)
  Definition bt_inv (q_clauses : idx_map (list nat * nat))
    (tries : idx_map (fptm unit * fptm unit)) : Prop :=
    forall n cl, map.get q_clauses n = Some cl ->
      exists ft, map.get tries n = Some ft
                 /\ fpt_depth (fst ft) (clen cl) /\ fpt_depth (snd ft) (clen cl).

  Lemma build_tries_for_symbol_depth
    (current_epoch : positive)
    (q_clauses : idx_map (list nat * nat))
    (tbl : fptm (db_entry positive analysis_result)) :
    bt_inv q_clauses
      (build_tries_for_symbol positive _ idx_map idx_map_plus
         (fun A => fptm A) analysis_result current_epoch q_clauses tbl).
  Proof.
    unfold build_tries_for_symbol.
    eapply (map.fold_spec (fun _ tries => bt_inv q_clauses tries)).
    - intros n cl Hget. exists (map.empty, map.empty).
      rewrite map_map_spec by exact idx_map_plus_ok. rewrite Hget. cbn [option_map].
      split; [reflexivity|]. cbn [fst snd].
      unfold map.empty, FullPosTrie.full_pos_trie_map. cbn [fpt_depth]. split; exact I.
    - intros k v m r Hgetm Hinv n cl Hget.
      rewrite intersect_spec by exact idx_map_plus_ok.
      destruct (Hinv n cl Hget) as [ft [Hgetr [Hdf Hds]]].
      rewrite Hgetr, Hget.
      destruct v as [epoch v0 a_an]. destruct ft as [full frontier]. cbn [fst snd] in Hdf, Hds.
      destruct cl as [cargs cv].
      eexists. split; [reflexivity|].
      destruct (match_clause positive positive_Eqb (cargs, cv) k v0) as [assignment|] eqn:Hmc.
      { apply match_clause_length in Hmc.
        destruct (eqb epoch current_epoch); cbn [fst snd]; split.
        - apply fpt_put_depth; [exact Hmc | exact Hdf].
        - apply fpt_put_depth; [exact Hmc | exact Hds].
        - apply fpt_put_depth; [exact Hmc | exact Hdf].
        - exact Hds. }
      { cbn [fst snd]. split; [exact Hdf | exact Hds]. }
  Qed.

End BuildTries.
