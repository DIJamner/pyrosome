(* ============================================================================
   Cluster II of trie #4: depth-uniformity of the [build_tries] output and the
   [variable_flags] bookkeeping facts.

   These discharge the [Hfd]/[H9] obligations of
   [FullPosTrieConv.fpt_spaced_intersect_inputs_hit] for the positive
   e-graph instantiation, so that H9/H10 at Automation.v can be closed and
   [egraph_sound] becomes axiom-free.  See WIP/trie4_P2_build_tries_depth_design.md.
   ============================================================================ *)
From Stdlib Require Import Lists.List Uint63 BinNums PArith Arith Lia.
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

  Lemma variable_flags_eq_map_filter (p : idx -> bool) (qv : list idx) :
    NoDup qv -> variable_flags idx Eqb_idx qv (filter p qv) = map p qv.
  Proof.
    induction qv as [|qx qv' IH]; intro Hnd.
    - reflexivity.
    - inversion Hnd as [|? ? Hnotin Hnd']; subst.
      cbn [filter variable_flags map].
      destruct (p qx) eqn:Hp.
      + rewrite eqb_refl_true by exact Eqb_idx_ok.
        cbn. f_equal. apply IH. exact Hnd'.
      + destruct (filter p qv') as [|cx cvs'] eqn:Hf.
        * cbn [variable_flags]. f_equal.
          rewrite IH; [| exact Hnd']. reflexivity.
        * assert (Hcx_in : In cx qv'). {
            assert (Hin : In cx (filter p qv')) by (rewrite Hf; left; reflexivity).
            apply filter_In in Hin. apply Hin. }
          assert (Hqx_ne_cx : qx <> cx). {
            intro Heq. subst. apply Hnotin. exact Hcx_in. }
          rewrite (@eqb_ineq_false idx Eqb_idx Eqb_idx_ok qx cx (or_introl Hqx_ne_cx)).
          cbn. f_equal. apply IH. exact Hnd'.
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
  Context (idx_leb : positive -> positive -> bool).

  Notation fptm := (@FullPosTrie.full_pos_trie_map).

  (* The fold invariant: every clause key's trie triple (full,new,old) is
     depth-[clen] in all three components. *)
  Definition bt_inv (q_clauses : idx_map (list nat * nat))
    (tries : idx_map (fptm unit * fptm unit * fptm unit)) : Prop :=
    forall n cl, map.get q_clauses n = Some cl ->
      exists ft, map.get tries n = Some ft
                 /\ fpt_depth (fst (fst ft)) (clen cl)
                 /\ fpt_depth (snd (fst ft)) (clen cl)
                 /\ fpt_depth (snd ft) (clen cl).

  Lemma build_tries_for_symbol_depth
    (current_epoch : positive) (window : nat)
    (q_clauses : idx_map (list nat * nat))
    (tbl : fptm (db_entry positive analysis_result)) :
    bt_inv q_clauses
      (build_tries_for_symbol positive _ Pos.succ idx_leb idx_map idx_map_plus
         (fun A => fptm A) analysis_result current_epoch window q_clauses tbl).
  Proof.
    unfold build_tries_for_symbol.
    eapply (map.fold_spec (fun _ tries => bt_inv q_clauses tries)).
    - intros n cl Hget. exists (map.empty, map.empty, map.empty).
      rewrite map_map_spec by exact idx_map_plus_ok. rewrite Hget. cbn [option_map].
      split; [reflexivity|]. cbn [fst snd].
      unfold map.empty, FullPosTrie.full_pos_trie_map. cbn [fpt_depth].
      split; [exact I | split; [exact I | exact I]].
    - intros k v m r Hgetm Hinv n cl Hget.
      rewrite intersect_spec by exact idx_map_plus_ok.
      destruct (Hinv n cl Hget) as [ft [Hgetr [Hdf [Hdn Hdo]]]].
      rewrite Hgetr, Hget.
      destruct v as [epoch v0 a_an]. destruct ft as [[full new] old]. cbn [fst snd] in Hdf, Hdn, Hdo.
      destruct cl as [cargs cv].
      eexists. split; [reflexivity|].
      destruct (match_clause positive positive_Eqb (cargs, cv) k v0) as [assignment|] eqn:Hmc.
      { apply match_clause_length in Hmc.
        destruct (idx_leb current_epoch (Nat.iter window Pos.succ epoch)); cbn [fst snd].
        - (* within window: full put, new put, old unchanged *)
          split; [|split].
          + apply fpt_put_depth; [exact Hmc | exact Hdf].
          + apply fpt_put_depth; [exact Hmc | exact Hdn].
          + exact Hdo.
        - (* outside window: full put, new unchanged, old put *)
          split; [|split].
          + apply fpt_put_depth; [exact Hmc | exact Hdf].
          + exact Hdn.
          + apply fpt_put_depth; [exact Hmc | exact Hdo]. }
      { cbn [fst snd]. split; [exact Hdf | split; [exact Hdn | exact Hdo]]. }
  Qed.

End BuildTries.

(* ============================================================================
   (C) [clen_compiled_eq_length_cvars]:
   the compiled-clause length equals the number of clause variables.

   Given qv (all query variables, NoDup) and out::args ⊆ qv,
   let cvars := filter (inb - (out::args)) qv  (the clause variables in order)
   and sub   := combine cvars (seq 0 (length cvars))  (position map).
   Then clen (map (lookup sub) args, lookup sub out) = length cvars.
   ============================================================================ *)

(* Helper: Eqb_ok for positive *)
Lemma positive_Eqb_ok' : Eqb_ok positive_Eqb.
Proof. intros a b; unfold eqb, positive_Eqb; destruct (Pos.eqb_spec a b); auto. Qed.

(* Helper: inb x l = true <-> In x l for positive *)
Lemma inb_positive_true (x : positive) (l : list positive) :
  inb x l = true <-> In x l.
Proof.
  unfold inb. rewrite existsb_exists. split.
  - intros [y [Hin Heq]]. unfold eqb, positive_Eqb in Heq.
    destruct (Pos.eqb_spec x y) as [E|E]; [subst; exact Hin | discriminate].
  - intro H. exists x. split; [exact H|]. unfold eqb, positive_Eqb. apply Pos.eqb_refl.
Qed.

(* Helper: named_list_lookup result is either the default or in (map snd l) *)
Lemma named_list_lookup_default_or_in (d : nat) (l : list (positive * nat)) (x : positive) :
  named_list_lookup d l x = d \/ In (named_list_lookup d l x) (map snd l).
Proof.
  induction l as [|[k v] l' IH]. { left; reflexivity. }
  cbn [named_list_lookup map snd]. destruct (eqb x k) eqn:Heq.
  - right. left. reflexivity.
  - destruct IH as [IH | IH]; [left; exact IH | right; right; exact IH].
Qed.

(* Helper: map snd (combine la lb) = lb when length la = length lb *)
Lemma map_snd_combine_gen {A B : Type} (la : list A) (lb : list B) :
  length la = length lb -> map snd (combine la lb) = lb.
Proof.
  revert lb. induction la as [|a la IH]; intros [|b lb] Hlen; cbn in *;
    try discriminate; try reflexivity.
  f_equal. apply IH. Lia.lia.
Qed.

(* Helper: lookup in (combine cvars (seq 0 n)) is always < n when n >= 1 *)
Lemma named_list_lookup_combine_seq_lt (cvars : list positive) (x : positive) :
  1 <= length cvars ->
  named_list_lookup 0 (combine cvars (seq 0 (length cvars))) x < length cvars.
Proof.
  intro Hn.
  pose proof (named_list_lookup_default_or_in 0 (combine cvars (seq 0 (length cvars))) x) as [Hdef | Hin].
  - rewrite Hdef. Lia.lia.
  - rewrite (map_snd_combine_gen cvars (seq 0 (length cvars))) in Hin.
    + apply in_seq in Hin. Lia.lia.
    + rewrite length_seq. reflexivity.
Qed.

(* Helper: default independence when key is present *)
Lemma named_list_lookup_present_indep (d1 d2 : nat) (l : list (positive * nat)) (x : positive) :
  (exists v, In (x, v) l) -> named_list_lookup d1 l x = named_list_lookup d2 l x.
Proof.
  intros [v Hin]. induction l as [|[k w] l' IH]. { inversion Hin. }
  cbn [named_list_lookup]. destruct (eqb x k) eqn:Heq. { reflexivity. }
  apply IH. destruct Hin as [Hin | Hin].
  - injection Hin as -> ->. rewrite eqb_refl_true in Heq by exact positive_Eqb_ok'. discriminate.
  - exact Hin.
Qed.

(* Helper: (nth i l d, base+i) ∈ combine l (seq base (length l)) *)
Lemma in_combine_seq_nth (l : list positive) (i : nat) (d : positive) (base : nat) :
  i < length l -> In (nth i l d, base + i) (combine l (seq base (length l))).
Proof.
  revert i base. induction l as [|x l' IH]; intros i base Hlt. { cbn in Hlt. Lia.lia. }
  cbn [length] in Hlt. cbn [combine seq].
  destruct i as [|i'].
  - cbn [nth]. left. f_equal. Lia.lia.
  - right. cbn [nth]. replace (base + S i') with (S base + i') by Lia.lia. apply IH. Lia.lia.
Qed.

(* Helper: NoDup l -> lookup of (nth i l d) in (combine l (seq 0 n)) = i *)
Lemma named_list_lookup_combine_seq_nth (l : list positive) (i : nat) (d : positive) :
  NoDup l -> i < length l ->
  named_list_lookup 0 (combine l (seq 0 (length l))) (nth i l d) = i.
Proof.
  intros Hnd Hlt.
  pose proof (in_combine_seq_nth l i d 0 Hlt) as Hin. cbn [Nat.add] in Hin.
  rewrite (named_list_lookup_present_indep 0 i _ _ (ex_intro _ i Hin)).
  revert i Hnd Hlt Hin.
  cut (forall base i, NoDup l -> i < length l ->
       named_list_lookup (base + i) (combine l (seq base (length l))) (nth i l d) = base + i).
  { intros H i Hnd' Hlt' _. specialize (H 0 i Hnd' Hlt'). cbn in H. exact H. }
  induction l as [|x l' IH]; intros base i Hnd' Hlt'. { cbn in Hlt'. Lia.lia. }
  cbn [combine seq nth named_list_lookup length] in *.
  inversion Hnd' as [|? ? Hnotin Hnd'']; subst.
  destruct i as [|i'].
  - cbn [nth]. rewrite eqb_refl_true by exact positive_Eqb_ok'. Lia.lia.
  - cbn [nth].
    assert (Hneq : eqb (nth i' l' d) x = false). {
      apply eqb_ineq_false; [exact positive_Eqb_ok'|left].
      intro Heq. subst. apply Hnotin. apply nth_In. Lia.lia. }
    rewrite Hneq. replace (base + S i') with (S base + i') by Lia.lia.
    apply IH; [exact Hnd'' | Lia.lia].
Qed.

(* Helper: fold_right Nat.max upper bound *)
Lemma fold_right_max_lt (l : list nat) (cv : nat) (B : nat) :
  (forall y, In y l -> y < B) -> cv < B -> fold_right Nat.max cv l < B.
Proof.
  induction l as [|x l' IH]; intros Hx Hcv. { exact Hcv. }
  cbn [fold_right]. apply Nat.max_lub_lt.
  - apply Hx. left. reflexivity.
  - apply IH; [| exact Hcv]. intros y Hy. apply Hx. right. exact Hy.
Qed.

(* Helper: fold_right Nat.max >= any element of the list *)
Lemma fold_right_max_ge_in (l : list nat) (cv v : nat) :
  In v l -> v <= fold_right Nat.max cv l.
Proof.
  induction l as [|x l' IH]; intros Hin. { inversion Hin. }
  cbn [fold_right]. destruct Hin as [-> | Hin]. { Lia.lia. }
  specialize (IH Hin). Lia.lia.
Qed.

(* Helper: fold_right Nat.max >= its seed cv *)
Lemma fold_right_max_ge_cv (l : list nat) (cv : nat) :
  cv <= fold_right Nat.max cv l.
Proof.
  induction l as [|x l' IH]; cbn [fold_right]; Lia.lia.
Qed.

Lemma clen_compiled_eq_length_cvars
  (qv args : list positive) (out : positive)
  (Hnd : NoDup qv)
  (Hsub : incl (out :: args) qv) :
  let cvars := filter (fun x => inb x (out :: args)) qv in
  let sub := combine cvars (seq 0 (length cvars)) in
  clen (map (named_list_lookup 0 sub) args, named_list_lookup 0 sub out) = length cvars.
Proof.
  intros cvars sub.
  unfold clen.
  set (n := length cvars).
  (* cvars is NoDup (filter preserves NoDup) *)
  assert (Hcvnd : NoDup cvars) by (apply NoDup_filter; exact Hnd).
  (* out ∈ cvars: it passes the filter since out ∈ out::args *)
  assert (Hout_cvars : In out cvars). {
    apply filter_In. split.
    - apply Hsub. left. reflexivity.
    - apply inb_positive_true. left. reflexivity. }
  (* every element of cvars is in out::args (by filter definition) *)
  assert (Hcvars_sub : forall x, In x cvars -> In x (out :: args)). {
    intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hinb].
    apply inb_positive_true. exact Hinb. }
  (* n >= 1 since out ∈ cvars *)
  assert (Hn1 : 1 <= n). {
    unfold n. destruct cvars as [|? ?]. { inversion Hout_cvars. }
    cbn [length]. Lia.lia. }
  fold n in sub.
  (* every lookup value < n (upper bound for each element) *)
  assert (Hlt_n : forall x, named_list_lookup 0 sub x < n). {
    intro x. unfold sub, n.
    apply named_list_lookup_combine_seq_lt. exact Hn1. }
  (* Upper bound: clen <= n *)
  assert (Hle : S (fold_right Nat.max (named_list_lookup 0 sub out)
                    (map (named_list_lookup 0 sub) args)) <= n). {
    apply Nat.le_succ_l.
    apply fold_right_max_lt.
    - intros y Hy. apply in_map_iff in Hy. destruct Hy as [x [<- _]]. apply Hlt_n.
    - apply Hlt_n. }
  (* Lower bound: the last element of cvars has lookup value n-1 *)
  set (lastv := nth (n - 1) cvars xH).
  assert (Hlastv_cvars : In lastv cvars). {
    apply nth_In. unfold lastv. Lia.lia. }
  assert (Hlastv_lookup : named_list_lookup 0 sub lastv = n - 1). {
    unfold sub, lastv.
    apply named_list_lookup_combine_seq_nth; [exact Hcvnd | Lia.lia]. }
  assert (Hlastv_in : In lastv (out :: args)) by (apply Hcvars_sub; exact Hlastv_cvars).
  (* Lower bound: n-1 appears in the fold, so clen >= n *)
  assert (Hge : n <= S (fold_right Nat.max (named_list_lookup 0 sub out)
                         (map (named_list_lookup 0 sub) args))). {
    destruct Hlastv_in as [Heq | Hin_args].
    - (* lastv = out: the seed cv equals n-1 *)
      rewrite <- Heq in Hlastv_lookup.
      pose proof (fold_right_max_ge_cv (map (named_list_lookup 0 sub) args)
                    (named_list_lookup 0 sub out)).
      rewrite Hlastv_lookup in *. Lia.lia.
    - (* lastv ∈ args: n-1 appears in the mapped list *)
      assert (Hin_map : In (n - 1) (map (named_list_lookup 0 sub) args)). {
        apply in_map_iff. exists (nth (n-1) cvars xH).
        split. { exact Hlastv_lookup. } exact Hin_args. }
      pose proof (fold_right_max_ge_in (map (named_list_lookup 0 sub) args)
                    (named_list_lookup 0 sub out) (n-1) Hin_map).
      Lia.lia. }
  Lia.lia.
Qed.
