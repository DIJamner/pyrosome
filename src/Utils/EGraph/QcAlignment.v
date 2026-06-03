(* ============================================================================
   Per-ptr clen alignment for the positive e-graph instantiation (S73).

   [compiled_rules_ptr_clen]: for each ptr (fsym, nptr, cvars) in a compiled
   erule, the map entry (cargs, cv) satisfies clen (cargs, cv) = length cvars.

   This is piece (a) of trie #4 — the qc-alignment hash-threading needed to
   show that trie_of_clause produces uniformly-depth tries.
   ============================================================================ *)
From Stdlib Require Import Lists.List BinNums PArith Arith Lia.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils Monad Default ExtraMaps.
From Utils Require Import FullPosTrie FullPosTrieConv PosListMap TrieMapFold.
From Utils Require Import EGraph.Defs.
From Utils.EGraph Require Import Semantics QueryOpt QueryOptSound BuildTriesDepth.

(* Abbreviation for the positive build_rule_set instantiation. *)
Definition brs (rf : nat) (rules : list (Semantics.sequent positive positive)) :=
  @QueryOpt.build_rule_set positive positive_Eqb Pos.succ positive_default
    positive TrieMap.trie_map TrieMap.ptree_map_plus
    TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A) rf rules.

Lemma compiled_rules_ptr_clen
  (rf : nat) (rules : list (Semantics.sequent positive positive)) :
  forall (er : erule positive positive),
    In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)) ->
    forall (fsym : positive) (nptr : positive) (cvars : list positive),
      In (Build_erule_query_ptr positive positive fsym nptr cvars)
         (uncurry cons (query_clause_ptrs positive positive er)) ->
      exists q_f cargs cv,
        map.get (Defs.query_clauses positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)) fsym = Some q_f
        /\ map.get q_f nptr = Some (cargs, cv)
        /\ clen (cargs, cv) = length cvars.
Proof.
  intros er Hin fsym nptr cvars Hptr.
  pose proof (@QueryOptSound.compiled_rules_ptr_shape
    positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pos.lt Pos.succ positive_default
    positive positive_Eqb BuildTriesDepth.positive_Eqb_ok'
    TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
    TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A)
    (fun A => @FullPosTrie.full_pos_trie_map A)
    (fun x y h1 h2 => Pos.lt_irrefl x (Pos.lt_trans _ _ _ h1 h2))
    Pos.lt_succ_diag_r Pos.lt_trans
    TrieMap.ptree_map_plus_ok
    rf rules er Hin fsym nptr cvars Hptr)
    as (q_f & cargs & cv & out & args & HgetQc & Hgetm & HNoDup & Hincl & Hcvars & Hcargs_eq & Hcv_eq).
  exists q_f, cargs, cv.
  refine (conj HgetQc (conj Hgetm _)).
  (* Reduce to clen_compiled_eq_length_cvars *)
  rewrite Hcargs_eq, Hcv_eq.
  rewrite Hcvars.
  exact (clen_compiled_eq_length_cvars (query_vars positive positive er) args out HNoDup Hincl).
Qed.

(* ============================================================================
   UNIT C: trie_of_clause_depth
   For each compiled erule ptr, the trie produced by trie_of_clause has
   fpt_depth equal to the length of the clause variable list.
   ============================================================================ *)

Lemma trie_of_clause_depth
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (e : Defs.instance positive positive TrieMap.trie_map TrieMap.trie_map
         (fun A => @FullPosTrie.full_pos_trie_map A) (option positive))
  (frontier_n f n : positive) (cvars : list positive)
  (Hptr : In (Defs.Build_erule_query_ptr positive positive f n cvars)
             (uncurry cons (Defs.query_clause_ptrs positive positive er))) :
  fpt_depth
    (fst (@Defs.trie_of_clause positive positive_Eqb positive
            TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
            (Defs.query_vars positive positive er)
            (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                    TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                    (fun A => @FullPosTrie.full_pos_trie_map A)
                    (option positive) (brs rf rules) e))
            frontier_n
            (Defs.Build_erule_query_ptr positive positive f n cvars)))
    (length cvars).
Proof.
  cbn [Defs.build_tries fst].
  unfold Defs.trie_of_clause.
  set (DBT := map_intersect
                (Defs.build_tries_for_symbol positive positive_Eqb TrieMap.trie_map
                   TrieMap.ptree_map_plus (fun A => @FullPosTrie.full_pos_trie_map A)
                   (option positive) (Defs.epoch e))
                (Defs.query_clauses positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules))
                (Defs.db e)).
  destruct (compiled_rules_ptr_clen rf rules er Hin f n cvars Hptr)
    as (q_f & cargs & cv & Hqc & Hgetn & Hclen).
  destruct (map.get DBT f) as [trie_list|] eqn:Hdbt.
  2: { cbn [fst fpt_depth]. exact I. }
  cbn [fst].
  unfold DBT in Hdbt.
  cbn [map_intersect] in Hdbt.
  rewrite (@intersect_spec positive TrieMap.trie_map TrieMap.ptree_map_plus TrieMap.ptree_map_plus_ok
    (TrieMap.trie_map (list nat * nat))
    (@FullPosTrie.full_pos_trie_map (Defs.db_entry positive (option positive)))
    (TrieMap.trie_map (@FullPosTrie.full_pos_trie_map unit * @FullPosTrie.full_pos_trie_map unit))
    (Defs.build_tries_for_symbol positive positive_Eqb TrieMap.trie_map
       TrieMap.ptree_map_plus (fun A => @FullPosTrie.full_pos_trie_map A)
       (option positive) (Defs.epoch e))
    f
    (Defs.query_clauses positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules))
    (Defs.db e)) in Hdbt.
  rewrite Hqc in Hdbt.
  destruct (map.get (Defs.db e) f) as [tbl_f|] eqn:Hdb.
  { (* Some tbl_f: trie_list = build_tries_for_symbol ... q_f tbl_f *)
    unfold Defs.db_map in Hdb.
    rewrite Hdb in Hdbt.
    injection Hdbt as Heq_tl.
    pose proof (@BuildTriesDepth.build_tries_for_symbol_depth
      TrieMap.trie_map TrieMap.ptree_map_plus TrieMap.ptree_map_plus_ok
      (option positive)
      (Defs.epoch e) q_f tbl_f n (cargs, cv) Hgetn)
      as (ft & Hgetft & Hdf & Hds).
    rewrite <- Heq_tl.
    unfold unwrap_with_default.
    rewrite Hgetft.
    destruct ft as [total frontier]. cbn [fst snd] in Hdf, Hds.
    rewrite <- Hclen.
    destruct (eqb n frontier_n); cbn [fst]; assumption. }
  { (* None: contradiction *)
    unfold Defs.db_map in Hdb.
    rewrite Hdb in Hdbt.
    exact (match Hdbt with end). }
Qed.

(* ============================================================================
   UNIT B2 helper lemmas and assembly:
   combined_bools of the ne_map over clause ptrs = repeat true (length qv).
   ============================================================================ *)

(* Helper: nth j (map2 orb (combine a b)) false = orb (nth j a false) (nth j b false) *)
Lemma nth_map2_orb_combine (a b : list bool) (j : nat) :
  j < length a -> length a = length b ->
  nth j (map2 orb (combine a b)) false = orb (nth j a false) (nth j b false).
Proof.
  revert b j. induction a as [|x a' IH]; intros b j Hlt Hlen.
  - cbn in Hlt. Lia.lia.
  - destruct b as [|y b']; cbn in Hlen; [discriminate|].
    cbn [combine map2 map].
    destruct j as [|j'].
    + reflexivity.
    + cbn [nth]. apply IH.
      * cbn [length] in Hlt. Lia.lia.
      * Lia.lia.
Qed.

(* Helper: length (map2 orb (combine a b)) = length a when |a|=|b| *)
Lemma length_map2_orb_combine (a b : list bool) :
  length a = length b ->
  length (map2 orb (combine a b)) = length a.
Proof.
  intro Hlen. unfold map2.
  rewrite length_map, length_combine. rewrite Hlen. Lia.lia.
Qed.

(* Helper: list with all elements true = repeat true L *)
Lemma all_true_repeat_true (l : list bool) (L : nat) :
  length l = L ->
  (forall j, j < L -> nth j l false = true) ->
  l = repeat true L.
Proof.
  revert l. induction L as [|L' IH]; intros l Hlen Hnth.
  - destruct l; [reflexivity | discriminate].
  - destruct l as [|x l']; [discriminate|].
    cbn [repeat]. cbn [length] in Hlen.
    assert (x = true). { apply (Hnth 0). Lia.lia. }
    subst x. f_equal.
    apply IH.
    + Lia.lia.
    + intros j Hj. apply (Hnth (S j)). Lia.lia.
Qed.

(* Main generic lemma: fold_left map2_orb is repeat true when coverage holds *)
Lemma fold_left_map2_orb_all_true (head : list bool) (tails : list (list bool)) (L : nat) :
  length head = L ->
  (forall t, In t tails -> length t = L) ->
  (forall j, j < L -> nth j head false = true
             \/ exists t, In t tails /\ nth j t false = true) ->
  fold_left (fun acc t => map2 orb (combine t acc)) tails head = repeat true L.
Proof.
  revert head. induction tails as [|t0 tails' IH]; intros head Hlen Hlens Hcov.
  - cbn [fold_left]. apply all_true_repeat_true; [exact Hlen|].
    intros j Hj. destruct (Hcov j Hj) as [H | (t & Hin & _)]; [exact H | inversion Hin].
  - cbn [fold_left].
    pose (Hlent0 := Hlens t0 (or_introl eq_refl)).
    apply IH.
    + unfold map2. rewrite length_map, length_combine, Hlent0, Hlen. Lia.lia.
    + intros t Hin. apply Hlens. right. exact Hin.
    + intros j Hj.
      assert (Hj' : j < length t0) by (rewrite Hlent0; exact Hj).
      assert (Hjeq : length t0 = length head) by (rewrite Hlent0, Hlen; reflexivity).
      rewrite (nth_map2_orb_combine t0 head j Hj' Hjeq).
      destruct (Hcov j Hj) as [Hh | (t & Hin & Ht)].
      * left. rewrite Hh. apply Bool.orb_true_r.
      * destruct Hin as [-> | Hin'].
        { left. rewrite Ht. reflexivity. }
        { right. exact (ex_intro _ t (conj Hin' Ht)). }
Qed.

(* Helper: fold_left extracting snd = fold_left over mapped snds *)
Lemma fold_left_map2_orb_snd_eq {A} (g : A -> list bool) (tails : list A) :
  forall (head : list bool),
  fold_left (fun acc ptr => map2 orb (combine (g ptr) acc)) tails head
  = fold_left (fun acc t => map2 orb (combine t acc)) (map g tails) head.
Proof.
  induction tails as [|t tails' IH]; intro head; cbn [fold_left map]; [reflexivity|].
  apply IH.
Qed.

(* Helper: x ∈ atom_ret :: atom_args (built from cvars_i by cargs/cv) → x ∈ cvars_i *)
Lemma atom_ret_args_in_cvars (cvars : list positive) (cargs : list nat) (cv : nat)
  (Hcargs : forall t, In t cargs -> t < length cvars)
  (Hcv : cv < length cvars)
  (x : positive)
  (Hx : In x (nth cv cvars positive_default :: map (fun k => nth k cvars positive_default) cargs)) :
  In x cvars.
Proof.
  destruct Hx as [<- | Hargs].
  - apply nth_In. exact Hcv.
  - apply in_map_iff in Hargs. destruct Hargs as [k [<- Hk]].
    apply nth_In. exact (Hcargs k Hk).
Qed.

(* Helper: nth on a mapped list at a valid index *)
Lemma nth_map_lt {A B} (f : A -> B) (l : list A) (j : nat) (d : B) (da : A) :
  j < length l -> nth j (map f l) d = f (nth j l da).
Proof.
  revert l. induction j as [|j' IH]; intros [|x l'] Hlt; cbn in *; try Lia.lia.
  - reflexivity.
  - apply IH. Lia.lia.
Qed.

(* ============================================================================
   UNIT B2 assembly: combined_bools of the intersection tries = repeat true N
   ============================================================================ *)

Lemma intersection_inputs_combined_bools
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (e : Defs.instance positive positive TrieMap.trie_map TrieMap.trie_map
         (fun A => @FullPosTrie.full_pos_trie_map A) (option positive))
  (frontier_n : positive) :
  let qv := Defs.query_vars positive positive er in
  let DBT := fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                    TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                    (fun A => @FullPosTrie.full_pos_trie_map A)
                    (option positive) (brs rf rules) e) in
  let toc := @Defs.trie_of_clause positive positive_Eqb positive
                TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A) qv DBT frontier_n in
  let tries_ne := ne_map toc (Defs.query_clause_ptrs positive positive er) in
  let cvt := fun (q : @FullPosTrie.full_pos_trie_map unit * list bool) =>
               (FullPosTrieConv.fpt_to_pt (fst q), snd q) in
  @PosListMapIntersectSpec.combined_bools unit
    (cvt (fst tries_ne), map cvt (snd tries_ne))
  = repeat true (length qv).
Proof.
  intros qv DBT toc tries_ne cvt.
  (* unfold combined_bools and ne_map *)
  unfold PosListMapIntersectSpec.combined_bools.
  cbn [fst snd].
  unfold tries_ne, ne_map. cbn [fst snd].
  (* Rewrite the fold to use t instead of snd p *)
  rewrite (fold_left_map2_orb_snd_eq (@snd pos_trie (list bool))
    (map cvt (map toc (snd (query_clause_ptrs positive positive er))))).
  (* Step 2: apply fold_left_map2_orb_all_true *)
  apply fold_left_map2_orb_all_true with (L := length qv).
  { (* length head = L *)
    destruct (fst (query_clause_ptrs positive positive er)) as [f_h n_h cvars_h].
    cbn [Defs.trie_of_clause toc snd cvt].
    destruct (map.get DBT f_h) as [tl|].
    - destruct (unwrap_with_default (map.get tl n_h)) as [tot fr].
      destruct (eqb n_h frontier_n); cbn [snd]; apply variable_flags_length.
    - cbn [snd]. apply variable_flags_length. }
  { (* lengths of tails = L *)
    intros t0 Hin_t0.
    apply in_map_iff in Hin_t0. destruct Hin_t0 as [[trie0 bl0] [Heq0 Hin0]].
    apply in_map_iff in Hin0. destruct Hin0 as [[trie1 bl1] [Heq1 Hin1]].
    apply in_map_iff in Hin1. destruct Hin1 as [[f2 n2 cvars2] [Heq2 _]].
    cbn [Defs.trie_of_clause toc] in Heq2.
    destruct (map.get DBT f2) as [tl2|].
    - destruct (unwrap_with_default (map.get tl2 n2)) as [tot2 fr2].
      destruct (eqb n2 frontier_n); cbn [snd] in Heq2;
        injection Heq2 as _ <-;
        cbn [snd cvt] in Heq1; injection Heq1 as _ <-;
        cbn [snd] in Heq0; rewrite <- Heq0; apply variable_flags_length.
    - cbn [snd] in Heq2. injection Heq2 as _ <-.
      cbn [snd cvt] in Heq1. injection Heq1 as _ <-.
      cbn [snd] in Heq0. rewrite <- Heq0. apply variable_flags_length. }
  { (* Coverage *)
    destruct er as [qvars (head_ptr & rest_ptrs) write_vars write_clauses write_unifs] eqn:Her.
    cbn [Defs.query_clause_ptrs Defs.query_vars fst snd].
    intros j Hj.
    (* Get compile step for NoDup *)
    pose proof (@QueryOptSound.in_compiled_rules_build_rule_set
      positive positive_Eqb Pos.lt Pos.succ positive_default
      positive TrieMap.trie_map TrieMap.ptree_map_plus
      TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
      rf rules _
      Hin) as (rule & st0 & st1 & _ & Hcompile).
    (* NoDup qvars *)
    pose proof (@QueryOptSound.compile_rule_inl_NoDup_query_vars
      positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pos.succ positive_default
      positive TrieMap.trie_map TrieMap.trie_map
      (fun A => @FullPosTrie.full_pos_trie_map A)
      rf rule st0 _ st1 Hcompile) as HNoDup_qvars.
    cbn [Defs.query_vars] in HNoDup_qvars.
    (* qvars[j] ∈ qvars *)
    pose proof (@nth_In positive j qvars positive_default Hj) as Hj_in.
    (* compiled_rules_qvar_coverage: get atom covering qvars[j] *)
    pose proof (@QueryOptSound.compiled_rules_qvar_coverage
      positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pos.lt Pos.succ positive_default
      positive positive_Eqb BuildTriesDepth.positive_Eqb_ok'
      TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
      TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A)
      (fun A => @FullPosTrie.full_pos_trie_map A)
      (fun x y h1 h2 => Pos.lt_irrefl x (Pos.lt_trans _ _ _ h1 h2))
      Pos.lt_succ_diag_r Pos.lt_trans
      TrieMap.ptree_map_plus_ok
      rf rules
      {| Defs.query_vars := qvars; Defs.query_clause_ptrs := (head_ptr, rest_ptrs);
         Defs.write_vars := write_vars; Defs.write_clauses := write_clauses;
         Defs.write_unifications := write_unifs |}
      Hin (nth j qvars positive_default) Hj_in)
      as (a & Ha_in & Hx_in_a).
    cbn [Defs.query_clause_ptrs Defs.query_vars uncurry Semantics.query_atoms] in Ha_in.
    apply in_map_iff in Ha_in.
    destruct Ha_in as [ptr_i [Ha_eq Hptr_i_in]].
    destruct ptr_i as [f_i n_i cvars_i].
    (* compiled_rules_ptr_valid for bounds *)
    pose proof (@QueryOptSound.compiled_rules_ptr_valid
      positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pos.lt Pos.succ positive_default
      positive positive_Eqb BuildTriesDepth.positive_Eqb_ok'
      TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
      TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A)
      (fun A => @FullPosTrie.full_pos_trie_map A)
      (fun x y h1 h2 => Pos.lt_irrefl x (Pos.lt_trans _ _ _ h1 h2))
      Pos.lt_succ_diag_r Pos.lt_trans
      TrieMap.ptree_map_plus_ok
      rf rules
      {| Defs.query_vars := qvars; Defs.query_clause_ptrs := (head_ptr, rest_ptrs);
         Defs.write_vars := write_vars; Defs.write_clauses := write_clauses;
         Defs.write_unifications := write_unifs |}
      Hin f_i n_i cvars_i Hptr_i_in)
      as (q_f' & cargs' & cv' & Pf & HgetQc' & Hgetm' & HcvarsEq' & Hcargs_lt & Hcv_lt).
    (* Establish qvars[j] ∈ cvars_i *)
    assert (Hx_cvars : In (nth j qvars positive_default) cvars_i). {
      apply (atom_ret_args_in_cvars cvars_i cargs' cv' Hcargs_lt Hcv_lt).
      (* Hx_in_a : In x (atom_ret a :: atom_args a) where a is built from cvars_i *)
      rewrite HgetQc', Hgetm' in Ha_eq.
      cbn [fst snd] in Ha_eq.
      rewrite <- Ha_eq in Hx_in_a.
      cbn [Defs.atom_ret Defs.atom_args] in Hx_in_a.
      exact Hx_in_a. }
    cbn [Defs.query_vars] in HcvarsEq'.
    rewrite HcvarsEq' in Hx_cvars.
    apply filter_In in Hx_cvars. destruct Hx_cvars as [_ Hpf_j].
    (* Pick the branch: head_ptr or rest_ptrs *)
    cbn [Defs.query_clause_ptrs uncurry fst snd] in Hptr_i_in.
    destruct Hptr_i_in as [Hhead | Hrest].
    { (* head_ptr = ptr_i *)
      left.
      rewrite Hhead.
      cbn [Defs.trie_of_clause toc snd cvt
           Defs.query_ptr_symbol Defs.query_ptr_ptr Defs.query_ptr_args].
      destruct (map.get DBT f_i) as [tl|].
      { destruct (unwrap_with_default (map.get tl n_i)) as [tot fr].
        destruct (eqb n_i frontier_n); cbn [snd].
        all: (replace qv with qvars in * by reflexivity;
              rewrite HcvarsEq';
              rewrite (@BuildTriesDepth.variable_flags_eq_map_filter
                         positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pf qvars HNoDup_qvars);
              erewrite (nth_map_lt Pf qvars j false positive_default Hj);
              exact Hpf_j). }
      { cbn [snd]. replace qv with qvars in * by reflexivity. rewrite HcvarsEq'.
        rewrite (@BuildTriesDepth.variable_flags_eq_map_filter
                   positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pf qvars HNoDup_qvars).
        erewrite (nth_map_lt Pf qvars j false positive_default Hj). exact Hpf_j. } }
    { (* ptr_i ∈ rest_ptrs *)
      right.
      refine (ex_intro _
        (snd (cvt (toc {| Defs.query_ptr_symbol := f_i; Defs.query_ptr_ptr := n_i;
                          Defs.query_ptr_args := cvars_i |}))) _).
      split.
      { apply in_map_iff.
        refine (ex_intro _ (cvt (toc {| Defs.query_ptr_symbol := f_i; Defs.query_ptr_ptr := n_i;
                                        Defs.query_ptr_args := cvars_i |})) (conj eq_refl _)).
        apply in_map_iff.
        refine (ex_intro _ (toc {| Defs.query_ptr_symbol := f_i; Defs.query_ptr_ptr := n_i;
                                   Defs.query_ptr_args := cvars_i |}) (conj eq_refl _)).
        apply in_map_iff.
        exact (ex_intro _ {| Defs.query_ptr_symbol := f_i; Defs.query_ptr_ptr := n_i;
                              Defs.query_ptr_args := cvars_i |} (conj eq_refl Hrest)). }
      { cbn [Defs.trie_of_clause toc snd cvt
             Defs.query_ptr_symbol Defs.query_ptr_ptr Defs.query_ptr_args].
        destruct (map.get DBT f_i) as [tl|].
        { destruct (unwrap_with_default (map.get tl n_i)) as [tot fr].
          destruct (eqb n_i frontier_n); cbn [snd].
          all: (replace qv with qvars in * by reflexivity;
                rewrite HcvarsEq';
                rewrite (@BuildTriesDepth.variable_flags_eq_map_filter
                           positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pf qvars HNoDup_qvars);
                erewrite (nth_map_lt Pf qvars j false positive_default Hj);
                exact Hpf_j). }
        { cbn [snd]. replace qv with qvars in * by reflexivity. rewrite HcvarsEq'.
          rewrite (@BuildTriesDepth.variable_flags_eq_map_filter
                     positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pf qvars HNoDup_qvars).
          erewrite (nth_map_lt Pf qvars j false positive_default Hj).
          exact Hpf_j. } } } }
Qed.

(* ============================================================================
   UNIT D: trie_join_H9 and trie_join_H10
   The two trie obligations at Automation.v:468/469 and :504/505.
   These discharge the last admits and make egraph_sound axiom-free.
   ============================================================================ *)

(* Local abbreviations for the fixed merge/merge_comm/merge_assoc at unit. *)
Local Notation merge_fn := (fun _ _ : unit => tt).
Local Notation merge_comm_pf := (fun (a b : unit) => @eq_refl unit tt).
Local Notation merge_assoc_pf := (fun (a b c : unit) => @eq_refl unit tt).

(* Helper: filter id (repeat true n) = repeat true n *)
Lemma filter_id_repeat_true (n : nat) : filter id (repeat true n) = repeat true n.
Proof.
  induction n; cbn [repeat filter id]; [reflexivity|].
  rewrite IHn; reflexivity.
Qed.

(* Helper: derive length cvars1 = length (filter id (variable_flags qv cvars1))
   using compiled_rules_ptr_shape to get cvars1 = filter Pf qv. *)
Lemma flags_filter_id_len
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (f n : positive) (cvars : list positive)
  (Hptr : In (Defs.Build_erule_query_ptr positive positive f n cvars)
             (uncurry cons (Defs.query_clause_ptrs positive positive er))) :
  length (filter id (Defs.variable_flags positive positive_Eqb
                       (Defs.query_vars positive positive er) cvars))
  = length cvars.
Proof.
  destruct (@QueryOptSound.compiled_rules_ptr_shape
    positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pos.lt Pos.succ positive_default
    positive positive_Eqb BuildTriesDepth.positive_Eqb_ok'
    TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
    TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A)
    (fun A => @FullPosTrie.full_pos_trie_map A)
    (fun x y h1 h2 => Pos.lt_irrefl x (Pos.lt_trans _ _ _ h1 h2))
    Pos.lt_succ_diag_r Pos.lt_trans
    TrieMap.ptree_map_plus_ok
    rf rules er Hin f n cvars Hptr)
    as (q_f & cargs & cv & out & args & HgetQc & Hgetm & HNoDup & Hincl & Hcvars & Hcargs_eq & Hcv_eq).
  set (Pf := fun x => inb x (out :: args)) in *.
  rewrite Hcvars.
  exact (@BuildTriesDepth.variable_flags_filter_id_len
           positive positive_Eqb BuildTriesDepth.positive_Eqb_ok' Pf
           (Defs.query_vars positive positive er)).
Qed.

(* Helper: S2 - each input trie has uniform depth = # true flags.
   Abstracted out because both H9 and H10 need it. *)
Lemma trie_inputs_fpt_depth
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (e : Defs.instance positive positive TrieMap.trie_map TrieMap.trie_map
         (fun A => @FullPosTrie.full_pos_trie_map A) (option positive))
  (frontier_n : positive)
  (p : @FullPosTrie.full_pos_trie_map unit * list bool) :
  In p (uncurry cons (ne_map
    (@Defs.trie_of_clause positive positive_Eqb positive
       TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
       (Defs.query_vars positive positive er)
       (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
               TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
               (fun A => @FullPosTrie.full_pos_trie_map A)
               (option positive) (brs rf rules) e))
       frontier_n)
    (Defs.query_clause_ptrs positive positive er))) ->
  fpt_depth (fst p) (length (filter id (snd p))).
Proof.
  intros Hp.
  (* uncurry cons (ne_map f (a, l)) = f a :: map f l *)
  cbn [uncurry ne_map fst snd] in Hp.
  (* Hp : In p (toc (fst ptrs) :: map toc (snd ptrs)) *)
  destruct Hp as [Hhead | Hrest].
  - (* p = toc (fst ptrs) *)
    subst p.
    destruct (fst (Defs.query_clause_ptrs positive positive er)) as [f1 n1 cvars1] eqn:Hhead_ptr.
    assert (Hptr_in : In (Defs.Build_erule_query_ptr positive positive f1 n1 cvars1)
                         (uncurry cons (Defs.query_clause_ptrs positive positive er))).
    { destruct (Defs.query_clause_ptrs positive positive er) as [hptr rptrs].
      cbn [uncurry fst] in Hhead_ptr. rewrite <- Hhead_ptr.
      left. reflexivity. }
    pose proof (trie_of_clause_depth rf rules er Hin e frontier_n f1 n1 cvars1 Hptr_in) as Hd_fpt.
    (* snd (toc frontier_n ptr) = variable_flags qv cvars1 *)
    assert (Hsnd : snd (Defs.trie_of_clause positive positive_Eqb positive TrieMap.trie_map
                          TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
                          (Defs.query_vars positive positive er)
                          (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                                  TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                                  (fun A => @FullPosTrie.full_pos_trie_map A)
                                  (option positive) (brs rf rules) e))
                          frontier_n
                          (Defs.Build_erule_query_ptr positive positive f1 n1 cvars1))
                  = Defs.variable_flags positive positive_Eqb (Defs.query_vars positive positive er) cvars1).
    { unfold Defs.trie_of_clause. cbn [Defs.query_ptr_args snd].
      destruct (map.get _ f1); [destruct (unwrap_with_default _) as [tot fr]; destruct (eqb n1 frontier_n)|]; reflexivity. }
    rewrite Hsnd.
    rewrite (flags_filter_id_len rf rules er Hin f1 n1 cvars1 Hptr_in).
    exact Hd_fpt.
  - (* p ∈ map toc (snd ptrs) *)
    apply in_map_iff in Hrest.
    destruct Hrest as [ptr [Heq Hptr_in]].
    subst p.
    destruct ptr as [f1 n1 cvars1].
    assert (Hptr_uncurry : In (Defs.Build_erule_query_ptr positive positive f1 n1 cvars1)
                              (uncurry cons (Defs.query_clause_ptrs positive positive er))).
    { destruct (Defs.query_clause_ptrs positive positive er) as [hptr rptrs].
      cbn [uncurry snd] in Hptr_in. right. exact Hptr_in. }
    pose proof (trie_of_clause_depth rf rules er Hin e frontier_n f1 n1 cvars1 Hptr_uncurry) as Hd_fpt.
    assert (Hsnd : snd (Defs.trie_of_clause positive positive_Eqb positive TrieMap.trie_map
                          TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
                          (Defs.query_vars positive positive er)
                          (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                                  TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                                  (fun A => @FullPosTrie.full_pos_trie_map A)
                                  (option positive) (brs rf rules) e))
                          frontier_n
                          (Defs.Build_erule_query_ptr positive positive f1 n1 cvars1))
                  = Defs.variable_flags positive positive_Eqb (Defs.query_vars positive positive er) cvars1).
    { unfold Defs.trie_of_clause. cbn [Defs.query_ptr_args snd].
      destruct (map.get _ f1); [destruct (unwrap_with_default _) as [tot fr]; destruct (eqb n1 frontier_n)|]; reflexivity. }
    rewrite Hsnd.
    rewrite (flags_filter_id_len rf rules er Hin f1 n1 cvars1 Hptr_uncurry).
    exact Hd_fpt.
Qed.

(* Helper: S3 - wf_tries at any key of length N.
   Abstracted out because both H9 and H10 need it. *)
Lemma trie_inputs_wf_at
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (e : Defs.instance positive positive TrieMap.trie_map TrieMap.trie_map
         (fun A => @FullPosTrie.full_pos_trie_map A) (option positive))
  (frontier_n : positive)
  (x : list positive)
  (Hlen : length x = length (Defs.query_vars positive positive er)) :
  let cvt := fun (q : @FullPosTrie.full_pos_trie_map unit * list bool) =>
               (FullPosTrieConv.fpt_to_pt (fst q), snd q) in
  let toc := @Defs.trie_of_clause positive positive_Eqb positive
               TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
               (Defs.query_vars positive positive er)
               (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                       TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                       (fun A => @FullPosTrie.full_pos_trie_map A)
                       (option positive) (brs rf rules) e))
               frontier_n in
  PosListMapIntersectSpec.wf_tries x
    (cvt (fst (ne_map toc (Defs.query_clause_ptrs positive positive er))),
     map cvt (snd (ne_map toc (Defs.query_clause_ptrs positive positive er)))).
Proof.
  intros cvt toc.
  set (qv := Defs.query_vars positive positive er) in toc, Hlen |- *.
  set (DBT := fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                    TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                    (fun A => @FullPosTrie.full_pos_trie_map A)
                    (option positive) (brs rf rules) e)) in toc |- *.
  pose proof (fun p Hp => trie_inputs_fpt_depth rf rules er Hin e frontier_n p Hp) as Hfd.
  (* fold qv, DBT in Hfd *)
  change (Defs.query_vars positive positive er) with qv in Hfd.
  change (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                    TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                    (fun A => @FullPosTrie.full_pos_trie_map A)
                    (option positive) (brs rf rules) e)) with DBT in Hfd.
  unfold PosListMapIntersectSpec.wf_tries.
  (* Helper: for any ptr in query_clause_ptrs, wf_input x (cvt (toc ptr)) *)
  assert (Hwf_ptr : forall ptr,
    In ptr (uncurry cons (Defs.query_clause_ptrs positive positive er)) ->
    PosListMapIntersectSpec.wf_input x (cvt (toc ptr))).
  { intros [f0 n0 cvars0] Hptr0.
    unfold PosListMapIntersectSpec.wf_input. cbn [toc cvt].
    split.
    + (* length (snd (cvt (toc ptr))) = length x *)
      assert (Hsnd0 : snd (toc (Defs.Build_erule_query_ptr positive positive f0 n0 cvars0))
                     = Defs.variable_flags positive positive_Eqb qv cvars0).
      { unfold toc. unfold Defs.trie_of_clause. cbn [Defs.query_ptr_args snd].
        destruct (map.get DBT f0) as [tl0|].
        - destruct (unwrap_with_default (map.get tl0 n0)) as [tot fr].
          destruct (eqb n0 frontier_n); reflexivity.
        - reflexivity. }
      cbn [cvt snd fst]. rewrite Hsnd0.
      rewrite @BuildTriesDepth.variable_flags_length. symmetry. exact Hlen.
    + (* depth *)
      specialize (Hfd (toc (Defs.Build_erule_query_ptr positive positive f0 n0 cvars0))).
      assert (Hp : In (toc (Defs.Build_erule_query_ptr positive positive f0 n0 cvars0))
                      (uncurry cons (ne_map toc (Defs.query_clause_ptrs positive positive er)))).
      { cbn [uncurry ne_map fst snd].
        destruct (Defs.query_clause_ptrs positive positive er) as [hptr rptrs] eqn:Hptrs.
        cbn [uncurry fst snd] in Hptr0.
        destruct Hptr0 as [Hh | Hr].
        - left. f_equal. exact Hh.
        - right. apply in_map_iff.
          exact (ex_intro _ (Defs.Build_erule_query_ptr positive positive f0 n0 cvars0)
                           (conj eq_refl Hr)). }
      specialize (Hfd Hp).
      assert (Hsnd0 : snd (toc (Defs.Build_erule_query_ptr positive positive f0 n0 cvars0))
                     = Defs.variable_flags positive positive_Eqb qv cvars0).
      { unfold toc. unfold Defs.trie_of_clause. cbn [Defs.query_ptr_args snd].
        destruct (map.get DBT f0) as [tl0|].
        - destruct (unwrap_with_default (map.get tl0 n0)) as [tot fr].
          destruct (eqb n0 frontier_n); reflexivity.
        - reflexivity. }
      rewrite Hsnd0 in Hfd.
      unfold qv in Hfd.
      rewrite (flags_filter_id_len rf rules er Hin f0 n0 cvars0 Hptr0) in Hfd.
      (* Hfd : fpt_depth (fst (toc ptr)) (length cvars0) *)
      cbn [cvt fst snd].
      (* rewrite snd (toc ptr) = variable_flags ... in the GOAL to unify the lengths *)
      rewrite Hsnd0.
      unfold qv.
      rewrite (flags_filter_id_len rf rules er Hin f0 n0 cvars0 Hptr0).
      set (t0 := fst (toc (Defs.Build_erule_query_ptr positive positive f0 n0 cvars0))).
      pose proof (FullPosTrieConv.fpt_to_pt_has_depth' t0 (length cvars0) Hfd) as Hdepth_pt.
      unfold depth in Hdepth_pt.
      destruct (FullPosTrieConv.fpt_to_pt t0) as [pt'|].
      * exact (@FullPosTrieConv.depth'_to_has_depth' unit _ pt' Hdepth_pt).
      * exact I. }
  split.
  - (* head *)
    apply Hwf_ptr.
    destruct (Defs.query_clause_ptrs positive positive er) as [hptr rptrs].
    cbn [uncurry fst]. left. reflexivity.
  - (* tail *)
    rewrite Forall_forall.
    intros cp Hcp.
    apply in_map_iff in Hcp.
    destruct Hcp as [p [Heq_cp Hp_in_rest]].
    subst cp.
    apply in_map_iff in Hp_in_rest.
    destruct Hp_in_rest as [ptr [Heq_p Hptr_in]].
    subst p.
    apply Hwf_ptr.
    destruct (Defs.query_clause_ptrs positive positive er) as [hptr rptrs] eqn:Hptrs.
    cbn [uncurry snd] in Hptr_in. cbn [uncurry]. right. exact Hptr_in.
Qed.

(* Helper: the compat_intersect R has uniform depth N.
   Derived from pt_spaced_intersect_depth using wf_tries at repeat xH N and Hbools. *)
Lemma trie_intersect_depth
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (e : Defs.instance positive positive TrieMap.trie_map TrieMap.trie_map
         (fun A => @FullPosTrie.full_pos_trie_map A) (option positive))
  (frontier_n : positive) :
  let qv := Defs.query_vars positive positive er in
  let N := length qv in
  let DBT := fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                    TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                    (fun A => @FullPosTrie.full_pos_trie_map A)
                    (option positive) (brs rf rules) e) in
  let toc := @Defs.trie_of_clause positive positive_Eqb positive
               TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A) qv DBT frontier_n in
  let tries_ne := ne_map toc (Defs.query_clause_ptrs positive positive er) in
  let cvt := fun (q : @FullPosTrie.full_pos_trie_map unit * list bool) =>
               (FullPosTrieConv.fpt_to_pt (fst q), snd q) in
  depth (compat_intersect merge_fn (cvt (fst tries_ne), map cvt (snd tries_ne))) N.
Proof.
  (* The let-binders in the statement match the concrete terms below by definitional equality.
     We use `change` to convert the goal to a form with explicit `set`-bound names. *)
  intros qv N DBT toc tries_ne cvt.
  set (qv' := Defs.query_vars positive positive er).
  set (N' := length qv').
  set (DBT' := fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                     TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                     (fun A => @FullPosTrie.full_pos_trie_map A)
                     (option positive) (brs rf rules) e)).
  set (toc_fn := @Defs.trie_of_clause positive positive_Eqb positive
                    TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A) qv' DBT' frontier_n).
  set (tries_ne' := ne_map toc_fn (Defs.query_clause_ptrs positive positive er)).
  set (cvt' := fun (q : @FullPosTrie.full_pos_trie_map unit * list bool) =>
                 (FullPosTrieConv.fpt_to_pt (fst q), snd q)).
  (* The intro'd let-binders are definitionally equal to the set-bound ones *)
  change (depth (compat_intersect merge_fn (cvt' (fst tries_ne'), map cvt' (snd tries_ne'))) N').
  (* B2 via intersection_inputs_combined_bools *)
  pose proof (intersection_inputs_combined_bools rf rules er Hin e frontier_n) as Hb.
  change (PosListMapIntersectSpec.combined_bools
            (cvt' (fst tries_ne'), map cvt' (snd tries_ne')) = repeat true N') in Hb.
  (* wf_tries at repeat xH N' *)
  assert (Hwf_dummy : PosListMapIntersectSpec.wf_tries (repeat xH N')
    (cvt' (fst tries_ne'), map cvt' (snd tries_ne'))).
  { apply (trie_inputs_wf_at rf rules er Hin e frontier_n (repeat xH N')).
    rewrite repeat_length. reflexivity. }
  (* pt_spaced_intersect_depth *)
  pose proof (@PosListMapIntersectSpec.pt_spaced_intersect_depth unit _
                merge_fn merge_comm_pf merge_assoc_pf
                (cvt' (fst tries_ne'), map cvt' (snd tries_ne'))
                (repeat xH N')
                Hwf_dummy) as Hdepth_raw.
  assert (Hlf : length (filter id (PosListMapIntersectSpec.combined_bools
                  (cvt' (fst tries_ne'), map cvt' (snd tries_ne')))) = N').
  { rewrite Hb. rewrite filter_id_repeat_true. apply repeat_length. }
  rewrite <- Hlf.
  exact Hdepth_raw.
Qed.

(* ============================================================================
   trie_join_H9: intersection key sigma has length = number of query vars.
   ============================================================================ *)
Lemma trie_join_H9
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (e : Defs.instance positive positive TrieMap.trie_map TrieMap.trie_map
         (fun A => @FullPosTrie.full_pos_trie_map A) (option positive)) :
  forall frontier_n sigma,
    In sigma (@Defs.intersection_keys positive (fun A => @FullPosTrie.full_pos_trie_map A)
                (@FullPosTrieConv.fpt_spaced_intersect)
                (ne_map (@Defs.trie_of_clause positive positive_Eqb positive
                           TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
                           (Defs.query_vars positive positive er)
                           (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                                   TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                                   (fun A => @FullPosTrie.full_pos_trie_map A)
                                   (option positive) (brs rf rules) e))
                           frontier_n)
                         (Defs.query_clause_ptrs positive positive er))) ->
    length (Defs.query_vars positive positive er) = length sigma.
Proof.
  intros frontier_n sigma Hin_sig.
  set (qv := Defs.query_vars positive positive er).
  set (N := length qv).
  set (DBT := fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                    TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                    (fun A => @FullPosTrie.full_pos_trie_map A)
                    (option positive) (brs rf rules) e)).
  set (toc_fn := @Defs.trie_of_clause positive positive_Eqb positive
                   TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A) qv DBT).
  set (tries_ne := ne_map (toc_fn frontier_n) (Defs.query_clause_ptrs positive positive er)).
  set (cvt := fun (q : @FullPosTrie.full_pos_trie_map unit * list bool) =>
               (FullPosTrieConv.fpt_to_pt (fst q), snd q)).
  set (R := compat_intersect merge_fn (cvt (fst tries_ne), map cvt (snd tries_ne))).
  (* Get depth *)
  pose proof (trie_intersect_depth rf rules er Hin e frontier_n) as Hdepth.
  change (depth (compat_intersect merge_fn (cvt (fst tries_ne), map cvt (snd tries_ne))) N)
    in Hdepth.
  (* Unfold intersection_keys *)
  unfold Defs.intersection_keys in Hin_sig.
  change (In sigma (@map.keys (list positive) unit (@FullPosTrie.full_pos_trie_map unit)
             (FullPosTrieConv.fpt_spaced_intersect merge_fn tries_ne))) in Hin_sig.
  (* fpt_spaced_intersect merge_fn tries_ne = pt_to_fpt R *)
  assert (Hsimp : FullPosTrieConv.fpt_spaced_intersect merge_fn tries_ne =
                  FullPosTrieConv.pt_to_fpt R).
  { unfold FullPosTrieConv.fpt_spaced_intersect, FullPosTrieConv.fpt_spaced_intersect_via_conv,
      R, tries_ne. cbn [fst snd]. reflexivity. }
  rewrite Hsimp in Hin_sig.
  (* map.in_keys_inv: In sigma (map.keys (pt_to_fpt R)) -> fpt_get (pt_to_fpt R) sigma <> None *)
  assert (Hbs : forall x y : list positive,
    BoolSpec (x = y) (x <> y) (if list_eq_dec Pos.eq_dec x y then true else false)).
  { intros x y. destruct (list_eq_dec Pos.eq_dec x y); constructor; assumption. }
  pose proof (@Properties.map.in_keys_inv (list positive) unit
                (@FullPosTrie.full_pos_trie_map unit) (@FullPosTrie.full_pos_trie_map_ok unit)
                _ Hbs sigma (FullPosTrieConv.pt_to_fpt R) Hin_sig) as Hget_ne.
  change (@map.get (list positive) unit (@FullPosTrie.full_pos_trie_map unit)
            (FullPosTrieConv.pt_to_fpt R) sigma)
    with (FullPosTrie.fpt_get (FullPosTrieConv.pt_to_fpt R) sigma) in Hget_ne.
  destruct (FullPosTrie.fpt_get (FullPosTrieConv.pt_to_fpt R) sigma) as [v|] eqn:Hfget.
  - (* fpt_depth_key_length *)
    pose proof (FullPosTrieConv.pt_to_fpt_depth R N Hdepth) as HfptD.
    symmetry.
    exact (@FullPosTrieConv.fpt_depth_key_length unit (FullPosTrieConv.pt_to_fpt R) N HfptD sigma v Hfget).
  - exfalso. apply Hget_ne. reflexivity.
Qed.

(* ============================================================================
   trie_join_H10: for each sigma in intersection keys and each clause ptr,
   the projected lookup in that ptr's trie hits Some tt.
   ============================================================================ *)
Lemma trie_join_H10
  (rf : nat) (rules : list (Semantics.sequent positive positive))
  (er : Defs.erule positive positive)
  (Hin : In er (Defs.compiled_rules positive positive TrieMap.trie_map TrieMap.trie_map (brs rf rules)))
  (e : Defs.instance positive positive TrieMap.trie_map TrieMap.trie_map
         (fun A => @FullPosTrie.full_pos_trie_map A) (option positive)) :
  forall frontier_n sigma,
    In sigma (@Defs.intersection_keys positive (fun A => @FullPosTrie.full_pos_trie_map A)
                (@FullPosTrieConv.fpt_spaced_intersect)
                (ne_map (@Defs.trie_of_clause positive positive_Eqb positive
                           TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
                           (Defs.query_vars positive positive er)
                           (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                                   TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                                   (fun A => @FullPosTrie.full_pos_trie_map A)
                                   (option positive) (brs rf rules) e))
                           frontier_n)
                         (Defs.query_clause_ptrs positive positive er))) ->
    forall fsym nptr cvars,
      In (Defs.Build_erule_query_ptr positive positive fsym nptr cvars)
         (uncurry cons (Defs.query_clause_ptrs positive positive er)) ->
      @map.get (list positive) unit (@FullPosTrie.full_pos_trie_map unit)
        (fst (@Defs.trie_of_clause positive positive_Eqb positive
                TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A)
                (Defs.query_vars positive positive er)
                (fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                        TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                        (fun A => @FullPosTrie.full_pos_trie_map A)
                        (option positive) (brs rf rules) e))
                frontier_n
                (Defs.Build_erule_query_ptr positive positive fsym nptr cvars)))
        (map fst (filter snd (combine sigma
           (Defs.variable_flags positive positive_Eqb
              (Defs.query_vars positive positive er) cvars))))
      = Some tt.
Proof.
  intros frontier_n sigma Hin_sig fsym nptr cvars Hptr.
  set (qv := Defs.query_vars positive positive er).
  set (N := length qv).
  set (DBT := fst (@Defs.build_tries positive positive_Eqb positive TrieMap.trie_map
                    TrieMap.ptree_map_plus TrieMap.trie_map TrieMap.ptree_map_plus
                    (fun A => @FullPosTrie.full_pos_trie_map A)
                    (option positive) (brs rf rules) e)).
  set (toc_fn := @Defs.trie_of_clause positive positive_Eqb positive
                   TrieMap.trie_map TrieMap.trie_map (fun A => @FullPosTrie.full_pos_trie_map A) qv DBT).
  set (tries_ne := ne_map (toc_fn frontier_n) (Defs.query_clause_ptrs positive positive er)).
  set (cvt := fun (q : @FullPosTrie.full_pos_trie_map unit * list bool) =>
               (FullPosTrieConv.fpt_to_pt (fst q), snd q)).
  set (R := compat_intersect merge_fn (cvt (fst tries_ne), map cvt (snd tries_ne))).
  (* H9: length sigma = N *)
  pose proof (trie_join_H9 rf rules er Hin e frontier_n sigma Hin_sig) as Hlen.
  (* Hlen : N = length sigma; so length sigma = N via symmetry *)
  (* Hbools *)
  pose proof (intersection_inputs_combined_bools rf rules er Hin e frontier_n) as Hbools.
  change (PosListMapIntersectSpec.combined_bools
            (cvt (fst tries_ne), map cvt (snd tries_ne)) = repeat true N) in Hbools.
  (* Hdepth *)
  pose proof (trie_intersect_depth rf rules er Hin e frontier_n) as Hdepth.
  change (depth (compat_intersect merge_fn (cvt (fst tries_ne), map cvt (snd tries_ne))) N)
    in Hdepth.
  (* wf_tries sigma *)
  pose proof (trie_inputs_wf_at rf rules er Hin e frontier_n sigma (eq_sym Hlen)) as Hwf.
  change (PosListMapIntersectSpec.wf_tries sigma
            (cvt (fst tries_ne), map cvt (snd tries_ne))) in Hwf.
  (* Unfold intersection_keys in Hin_sig *)
  unfold Defs.intersection_keys in Hin_sig.
  change (In sigma (@map.keys (list positive) unit (@FullPosTrie.full_pos_trie_map unit)
             (FullPosTrieConv.fpt_spaced_intersect merge_fn tries_ne))) in Hin_sig.
  assert (Hsimp : FullPosTrieConv.fpt_spaced_intersect merge_fn tries_ne =
                  FullPosTrieConv.pt_to_fpt R).
  { unfold FullPosTrieConv.fpt_spaced_intersect, FullPosTrieConv.fpt_spaced_intersect_via_conv,
      R, tries_ne. cbn [fst snd]. reflexivity. }
  rewrite Hsimp in Hin_sig.
  (* p = toc_fn frontier_n (Build_erule_query_ptr fsym nptr cvars) in tries::rest *)
  set (p := toc_fn frontier_n (Defs.Build_erule_query_ptr positive positive fsym nptr cvars)).
  assert (Hp_in : In p (fst tries_ne :: snd tries_ne)).
  { unfold p, tries_ne.
    destruct (Defs.query_clause_ptrs positive positive er) as [hptr rptrs].
    cbn [ne_map fst snd uncurry] in Hptr |- *.
    destruct Hptr as [Hhead | Hrest_ptr].
    - left. rewrite <- Hhead. reflexivity.
    - right. apply in_map_iff.
      exact (ex_intro _ (Defs.Build_erule_query_ptr positive positive fsym nptr cvars)
                      (conj eq_refl Hrest_ptr)). }
  (* Apply fpt_spaced_intersect_inputs_hit *)
  (* snd p = variable_flags qv cvars *)
  assert (Hsnd_p : snd p = Defs.variable_flags positive positive_Eqb qv cvars).
  { unfold p. unfold toc_fn. unfold Defs.trie_of_clause. cbn [Defs.query_ptr_args snd].
    destruct (map.get DBT fsym) as [tl0|].
    - destruct (unwrap_with_default (map.get tl0 nptr)) as [tot fr].
      destruct (eqb nptr frontier_n); reflexivity.
    - reflexivity. }
  (* Apply fpt_spaced_intersect_inputs_hit *)
  pose proof (@FullPosTrieConv.fpt_spaced_intersect_inputs_hit unit _
                merge_fn merge_comm_pf merge_assoc_pf
                (fst tries_ne) (snd tries_ne) sigma N
                Hin_sig (eq_sym Hlen) Hdepth Hbools Hwf
                (fun q Hq => trie_inputs_fpt_depth rf rules er Hin e frontier_n q Hq)
                p Hp_in) as (v & Hv).
  (* Hv : fpt_get (fst p) (map fst (filter snd (combine sigma (snd p)))) = Some v *)
  (* Goal has variable_flags qv cvars. Rewrite <-Hsnd_p to get snd p in goal. *)
  rewrite <- Hsnd_p.
  (* Now goal: map.get (fst p) (... snd p ...) = Some tt *)
  (* map.get = fpt_get by defeq *)
  change (@map.get (list positive) unit (@FullPosTrie.full_pos_trie_map unit) (fst p)
    (map fst (filter snd (combine sigma (snd p)))))
    with (FullPosTrie.fpt_get (fst p) (map fst (filter snd (combine sigma (snd p))))).
  destruct v. exact Hv.
Qed.
