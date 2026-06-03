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
