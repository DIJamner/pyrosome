(* ============================================================================
   pos_trie_map_ok is FALSE  (machine-checked disproof)
   ============================================================================

   Context: src/Pyrosome/Tools/EGraph/Automation.v (StepInst / CongInst) takes
       Context (pos_trie_map_ok : forall A, map.ok (@pos_trie_map A)).
   as a hypothesis and feeds it to the generic e-graph soundness lemmas
   (ReducingCong, Section CongMain: parameter [V_trie_ok]).  The
   "trie-lawfulness" subproject set out to discharge it.  Its partner
   [trie_map_ok] (TrieMap.trie_map) IS true and is proven (src/Utils/TrieMapFold.v,
   commit 4406cbe).  This file shows the pos_trie half is NOT.

   WHY IT IS FALSE.
   [map.ok] requires, for ALL representations [m : rep], ALL keys [k], values [v]:
       get (put m k v) k = Some v          (get_put_same)
   But [rep = pos_trie = option pos_trie'] and [pos_trie'] admits a *leaf at the
   top* combined with a *non-empty key* -- an ill-formed, mixed-depth trie that
   map.ok still quantifies over.  On such a trie:
     - [pt_put'] on a [pos_trie_leaf] returns [pos_trie_leaf v] for ANY key,
       discarding the key (PosListMap.v line ~320:  pos_trie_leaf _, _ => pos_trie_leaf v).
     - [pt_get'] on a [pos_trie_leaf] with a NON-empty key falls through to the
       catch-all [_, _ => None] (PosListMap.v line ~302).
   Hence with  m := Some (pos_trie_leaf 7),  k := [1],  v := 9 :
       get (put m k v) k
     = pt_get (Some (pos_trie_leaf 9)) [1]
     = pt_get' (pos_trie_leaf 9) [1]
     = None                         (* leaf + non-empty key *)
     <> Some 9.
   So [get_put_same] fails, and [map.ok (@pos_trie_map positive)] is false; a
   fortiori [forall A, map.ok (@pos_trie_map A)] is false.

   The lemma below is the [vm_compute]+[discriminate] formalization of exactly
   that counterexample.  Verified Qed, 0 axioms, against the real PosListMap.v.

   CONSEQUENCE FOR THE PLAN.  See WIP/Rebuild_map.md / memory
   [[project-trie-lawfulness]].  In real e-graph use every key of a per-symbol
   db table has the SAME length (the symbol's arity), so the relevant tries are
   uniform-depth and DO satisfy the laws restricted to keys of that depth.  The
   depth invariant already exists ([depth']/[depth]/[has_depth'] in PosListMap.v
   ~904-921; [wf_tries] in PosListMapIntersectSpec.v ~66), and
   [pt_spaced_intersect_correct] already relies on it rather than on [map.ok].
   The fix is therefore an *interface* change (depth-indexed lawfulness threaded
   through [egraph_ok] and the generic soundness lemmas), NOT a proof of the
   stated [map.ok] -- which is impossible.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List.
Import ListNotations.
From Utils Require Import PosListMap.
From coqutil Require Import Map.Interface.

Lemma pos_trie_map_ok_is_false
  : ~ (forall A, map.ok (@pos_trie_map A)).
Proof.
  intro H.
  specialize (H positive).
  pose proof (map.get_put_same (map:=@pos_trie_map positive)
                (Some (pos_trie_leaf 7%positive)) [1%positive] 9%positive) as Hp.
  vm_compute in Hp.
  discriminate Hp.
Qed.
