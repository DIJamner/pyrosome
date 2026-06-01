(* ============================================================================
   Conversions between the two positive-list-keyed tries, and a conversion-
   wrapper generic-join.

   - [pos_trie] (PosListMap.v): the EFFICIENT query trie; carries
     [pt_spaced_intersect] (the generic join) and its 3352-line correctness
     proof, but [map.ok] is provably FALSE (mixed-depth tries break get_put).
   - [fpt]/[full_pos_trie_map] (FullPosTrie.v): a fattened (3-constructor)
     LAWFUL map ([map.ok] holds unconditionally), used as the e-graph carrier.

   To run the pos_trie-specialized generic join on the lawful [fpt] carrier we
   convert at the intersection boundary: [fpt_spaced_intersect] converts each
   input [fpt] to a [pos_trie], runs [compat_intersect], and converts back.
   This is a TEMPORARY wrapper (runtime conversion cost); a native [fpt]
   generic-join is a planned optimization that will reuse the get-preservation
   lemmas below.

   The conversions are fold-rebuild: fold the source map and re-[map.put] each
   binding into an empty target.  The two reps (option pos_trie' vs option fpt')
   are DISTINCT types, so the [map.put]/[map.empty]/[map.fold] instances are
   inferred unambiguously -- but [rep] is a Coercion and is NOT resolved back to
   its instance, so every projection must name its instance explicitly.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils Default FullPosTrie PosListMap PosListMapLaws.

Set Implicit Arguments.

Section Conv.
  Context {B : Type}.

  Definition pt_to_fpt (t : @pos_trie B) : @FullPosTrie.fpt B :=
    @map.fold (list positive) B (@pos_trie_map B) (@FullPosTrie.fpt B)
      (fun acc k v => @map.put (list positive) B (@FullPosTrie.full_pos_trie_map B) acc k v)
      (@map.empty (list positive) B (@FullPosTrie.full_pos_trie_map B)) t.

  Definition fpt_to_pt (t : @FullPosTrie.fpt B) : @pos_trie B :=
    @map.fold (list positive) B (@FullPosTrie.full_pos_trie_map B) (@pos_trie B)
      (fun acc k v => @map.put (list positive) B (@pos_trie_map B) acc k v)
      (@map.empty (list positive) B (@pos_trie_map B)) t.

End Conv.

Definition fpt_spaced_intersect {B} `{WithDefault B} (merge : B -> B -> B)
  (tries : (@FullPosTrie.fpt B * list bool)
           * list (@FullPosTrie.fpt B * list bool))
  : @FullPosTrie.fpt B :=
  let conv := fun p : @FullPosTrie.fpt B * list bool => (fpt_to_pt (fst p), snd p) in
  pt_to_fpt (compat_intersect merge (conv (fst tries), List.map conv (snd tries))).
