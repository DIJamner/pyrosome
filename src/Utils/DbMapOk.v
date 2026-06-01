(* ============================================================================
   Depth-indexed map-laws interface for e-graph db-tries.

   The e-graph's per-symbol tables are tries keyed on [list V] (the atom args),
   and at the positive instantiation the map family is [pos_trie_map], for which
   the full coqutil [map.ok] is PROVABLY FALSE (it quantifies over ill-formed
   mixed-depth tries; see WIP/PosTrieMapOk_false.v). However every db-trie that
   actually arises has all keys of a single fixed length (the symbol arity), and
   on that uniform-depth regime exactly the subset of laws the e-graph uses DOES
   hold.  [db_map_ok] packages that subset: a depth predicate plus the
   depth-restricted get/put/remove/fold laws.

   This record replaces the [V_trie_ok : forall A, map.ok (V_trie A)] Context in
   the e-graph soundness development.  The positive instance is
   [pos_trie_db_map_ok] in PosListMapLaws.v.
   ============================================================================ *)

From coqutil Require Import Map.Interface.

Set Implicit Arguments.

Section DbMapOk.
  Context {V : Type}.

  Record db_map_ok (mt : forall A, map.map (list V) A) : Type :=
    {
      (* depth predicate: [dmo_depth m n] means every key of [m] has length [n] *)
      dmo_depth : forall A, mt A -> nat -> Prop ;

      (* the empty map vacuously has every depth *)
      dmo_empty_depth : forall A n, dmo_depth A (map.empty : mt A) n ;

      dmo_get_empty : forall A (k : list V),
          map.get (map.empty : mt A) k = None ;

      dmo_get_put_same : forall A (m : mt A) k v,
          dmo_depth A m (length k) ->
          map.get (map.put m k v) k = Some v ;

      dmo_get_put_diff : forall A (m : mt A) k k' v,
          length k = length k' -> k <> k' -> dmo_depth A m (length k') ->
          map.get (map.put m k' v) k = map.get m k ;

      dmo_put_depth : forall A (m : mt A) k v,
          dmo_depth A m (length k) ->
          dmo_depth A (map.put m k v) (length k) ;

      dmo_get_remove_same : forall A (m : mt A) k,
          map.get (map.remove m k) k = None ;

      dmo_get_remove_diff : forall A (m : mt A) k k',
          length k = length k' -> k <> k' -> dmo_depth A m (length k') ->
          map.get (map.remove m k') k = map.get m k ;

      dmo_remove_depth : forall A (m : mt A) k n,
          dmo_depth A m n ->
          dmo_depth A (map.remove m k) n ;

      dmo_fold_spec : forall A (R : Type) (P : mt A -> R -> Prop)
                             (f : R -> list V -> A -> R) r0 n,
          P map.empty r0 ->
          (forall k v (m : mt A) r,
              length k = n -> dmo_depth A m n -> map.get m k = None -> P m r ->
              P (map.put m k v) (f r k v)) ->
          forall m, dmo_depth A m n -> P m (map.fold f r0 m) ;
    }.

End DbMapOk.

Arguments dmo_depth {V mt} _ {A}.
Arguments dmo_empty_depth {V mt} _ {A}.
Arguments dmo_get_empty {V mt} _ {A}.
Arguments dmo_get_put_same {V mt} _ {A}.
Arguments dmo_get_put_diff {V mt} _ {A}.
Arguments dmo_put_depth {V mt} _ {A}.
Arguments dmo_get_remove_same {V mt} _ {A}.
Arguments dmo_get_remove_diff {V mt} _ {A}.
Arguments dmo_remove_depth {V mt} _ {A}.
Arguments dmo_fold_spec {V mt} _ {A R}.
