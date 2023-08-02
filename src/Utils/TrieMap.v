Require Import ZArith.
Require Import coqutil.Map.Interface.
Require Import Tries.Canonical.
Import PTree.

Require Utils.ArrayList.

Section Folds.
  Context {B A : Type}.

  Section __.
    Context (f : A -> positive -> B -> A).
    
    (* positives consed when they should be appended*)
    Fixpoint trie_fold' (acc : A) (m : PTree.tree' B)
      (*TODO: find a better way*)
      (num : positive -> positive) : A :=
      match m with
      | Node001 r => trie_fold' acc r (fun a => num (xI a))
      | Node010 y => f acc (num xH) y
      | Node011 y r =>
          let acc := f acc (num xH) y in
          trie_fold' acc r (fun a => num (xI a))
      | Node100 l => trie_fold' acc l (fun a => num (xO a))
      | Node101 l r =>      
          let acc := trie_fold' acc r (fun a => num (xI a)) in
          trie_fold' acc l (fun a => num (xO a))
      | Node110 l y => 
          let acc := f acc (num xH) y in
          trie_fold' acc l (fun a => num (xO a))
      | Node111 l y r =>
          let acc := f acc (num xH) y in
          let acc := trie_fold' acc r (fun a => num (xI a)) in
          trie_fold' acc l (fun a => num (xO a))
      end.


    Definition trie_fold (acc : A) (m : PTree.t B) : A :=
      match m with
      | Empty => acc
      | Nodes m' => trie_fold' acc m' id
      end.

  End __.
  

  Section __.
    Context (f : B -> A -> A).

    (* A fold over just the values, avoids the issues of rebuilding the keys *)
    Fixpoint map_fold_values' (m : PTree.tree' B) (acc : A) :=
      match m with
      | Node001 r => map_fold_values' r acc
      | Node010 y => f y acc
      | Node011 y r =>
          let acc := f y acc in
          map_fold_values' r acc
      | Node100 l => map_fold_values' l acc
      | Node101 l r =>      
          let acc := map_fold_values' r acc in
          map_fold_values' l acc
      | Node110 l y => 
          let acc := f y acc in
          map_fold_values' l acc
      | Node111 l y r =>
          let acc := f y acc in
          let acc := map_fold_values' r acc in
          map_fold_values' l acc
      end.
                                                               
    Definition map_fold_values (m : PTree.tree B) (acc : A) : A :=
      match m with
      | Empty => acc
      | Nodes m' => map_fold_values' m' acc
      end.
  End __.

End Folds.

Section __.

  
  Context (value : Type).

  
  Definition map : map.map positive value :=
    {|
      map.rep := PTree.t value;
      map.empty := PTree.empty value;
      map.get m k := PTree.get k m;
      map.put m k v := PTree.set k v m;
      map.remove m k := PTree.remove k m;
      map.fold := @trie_fold value;
    |}.
  (* TODO: prove map.ok *)
End __.


Module TrieArrayList.

  Open Scope positive.

  Definition trie_array A : Type := positive * (map A) * A.
  #[global] Instance trie_arraylist : ArrayList.ArrayList positive trie_array :=
    {
      make _ a := (1, map.empty, a);
      get _ '(_,m,a) i := match map.get m i with Some a' => a' | None => a end;
      set _ '(p,m,a) i a' := (Pos.max p (i+1), map.put m p a', a);
      length _ '(p,_,_) := p;
    (*TODO: wrong since positive has no true zero. Should be p-1.
      Use N instead of positive?
     *)
      alloc _ '(p,m,a) a' := (p,(p+1, map.put m p a',a));
    }.

End TrieArrayList.
