Require Import ZArith.
Require Import coqutil.Map.Interface.
Require Import Tries.Canonical.
Import PTree.

(* positives consed when they should be appended*)
Fixpoint trie_fold' {B A} (f : A -> positive -> B -> A) (acc : A) (m : PTree.tree' B)
         (*TODO: find a better way*)
         (num : positive -> positive) : A :=
  match m with
  | Node001 r => trie_fold' f acc r (fun a => num (xI a))
  | Node010 y => f acc (num xH) y
  | Node011 y r =>
      let acc := f acc (num xH) y in
      trie_fold' f acc r (fun a => num (xI a))
  | Node100 l => trie_fold' f acc l (fun a => num (xO a))
  | Node101 l r =>      
      let acc := trie_fold' f acc r (fun a => num (xI a)) in
      trie_fold' f acc l (fun a => num (xO a))
  | Node110 l y => 
      let acc := f acc (num xH) y in
      trie_fold' f acc l (fun a => num (xO a))
  | Node111 l y r =>
      let acc := f acc (num xH) y in
      let acc := trie_fold' f acc r (fun a => num (xI a)) in
      trie_fold' f acc l (fun a => num (xO a))
end.


Definition trie_fold {B A} (f : A -> positive -> B -> A) (acc : A) (m : PTree.t B) : A :=
  match m with
  | Empty => acc
  | Nodes m' => trie_fold' f acc m' id
  end.
  

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

