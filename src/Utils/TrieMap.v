Require Import Coq.Numbers.BinNums.
Require Import coqutil.Map.Interface.
Require Import Tries.Canonical.
Import PTree.

Fixpoint trie_fold' {B A} (f : A -> positive -> B -> A) (acc : A) (m : PTree.tree' B) (num : positive) : A :=
  match m with
  | Node001 r => trie_fold' f acc r (xI num)
  | Node010 y => f acc num y
  | Node011 y r => trie_fold' f (f acc num y) r (xI num)
  | Node100 l => trie_fold' f acc l (xO num)
  | Node101 l r => trie_fold' f (trie_fold' f acc r (xI num)) l (xO num)
  | Node110 l y => trie_fold' f (f acc num y) l (xO num)
  | Node111 l y r => trie_fold' f (trie_fold' f (f acc num y) r (xI num)) l (xO num)
end.

Definition trie_fold {B A} (f : A -> positive -> B -> A) (acc : A) (m : PTree.t B) : A :=
  match m with
  | Empty => acc
  | Nodes m' => trie_fold' f acc m' xH
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
