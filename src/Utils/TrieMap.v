Require Import ZArith.
Require Import coqutil.Map.Interface.
Require Import Tries.Canonical.
Import PTree.

Require Utils.ArrayList.
Require Import Utils.ExtraMaps.

Section Folds.
  Context {B A : Type}.

  Section __.
    Context (f : A -> positive -> B -> A).
    
    (* positives consed when they should be appended

    TODO: to make folds more efficient at the cost of space,
    can just include each key at the leaf.
    To do so: implement map.map positive v for PTree.tree (positive*v)?
     *)
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

Section MapIntersect.
  Context {A B C} (elt_intersect : A -> B -> C).

  Import Canonical.PTree.
  Arguments empty {A}%type_scope.
                                            
  Fixpoint intersect' m1 m2 : tree _ :=
    match m1, m2 with
    (* just an element*)                                            
    | Node010 a, Node010 b
    | Node010 a, Node011 b _
    | Node010 a, Node110 _ b
    | Node010 a, Node111 _ b _                                            
    | Node011 a _, Node010 b                                            
    | Node110 _ a, Node010 b                                            
    | Node111 _ a _, Node010 b                                       
    | Node110 _ a, Node011 b _                                       
    | Node011 a _, Node110 _ b => Node empty (Some (elt_intersect a b)) empty
                                                  
    (* RHS only in result*)
    | Node001 r1, Node001 r2
    | Node001 r1, Node011 _ r2
    | Node001 r1, Node101 _ r2
    | Node001 r1, Node111 _ _ r2
    | Node011 _ r1, Node001 r2
    | Node101 _ r1, Node001 r2
    | Node111 _ _ r1, Node001 r2
    | Node011 _ r1, Node101 _ r2
    | Node101 _ r1, Node011 _ r2 => Node empty None (intersect' r1 r2)
                                            
    (* LHS only in result*)
    | Node100 l1, Node100 l2
    | Node100 l1, Node110 l2 _
    | Node100 l1, Node101 l2 _
    | Node100 l1, Node111 l2 _ _
    | Node110 l1 _, Node100 l2
    | Node101 l1 _, Node100 l2
    | Node111 l1 _ _, Node100 l2
    | Node110 l1 _, Node101 l2 _
    | Node101 l1 _, Node110 l2 _ => Node (intersect' l1 l2) None empty

    (* RHS + element *)
    | Node011 a r1, Node011 b r2
    | Node011 a r1, Node111 _ b r2
    | Node111 _ a r1, Node011 b r2 => Node empty (Some (elt_intersect a b)) (intersect' r1 r2)
                                                
    (* LHS + element *)
    | Node110 l1 a, Node110 l2 b
    | Node110 l1 a, Node111 l2 b _
    | Node111 l1 a _, Node110 l2 b => Node (intersect' l1 l2) (Some (elt_intersect a b)) empty

    (* everything *)
    | Node111 l1 a r1, Node111 l2 b r2 => Node (intersect' l1 l2) (Some (elt_intersect a b)) (intersect' r1 r2)
     
    (* No overlap *)
    | _, _ => empty
    end.

  Definition intersect m1 m2 :=
    match m1, m2 with
    | Empty, _
    | _, Empty => empty
    | Nodes m1', Nodes m2' => intersect' m1' m2'
    end.
End MapIntersect.


#[export] Instance ptree_map_plus : map_plus map :=
  {
    map_intersect := @intersect;
    map_fold_values := @map_fold_values;
    (* TODO: check whether the filter overhead is detectable *)
    map_map _ _ f := map_filter (fun x => Some (f x));
  }.

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
