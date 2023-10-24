Require Import NArith.
From coqutil Require Import Map.Interface.

From Utils Require Import Base.
From Utils Require TrieMap.

(* what I want*)
(*#[bypass_check(positivity)]*)
Fail Inductive tree {key} {m : forall A, map.map key A} {A} :=
| leaf : A -> tree
| node : m tree -> tree
(* a useful additional case: the all-inputs constant map.
   Breaks extensionality when key is finite, but is important for generic join.
 *)
| top_node : tree -> tree.
  
  
Section WithMap.
  Context
    {key : Type}
      (*(Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx) *)
      (m : forall A, map.map key A).

  Class map_tree : Type :=
    {
      rep : Type -> Type;
      leaf : forall {A}, A -> rep A;
      node : forall {A}, m (rep A) -> rep A;
    (* a useful additional case: the all-inputs constant map.
       Breaks extensionality when key is finite, but is important for generic join.
     *)
      top_node : forall {A}, rep A -> rep A;
      (*Note: this is simply typed, but for full generality, should be dependent
        TODO: make appropriately recursive
       *)
      tree_match : forall {A B}, (A -> B) -> (m (rep A) -> B) -> (rep A -> B) -> rep A -> B;
    }.

  Context (tree : map_tree).

  Class map_tree_ok : Prop :=
    {
      tree_match_leaf A B (f : A -> B) g h a : tree_match f g h (leaf a) = f a;
      tree_match_node A B (f : A -> B) g h mr : tree_match f g h (node mr) = g mr;
      map_tree_ind A (P : _ -> Prop) : (forall a : A, P (leaf a)) ->
                                     (forall r, P (node r)) ->
                                     (forall r, P (top_node r)) ->
                                     forall p, P p;
    }.
  

End WithMap.


Arguments leaf {key}%type_scope {m}%function_scope {map_tree} {A}%type_scope _.
Arguments top_node {key}%type_scope {m}%function_scope {map_tree} {A}%type_scope _.
Arguments node {key}%type_scope {m}%function_scope {map_tree} {A}%type_scope _.

Global Coercion rep : map_tree >-> Funclass.
Arguments map_tree_ok {key}%type_scope {m}%function_scope tree.
  
Section Positive.
  Local Open Scope positive.
  
  Inductive positive_map_tree' {A} :=
  | pm_leaf : A -> positive_map_tree'
  | pm_node : TrieMap.trie_map positive_map_tree' -> positive_map_tree'
  | pm_top_node : positive_map_tree' -> positive_map_tree'.
  #[local] Hint Constructors positive_map_tree' : core.
  
  #[export] Instance positive_map_tree : map_tree TrieMap.trie_map :=
    {
      rep := @positive_map_tree';
      leaf := @pm_leaf;
      node := @pm_node;
      top_node := @pm_top_node;
      tree_match _ B f g h := positive_map_tree'_rect _ (fun _ => B) f g (fun r _ => h r);
    }.

  #[export] Instance positive_map_tree_ok : map_tree_ok positive_map_tree.
  Proof.
    constructor;
      unfold tree_match, leaf, node, positive_map_tree;
      basic_goal_prep; eauto.
    {
      eapply positive_map_tree'_ind; eauto.
    }
  Qed.

End Positive.




(* Specialized tree map to make termination work for map_tree_intersect *)
Section MapSpecial.

  Import Canonical.PTree.
  Context {A B C : Type} (mti : A -> B -> C) (b:B).

  Fixpoint map_special' (m: tree' A) : tree' C :=
    match m with
    | Node001 r => Node001 (map_special' r)
    | Node010 x => Node010 (mti x b)
    | Node011 x r => Node011 (mti x b) (map_special' r)
    | Node100 l => Node100 (map_special' l)
    | Node101 l r => Node101 (map_special' l) (map_special' r)
    | Node110 l x => Node110 (map_special' l) (mti x b)
    | Node111 l x r => Node111 (map_special' l) (mti x b) (map_special' r)
    end.

  Definition map_special (m: tree A) : tree C :=
    match m with
    | Empty => Empty
    | Nodes m' => Nodes (map_special' m')
    end.

End MapSpecial.

Section MapTreeIntersectPositive.
  Context {A B C : Type} (merge : A -> B -> C).
  Import Canonical.PTree.

  Fixpoint map_tree_intersect (t1 : @positive_map_tree' A) (t2 : @positive_map_tree' B) {struct t1}
  : @positive_map_tree' C :=
    match t1, t2 with
    | pm_leaf a, pm_leaf b => leaf (merge a b)
    | pm_top_node t1', pm_top_node t2' => top_node (map_tree_intersect t1' t2')
    | pm_node m1, pm_node m2 => node (TrieMap.intersect map_tree_intersect m1 m2)
    | pm_node m, pm_top_node t => node (map_special map_tree_intersect t m)
    | pm_top_node t, pm_node m => node (map_filter (fun t' => Some (map_tree_intersect t t')) m)
    | _, _ => node map.empty
    end.
  
End MapTreeIntersectPositive.                                   

Section Folds.
  Context {A B : Type}
    (f : A -> B -> B).

  (* Note: does not guarantee anything about order *)
  Fixpoint map_tree_fold_values (t : positive_map_tree A) acc : B :=
    match t with
    | pm_leaf a => f a acc
    | pm_top_node t' => map_tree_fold_values t' acc
    | pm_node m =>
        TrieMap.map_fold_values map_tree_fold_values m acc
    end.
  
End Folds.
