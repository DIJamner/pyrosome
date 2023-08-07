Require Import NArith Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.

From Utils Require Import Base ExtraMaps Monad.
From Utils Require TrieMap.



(* what I want (copied from MapTree): *)
(*#[bypass_check(positivity)]*)
Fail Inductive tree {key} {m : forall A, map.map key A} {A} :=
| leaf : A -> tree
| node : m tree -> tree
(* a useful additional case: the all-inputs constant map.
   Breaks extensionality when key is finite, but is important for generic join.
 *)
| top_node : tree -> tree.

(* For eqsat purposes, we will always know statically the depth of the tree.
   Thus, we can use a fixpoint on that depth as the type.
 *)

Section __.
  Context {key} {m : forall A, map.map key A}.
  Context (A : Type).
  Fixpoint ntree n :=
    match n with
    | 0 => A
    | S n => m (ntree n)
    end.
                                          
  Section __.
    Context {B} (f : B -> list key -> A -> B).

    (*TODO: benchmark which is better: rev in fold, or rev in get*)
    Fixpoint ntree_fold' n acc keystack : ntree n -> _ :=
      match n with
      | 0 => f acc (rev keystack)
      | S n' => map.fold (fun acc k => ntree_fold' n' acc (k::keystack)) acc
      end.
    
    Definition ntree_fold n (t:ntree n) acc :=
      ntree_fold' n acc [] t.

  End __.

  (*
    TODO: determine whether dependent types will cause issues
    (probably will?)
   *)
  Fixpoint ntree_get k : ntree (length k) -> option A :=
    match k with
    | [] => fun t => Some t
    | k1::k' =>
        fun t =>
          @! let next <- map.get t k1 in
            (ntree_get k' next)
    end.

  Fixpoint ntree_singleton k v : ntree (length k) :=
    match k with
    | [] => v
    | k1::k' =>
        map.singleton k1 (ntree_singleton k' v)
    end.
  
  Fixpoint ntree_set k v : ntree (length k) -> ntree (length k) :=
    match k with
    | [] => fun _ => v
    | k1 :: k' =>
        fun t =>
          match map.get t k1 with
          | Some next => map.put t k1 (ntree_set k' v next)
          | None => map.put t k1 (ntree_singleton k' v)
          end
    end.
  
End __.
