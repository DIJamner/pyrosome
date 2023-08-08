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
    Assumes k has length exactly n.
   *)
  Fixpoint ntree_get n : ntree n -> _ -> option A :=
    match n with
    | 0 => fun t k => Some t
    | S n' =>
        fun t k =>
          match k with
          | k1::k' =>
              @! let next <- map.get t k1 in
                (ntree_get n' next k')
          | _ => None
          end
    end.

  (*
    Assumes k has length exactly n.
   *)
  Fixpoint ntree_singleton n k v : ntree n :=
    match n with
    | 0 => v
    | S n' =>
        match k with
        | k1 :: k' => map.singleton k1 (ntree_singleton n' k' v)
        | _ => map.empty
        end
    end.
  
  (*
    Assumes k has length exactly n
   *)
  Fixpoint ntree_set n : ntree n -> list key -> A -> ntree n :=
    match n with
    | 0 => fun _ _ a => a
    | S n' =>
        fun t k v =>
          match k with
          | k1 :: k' =>
              match map.get t k1 with
              | Some next => map.put t k1 (ntree_set n' next k' v)
              | None => map.put t k1 (ntree_singleton n' k' v)
              end
          | _ => t
          end
    end.
  
End __.

Arguments ntree key%type_scope {m}%function_scope A%type_scope n%nat_scope.
