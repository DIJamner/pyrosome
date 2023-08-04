Require Import NArith.
From coqutil Require Import Map.Interface.

From Utils Require Import Base ExtraMaps.
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

  Variant node (child : Type) :=
    | fin_node : m child -> node child
    | top_node : child -> node child.
  Arguments fin_node {child}%type_scope _.
  Arguments top_node {child}%type_scope _.

  Section __.
    Context (A : Type).
    Fixpoint ntree n :=
      match n with
      | 0 => A
      | S n => node (ntree n)
      end.    
  End __.

  Section MapPlus.

    Context `{@map_plus key m}.

    
    Section __.
    Context {A B C : Type} (merge : A -> B -> C).
    Definition merge_node (na : node A) (nb : node B) : node C :=
      match na, nb with
      | fin_node ma, fin_node mb => fin_node (map_intersect merge ma mb)
      | top_node c1, top_node c2 => top_node (merge c1 c2)
      | fin_node m, top_node c => fin_node (map_map (fun a => merge a c) m)
      | top_node c, fin_node m => fin_node (map_map (merge c) m)
      end.
    End __.

    Section __.
    Context {A B C : Type} (merge : A -> B -> C).
    
    Fixpoint ntree_intersect n : ntree A n -> ntree B n -> ntree C n :=
      match n with
      | 0 => merge
      | S n' => merge_node (ntree_intersect n')
      end.
    End __.

    Section __.
      Context {A B : Type}
        (f : A -> B -> B).

      (* Note: does not guarantee anything about order *)
      Fixpoint map_tree_fold_values n : ntree A n -> B -> B :=
        match n with
        | 0 => f
        | S n' =>
            fun b =>
              match b with
              | fin_node m => map_fold_values (map_tree_fold_values n') m
              | top_node c => map_tree_fold_values n' c
              end
        end.
    End __.

    
  End MapPlus.
  
End __.
