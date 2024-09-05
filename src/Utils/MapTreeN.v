Require Import NArith Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.

From Utils Require Import Base Options ExtraMaps Monad.
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

  Section __.
  
  Context (A : Type).
  Fixpoint ntree n : Type :=
    match n with
    | 0 => A
    | S n => m (ntree n) (*+ ntree n (*top*)*)
    end.
                                          
  Section __.
    Context {B} (f : B -> list key -> A -> B).

    (*TODO: benchmark which is better: rev in fold, or rev in get*)
    Fixpoint ntree_fold' n acc keystack : ntree n -> _ :=
      match n with
      | 0 => f acc (rev keystack)
      | S n' => (map.fold (fun acc k => ntree_fold' n' acc (k::keystack)) acc)
      end.

    Definition ntree_fold n (t:ntree n) acc :=
      ntree_fold' n acc [] t.

  End __.
  Import StateMonad.
  Section __.
    Context {B ST} (f : B -> list key -> A -> state ST B).

    (*TODO: benchmark which is better: rev in fold, or rev in get*)
    Fixpoint ntree_Mfold' n (acc :B) keystack : ntree n -> state ST B :=
      match n with
      | 0 => f acc (rev keystack)
      | S n' => (fun m : map.rep => map_Mfold (fun k v acc => ntree_Mfold' n' acc (k::keystack) v) m acc)
      end.

    Definition ntree_Mfold n (t:ntree n) acc :=
      ntree_Mfold' n acc [] t.

  End __.


  
  Definition ntree_to_tuples n (t : ntree n) : list (list key * A) :=
    ntree_fold (fun acc k v => cons (k,v) acc) n t [].

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
  Arguments ntree_get [n]%nat_scope _ _%list_scope.

  
  (*TODO: DUPLICATED! move this somewhere?
    TODO: sometimes maps can implement this more efficiently
   *)
  Definition map_update {K V} {mp : map.map K V} (m : mp) x (f : V -> V) :=
    match map.get m x with
    | Some v => map.put m x (f v)
    | None => m
    end.
  
  (*
    Assumes k has length exactly n.
   *)
  Fixpoint ntree_remove n {struct n} : ntree n -> list _ -> ntree n :=
    match n with
    (* TODO: not well-defined on 0! should the last level be an option?
       Have this awkward workaround for matching the n=1 case
     *)
    | 0 => fun t k => t
    | S n' =>
        match n' with
        | 0 => fun t k =>
                 match k with
                 | k1::[] =>
                     map.remove t k1
                 | _ => t
                 end
        | _ => fun t k =>
                 match k with
                 | k1::k' =>
                     map_update t k1 (fun t' => ntree_remove n' t' k)
                 | _ => t
                 end
        end
    end.
  Arguments ntree_remove [n]%nat_scope _ _%list_scope.

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

    Note: will fail silently if the final node is a top node
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

  Arguments ntree_get {A}%type_scope [n]%nat_scope _ _%list_scope.

  (* Question: Should I handle empty ntree 0s?
   *)
  Context {A B C : Type}
    (merge : A -> B -> C)
    `{map_plus_ok key (m := m)}.
  Fixpoint ntree_intersect n : ntree A n -> ntree B n -> ntree C n :=
    match n with
    | 0 => merge
    | S n' =>
        fun m1 m2 => map_intersect (ntree_intersect n') m1 m2
    end.
  Arguments ntree_intersect [n]%nat_scope _ _.
  
    Lemma ntree_intersect_spec n (t1 : ntree A n) (t2 : ntree B n) k
      : ntree_get (ntree_intersect t1 t2) k
        = match ntree_get t1 k, ntree_get t2 k with
          | Some a, Some b => Some (merge a b)
          | _, _ => None
          end.
    Proof.
      revert t1 t2 k;
        induction n;
        basic_goal_prep; try now intuition eauto.
      destruct k;
        basic_goal_prep;
        intuition eauto;
        rewrite ?intersect_spec; eauto.
      all: repeat case_match; try congruence.
      all: rewrite ?map_map_spec in *.
      all:try(unfold ntree in *;
              cbn in *;
              repeat lazymatch goal with
                | H1 : context[?A], H2 : None = ?A |- _ =>
                    rewrite <- H2 in H1;
                    try safe_invert H1
                | H1 : context[?A], H2 : Some _ = ?A |- _ =>
                    rewrite <- H2 in H1;
                    try safe_invert H1
                end;
              try congruence).
      all: rewrite ?IHn.
      all: repeat case_match; try congruence.
    Qed.
  
End __.

Arguments ntree key%type_scope {m}%function_scope A%type_scope n%nat_scope.
Arguments ntree_get {key}%type_scope {m}%function_scope {A}%type_scope [n]%nat_scope _ _%list_scope.
Arguments ntree_intersect {key}%type_scope {m}%function_scope {A B C}%type_scope merge%function_scope {H} [n]%nat_scope _ _.
