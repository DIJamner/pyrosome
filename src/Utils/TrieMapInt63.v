Require Import ZArith Int63.
Open Scope int63.
Require Import coqutil.Map.Interface.
Require Import Tries.Canonical.
Import PTree.

Require Utils.ArrayList Utils.TrieMap.
(*
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
  
 *)

(** PTree operations reimplemented for i63.
    Note that we can't differentiate between 0 and 000 by default,
    so we trim all leading 0s to avoid making each access have depth 64.
 *)

(* Note: this can be expensive for large numbers, should only be called on small ones.
   Invariant: this file only calls it on numbers <= digits
 *)
Local Definition int_to_nat (i : int) := Z.to_nat (Uint63.to_Z i).

Fixpoint get' {A} (p: int) (m: tree' A) (msb : nat) : option A :=
  let q := p >> 1 in
  match msb, m, is_zero (p land 1) with
  | O, Node001 _, _ => None
  | O, Node010 x, _ => Some x
  | O, Node011 x _, _ => Some x
  | O, Node100 _, _ => None
  | O, Node101 _ _, _ => None
  | O, Node110 _ x, _ => Some x
  | O, Node111 _ x _, _ => Some x
  | S msb, Node001 _, true => None
  | S msb, Node010 _, true => None
  | S msb, Node011 _ _, true => None
  | S msb, Node100 m', true => get' q m' msb
  | S msb, Node101 m' _, true => get' q m' msb
  | S msb, Node110 m' _, true => get' q m' msb
  | S msb, Node111 m' _ _, true => get' q m' msb
  | S msb, Node001 m', false => get' q m' msb
  | S msb, Node010 _, false => None
  | S msb, Node011 _ m', false => get' q m' msb
  | S msb, Node100 m', false => None
  | S msb, Node101 _ m', false => get' q m' msb
  | S msb, Node110 _ _, false => None
  | S msb, Node111 _ _ m', false => get' q m' msb
  end.

(* TODO: we always use int_to_nat (msb p). Should we implement that directly?
   It would probably be faster.
 *)
Definition msb i := digits - (head0 i).

Definition get {A} (m : tree A) (p: int) : option A :=
  match m with
  | Empty => None
  | Nodes m' => get' p m' (int_to_nat (msb p))
  end.

Fixpoint set0 {A} (p: int) (x: A) (msb : nat) : tree' A :=
  let q := p >> 1 in
  match msb, is_zero (p land 1) with
  | O, _ => Node010 x
  | S msb, true => Node100 (set0 q x msb)
  | S msb, false => Node001 (set0 q x msb)
  end.

Fixpoint set' {A} (p: int) (x: A) (m: tree' A) (msb : nat) : tree' A :=
  let q := p >> 1 in
match msb, m, is_zero (p land 1) with
| O, Node001 r, _ => Node011 x r
| O, Node010 _, _ => Node010 x
| O, Node011 _ r, _ => Node011 x r
| O, Node100 l, _ => Node110 l x
| O, Node101 l r, _ => Node111 l x r
| O, Node110 l _, _ => Node110 l x
| O, Node111 l _ r, _ => Node111 l x r
| S msb, Node001 r, true => Node101 (set0 q x msb) r
| S msb, Node010 y, true => Node110 (set0 q x msb) y
| S msb, Node011 y r, true => Node111 (set0 q x msb) y r
| S msb, Node100 l, true => Node100 (set' q x l msb)
| S msb, Node101 l r, true => Node101 (set' q x l msb) r
| S msb, Node110 l y, true => Node110 (set' q x l msb) y
| S msb, Node111 l y r, true => Node111 (set' q x l msb) y r
| S msb, Node001 r, false => Node001 (set' q x r msb)
| S msb, Node010 y, false => Node011 y (set0 q x msb)
| S msb, Node011 y r, false => Node011 y (set' q x r msb)
| S msb, Node100 l, false => Node101 l (set0 q x msb)
| S msb, Node101 l r, false => Node101 l (set' q x r msb)
| S msb, Node110 l y, false => Node111 l y (set0 q x msb)
| S msb, Node111 l y r, false => Node111 l y (set' q x r msb)
end.

Definition set {A} (m: tree A) (p: int) (x: A) : tree A :=
match m with
| Empty => Nodes (set0 p x (int_to_nat (msb p)))
| Nodes m' => Nodes (set' p x m' (int_to_nat (msb p)))
end.


Fixpoint rem' {A} (p: int) (m: tree' A) (msb : nat) : tree A :=
  let q := p >> 1 in
  match msb, m, is_zero (p land 1) with
  | O, Node001 r,_ => Nodes m
  | O, Node010 _,_ => Empty
  | O, Node011 _ r,_ => Nodes (Node001 r)
  | O, Node100 l,_ => Nodes m
  | O, Node101 l r,_ => Nodes m
  | O, Node110 l _,_ => Nodes (Node100 l)
  | O, Node111 l _ r,_ => Nodes (Node101 l r)
  | S msb, Node001 r, true => Nodes m
  | S msb, Node010 y, true => Nodes m
  | S msb, Node011 y r, true => Nodes m
  | S msb, Node100 l, true => Node (rem' q l msb) None Empty
  | S msb, Node101 l r, true => Node (rem' q l msb) None (Nodes r)
  | S msb, Node110 l y, true => Node (rem' q l msb) (Some y) Empty
  | S msb, Node111 l y r, true => Node (rem' q l msb) (Some y) (Nodes r)
  | S msb, Node001 r, false => Node Empty None (rem' q r msb)
  | S msb, Node010 y, false => Nodes m
  | S msb, Node011 y r, false => Node Empty (Some y) (rem' q r msb)
  | S msb, Node100 l, false => Nodes m
  | S msb, Node101 l r, false => Node (Nodes l) None (rem' q r msb)
  | S msb, Node110 l y, false => Nodes m
  | S msb, Node111 l y r, false => Node (Nodes l) (Some y) (rem' q r msb)
  end.

(** This use of [Node] causes some run-time overhead, which we eliminate
    by asking Coq to unfold the definition of [Node] in [rem'],
    then simplify the definition.  This is a form of partial evaluation. *)

Definition remove' := Eval cbv [rem' Node] in @rem'.

Definition remove {A} (m: tree A)  (p: int) : tree A :=
match m with
| Empty => Empty
| Nodes m' => remove' _ p m' (int_to_nat (msb p))
end.

(*
Fixpoint msb' (fuel : nat) (i : int) : nat * int :=
  match fuel with
  (* Should never happen? *)
  | 0 => (O, 0)
  | S fuel =>
      let i' := i >> 1 in
      if is_zero i'
      then (O,0)
      else
        let (n,i) := msb' fuel i' in
        (S n, i + 1)
  end.

Definition msb := msb' size.

(* Note: this should not be used outside this module.
   It does not represent an principled transformation.
 (* Note: assumes the input is nonnegative, in which case the function is bijective *)
 *)
Local Definition to_pos (i:int) : positive :=
  (*adding 1 to make sure that 0 gets mapped to a positive. *)
  match to_Z (i + 1) with
  | Zpos p => p
  (*should never happen*)
  | _ => xH
  end.
(*
  TODO: this is a very poor implementation of fold, improve
 *)*)

Section __.

  
  Context (value : Type).
  

  Section Fold.
    Context {R : Type} (f : R -> int -> value -> R).


    Fixpoint fold' (acc : R) (m : tree' value) (i : int) : R :=
      (*0 bit ~> left
        1 bit ~> right
       *)
      let i'_l := i << 1 in
      let i'_r := i'_l lor 1 in
      match m with
      | Node001 r => fold' acc r i'_r
      | Node010 v => f acc i v
      | Node011 v r => fold' (f acc i v) r i'_r
      | Node100 l => fold' acc l i'_l
      | Node101 l r => fold' (fold' acc r i'_r) l i'_l
      | Node110 l v => fold' (f acc i v) l i'_l
      | Node111 l v r => fold' (fold' (f acc i v) r i'_r) l i'_l
      end.
    
    Definition fold (acc : R) (m : tree value) : R :=
      match m with
      | Empty => acc
      | Nodes m' => fold' acc m' 0
      end.

  End Fold.

  Instance map : map.map int value :=
    {|
      map.rep := PTree.t value;
      map.empty := PTree.empty value;
      map.get := get;
      map.put := set;
      map.remove := remove;
      map.fold := @fold;
    |}.

  (* TODO: prove map.ok *)
End __.
