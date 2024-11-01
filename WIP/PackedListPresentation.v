Require Import PArray Lists.List NArith Uint63.

Fixpoint nat_to_int n : int :=
  match n with
  | O => 0
  | S n => 1 + (nat_to_int n)
  end.


(* Tests *)
Goal False.
  (*regular list-of-small-lists instantiation*)
  Time Let l_small := Eval vm_compute in
      (let l1 := repeat 0 10 in repeat l1 20000).
  (* 0.9 s *)
  time let _ := eval vm_compute in
       (map (map S) l_small)
         in
         idtac.
  (* 0.407 s *)
  
  (*regular list-of-large-lists instantiation*)
  Time Let l_large := Eval vm_compute in
      (let l1 := repeat 0 1000 in repeat l1 1000).
  (* 3.278 s *)
  time let _ := eval vm_compute in
       (map (map S) l_large)
         in
         idtac.
  (* 1.632 s *)
Abort.


(*
  Ignores issues of max length.
  For theorem purposes, it could devolve into a standard linked list above max_length,
  likely with only a small performance penalty below that.

  Requires a default element.

  Not canonical! due to defaults and size of backing arrays.
  This means bijection with list is only up to some equivalence relation.
 *)
Module ArrayList.

  Section Base.
    Context {A : Type}.
    (* To know where the end of the list is in the backing array,
     as well as to have a recursor, we need a length field.

     Since it's already non-canonical, we include the length_int field
     to avoid converting the length to an int repeatedly

     TODO: N vs nat for length
     *)
    Record t := mkl { lst : array A; length : nat; length_int : int }.

    Context (default_A : A).
    (* picking a magic number here: 16*)
    Definition nil : t :=
      mkl (make 16 default_A) 0 0.

    (* map without the function *)
    Fixpoint copy_n (l' : array A) len (idx : int) out : array A :=
      match len with
      | 0 => out
      | S len' => copy_n l' len' (idx + 1) out.[idx <- l'.[idx]]
      end.

    Definition grow l :=
      mkl (copy_n l.(lst) l.(length) 0 (make (2 * PArray.length l.(lst)) (default l.(lst))))
        (2*l.(length)) (2*l.(length_int)).

    Definition cons a l :=
      let l' := if ltb l.(length_int) (PArray.length l.(lst)) then l else grow l in
      mkl l.(lst).[l.(length_int) <- a] (S l.(length)) (1+l.(length_int)).

    Definition repeat (x : A) (n : nat) : t :=
      let ni := nat_to_int n in
      mkl (make ni x) n ni.
      
  End Base.
  Arguments t : clear implicits.
  Arguments mkl {A}%_type.

  Section Map.
    Context A B (f : A -> B).
    Fixpoint map' (l' : array A) len (idx : int) out : array B :=
      match len with
      | 0 => out
      | S len' => map' l' len' (idx + 1) out.[idx <- f l'.[idx]]
      end.

    Definition map (l : t A) : t B :=
      mkl (map' l.(lst) l.(length) 0 (make (PArray.length l.(lst)) (f (default l.(lst)))))
        l.(length)
        l.(length_int).

  End Map.

  Arguments map {A B}.

  
  (* Tests *)
  Goal False.
    (*list-of-small-lists instantiation*)
    Time Let l_small' := Eval vm_compute in
        (let l1 := repeat 0 10 in repeat l1 20000).
    (* 0.9 s *)
    time let _ := eval vm_compute in
         (map (map S) l_small')
           in
           idtac.
    (* 0.4 s *)
    
    (*list-of-large-lists instantiation*)
    Time Let l_large' := Eval vm_compute in
        (let l1 := repeat 0 1000 in repeat l1 1000).
    (* 2.0 s *)
    time let _ := eval vm_compute in
         (map (map S) l_large')
           in
           idtac.
    (* 0.9 s *)
  Abort.

End ArrayList.

Module DoubleList.
  
  Section __.
    Context {A : Type}.

    Inductive double_list := dnil | dsingle (a:A) | dcons_two (a1 a2 : A) (tl : double_list).

    Fixpoint dcons (a:A) l :=
      match l with
      | dnil => dsingle a
      | dsingle a' => dcons_two a a' dnil
      | dcons_two a1 a2 tl => dcons_two a a1 (dcons a2 tl)
      end.

  End __.
  
End DoubleList.

Module TwoPackv1.

  Section __.
    Context {A : Type}.
    
    Inductive two_list := two_nil | two_cons (a1 a2 : A) (tl : two_list).

    Inductive twopack_list := even_list (l : two_list) | odd_list (a : A) (l : two_list).
  
    Definition tp_cons a l :=
      match l with
      | even_list l' => odd_list a l'
      | odd_list a' l' => even_list (two_cons a a' l')
      end.

  End __.
End TwoPackv1.

Module TwoPackv2.

  Section __.
    Context {A : Type}.
    
    Inductive ne_two_list := two_base (a1 a2 : A) | two_cons (a1 a2 : A) (tl : ne_two_list).

    Inductive twopack_list :=
    | tp_nil
    | tp_single (a:A)
    | even_list (l : ne_two_list)
    | odd_list (a : A) (l : ne_two_list).
  
    Definition tp_cons a l :=
      match l with
      | tp_nil => tp_single a
      | tp_single a' => even_list (two_base a a')
      | even_list l' => odd_list a l'
      | odd_list a' l' => even_list (two_cons a a' l')
      end.
  End __.

    Section Map.
      Context A B (f : A -> B).

      Fixpoint ne_two_list_map l :=
        match l with
        | two_base a1 a2 => two_base (f a1) (f a2)
        | two_cons a1 a2 tl => two_cons (f a1) (f a2) (ne_two_list_map tl)
        end.

      Definition map l :=
        match l with
        | tp_nil => tp_nil
        | tp_single a => tp_single (f a)
        | even_list l => even_list (ne_two_list_map l)
        | odd_list a l => odd_list (f a) (ne_two_list_map l)
        end.
      
    End Map.
  
End TwoPackv2.
