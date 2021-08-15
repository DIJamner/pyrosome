(* A union-find data structure that can be instantiated 
   with either persistent arrays or a functional implementation of the same spec.
   The instantiation with persistent arrays should be performant,
   while the instantiation with a function implementation should be closed
   under the global context.
*)
Require Import Equalities Orders.

Require Int63 PArray.

Module Type ArrayListOps (Idx : EqLtLe).

  Parameter array : Type -> Type.

  (* Since the arrays are dynamically extensible,
     make does not need a size
   *)
  Parameter make : forall {A}, A -> array A.
  
  Parameter get : forall {A}, array A -> Idx.t -> A.

  (* Sets a index to a new value if that index is less than max_length.
     Can extend the array.

     TODO: profile performance of PArray implementation to decide whether
     a non-extending version is worth adding to the interface
   *)
  Parameter set : forall {A}, array A -> Idx.t -> A -> array A.

 
  (*TODO: how best to handle optional max?
    make extend op. return an option?
    shouldn't extend be wrapped into set?
  Parameter set_extensible : forall {A}, array A -> Idx.t -> A -> array A.
   *)

  Parameter length : forall {A}, array A -> Idx.t.

  (* TODO: length is broken in impl below; fix and then restore this
  (* Note: returns l if (length l) = max_length *)
  Definition cons {A} a (l : array A) : array A :=
    set l (length l) a.
   *)

  (*If this is none, no max length*)
  Parameter max_length : option Idx.t.

End ArrayListOps.


(*Copied and modified from primitive arrays*)
Module ArrayNotations
       (Idx : EqLtLe)
       (Import IdxFns : OrderFunctions Idx)
       (Import AO : (ArrayListOps Idx)).
  Delimit Scope array_scope with array.
  Notation "t .[ i ]" :=
    (get t i)
      (at level 2, left associativity, format "t .[ i ]").
  Notation "t .[ i <- a ]" :=
    (set t i a)
      (at level 2, left associativity, format "t .[ i <- a ]").
  Notation "a ::! t" :=
    (cons a t)
      (at level 60, right associativity, format "a ::! t").
  
  Infix "=?" := eqb (at level 70, no associativity).
  Infix "<?" := ltb (at level 70, no associativity).
  Infix "<=?" := leb (at level 70, no associativity).
End ArrayNotations.

Module Type ArrayListSpec 
       (Idx : EqLtLe)
       (Import IdxFns : OrderFunctions Idx)
       (Import AO : (ArrayListOps Idx)).

  Module Import N := (ArrayNotations Idx IdxFns AO).

  (* Checks whether an index is writable
     i.e. whether it's less than the maximum size of an array
   *)
  Definition in_bounds i :=
    match max_length with
    | Some m => i <? m
    | None => true
    end.
  
  Axiom get_set_same : forall A t i (a:A), in_bounds i = true ->t.[i<-a].[i] = a.
  Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].

  
  Axiom get_make : forall A (a:A) i, (make a).[i] = a.

  Definition max (x y : Idx.t) :=
    if x <=? y then y else x.
    
  (* Note: differs from PArray because set dynamically scales *)
  Axiom length_set : forall A t i (a:A),
      length t.[i<-a] = if in_bounds i then max (length t) i else (length t).

  (*TODO: rest of array axioms as necessary *)
End ArrayListSpec.  

Module Int63EqLtLe <: EqLtLe.
  
  Import Int63.
  Definition t := int.
  Definition eq : int -> int -> Prop := @eq int.
  Definition lt x y := BinInt.Z.lt φ (x)%int63 φ (y)%int63.
  Definition le x y := BinInt.Z.le φ (x)%int63 φ (y)%int63.

End Int63EqLtLe.

Module Int63Fns <: OrderFunctions Int63EqLtLe.

  Import Int63 Int63EqLtLe.
  Definition compare := compare.
  
  Lemma compare_spec :
    forall x y : int, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros.
    rewrite compare_spec.
    unfold eq.
    destruct (BinInt.Z.compare_spec φ (x)%int63 φ (y)%int63); auto using to_Z_inj.
  Qed.

  Definition eqb := eqb.
  Definition ltb := ltb.
  Definition leb := leb.
  
  Definition eqb_eq : forall x y : int, eqb x y = true <-> eq x y := eqb_spec.
  Definition ltb_lt : forall x y : int, ltb x y = true <-> lt x y := ltb_spec.
  Definition leb_le : forall x y : int, leb x y = true <-> le x y := leb_spec.

End Int63Fns.

(*TODO: right place for this?*)
Import Int63.
Import Int63EqLtLe.
Require Import ZArith.


(*TODO: small inefficiency by going through N.recursion*)
Definition posZrec {A} base rec z : A :=
  let rec' n := rec (Z.of_N n) in
  match z with
  | Zpos p => N.recursion base rec' (Npos p)
  | _ => base
  end.


(* TODO: check the inefficiency due to converting Z to int at each iteration *)
Definition intrec {A} base rec i : A :=
  let rec' z := rec (of_Z z) in
  posZrec base rec' (to_Z i).


Module PArrayListOps <: (ArrayListOps Int63EqLtLe).

  Import Int63 PArray.
  
  Definition array := array.

  (* initial size is hardcoded *)
  Definition make {A} := @make A (4)%int63.

  Definition get {A} := @get A.


  Definition copyNth {A} l i (l' : array A) : array A :=
    l'.[i <- l.[i]].
  
  (* TODO: this one is tricky. Make sure it computes nicely *)
  Definition copyUpTo {A} (l l' : array A) : int -> array A :=
    intrec l (copyNth l').

  (*TODO: duplicated; refactor*)
  Definition max (x y : int) :=
    if leb x y then y else x.

  (*TODO: separate order notations so that I can use them here*)
  Definition expandToContain {A} i (l : array A) :=
    let len := length l in
    if ltb i len then l
    else
      let len' := max (2 * len)%int63 i in
      copyUpTo l (PArray.make len (get l len)) len.
  
  (* Dynamically grows the array as necessary *)
  Definition set {A} l i (a : A) := set (expandToContain i l) i a.      
 
  Definition length {A} := @length A.

  (* TODO: does not work due to exponential growth in copy.
     Will need to keep a counter w/ filled length to make this work
  (* Note: returns l if (length l) = max_length *)
  Definition cons {A} a (l : array A) : array A :=
    set l (length l) a.
   *)

  Definition max_length := Some max_length.

End PArrayListOps.

(*Testing*)
Import PArrayListOps.
Module Import N := (ArrayNotations Int63EqLtLe Int63Fns PArrayListOps).

Compute make 4.
Compute (expandToContain 5 (make 4)).
Compute (make 4).[5 <- 5]%int63.
(*TODO: needs to be instant*)
Compute (make 4).[33 <- 5]%int63.
