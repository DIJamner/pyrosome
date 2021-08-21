Require Import Orders.

From Utils Require Import Natlike.

(* HasT modules provide a type t and operations on elements of that type. *)
Module Type HasT.
  Parameter t : Type.
End HasT.

(* Modules that satisfy (ArrayListOps Idx) provide a type 'array A' and operations on that type
   such that elements of 'array A' can be used as growable arrays indexed by elements of Idx.t.
   Note that if Idx.t is finite, arrays may not support unlimited concatenation.

   Properties of these operations are separated into another module.
*)
Module Type ArrayList (Idx : HasT).

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

  Parameter length : forall {A}, array A -> Idx.t.
  
  Parameter alloc : forall {A}, array A -> A -> Idx.t * array A.

End ArrayList.
  

(*Copied and modified from primitive arrays*)
Module ArrayNotations
       (Idx : Natlike)
       (Import AO : (ArrayList Idx)).
  
  Notation "t .[ i ]" :=
    (get t i)
      (at level 2, left associativity, format "t .[ i ]").
  Notation "t .[ i <- a ]" :=
    (set t i a)
      (at level 2, left associativity, format "t .[ i <- a ]").
  Notation "'new!' a :: t" :=
    (alloc t a)
      (at level 60, right associativity, format "new! a :: t").

End ArrayNotations.

(* The properties that should hold about ArrayList operations *)
Module Type ArrayListSpec
       (Idx : Natlike)
       (Import AO : (ArrayList Idx)).

  Module Import Notations := (NatlikeNotations Idx) <+ (ArrayNotations Idx AO).

  (* Include an arbitrary predicate for specifying a well-formed subset of the array type.
     Ideally we would prove a parametricity result that shows all arrays constructed from
     the arraylist interface have this property,
     but this is difficult to do internally to Coq.
     We could include the property in each array as a refinement type,
     but this would include it in computations, which are supposed to be fast.
   *)
  Parameter well_formed : forall {A}, array A -> Prop.

  Axiom make_well_formed : forall A (a:A), well_formed (make a).

  Axiom set_well_formed : forall A t i (a:A), well_formed t -> well_formed t.[i<-a].

  Axiom alloc_well_formed
    : forall A t (a:A) i t',
      well_formed t ->
      (i,t') = alloc t a ->
      well_formed t'.
  
  Axiom get_set_same : forall A t i (a:A),
      well_formed t ->
      (* Not needed for current implementations,
         but should probably be added anyway.
         Assigning to the top element should not be relied on.
        (exists i', Idx.lt (length l) i') ->
       *)
      t.[i<-a].[i] = a.
  
  Axiom get_set_other : forall A t i j (a:A), well_formed t -> i <> j -> t.[i<-a].[j] = t.[j].
  
  Axiom get_make : forall A (a:A) i, (make a).[i] = a.

  Axiom get_alloc_same
    : forall A l (a:A) l' i,
      well_formed l ->
      (i,l') = alloc l a ->
      l'.[i] = a.

  Axiom alloc_fresh
    : forall A l (a:A) l' i,
      (i,l') = alloc l a ->
      (exists i', Idx.lt (length l) i') ->
      Idx.eq i (length l).

  (*TODO: move to the right place*)
  Definition max (x y : Idx.t) :=
    if x <=? y then y else x.

  Axiom length_set :
    forall A t i (a : A),
      (exists i', Idx.lt i i') ->
      length t.[i <- a] = max (length t) (i.+1).

  Axiom length_make : forall A (a:A), length (make a) = Idx.zero.

  Axiom length_alloc
    : forall A l (a:A) l' i,
      (i,l') = alloc l a ->
      (exists i', Idx.lt (length l) i') ->
      Idx.eq (length l') (Idx.succ (length l)).

  (*TODO: rest of array axioms as necessary *)
  
End ArrayListSpec.  
