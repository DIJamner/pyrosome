Require Import Orders.


Module Ops.
(* Make typeclasses out of the important features of Natlike 
   since passing some instances to functors breaks the VM
   (issue #12519)
 *)
Class NatlikeOps t :=
  {
  eqb : t -> t -> bool;
  ltb : t -> t -> bool;
  leb : t -> t -> bool;
  zero : t;
  succ : t -> t;
  is_top : t -> bool;
  iter : forall {A},
      A -> (A -> A) -> t -> A
  }.
End Ops.

(* All of the properties we expect from indices,
   primarily a computable comparison operation,
   zero element, and successor operation.
*)
Module Type Natlike.
  
  Include OrderedTypeFull. (* subsumes HasT *)
  
  Include HasBoolOrdFuns <+ BoolOrdSpecs.

  Parameter zero : t.
  
  Parameter succ : t -> t.

  (* checks whether an element is the greatest element.
     If there is no greatest element, this will be a constant function.
   *)
  Parameter is_top : t -> bool.

  (* short-circuiting iteration*)
  Parameter iter
    : forall {A},
      A -> (A -> A) -> t -> A.

  Axiom zero_spec
    : forall a, le zero a.

  (* Note that the behavior of succ is unspecified on the top element *)
  Axiom succ_greater
    : forall a, (exists b, lt a b) -> lt a (succ a).
  
  Axiom succ_least
    : forall a b, lt a b -> le (succ a) b.

  Axiom is_top_spec
    : forall a, is_top a = false <-> (exists b, lt a b).

  Axiom iter_zero
    : forall A (a:A) f, iter a f zero = a.

  Axiom iter_succ
    : forall A (a:A) f i, (exists b, lt i b) -> iter a f (succ i) = f (iter a f i).
  
  Axiom natlike_ind
    : forall P : t -> Prop,
      P zero -> (forall n, is_top n = false -> P n -> P (succ n)) -> forall n, P n.

  Instance natlike_ops : Ops.NatlikeOps t :=
    {
    eqb := eqb;
    ltb := ltb;
    leb := leb;
    zero := zero;
    succ := succ;
    is_top := is_top;
    iter := @iter
    }.

End Natlike.

(* Notations for conveniently working with natlike elements *)
Module NatlikeNotations (Import NL : Natlike).

  (*TODO: add a number notation?*)
  
  Infix "=?" := eqb (at level 70, no associativity).
  Infix "<?" := ltb (at level 70, no associativity).
  Infix "<=?" := leb (at level 70, no associativity).
  Notation "i .+1" := (succ i) (at level 70, no associativity).

End NatlikeNotations.

