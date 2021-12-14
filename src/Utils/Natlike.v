Require Import Orders.

From Utils Require Import Utils.


Class Natlike t :=
  {
  natlike_eqb :> Eqb t;
  ltb : t -> t -> bool;
  leb : t -> t -> bool;
  zero :> WithDefault t;
  succ : t -> t;
  is_top : t -> bool;
  iter : forall {A},
      A -> (A -> A) -> t -> A
  }.

Section WithNatlike.
  Context (t : Type)
          `{Natlike t}.

  (*TODO: include specs of ltb, leb*)
  (*TODO: replace module below w/ this*)
  Class Natlike_ok : Type :=
    {
      (* Note that the behavior of succ is unspecified on the top element *)
      succ_greater
      : forall a : t, (exists b, ltb a b = true) -> ltb a (succ a) = true;
      
      succ_least
      : forall (a b : t), ltb a b = true -> leb (succ a) b = true;

      is_top_spec
      : forall (a : t), is_top a = false <-> (exists b, ltb a b = true);

      iter_zero
      : forall A (a:A) f, iter a f (zero : t) = a;

      iter_succ
      : forall A (a:A) f (i : t),
        (exists b, ltb i b = true) -> iter a f (succ i) = f (iter a f i);
      
      natlike_ind
      : forall P : t -> Prop,
        P zero -> (forall n, is_top n = false -> P n -> P (succ n)) -> forall n, P n;   
    }.
End WithNatlike.


(*TODO: deprecated; use the typeclass interface,
  not the module one since passing some instances to functors breaks the VM
   (issue #12519)
*)
(* All of the properties we expect from indices,
   primarily a computable comparison operation,
   zero element, and successor operation.
*)
Module Type __Natlike.
  
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

End __Natlike.

(*TODO: deprecated*)
(* Notations for conveniently working with natlike elements *)
Module __NatlikeNotations (Import NL : __Natlike).

  (*TODO: add a number notation?*)
  
  Infix "=?" := eqb (at level 70, no associativity).
  Infix "<?" := ltb (at level 70, no associativity).
  Infix "<=?" := leb (at level 70, no associativity).
  Notation "i .+1" := (succ i) (at level 70, no associativity).

End __NatlikeNotations.

