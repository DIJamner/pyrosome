Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Class Monad (M : Type -> Type) : Type :=
  {
  Mret : forall {A}, A -> M A;
  Mbind : forall {A B}, (A -> M B) -> M A -> M B
  }.


Declare Custom Entry monadic_do.

Notation "'do' e" := (e) (at level 200, e custom monadic_do).


Notation "'let' p <- e 'in' b" :=
  (Mbind (fun p => b) e)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).

(*TODO: add fail
(* Uses the partiality of fail to perform additional matching where desired *)
Notation "p <?- e ; b" :=
  (Mbind (fun x => match x with p => b | _ => Mfail end) e)
    (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).
*)


Notation "'let' p := e 'in' b" :=
  (let p := e in b)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).


Notation "'if' c 'then' b1 'else' b2" :=
  (if c then b1 else b2)
    (in custom monadic_do at level 200, left associativity,
        c constr, b1 custom monadic_do, b2 custom monadic_do).

Notation "'ret' e" := (Mret e) (in custom monadic_do at level 90, e constr).

Notation "e" := e (in custom monadic_do at level 90, e constr at level 0).

(*Notation "e" := (e) (in custom monadic_do at level 80, e constr at level 80).*)

(*
Notation "! e ; b" :=
  (if e then b else Mfail)
    (in custom monadic_do at level 90, left associativity, e constr, b custom monadic_do).
TODO: add fail
*)

Generalizable Variable M.
Definition Mfmap `{mmon:Monad M} {A B:Set} (f : A -> B) (ma: M A) : M B :=
  do let a <- ma in ret f a.
