Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* Monad with a fail operation*)
Class Monad (M : Set -> Set) : Type :=
  {
  Mret : forall {A:Set}, A -> M A;
  Mbind : forall {A B:Set}, (A -> M B) -> M A -> M B;
  Mfail : forall {A:Set}, M A;
  }.


Declare Custom Entry monadic_do.

Notation "'do' e" := (e) (at level 92, e custom monadic_do).


Notation "p <- e ; b" :=
  (Mbind (fun p => b) e)
    (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).

(* Uses the partiality of fail to perform additional matching where desired *)
Notation "p <?- e ; b" :=
  (Mbind (fun x => match x with p => b | _ => Mfail end) e)
    (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).


Notation "'let' p := e ; b" :=
  (let p := e in b)
    (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).

Notation "'ret' e" := (Mret e) (in custom monadic_do at level 90, e constr).

(*Notation "e" := (e) (in custom monadic_do at level 80, e constr at level 80).*)

Notation "! e ; b" :=
  (if e then b else Mfail)
    (in custom monadic_do at level 90, left associativity, e constr, b custom monadic_do).

Generalizable Variable M.
Definition Mfmap `{mmon:Monad M} {A B:Set} (f : A -> B) : M A -> M B :=
  @Mbind M mmon A B (fun x => Mret (f x)).
