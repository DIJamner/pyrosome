Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require List.
From Utils Require Import Utils.

Class Monad (M : Type -> Type) : Type :=
  {
  Mret : forall {A}, A -> M A;
  Mbind : forall {A B}, (A -> M B) -> M A -> M B
  }.

Definition Mseq {M} `{Monad M} {A B} (mu : M A) (ma : M B) : M B :=
  Mbind (fun _ => ma) mu.

Declare Custom Entry monadic_do.

(* I would use 'do', but it interferes with proof general indentation *)
Notation "@! e" := (e) (at level 200, e custom monadic_do).


Notation "'let' p <- e 'in' b" :=
  (Mbind (fun p => b) e)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).

(*TODO: add fail
(* Uses the partiality of fail to perform additional matching where desired *)
Notation "p <?- e ; b" :=
  (Mbind (fun x => match x with p => b | _ => Mfail end) e)
    (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).
*)

(*TODO: this notation prints too readily*)
Notation "'let' p := e 'in' b" :=
  (let p := e in b)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).


Notation "'let' p <?- e 'in' b" :=
  (Mbind (fun x => match x with p => b | _ => default end) e)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).

Notation "'let' ! e 'in' b" :=
  (if e then b else default)
    (in custom monadic_do at level 200, left associativity, e constr, b custom monadic_do).

Instance option_monad : Monad option :=
  {
    Mret _ := Some;
    Mbind _ _ f ma := match ma with Some a => f a | None => None end;
  }.

Notation "'if' c 'then' b1 'else' b2" :=
  (if c then b1 else b2)
    (in custom monadic_do at level 200, left associativity,
        c constr, b1 custom monadic_do, b2 custom monadic_do).

Notation "e1 ; e2" :=
  (Mseq e1 e2)
    (in custom monadic_do at level 100, left associativity,
        e1 custom monadic_do,
        e2 custom monadic_do).

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
Definition Mfmap `{mmon:Monad M} {A B} (f : A -> B) (ma: M A) : M B :=
  @! let a <- ma in ret f a.

(*TODO: move these into separate files? *)

Section MonadListOps.
  Import List List.ListNotations.
  Context {M A B} `{Monad M}
          (f : A -> M B).

  Fixpoint list_Mmap (l : list A) : M (list B) :=
    match l with
    | [] => @! ret []
    | a::al' =>
        @! let b <- f a in
           let bl' <- list_Mmap al' in
           ret (b::bl')
    end.
  
  Fixpoint list_Miter (f : A -> M unit) (l : list A) : M unit :=
    match l with
    | [] => @! ret tt
    | a::al' =>
        @! let b <- f a in
           let tt <- list_Miter f al' in
           ret tt
    end.
End MonadListOps.


From coqutil Require Map.Interface.

Module StateMonad.

  Definition ST S A := S -> (S * A).

  Instance state_monad {S} : Monad (ST S) :=
    {
      Mret _ a := fun s => (s,a);
      Mbind _ _ f ma :=
      fun s =>
        let (s,a) := ma s in
        f a s
    }.

  
  (*TODO: double check this is the right name*)
  (* backtracks the state if ma returns None *)       
  Definition try_with_backtrack {S A}
             (ma : ST S (option A)) : ST S (option A) :=
    fun g =>
      match ma g with
      | (g', Some a) => (g', Some a)
      | (_, None) => (g, None)
      end.
  
  Section MapOps.
    
    Import Map.Interface.
    
    Definition map_Mfold {S K V A}
               {MP : map.map K V}
               (f : K -> V -> A -> ST S A)
               (p : @map.rep _ _ MP) a : ST S A :=
      fun g =>
        map.fold
          (fun '(g, a) k v => f k v a g)
          (g, a) p.

    Definition map_Miter {S K V}
               {MP : map.map K V}
               (f : K -> V -> ST S unit)
               (p : @map.rep _ _ MP) : ST S unit :=
      map_Mfold (fun k v _ => f k v) p tt.

  End MapOps.

  Notation "'for' kp vp 'from' m 'in' b" :=
    (map_Miter (fun kp vp => b) m)                       
      (in custom monadic_do at level 200, left associativity,
          kp pattern at level 0,
          vp pattern at level 0,
          m constr, b custom monadic_do).
  
  Notation "'for/fold' kp vp 'from' m [[ acc := a ]] 'in' b" :=
    (map_Mfold (fun kp vp acc => b) m a)                       
      (in custom monadic_do at level 200, left associativity,
          kp pattern at level 0,
          vp pattern at level 0,
          acc pattern at level 0,
          m constr, b custom monadic_do).

End StateMonad.
