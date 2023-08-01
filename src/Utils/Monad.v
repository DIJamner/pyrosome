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

(* For disambiguation (usually debugging) *)
Notation "'ret' { M } e" :=
  (Mret (M:=M) e)
    (in custom monadic_do at level 90, e constr, only parsing).

Notation "'let' { M } p <- e 'in' b" :=
  (Mbind (M:=M) (fun p => b) e)
    (in custom monadic_do at level 200, left associativity,
        p pattern at level 0, e constr, b custom monadic_do,
        only parsing).

Notation "'let' { M } p <?- e 'in' b" :=
  (Mbind (M:=M) (fun x => match x with p => b | _ => default end) e)
    (in custom monadic_do at level 200, left associativity,
        p pattern at level 0, e constr, b custom monadic_do,
        only parsing).

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
  Context {M} {A B : Type} `{Monad M}.

  Fixpoint list_Mfoldl (f : B -> A -> M B) (l : list A) (acc : B) : M B :=
    match l with
    | [] => @! ret acc
    | a::al' =>
        @! let fab <- f acc a in
          (list_Mfoldl f al' fab)
    end.

  Fixpoint list_Mmap (f : A -> M B) (l : list A) : M (list B) :=
    match l with
    | [] => @! ret []
    | a::al' =>
        @! let b <- f a in
           let bl' <- list_Mmap f al' in
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

  
  Fixpoint list_Miter_idx' (f : nat -> A -> M unit) (l : list A) n : M unit :=
    match l with
    | [] => @! ret tt
    | a::al' =>
        @! let b <- f n a in
           let tt <- list_Miter_idx' f al' (S n) in
           ret tt
    end.

  Definition list_Miter_idx  (f : nat -> A -> M unit) (l : list A) := list_Miter_idx' f l 0.
  
End MonadListOps.



Class MonadTrans (T : (Type -> Type) -> Type -> Type) : Type :=
  {
    transformer_monad :> forall `{Monad M}, Monad (T M);
    lift : forall `{Monad M} {A}, M A -> T M A
  }.

#[export] Instance id_monad : Monad id :=
  {
    Mret _ a := a;
    Mbind _ _ f := f;
  }.


Notation "'let' p <^- e 'in' b" :=
  (Mbind (fun p => b) (lift e))
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).


Definition optionT (M : Type -> Type) A := M (option A).

#[export] Instance optionT_trans : MonadTrans optionT :=
  {|
    transformer_monad M _ :=
      {|
        Mret _ a := (Mret (Some a));
        Mbind _ _ f :=
          Mbind (M:=M) (fun ma => match ma with
                                      | Some a => f a
                                      | None => Mret None
                                      end)
      |};
  lift M _ A ma := @! let a <- ma in ret Some a
  |}.


Definition option_monad : Monad option :=
  Eval cbv in (optionT_trans.(transformer_monad) : Monad (optionT id)).
#[export] Existing Instance option_monad.

From coqutil Require Map.Interface.

Module StateMonad.

  Section WithS.

  Context {S : Type}.

  Definition stateT M A := S -> M (A * S)%type.

  #[export] Instance stateT_trans : MonadTrans stateT :=
    {|
      transformer_monad M _ :=
        {|      
          Mret _ a := fun s => Mret (a,s);
          Mbind _ _ f :=
            Basics.compose (Mbind (uncurry f))
        |};
      lift M _ A ma s := Mbind  (fun x => Mret (x,s)) ma
    |}.

  Definition state := Eval cbv in stateT id.
  
  Definition state_monad : Monad state :=
    Eval cbv in (stateT_trans.(transformer_monad) : Monad (stateT id)).
  #[export] Existing Instance state_monad.

  
  (*TODO: double check this is the right name*)
  (* backtracks the state if ma returns None *)       
  Definition try_with_backtrack {A}
             (ma : optionT (stateT id) A) :  optionT (stateT id) A :=
    fun g =>
      match ma g with
      | (Some a, g') => (Some a, g')
      | (None,_) => (None, g)
      end.
  
  Section MapOps.
    
    Import Map.Interface.
    
    Definition map_Mfold {K V A}
               {MP : map.map K V}
               (f : K -> V -> A -> state A)
               (p : @map.rep _ _ MP) a : state A :=
      fun g =>
        map.fold
          (fun '(a, g) k v => f k v a g)
          (a, g) p.

    Definition map_Miter {K V}
               {MP : map.map K V}
               (f : K -> V -> state unit)
               (p : @map.rep _ _ MP) : state unit :=
      map_Mfold (fun k v _ => f k v) p tt.

  End MapOps.

  End WithS.

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
  
  Arguments stateT S%type_scope M%function_scope A%type_scope : clear implicits.
  Arguments state S%type_scope A%type_scope : clear implicits.
  
End StateMonad.

