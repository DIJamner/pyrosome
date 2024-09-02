Require Import Lists.List.
Import ListNotations.

Section __.
  Context {A : Type}.

  Fixpoint ntuple n : Type :=
    match n with
    | 0 => unit
    | S n => ntuple n * A
    end.

  Fixpoint to_list n : ntuple n -> list A :=
    match n with
    | 0 => fun _ => []
    | S n => fun p => cons (snd p) (to_list n (fst p))
    end.

  Fixpoint of_list l : ntuple (length l) :=
    match l with
    | [] => tt
    | a::l => (of_list l,a)
    end.

End __.
            
