Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require List.
From Utils Require Import Utils Monad.

Section __.

  Context {Err : Type}.
  
  Instance sum_monad : Monad (sum Err) :=
    {
      Mret := @inr _;
      Mbind _ _ f ma :=
      match ma with
      | inr x => f x
      | inl e => inl e
      end
    }.

  Definition Merror {A} := @inl Err A.

  Definition Merr_unless (b : bool) e {A} `{WithDefault A} : Err + A :=
    if b then inr default else Merror e.

End __.

Existing Instance sum_monad.
