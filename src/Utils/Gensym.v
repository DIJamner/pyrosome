Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require List.
From Utils Require Import Utils Natlike Monad.

Section __.
  Import StateMonad.

  Context {S : Type}
          `{Natlike S}.

  Local Notation ST := (ST S).

  Definition gensym : ST S :=
    fun s => (succ s, s).

End __.
