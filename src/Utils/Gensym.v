Set Implicit Arguments.

Require Lists.List.
From Utils Require Import Utils Natlike Monad.

Section __.
  Import StateMonad.

  Context {S : Type}
          `{Natlike S}.

  Local Notation state := (state S).

  Definition gensym : state S :=
    fun s => (succ s, s).

End __.
