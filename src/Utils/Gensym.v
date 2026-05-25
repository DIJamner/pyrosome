Set Implicit Arguments.

From Stdlib Require Lists.List.
From Utils Require Import Natlike Monad.

Section __.
  Import StateMonad.

  Context {S : Type}
          `{Natlike S}.

  Local Notation state := (state S).

  Definition gensym : state S :=
    fun s => (succ s, s).

End __.
