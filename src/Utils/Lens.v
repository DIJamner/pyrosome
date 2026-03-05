From Utils Require Import Utils Monad.
Import StateMonad.

Class Lens (A:Type) (B: Type) : Type :=
  {
    lens_get : A -> B;
    lens_set : A -> B -> A;
  }.

(*TODO: move to state monad? *)
Class StateMonad S M `{Monad M} : Type :=
  {
    get_state : M S;
    set_state : S -> M unit;
  }.

#[export] Instance StateMonad_stateT {S M} `{Monad M}
  : StateMonad S (stateT S M) :=
  {
    get_state s := Mret (s,s);
    set_state s_new _ := Mret (tt,s_new);
  }.

#[export] Instance StateMonad_state {S}
  : StateMonad S (state S) :=
  {
    get_state s := (s,s);
    set_state s_new _ := (tt,s_new);
  }.


#[export] Instance StateMonad_stateT_lens {S S' M} `{Monad M} `{Lens S S'}
  : StateMonad S' (stateT S M) :=
  {
    get_state s := Mret (lens_get s,s);
    set_state s_new s := Mret (tt,lens_set s s_new);
  }.

#[export] Instance StateMonad_state_lens {S S'} `{Lens S S'}
  : StateMonad S' (state S) :=
  {
    get_state s := (lens_get s,s);
    set_state s_new s := (tt,lens_set s s_new);
  }.

Definition state_embed
  {S S' M} `{StateMonad S M} `{Lens S S'} {A}
  (comp : state S' A) : M A :=
  @!let s <- get_state in
    let (r,s') := comp (lens_get s) in
    let _ <- set_state (lens_set s s') in
    ret r.
