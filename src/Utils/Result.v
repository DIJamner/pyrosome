From Stdlib Require Import String.
From coqutil Require Import Datatypes.Result Datatypes.dlist.
From Utils Require Import Monad.

Open Scope string.

(*TODO: is there a better place for this?
  Used to put some info in the type of a failing computation.
 *)
Inductive Impossible {A} (a:A) : Prop := .
Definition Is_Success {A} (r : result A) : Prop :=
  if r then True else Impossible r.

Definition true_or (b:bool) els : result unit :=
  if b then Success tt else els.

Definition Some_or {A} (b:option A) els : result A :=
  match b with
  | Some a => Success a
  | None => els
  end.

Definition resultT (M : Type -> Type) A := M (result A).

#[export] Instance resultT_trans : MonadTrans resultT :=
  {|
    transformer_monad M _ :=
      {|
        Mret _ a := (Mret (Success a));
        Mbind _ _ f :=
          Mbind (M:=M) (fun ma => match ma with
                                      | Success a => f a
                                      | Failure err => Mret (Failure err)
                                      end)
      |};
  lift M _ A ma := @! let a <- ma in ret Success a
  |}.


Definition result_monad : Monad result :=
  Eval cbv in (resultT_trans.(transformer_monad) : Monad (resultT id)).
#[export] Existing Instance result_monad.


Polymorphic Fixpoint dapp (l1 l2 : dlist) :=
  match l1 with
  | dnil => l2
  | dcons x l1 => dcons x (dapp l1 l2)
  end.

Section __.
  Context {A B} (comp : A -> result B).

  Polymorphic Fixpoint res_exists'  l acc : result B :=
    match l with
    | nil => Failure acc
    | cons x l =>
        match comp x with
        | Success x => Success x
        | Failure err => res_exists' l (dapp err (dcons "|" acc))
        end
    end.

  Polymorphic Definition res_exists l := res_exists' l dnil.
End __.
