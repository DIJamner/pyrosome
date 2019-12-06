
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Tactic Notation "intro_to" constr(ty) :=
  repeat match goal with
         | |- ty -> _ => idtac
         | |- ty _ -> _ => idtac
         | |- ty _ _-> _ => idtac
         | |- ty _ _ _ -> _ => idtac
         | |- ty _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ _ -> _ => idtac
         | |- _ -> _ => intro
         | |- _ => fail 2 "could not find argument with head" ty
         end.


Ltac construct_with t :=
  constructor; apply: t; eauto.


Tactic Notation "inversion" :=
  let H := fresh in
  move => H; inversion H.
