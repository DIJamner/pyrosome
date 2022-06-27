Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.


From Ltac2 Require Import Ltac2 Constr.
Set Default Proof Mode "Classic".


Inductive telescope : Type :=
| tele_nil : telescope
| tele_cons {A} (a:A) : (forall (x:=a), telescope) -> telescope.
Arguments tele_cons {A}%type_scope a _.

Fixpoint tnth_ty n t : Type :=
  match n with
  | 0 => match t with
         | tele_nil => unit
         | @tele_cons A _ _ => A
         end
  | S m => match t with
           | tele_nil => unit
           | tele_cons _ t => tnth_ty m t
           end
  end.

Fixpoint tnth n t : tnth_ty n t :=
  match n with
  | 0 => match t with
         | tele_nil => tt
         | tele_cons x _ => x
         end
  | S m => match t with
           | tele_nil => tt
           | tele_cons _ t => tnth m t
           end
  end.

Variant memoizer (next : nat) : Prop := mem_init : memoizer next.


    Ltac memoized_prove_A t A e acc :=
    lazymatch e with
    | @tele_cons ?B ?H ?e' =>
        tryif constr_eq_strict A B
        then exact (tnth acc t)
        else memoized_prove_A t A e' constr:(S acc)
    | _ => fail
    end.

    Ltac memoized_assumption :=
    lazymatch goal with
      [ t := ?e : telescope|-?G] =>
        memoized_prove_A t G e constr:(0)
    end.

Ltac init_memoization :=
  let t := open_constr:(_ : telescope) in
  pose t.


Ltac2 unshelve_evar e :=
  match Unsafe.kind e with
  | Unsafe.Evar e _ => Control.new_goal e
  | _ => fail
  end.
Ltac unshelve_evar e :=
  let x := ltac2:(e|- match Ltac1.to_constr e with Some e => unshelve_evar e | _ => fail end) in
  x e.
Ltac tele_tail e :=
  lazymatch e with
  | tele_cons _ ?tl => tele_tail tl
  | _ => e
  end.

Ltac memoize tac :=
  first [ memoized_assumption
        | lazymatch goal with
            [t:= ?e : telescope |- ?G] =>
              let t_tl := tele_tail e in
              let t' := open_constr:(@tele_cons G _ _) in
              unify t_tl t';
              lazymatch t' with
                (tele_cons ?G' _) =>
                  unshelve_evar G';
                  [memoized_assumption| solve[ tac]]
              end
          end].


Arguments tele_cons A%type_scope {a} _.
Global Hint Resolve tele_nil : core.

Goal forall (A B C : Prop), (A -> B) -> A -> (B -> B -> C) -> A/\ A/\ C.
  intros.
  init_memoization.

  split.
  time memoize intuition.
  split.
  time memoize intuition.
  apply H1.
  time memoize intuition.
  time memoize intuition.
  Unshelve.
  constructor.
Qed.
