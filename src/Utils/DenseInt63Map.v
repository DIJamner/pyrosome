Require Import ZArith Int63.
Open Scope int63.
Require Import coqutil.Map.Interface.

Require Import Utils.PersistentArrayList.
Import PArrayList.

(*
  Implements the map interface with an arraylist.
  Has good performance if the map keys are dense.
 *)
(*
  TODO: generalize to any arraylist?
 *)

Section __.

  Context (value : Type).

  Section Fold.
    Context {R} (f : R -> int -> value -> R)
      (m : array (option value)).
    
    (*TODO: performance of structural argument.
     Note: behaviour depends on having the exact fuel *)
    Fixpoint fold' (fuel : nat) (acc : R) (i : int) :=
      match fuel with
      | 0 => acc
      | S fuel =>
          let acc :=
          match get m i with
          | Some v => (f acc i v)
          | None => acc
          end in
          fold' fuel acc (succ i)
      end.
  End Fold.

  Instance map : map.map int value :=
    {|
      map.rep := array (option value);
      map.empty := make None;
      map.get := get;
      map.put m k v := set m k (Some v);
      map.remove m k := set m k None;
      map.fold A f acc m := fold' f m (Z.to_nat (to_Z m.(len))) acc 0;
    |}.
  (* TODO: prove map.ok *)
End __.
