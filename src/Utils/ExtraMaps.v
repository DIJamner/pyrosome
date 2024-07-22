From coqutil Require Import Map.Interface Map.Solver.

From Utils Require Import Eqb Options.

(*
TODO: implement map with tries?
Require Import Tries.Canonical.

TODO: implement map Int63 with ArrayList?

TODO: should union be here?
*)

Module Sets.

  Class set (A : Type) :=
    {
      set_as_map :> map.map A unit;
      intersection : set_as_map -> set_as_map -> set_as_map;
      union : set_as_map -> set_as_map -> set_as_map;
    }.
  Arguments set : clear implicits.
  Local Coercion set_as_map : set >-> map.map.
  
  Class ok {A} (iset : set A) :=
    {
      set_as_map_ok :> map.ok iset;
      get_intersect_same : forall (m1 m2 : iset) k,
        map.get m1 k = map.get m2 k ->
        map.get (intersection m1 m2) k = map.get m1 k;
      get_intersect_diff : forall (m1 m2 : iset) k,
        ~ (map.get m1 k = map.get m2 k) ->
        map.get (intersection m1 m2) k = None;
      get_union_left : forall (m1 m2 : iset) k,
        map.get m2 k = None ->
        map.get (union m1 m2) k = map.get m1 k;
      get_union_right : forall (m1 m2 : iset) k,
        map.get m1 k = None ->
        map.get (union m1 m2) k = map.get m2 k;
      (*TODO: rephrase proerties to be better suited to unit*)
    }.

  
  Section __.
    Context {A:Type}.
    Context {set_instance : set A}.
    Local Hint Mode map.map - - : typeclass_instances. 
    
    Definition member s (a : A) :=
      if map.get s a then true else false.

    Definition add_elt s (a : A) :=
      map.put s a tt.
    
  End __.

  (* Implements union and intersection as folds. *)
  Local Instance set_from_map {A} (m : map.map A unit) : set A :=
    {
      set_as_map := m;
      intersection m1 := map.fold (fun acc k _ => if map.get m1 k then map.put acc k tt else acc) map.empty;
      union := map.fold map.put;
    }.

End Sets.
Global Coercion Sets.set_as_map : Sets.set >-> map.map.

Require Import Utils.Monad.
(*TODO: is this the right place for this?*)
Section __.

  
  Context {A B value : Type}.
  Context {B_map : map.map B value}.
  Context {A_map : map.map A B_map}.

  
  
  Local Instance pair_map : map.map (A * B) value :=
    {
      map.rep := A_map;
      map.empty := map.empty;
      map.get m '(ka, kb) :=
      Mbind (fun mb => map.get mb kb) (map.get m ka);
      map.put m '(ka, kb) v :=
      match map.get m ka with
      | None => map.put m ka (map.singleton kb v)
      | Some mb => map.put m ka (map.put mb kb v)
      end;
      map.remove m '(ka,kb) :=
      match map.get m ka with
      | None => m
      | Some mb => map.put m ka (map.remove mb kb)
      end;
      map.fold _ f :=
        map.fold (fun acc ka mb =>
                    map.fold (fun acc kb v => f acc (ka,kb) v) acc mb)
    }.

End __.


Ltac find_map_ok :=
  let m1 := lazymatch goal with
              |- ?m1 = _ => m1
            end in
  let map := lazymatch type of m1 with
               @map.rep _ _ ?map => map
             end in
  constr:(_ : map.ok map).


Ltac maps_equal :=
  let map_ok := find_map_ok in
  eapply map.map_ext;
  intros;
  Solver.map_solver_core_impl map_ok;
  repeat lazymatch goal with
    | |- context c [eqb ?a ?b] =>
        pose proof (eqb_spec a b);
        destruct (eqb a b)
    end;
  subst;
  try congruence.


Section __.

  Context {key : Type}.
  Context (m : forall A, map.map key A).
  
  (* TODO: define map_plus_ok *)
  (* Extra features that are generally easy to implement on a map,
     but can be implemented more efficiently directly than by map.fold
   *)
  Class map_plus : Type := {
      map_intersect : forall {A B C}, (A -> B -> C) -> m A -> m B -> m C;
      map_fold_values : forall {A B}, (A -> B -> B) -> m A -> B -> B;
      map_map : forall {A B}, (A -> B) -> m A -> m B;
    }.

  (*TODO: strengthen from Is_Some to a result about the value*)
  Class map_plus_ok `{map_plus} : Prop := {
      (*base_map_ok :> forall A, map.ok (m A);*)
      intersect_spec : forall A B C (f : A -> B -> C) k t1 t2,
        map.get (map_intersect f t1 t2) k
        = match map.get t1 k, map.get t2 k with
          | Some a, Some b => Some (f a b)
          | _, _ => None
          end;
      
      map_map_spec : forall A B (f : A -> B) m k,
        map.get (map_map f m) k = option_map f (map.get m k);
    }.

End __.

Arguments map_intersect {key}%type_scope {m}%function_scope {map_plus} {A B C}%type_scope _%function_scope _ _.
Arguments map_fold_values {key}%type_scope {m}%function_scope {map_plus} {A B}%type_scope _%function_scope _ _.
Arguments map_map {key}%type_scope {m}%function_scope {map_plus} {A B}%type_scope _%function_scope _.
