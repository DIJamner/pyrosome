From coqutil Require Import Map.Interface.
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

End Sets.
Global Coercion Sets.set_as_map : Sets.set >-> map.map.

