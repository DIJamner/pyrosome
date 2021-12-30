From coqutil Require Import Map.Interface.
(*
TODO: implement map with tries?
Require Import Tries.Canonical.

TODO: implement map Int63 with ArrayList?

TODO: should union be here?
*)

Module SetlikeMap.

  Class setlike_map (K V : Type) :=
    {
      map :> map.map K V;
      intersection : map -> map -> map;
      union : map -> map -> map;
    }.
  Arguments setlike_map : clear implicits.
  Local Coercion map : setlike_map >-> map.map.
  
  Class ok {K V} (imap : setlike_map K V) :=
    {
      map_ok :> map.ok imap;
      get_intersect_same : forall (m1 m2 : imap) k,
        map.get m1 k = map.get m2 k ->
        map.get (intersection m1 m2) k = map.get m1 k;
      get_intersect_diff : forall (m1 m2 : imap) k,
        ~ (map.get m1 k = map.get m2 k) ->
        map.get (intersection m1 m2) k = None;
      get_union_left : forall (m1 m2 : imap) k,
        map.get m2 k = None ->
        map.get (union m1 m2) k = map.get m1 k;
      get_union_right : forall (m1 m2 : imap) k,
        map.get m1 k = None ->
        map.get (union m1 m2) k = map.get m2 k;
      (*TODO: properties of some*)
    }.

End SetlikeMap.
Global Coercion SetlikeMap.map : SetlikeMap.setlike_map >-> map.map.
Notation intersection := SetlikeMap.intersection.
Notation union := SetlikeMap.union.


Module Sets.
  Section __.
    Context {A:Type}.

    Notation set := (SetlikeMap.setlike_map A unit).

    Context {set_instance : set}.

    Local Hint Mode map.map - - : typeclass_instances.  

    Definition member s (a : A) :=
      if map.get s a then true else false.

    Definition add_elt s (a : A) :=
      map.put s a tt.

  End __.

  Global Notation set A := (SetlikeMap.setlike_map A unit).
  
End Sets.

