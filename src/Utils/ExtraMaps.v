From coqutil Require Import Map.Interface.
(*
TODO: implement map with tries?
Require Import Tries.Canonical.

TODO: implement map Int63 with ArrayList?
*)

Module IntersectableMap.

  Class intersectable_map (K V : Type) :=
    {
      map :> map.map K V;
      intersection : map -> map -> map
    }.
  Arguments intersectable_map : clear implicits.
  Local Coercion map : intersectable_map >-> map.map.
  
  Class ok {K V} (imap : intersectable_map K V) :=
    {
      map_ok :> map.ok imap;
      get_intersect_same : forall (m1 m2 : imap) k,
        map.get m1 k = map.get m2 k ->
        map.get (intersection m1 m2) k = map.get m1 k;
      get_intersect_diff : forall (m1 m2 : imap) k,
        ~ (map.get m1 k = map.get m2 k) ->
        map.get (intersection m1 m2) k = None;
    }.

End IntersectableMap.
Global Coercion IntersectableMap.map : IntersectableMap.intersectable_map >-> map.map.
Notation intersection := IntersectableMap.intersection.


Module Sets.
  Section __.
    Context {A:Type}.

    Notation set := (IntersectableMap.intersectable_map A unit).

    Context {set_instance : set}.

    Local Hint Mode map.map - - : typeclass_instances.  

    Definition member s (a : A) :=
      if map.get s a then true else false.

    Definition add_elt s (a : A) :=
      map.put s a tt.

  End __.

  Global Notation set A := (IntersectableMap.intersectable_map A unit).
  
End Sets.

