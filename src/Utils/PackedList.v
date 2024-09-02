Require Import Lists.List.
Import ListNotations.

From Utils Require Import Utils NTuple.

Section __.
  Context {A : Type}.

  (* non-empty lists with n*16 elements *)
  Inductive block_list : Type :=
  | blist_base : A -> A -> A -> A ->
                 A -> A -> A -> A ->
                 A -> A -> A -> A ->
                 A -> A -> A -> A ->
                 block_list
  | blist_cons : A -> A -> A -> A ->
                 A -> A -> A -> A ->
                 A -> A -> A -> A ->
                 A -> A -> A -> A ->
                 block_list -> block_list.

  Variant plist : Type :=
  (* we have special cases for the first n-sized lists *)
  | pnil : plist
  | tuple1 : A -> plist
  | tuple2 : A -> A -> plist
  | tuple3 : A -> A -> A -> plist
  | tuple4 : A -> A -> A -> A ->
             plist
  | tuple5 : A -> A -> A -> A ->
             A ->
             plist
  | tuple6 : A -> A -> A -> A ->
             A -> A ->
             plist
  | tuple7 : A -> A -> A -> A ->
             A -> A -> A ->
             plist
  | tuple8 : A -> A -> A -> A ->
             A -> A -> A -> A ->
             plist
  | tuple9 : A -> A -> A -> A ->
             A -> A -> A -> A ->
             A ->
             plist
  | tuple10 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A ->
              plist
  | tuple11 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A ->
              plist
  | tuple12 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              plist
  | tuple13 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              A ->
              plist
  | tuple14 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A ->
              plist
  | tuple15 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A ->
              plist
  (* we duplicate each constructor for the >n cases
     rather than allow a nil tail to avoid the second
     dereference on small lists
   *)
  | phd0 : block_list -> plist
  | phd1 : A -> block_list -> plist
  | phd2 : A -> A -> block_list -> plist
  | phd3 : A -> A -> A -> block_list -> plist
  | phd4 : A -> A -> A -> A ->
           block_list -> plist
  | phd5 : A -> A -> A -> A ->
           A ->
           block_list -> plist
  | phd6 : A -> A -> A -> A ->
           A -> A ->
           block_list -> plist
  | phd7 : A -> A -> A -> A ->
           A -> A -> A ->
           block_list -> plist
  | phd8 : A -> A -> A -> A ->
           A -> A -> A -> A ->
           block_list -> plist
  | phd9 : A -> A -> A -> A ->
           A -> A -> A -> A ->
           A ->
           block_list -> plist
  | phd10 : A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A ->
            block_list -> plist
  | phd11 : A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A -> A ->
            block_list -> plist
  | phd12 : A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A -> A -> A ->
            block_list -> plist
  | phd13 : A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A -> A -> A ->
            A ->
            block_list -> plist
  | phd14 : A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A ->
            block_list -> plist
  | phd15 : A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A -> A -> A ->
            A -> A -> A ->
            block_list -> plist.
  Hint Constructors block_list plist : utils.

  (* TODO: call list foldl/r here? fold_right *)
  Section __.
    Context {B} (f : A -> B -> B) (base : B).
    Definition block_list_foldrF F l :=
      match l with
      | blist_base x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
          fold_right f base
            [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
      | blist_cons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l' =>
          fold_right f (F l')
            [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14] 
      end.

    Definition plist_foldrF' block_list_foldr (l:plist) :=
      match l with
      | pnil => base
      | tuple1 x => fold_right f base [x]
      | tuple2 x x0 => fold_right f base [x; x0]
      | tuple3 x x0 x1 => fold_right f base [x; x0; x1]
      | tuple4 x x0 x1 x2 => fold_right f base [x; x0; x1; x2]
      | tuple5 x x0 x1 x2 x3 =>
          fold_right f base [x; x0; x1; x2; x3]
      | tuple6 x x0 x1 x2 x3 x4 =>
          fold_right f base [x; x0; x1; x2; x3; x4]
      | tuple7 x x0 x1 x2 x3 x4 x5 =>
          fold_right f base [x; x0; x1; x2; x3; x4; x5]
      | tuple8 x x0 x1 x2 x3 x4 x5 x6 =>
          fold_right f base [x; x0; x1; x2; x3; x4; x5; x6]
      | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 =>
          fold_right f base [x; x0; x1; x2; x3; x4; x5; x6; x7]
      | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
          fold_right f base [x; x0; x1; x2; x3; x4; x5; x6; x7; x8]
      | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
          fold_right f base [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9]
      | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
          fold_right f base [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10]
      | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
          fold_right f base [x; x0; x1; x2; x3; x4;
                        x5; x6; x7; x8; x9; x10; x11]           
      | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => 
          fold_right f base [x; x0; x1; x2; x3; x4; x5; x6;
                        x7; x8; x9; x10; x11; x12]           
      | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
          fold_right f base [x; x0; x1; x2; x3; x4; x5; x6; x7;
                        x8; x9; x10; x11; x12; x13]           
      | phd0 bl => (block_list_foldr bl)
      | phd1 x bl => fold_right f (block_list_foldr bl) [x]
      | phd2 x x0 bl => fold_right f (block_list_foldr bl) [x; x0]
      | phd3 x x0 x1 bl => fold_right f (block_list_foldr bl) [x; x0; x1]
      | phd4 x x0 x1 x2 bl => fold_right f (block_list_foldr bl) [x; x0; x1; x2]
      | phd5 x x0 x1 x2 x3 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3]
      | phd6 x x0 x1 x2 x3 x4 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4]
      | phd7 x x0 x1 x2 x3 x4 x5 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4; x5]
           
      | phd8 x x0 x1 x2 x3 x4 x5 x6 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4; x5; x6]
           
      | phd9 x x0 x1 x2 x3 x4 x5 x6 x7 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4; x5; x6; x7]
           
      | phd10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4; x5; x6; x7; x8]
           
      | phd11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl =>
          fold_right f (block_list_foldr bl)
            [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9]
           
      | phd12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl =>
          fold_right f (block_list_foldr bl)
            [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10]
           
      | phd13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4;
                        x5; x6; x7; x8; x9; x10; x11]
           
      | phd14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl => 
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4; x5; x6;
                        x7; x8; x9; x10; x11; x12]
           
      | phd15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl =>
          fold_right f (block_list_foldr bl) [x; x0; x1; x2; x3; x4; x5; x6; x7;
                        x8; x9; x10; x11; x12; x13]
      end.
        
    Definition plist_foldrF :=
      Eval compute in plist_foldrF'.    
    
    Definition block_list_foldr :=
      Eval compute in fix block_list_foldr l := block_list_foldrF block_list_foldr l.

    Definition plist_foldr :=
      Eval cbv [plist_foldrF] in plist_foldrF block_list_foldr.  
        
  End __.

  (*TODO: as above*)
  Section __.
    Context {B} (f : B -> A -> B).
    Fixpoint block_list_foldl' l (base : B) :=
      match l with
      | blist_base x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
          fold_left f
            [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
            base
      | blist_cons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l' =>
          let base' :=
            fold_left f
              [x; x0; x1; x2; x3; x4; x5; x6; x7; x8;
               x9; x10; x11; x12; x13; x14]
              base in
          block_list_foldl' l' base'
      end.
    Definition block_list_foldl :=
      Eval compute in block_list_foldl'.
    
    Definition plist_foldl' (l:plist) base :=
      match l with
      | pnil => base
      | tuple1 x => fold_left f [x] base
      | tuple2 x x0 => fold_left f [x; x0] base
      | tuple3 x x0 x1 => fold_left f [x; x0; x1] base
      | tuple4 x x0 x1 x2 => fold_left f [x; x0; x1; x2] base
      | tuple5 x x0 x1 x2 x3 =>
          fold_left f [x; x0; x1; x2; x3] base
      | tuple6 x x0 x1 x2 x3 x4 =>
          fold_left f [x; x0; x1; x2; x3; x4] base
      | tuple7 x x0 x1 x2 x3 x4 x5 =>
          fold_left f [x; x0; x1; x2; x3; x4; x5] base
      | tuple8 x x0 x1 x2 x3 x4 x5 x6 =>
          fold_left f [x; x0; x1; x2; x3; x4; x5; x6] base
      | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 =>
          fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7] base
      | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
          fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] base
      | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
          fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] base
      | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
          fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] base
      | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
          fold_left f [x; x0; x1; x2; x3; x4;
                        x5; x6; x7; x8; x9; x10; x11]
            base
      | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => 
          fold_left f [x; x0; x1; x2; x3; x4; x5; x6;
                        x7; x8; x9; x10; x11; x12]
            base
      | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
          fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7;
                        x8; x9; x10; x11; x12; x13]
            base
      | phd0 bl => (block_list_foldl bl base)
      | phd1 x bl => block_list_foldl bl (fold_left f [x] base)
      | phd2 x x0 bl => block_list_foldl bl (fold_left f [x; x0] base)
      | phd3 x x0 x1 bl => block_list_foldl bl (fold_left f [x; x0; x1] base)
      | phd4 x x0 x1 x2 bl => block_list_foldl bl (fold_left f [x; x0; x1; x2] base)
      | phd5 x x0 x1 x2 x3 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3] base)
      | phd6 x x0 x1 x2 x3 x4 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4] base)
      | phd7 x x0 x1 x2 x3 x4 x5 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5]
            base)
      | phd8 x x0 x1 x2 x3 x4 x5 x6 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5; x6]
            base)
      | phd9 x x0 x1 x2 x3 x4 x5 x6 x7 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7]
            base)
      | phd10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8]
            base)
      | phd11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9]
            base)
      | phd12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10]
            base)
      | phd13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4;
                        x5; x6; x7; x8; x9; x10; x11]
            base)
      | phd14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl => 
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5; x6;
                        x7; x8; x9; x10; x11; x12]
            base)
      | phd15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl =>
          block_list_foldl bl (fold_left f [x; x0; x1; x2; x3; x4; x5; x6; x7;
                        x8; x9; x10; x11; x12; x13]
            base)
      end.
    
    Definition plist_foldl :=
      Eval cbv -[block_list_foldl] in plist_foldl'.
  End __.

 Definition pcons a (l:plist) :=
    match l with
    | pnil => tuple1 a
    | tuple1 x => tuple2 a x
    | tuple2 x x0 => tuple3 a x x0
    | tuple3 x x0 x1 => tuple4 a x x0 x1
    | tuple4 x x0 x1 x2 => tuple5 a x x0 x1 x2
    | tuple5 x x0 x1 x2 x3 => tuple6 a x x0 x1 x2 x3
    | tuple6 x x0 x1 x2 x3 x4 => tuple7 a x x0 x1 x2 x3 x4
    | tuple7 x x0 x1 x2 x3 x4 x5 => tuple8 a x x0 x1 x2 x3 x4 x5
    | tuple8 x x0 x1 x2 x3 x4 x5 x6 => tuple9 a x x0 x1 x2 x3 x4 x5 x6
    | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 => tuple10 a x x0 x1 x2 x3 x4 x5 x6 x7
    | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
        tuple11 a x x0 x1 x2 x3 x4 x5 x6 x7 x8
    | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
        tuple12 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
        tuple13 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
        tuple14 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 =>
        tuple15 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
        phd0 (blist_base a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    | phd0 bl => phd1 a bl
    | phd1 x bl => phd2 a x bl 
    | phd2 x x0 bl => phd3 a x x0 bl 
    | phd3 x x0 x1 bl => phd4 a x x0 x1 bl
    | phd4 x x0 x1 x2 bl => phd5 a x x0 x1 x2 bl
    | phd5 x x0 x1 x2 x3 bl => phd6 a x x0 x1 x2 x3 bl
    | phd6 x x0 x1 x2 x3 x4 bl => phd7 a x x0 x1 x2 x3 x4 bl
    | phd7 x x0 x1 x2 x3 x4 x5 bl => phd8 a x x0 x1 x2 x3 x4 x5 bl
    | phd8 x x0 x1 x2 x3 x4 x5 x6 bl =>
        phd9 a x x0 x1 x2 x3 x4 x5 x6 bl
    | phd9 x x0 x1 x2 x3 x4 x5 x6 x7 bl =>
        phd10 a x x0 x1 x2 x3 x4 x5 x6 x7 bl
    | phd10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl =>
        phd11 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl
    | phd11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl =>
        phd12 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl
    | phd12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl =>
        phd13 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl
    | phd13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl =>
        phd14 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl              
    | phd14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl =>
        phd15 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl
    | phd15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl =>
        phd0 (blist_cons a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl)
    end.

 (* TODO: should I have a block_list eta too?*)
 Definition plist_eta {B} (f : plist -> B) (l:plist) :=
    match l with
    | pnil => f pnil
    | tuple1 x => f (tuple1 x)
    | tuple2 x x0 => f (tuple2 x x0)
    | tuple3 x x0 x1 => f (tuple3 x x0 x1)
    | tuple4 x x0 x1 x2 => f (tuple4 x x0 x1 x2)
    | tuple5 x x0 x1 x2 x3 => f (tuple5 x x0 x1 x2 x3)
    | tuple6 x x0 x1 x2 x3 x4 => f (tuple6 x x0 x1 x2 x3 x4)
    | tuple7 x x0 x1 x2 x3 x4 x5 => f (tuple7 x x0 x1 x2 x3 x4 x5)
    | tuple8 x x0 x1 x2 x3 x4 x5 x6 => f (tuple8 x x0 x1 x2 x3 x4 x5 x6)
    | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 => f (tuple9 x x0 x1 x2 x3 x4 x5 x6 x7)
    | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
        f (tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8)
    | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
        f (tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
        f (tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
        f (tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 =>
        f (tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
        f (tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    | phd0 bl => f (phd0 bl)
    | phd1 x bl => f (phd1 x bl)
    | phd2 x x0 bl => f (phd2 x x0 bl)
    | phd3 x x0 x1 bl => f (phd3 x x0 x1 bl)
    | phd4 x x0 x1 x2 bl => f (phd4 x x0 x1 x2 bl)
    | phd5 x x0 x1 x2 x3 bl => f (phd5 x x0 x1 x2 x3 bl)
    | phd6 x x0 x1 x2 x3 x4 bl => f (phd6 x x0 x1 x2 x3 x4 bl)
    | phd7 x x0 x1 x2 x3 x4 x5 bl => f (phd7 x x0 x1 x2 x3 x4 x5 bl)
    | phd8 x x0 x1 x2 x3 x4 x5 x6 bl =>
        f (phd8 x x0 x1 x2 x3 x4 x5 x6 bl)
    | phd9 x x0 x1 x2 x3 x4 x5 x6 x7 bl =>
        f (phd9 x x0 x1 x2 x3 x4 x5 x6 x7 bl)
    | phd10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl =>
        f (phd10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl)
    | phd11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl =>
        f (phd11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl)
    | phd12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl =>
        f (phd12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl)
    | phd13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl =>
        f (phd13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl)             
    | phd14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl =>
        f (phd14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl)
    | phd15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl =>
        f (phd15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl)
    end.
 
 Definition pconsK {B} a (k : plist -> B)  (l:plist) :=
   match l with
   | pnil => k (tuple1 a)
   | tuple1 x => k (tuple2 a x)
   | tuple2 x x0 => k (tuple3 a x x0)
   | tuple3 x x0 x1 => k (tuple4 a x x0 x1)
   | tuple4 x x0 x1 x2 => k (tuple5 a x x0 x1 x2)
   | tuple5 x x0 x1 x2 x3 => k (tuple6 a x x0 x1 x2 x3)
   | tuple6 x x0 x1 x2 x3 x4 => k (tuple7 a x x0 x1 x2 x3 x4)
   | tuple7 x x0 x1 x2 x3 x4 x5 => k (tuple8 a x x0 x1 x2 x3 x4 x5)
   | tuple8 x x0 x1 x2 x3 x4 x5 x6 => k (tuple9 a x x0 x1 x2 x3 x4 x5 x6)
   | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 => k (tuple10 a x x0 x1 x2 x3 x4 x5 x6 x7)
   | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
       k (tuple11 a x x0 x1 x2 x3 x4 x5 x6 x7 x8)
   | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
       k (tuple12 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
   | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
       k (tuple13 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
   | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
       k (tuple14 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
   | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 =>
       k (tuple15 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
   | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
       k (phd0 (blist_base a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))
   | phd0 bl => k (phd1 a bl)
   | phd1 x bl => k (phd2 a x bl)
   | phd2 x x0 bl => k (phd3 a x x0 bl)
   | phd3 x x0 x1 bl => k (phd4 a x x0 x1 bl)
   | phd4 x x0 x1 x2 bl => k (phd5 a x x0 x1 x2 bl)
   | phd5 x x0 x1 x2 x3 bl => k (phd6 a x x0 x1 x2 x3 bl)
   | phd6 x x0 x1 x2 x3 x4 bl => k (phd7 a x x0 x1 x2 x3 x4 bl)
   | phd7 x x0 x1 x2 x3 x4 x5 bl => k (phd8 a x x0 x1 x2 x3 x4 x5 bl)
   | phd8 x x0 x1 x2 x3 x4 x5 x6 bl =>
       k (phd9 a x x0 x1 x2 x3 x4 x5 x6 bl)
   | phd9 x x0 x1 x2 x3 x4 x5 x6 x7 bl =>
       k (phd10 a x x0 x1 x2 x3 x4 x5 x6 x7 bl)
   | phd10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl =>
       k (phd11 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 bl)
   | phd11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl =>
       k (phd12 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 bl)
   | phd12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl =>
       k (phd13 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 bl)
   | phd13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl =>
       k (phd14 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bl)              
   | phd14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl =>
       k (phd15 a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 bl)
   | phd15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl =>
       k (phd0 (blist_cons a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 bl))
   end.

 Section ListRec16.
   Context {B} (f : list A -> B -> B) (base : B).
   Definition list_rec16FP rec l
     x' x0' x1' x2' x3' x4' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' : B :=
    match l with
    | [] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
           x5'; x6'; x7'; x8'; x9'; x10';
           x11'; x12'; x13'; x14'] base
    | [x] => f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x] base
    | [x; x0] => f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0] base
    | [x; x0; x1] => f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1] base
    | [x; x0; x1; x2] => f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2] base
    | [x; x0; x1; x2; x3] => f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3] base
    | [x; x0; x1; x2; x3; x4] => f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4] base
    | [x; x0; x1; x2; x3; x4; x5] => f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5] base
    | [x; x0; x1; x2; x3; x4; x5; x6] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6] base
    | [x; x0; x1; x2; x3; x4; x5; x6; x7] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6; x7] base
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6; x7; x8] base
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] =>
        f [x'; x0'; x1'; x2'; x3'; x4';
                x5'; x6'; x7'; x8'; x9'; x10';
                x11'; x12'; x13'; x14';
                x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] base        
    | x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l =>
        f [x'; x0'; x1'; x2'; x3'; x4'; x5'; x6'; x7'; x8'; x9'; x10'; x11'; x12'; x13'; x14']
          (rec l x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)        
    end.

   Definition list_rec16P :=
     Eval cbv in fix list_rec16P l := list_rec16FP list_rec16P l.
  
   Definition list_rec16F list_rec16P l : B :=
    match l with
    | [] => f [] base
    | [x] => f [x] base
    | [x; x0] => f [x; x0] base
    | [x; x0; x1] => f [x; x0; x1] base
    | [x; x0; x1; x2] => f [x; x0; x1; x2] base
    | [x; x0; x1; x2; x3] => f [x; x0; x1; x2; x3] base
    | [x; x0; x1; x2; x3; x4] => f [x; x0; x1; x2; x3; x4] base
    | [x; x0; x1; x2; x3; x4; x5] => f [x; x0; x1; x2; x3; x4; x5] base
    | [x; x0; x1; x2; x3; x4; x5; x6] =>
        f [x; x0; x1; x2; x3; x4; x5; x6] base
    | [x; x0; x1; x2; x3; x4; x5; x6; x7] =>
        f [x; x0; x1; x2; x3; x4; x5; x6; x7] base
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] =>
        f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] base
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] =>
        f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] =>
        f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] =>
        f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] =>
        f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] base        
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] =>
        f [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] base        
    | x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l =>
        list_rec16P l x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14      
    end.

   Definition list_rec16 :=
     Eval cbv -[list_rec16P] in
       list_rec16F list_rec16P.
   
 End ListRec16.
 

 Definition block_to_list :=
   Eval compute in fix block_to_list l := block_list_foldrF cons nil block_to_list l.
 
 Definition to_list :=
   Eval cbv -[block_to_list] in plist_foldrF cons nil block_to_list.

 
 Definition of_list' :=
   Eval compute in
     fix list_rec16P l :=
     list_rec16FP (fold_right pconsK id) pnil list_rec16P l.
 
 Definition of_list :=
   Eval cbv -[of_list'] in list_rec16F (fold_right pconsK id) pnil of_list'.

 
(*TODO:
 Lemma block_of_list_to_list b
   : of_list (block_list_foldr cons [] b) = phd0 b.
 Proof.
   induction b;
     basic_goal_prep; auto.
   rewrite IHb.
   cbv.
   congruence.
 Qed.
 
 Lemma of_list_to_list l : of_list (to_list l) = l.
 Proof.
   destruct l;
     basic_goal_prep; rewrite ?block_of_list_to_list;
     auto.
 Qed.

 
 Lemma cons_pcons a l : cons a (to_list l) = to_list (pcons a l).
 Proof.
   revert a.
   induction l;
     basic_goal_prep; basic_utils_crush.
 Qed.

 Lemma pcons_cons a l : pcons a (of_list l) = of_list (cons a l).
 Proof.
   rewrite <- of_list_to_list with (l:=pcons _ _).
   rewrite <- cons_pcons.
   cbn.
   rewrite of_list_to_list.
   reflexivity.
 Qed.

 Lemma to_list_of_list l : to_list (of_list l) = l.
 Proof.   
   remember (length l) as n.
   assert (length l <= n) as Hlt by Lia.lia.
   clear Heqn.
   revert l Hlt.
   induction n.
   1: destruct l; basic_goal_prep; basic_utils_crush; Lia.lia.
   do 16 (destruct l as [|? l ]; [basic_utils_crush|]).
   cbn.
   rewrite <- !cons_pcons.
   basic_goal_prep.
   repeat f_equal.
   apply IHn.
   Lia.lia.
 Qed.

 *)
 
 (*
 Definition plist_eta {B} (f : plist -> B) :=
   plist_foldr (fun l => f (of_list l))
  *)

 
 Definition block_pcons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 :=
   Eval compute in
     fold_right pconsK id [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14].

 (* Not computed. Should it be? Not much benefit
    TODO: can I use block_list_foldrF?
  *)
 Fixpoint block_list_app (bl : block_list) (pl : plist) :=
   match bl with
   | blist_base x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
       block_pcons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 pl
   | blist_cons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 bl' =>
       block_pcons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
         (block_list_app bl' pl)
   end.

 
 Definition papp (l : plist) : plist -> plist :=
   Eval cbv -[block_list_app] in
     plist_foldrF pconsK id block_list_app l.

 (*TODO: could probably implement repeat faster*)
 
 Fixpoint block_repeat' n (x:A) acc :=
   match n with
   | 0 => acc
   | S n => block_repeat' n x (blist_cons x x x x x x x x x x x x x x x x acc)
   end.

 (*
   TODO: can significantly speed up
   TODO: wrong
  *)
 Definition prepeat (x:A) n :=
   let (blocks,hd_len_minus) := Nat.divmod n 15 0 15 in
   let hd_len := 15 - hd_len_minus in
   match blocks with
   | 0 =>
   (*TODO: compute, assuming hd_len <=15*)
       Nat.iter hd_len (pcons x) pnil
   | S blocks_minus_1 =>
       let base := blist_base x x x x x x x x x x x x x x x x in
       Nat.iter hd_len (pcons x) (phd0 (block_repeat' blocks_minus_1 x base))
   end.
       
End __.

Arguments block_list : clear implicits.
Arguments plist : clear implicits.
#[export] Hint Constructors block_list plist : utils.

Section __.
  Context {A B} (f : A -> B).

  (* TODO: is there a way to generate this? *)
  Fixpoint block_map (bl : block_list A) :=
    match bl with
    | blist_base x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
        blist_base (f x) (f x0) (f x1) (f x2) (f x3) (f x4) (f x5) (f x6)
          (f x7) (f x8) (f x9) (f x10) (f x11) (f x12) (f x13) (f x14)
    | blist_cons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 bl' =>
        blist_cons (f x) (f x0) (f x1) (f x2) (f x3) (f x4) (f x5) (f x6)
          (f x7) (f x8) (f x9) (f x10) (f x11) (f x12) (f x13) (f x14)
          (block_map bl')
    end.
  
  Definition pmap (l : plist A) : plist B :=
    Eval cbv -[block_map] in
      plist_foldrF (fun a => pcons (f a)) pnil (fun b => phd0 (block_map b)) l.
End __.

(*
(* Tests *)
Goal False.
  (*regular list-of-small-lists instantiation*)
  Time Let l_small := Eval vm_compute in
      (let l1 := repeat 0 10 in repeat l1 20000).
  (* 0.9 s *)
  (* list-of-small-packed-lists instantiation*)
  Time Let pl_small := Eval vm_compute in
      (let l1 := prepeat 0 10 in repeat l1 20000).
  (* 0.366 s *)
  (* list-of-small-packed-lists instantiation*)
  Time Let pl_pl_small := Eval vm_compute in
      (let l1 := prepeat 0 10 in prepeat l1 20000).
  (* 0.288 s *)
  time let _ := eval vm_compute in
       (map (map S) l_small)
         in
         idtac.
  (* 0.407 s *)
  time let _ := eval vm_compute in
       (map (pmap S) pl_small)
         in
         idtac.
  (* 0.263 s *)
  time let _ := eval vm_compute in
       (pmap (pmap S) pl_pl_small)
         in
         idtac.
  (* 0.214 s *)
  
  (*regular list-of-large-lists instantiation*)
  Time Let l_large := Eval vm_compute in
      (let l1 := repeat 0 1000 in repeat l1 1000).
  (* 3.278 s *)
  (* list-of-large-packed-lists instantiation*)
  Time Let pl_large := Eval vm_compute in
      (let l1 := prepeat 0 1000 in repeat l1 1000).
  (* 1.205 s *)
  (* list-of-large-packed-lists instantiation*)
  Time Let pl_pl_large := Eval vm_compute in
      (let l1 := prepeat 0 1000 in prepeat l1 1000).
  (* 1.225 s *)
  time let _ := eval vm_compute in
       (map (map S) l_large)
         in
         idtac.
  (* 1.632 s *)
  time let _ := eval vm_compute in
       (map (pmap S) pl_large)
         in
         idtac.
  (* 0.906 s *)
  time let _ := eval vm_compute in
       (pmap (pmap S) pl_pl_large)
         in
         idtac.
  (* 0.95 s *)

(*
  Timing conclusions:
  Using plist instead of list can expect to execute the list-processing
  parts 1.5-2x faster when the data in the list is small.
 *)
Abort.
*)
