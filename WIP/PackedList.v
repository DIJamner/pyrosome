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
    Fixpoint block_list_foldr' l :=
      match l with
      | blist_base x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
          fold_right f base
            [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
      | blist_cons x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l' =>
          fold_right f (block_list_foldr' l')
            [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14] 
      end.
    Definition block_list_foldr :=
      Eval compute in block_list_foldr'.

    Definition plist_foldr' (l:plist) :=
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
        
    Definition plist_foldr :=
      Eval cbv -[block_list_foldr] in plist_foldr'.
        
  End __.
  
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

 (*TODO: is it worth computing these?
   For now, no: these should not be assumed to be optimally effficient
  *)
 Definition to_list := plist_foldr cons nil.
 (* computed definition not optimal *)
 Definition of_list := fold_right pcons pnil.

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

 (*
 Definition plist_eta {B} (f : plist -> B) :=
   plist_foldr (fun l => f (of_list l))
  *)
 
 Definition papp (l1 l2 : plist) :=
   plist_foldr pcons l2 l1.
 Compute papp. (*TODO: nests matches wrong, sim. to to_list. How to fix? eta?*)
  
  Variant frame : Type :=
  | frame1 : A -> frame
  | frame2 : A -> A -> frame
  | frame3 : A -> A -> A -> frame
  | frame4 : A -> A -> A -> A ->
             frame
  | frame5 : A -> A -> A -> A ->
             A ->
             frame
  | frame6 : A -> A -> A -> A ->
             A -> A ->
             frame
  | frame7 : A -> A -> A -> A ->
             A -> A -> A ->
             frame
  | frame8 : A -> A -> A -> A ->
             A -> A -> A -> A ->
             frame
  | frame9 : A -> A -> A -> A ->
             A -> A -> A -> A ->
             A ->
             frame
  | frame10 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A ->
              frame
  | frame11 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A ->
              frame
  | frame12 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              frame
  | frame13 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              A ->
              frame
  | frame14 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A ->
              frame
  | frame15 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A ->
              frame
 (* (* TODO: do I want this *)
  | frame16 : A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              A -> A -> A -> A ->
              frame. *).
  Hint Constructors frame : utils.

  Definition cons_frame : Type := ntuple (A:=A) 16.
  
  Definition frame_to_ne_list (f:frame) : A * list A :=
    match f with
    | frame1 x => (x,[])
    | frame2 x x0 => (x,[x0])
    | frame3 x x0 x1 => (x,[x0; x1])
    | frame4 x x0 x1 x2 => (x,[x0; x1; x2])
    | frame5 x x0 x1 x2 x3 => (x,[x0; x1; x2; x3])
    | frame6 x x0 x1 x2 x3 x4 => (x,[x0; x1; x2; x3; x4])
    | frame7 x x0 x1 x2 x3 x4 x5 => (x,[x0; x1; x2; x3; x4; x5])
    | frame8 x x0 x1 x2 x3 x4 x5 x6 => (x,[x0; x1; x2; x3; x4; x5; x6])
    | frame9 x x0 x1 x2 x3 x4 x5 x6 x7 => (x,[x0; x1; x2; x3; x4; x5; x6; x7])
    | frame10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
        (x,[x0; x1; x2; x3; x4; x5; x6; x7; x8])
    | frame11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
        (x,[x0; x1; x2; x3; x4; x5; x6; x7; x8; x9])
    | frame12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
        (x,[x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10])
    | frame13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
        (x,[x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11])
    | frame14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => 
        (x,[x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12])
    | frame15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
        (x,[x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13])
    (*
    | frame16 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
        (x,[x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14])*)
    end.

  Definition ne_to_list {A} := uncurry (A:=A) cons.
  (* TODO: uniform inheritance warking
  Local Coercion ne_to_list : prod >-> list.
   *)

  Definition split_frame_of_list l : option (frame + (cons_frame * list A)) :=
    match l with
    | [] => None
    | [x] => Some (inl (frame1 x))
    | [x; x0] => Some (inl (frame2 x x0))
    | [x; x0; x1] => Some (inl (frame3 x x0 x1))
    | [x; x0; x1; x2] => Some (inl (frame4 x x0 x1 x2))
    | [x; x0; x1; x2; x3] => Some (inl (frame5 x x0 x1 x2 x3))
    | [x; x0; x1; x2; x3; x4] => Some (inl (frame6 x x0 x1 x2 x3 x4))
    | [x; x0; x1; x2; x3; x4; x5] => Some (inl (frame7 x x0 x1 x2 x3 x4 x5))
    | [x; x0; x1; x2; x3; x4; x5; x6] => Some (inl (frame8 x x0 x1 x2 x3 x4 x5 x6))
    | [x; x0; x1; x2; x3; x4; x5; x6; x7] => Some (inl (frame9 x x0 x1 x2 x3 x4 x5 x6 x7))
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] =>
        Some (inl (frame10 x x0 x1 x2 x3 x4 x5 x6 x7 x8))
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] =>
        Some (inl (frame11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9))
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] =>
        Some (inl (frame12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] =>
        Some (inl (frame13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11))
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] =>
        Some (inl (frame14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] =>
        Some (inl (frame15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))
    | x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l =>
        Some (inr ((tt, x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14), l))
    end.

  
  (* Note: only well-defined if |l| <=16*)
  Definition split_frame_of_ne_list '(x,l) : frame + (cons_frame * list A) :=
    match l with
    | [] => inl (frame1 x)
    | [x0] => inl (frame2 x x0)
    | [x0; x1] => inl (frame3 x x0 x1)
    | [x0; x1; x2] => inl (frame4 x x0 x1 x2)
    | [x0; x1; x2; x3] => inl (frame5 x x0 x1 x2 x3)
    | [x0; x1; x2; x3; x4] => inl (frame6 x x0 x1 x2 x3 x4)
    | [x0; x1; x2; x3; x4; x5] => inl (frame7 x x0 x1 x2 x3 x4 x5)
    | [x0; x1; x2; x3; x4; x5; x6] => inl (frame8 x x0 x1 x2 x3 x4 x5 x6)
    | [x0; x1; x2; x3; x4; x5; x6; x7] => inl (frame9 x x0 x1 x2 x3 x4 x5 x6 x7)
    | [x0; x1; x2; x3; x4; x5; x6; x7; x8] =>
        inl (frame10 x x0 x1 x2 x3 x4 x5 x6 x7 x8)
    | [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] =>
        inl (frame11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    | [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] =>
        inl (frame12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    | [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] =>
        inl (frame13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    | [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] =>
        inl (frame14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    | [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] =>
        inl (frame15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    | x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l =>
        inr ((tt, x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14), l)
    end.

  Fixpoint prepeat (x : A) (n : nat) {struct n} : plist :=
    match n with
    | 0  =>    pnil
    | 1  =>  tuple1 x
    | 2  =>  tuple2 x x
    | 3  =>  tuple3 x x x
    | 4  =>  tuple4 x x x x
    | 5  =>  tuple5 x x x x x
    | 6  =>  tuple6 x x x x x x
    | 7  =>  tuple7 x x x x x x x
    | 8  =>  tuple8 x x x x x x x x
    | 9  =>  tuple9 x x x x x x x x x
    | 10 => tuple10 x x x x x x x x x x
    | 11 => tuple11 x x x x x x x x x x x
    | 12 => tuple12 x x x x x x x x x x x x
    | 13 => tuple13 x x x x x x x x x x x x x
    | 14 => tuple14 x x x x x x x x x x x x x x
    | 15 => tuple15 x x x x x x x x x x x x x x x
    | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n))))))))))))))) =>
        pcons' x x x x x x x x x x x x x x x x (prepeat x n)
    end.

  Definition split_frame (l : plist) : option (frame + (cons_frame * plist)) :=
    match l with
    | pnil => None
    | tuple1 x => Some (inl (frame1 x))
    | tuple2 x x0 => Some (inl (frame2 x x0))
    | tuple3 x x0 x1 => Some (inl (frame3 x x0 x1))
    | tuple4 x x0 x1 x2 => Some (inl (frame4 x x0 x1 x2))
    | tuple5 x x0 x1 x2 x3 => Some (inl (frame5 x x0 x1 x2 x3))
    | tuple6 x x0 x1 x2 x3 x4 =>
        Some (inl (frame6 x x0 x1 x2 x3 x4))
    | tuple7 x x0 x1 x2 x3 x4 x5 =>
        Some (inl (frame7 x x0 x1 x2 x3 x4 x5))
    | tuple8 x x0 x1 x2 x3 x4 x5 x6 =>
        Some (inl (frame8 x x0 x1 x2 x3 x4 x5 x6)) 
    | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 =>
        Some (inl (frame9 x x0 x1 x2 x3 x4 x5 x6 x7))
    | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
        Some (inl (frame10 x x0 x1 x2 x3 x4 x5 x6 x7 x8))
    | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
        Some (inl (frame11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)) 
    | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
        Some (inl (frame12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) 
    | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
        Some (inl (frame13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)) 
    | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => 
        Some (inl (frame14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)) 
    | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
        Some (inl (frame15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)) 
    | pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l =>
        Some (inr ((tt, x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14), l))
    end.

  Definition frame_add' (f1 f2 : frame) : (option cons_frame * frame) :=
    let (a,l1) := frame_to_ne_list f1 in
    let l2 := l1 ++ ne_to_list (frame_to_ne_list f2) in
    match split_frame_of_ne_list (a,l2) with
    | inl f => (None,f)
    | inr (cf,l) =>
        match split_frame_of_list l with
        | Some (inl f') => (Some cf, f')
        | inr _ => (*never happens*) (None, f1)
        end
    end.

    
  Definition frame_eta {B} (f:frame -> B) (fr:frame) : B :=
    match fr with
    | frame1 x => f (frame1 x)
    | frame2 x x0 => f (frame2 x x0)
    | frame3 x x0 x1 => f (frame3 x x0 x1)
    | frame4 x x0 x1 x2 => f (frame4 x x0 x1 x2)
    | frame5 x x0 x1 x2 x3 => f (frame5 x x0 x1 x2 x3)
    | frame6 x x0 x1 x2 x3 x4 => f (frame6 x x0 x1 x2 x3 x4)
    | frame7 x x0 x1 x2 x3 x4 x5 => f (frame7 x x0 x1 x2 x3 x4 x5)
    | frame8 x x0 x1 x2 x3 x4 x5 x6 => f (frame8 x x0 x1 x2 x3 x4 x5 x6)
    | frame9 x x0 x1 x2 x3 x4 x5 x6 x7 => f (frame9 x x0 x1 x2 x3 x4 x5 x6 x7)
    | frame10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
        f (frame10 x x0 x1 x2 x3 x4 x5 x6 x7 x8)
    | frame11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
        f (frame11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    | frame12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
        f (frame12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    | frame13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
        f (frame13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    | frame14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => 
        f (frame14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    | frame15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
        f (frame15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    | frame16 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
        f (frame16 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
    end.
  
  Definition frame_add :=
    Eval compute in
      (frame_eta (fun f => frame_eta (frame_add' f))).
  
  (* O(n) *)
  Fixpoint pcons a (l : plist) {struct l} : plist :=
    match l with
    | pnil => tuple1 a
    | tuple1 x => tuple2 a x
    | tuple2 x x0 => tuple3 a x x0
    | tuple3 x x0 x1 => tuple4 a x x0 x1
    | tuple4 x x0 x1 x2 => tuple5 a x x0 x1 x2
    | tuple5 x x0 x1 x2 x3 => tuple6 a x x0 x1 x2 x3
    | tuple6 x x0 x1 x2 x3 x4 =>
        tuple7 a x x0 x1 x2 x3 x4
    | tuple7 x x0 x1 x2 x3 x4 x5 =>
        tuple8 a x x0 x1 x2 x3 x4 x5
    | tuple8 x x0 x1 x2 x3 x4 x5 x6 =>
        tuple9 a x x0 x1 x2 x3 x4 x5 x6 
    | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 =>
        tuple10 a x x0 x1 x2 x3 x4 x5 x6 x7 
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
        pcons' a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 pnil
    | pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l =>
        pcons' a x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (pcons x14 l)
    end.

  
  (*TODO: how to generalize to pcons? fold_left?*)
  Section __.
    Context {B}
      (base : B)
      (rec : list A -> B -> B).
    Fixpoint prec (l:plist) : B :=
      match l with
      | pnil => base
      | tuple1 x => rec [x] base
      | tuple2 x x0 => rec [x; x0] base
      | tuple3 x x0 x1 => rec [x; x0; x1] base
      | tuple4 x x0 x1 x2 => rec [x; x0; x1; x2] base
      | tuple5 x x0 x1 x2 x3 => rec [x; x0; x1; x2; x3] base
      | tuple6 x x0 x1 x2 x3 x4 => rec [x; x0; x1; x2; x3; x4] base
      | tuple7 x x0 x1 x2 x3 x4 x5 => rec [x; x0; x1; x2; x3; x4; x5] base
      | tuple8 x x0 x1 x2 x3 x4 x5 x6 => rec [x; x0; x1; x2; x3; x4; x5; x6] base
      | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 => rec [x; x0; x1; x2; x3; x4; x5; x6; x7] base
      | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
          rec [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] base
      | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
          rec [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] base
      | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
          rec [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] base
      | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
          rec [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11]  base
      | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => 
          rec [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12]  base
      | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
          rec [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] base
      | pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l =>
          rec [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14] (prec l)
      end.
  End __.

  Definition to_list :=
    Eval compute in
      prec [] (app (A:=_)).

  (*
  Fixpoint to_list (l:plist) : list A :=
    match l with
    | pnil => []
    | tuple1 x => [x]
    | tuple2 x x0 => [x; x0]
    | tuple3 x x0 x1 => [x; x0; x1]
    | tuple4 x x0 x1 x2 => [x; x0; x1; x2]
    | tuple5 x x0 x1 x2 x3 => [x; x0; x1; x2; x3]
    | tuple6 x x0 x1 x2 x3 x4 => [x; x0; x1; x2; x3; x4]
    | tuple7 x x0 x1 x2 x3 x4 x5 => [x; x0; x1; x2; x3; x4; x5]
    | tuple8 x x0 x1 x2 x3 x4 x5 x6 => [x; x0; x1; x2; x3; x4; x5; x6]
    | tuple9 x x0 x1 x2 x3 x4 x5 x6 x7 => [x; x0; x1; x2; x3; x4; x5; x6; x7]
    | tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8 =>
        [x; x0; x1; x2; x3; x4; x5; x6; x7; x8]
    | tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
        [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9]
    | tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =>
        [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10]
    | tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =>
        [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] 
    | tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => 
        [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] 
    | tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =>
        [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13]
    | pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l =>
        x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::(to_list l)
    end.
   *)
  
  Fixpoint of_list (l : list A) : plist :=
    match l with
    | [] => pnil
    | [x] => tuple1 x
    | [x; x0] => tuple2 x x0
    | [x; x0; x1] => tuple3 x x0 x1
    | [x; x0; x1; x2] => tuple4 x x0 x1 x2 
    | [x; x0; x1; x2; x3] => tuple5 x x0 x1 x2 x3
    | [x; x0; x1; x2; x3; x4] => tuple6 x x0 x1 x2 x3 x4
    | [x; x0; x1; x2; x3; x4; x5] => tuple7 x x0 x1 x2 x3 x4 x5
    | [x; x0; x1; x2; x3; x4; x5; x6] => tuple8 x x0 x1 x2 x3 x4 x5 x6
    | [x; x0; x1; x2; x3; x4; x5; x6; x7] => tuple9 x x0 x1 x2 x3 x4 x5 x6 x7
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] =>
        tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] =>
        tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] =>
        tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] =>
        tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] =>
        tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] =>
        tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 
    | x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l =>
        pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (of_list l)
    end.

  Lemma of_list_to_list l : of_list (to_list l) = l.
  Proof.
    induction l;
      basic_goal_prep; auto.
    congruence.
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
    basic_goal_prep.
    repeat f_equal.
    apply IHn.
    Lia.lia.
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
    rewrite to_list_of_list.
    reflexivity.
  Qed.
  
  Section __.
    Context {B} (f : A -> B -> B).
    Definition pfold_right acc :=
    Eval compute in
        prec acc (fun pre acc => fold_right f acc pre).
  End __.

  
  Definition frame_to_plist :=
    Eval compute in
      (frame_eta (fun f => of_list (ne_to_list (frame_to_ne_list f)))).

  
  Fixpoint frame_pcons f l :=
    match split_frame l with
    | None => frame_to_plist f
    | Some (f', l') =>
        let (a,fl) := frame_to_ne_list f in
        let f'l := frame_to_list f' in
        let (f3,l3) := split_frame_of_ne_list (a,fl++f'l) in
        match split_frame_of_list l3 with
        | 
        
    let 
  
  Definition frame_pcons :=
    Eval compute in
      fix frame_pcons f l :=
      match split_frame l with
      | None => frame_to_plist f
      | Some (f', l') =>
          ...
      let (a,l1) := frame_to_ne_list f1 in
    let l2 := l1 ++ ne_to_list (frame_to_ne_list f2) in
    let (f1,l3) := split_frame_of_ne_list (a,l2) in
    (f1, option_map fst (split_frame_of_list l3)).
          
          Fixpoint frame_pcons f l :=
            match split_frame l with
            | None => frame_to_plist f
            | Some (f', l') =>
                let (f1,f2) := add_frame f f' in
                let fo := (*TODO: turn f into pcons'*) in
                fo::(frame_pcons f2 l')
                  issue: what if f' < 15
  
  (*
  Fixpoint frame_of_list (l : list A) : option frame :=
    match l with
    | [] => None
    | [x] => frame1 x
    | [x; x0] => frame2 x x0
    | [x; x0; x1] => frame3 x x0 x1
    | [x; x0; x1; x2] => frame4 x x0 x1 x2 
    | [x; x0; x1; x2; x3] => frame5 x x0 x1 x2 x3
    | [x; x0; x1; x2; x3; x4] => frame6 x x0 x1 x2 x3 x4
    | [x; x0; x1; x2; x3; x4; x5] => frame7 x x0 x1 x2 x3 x4 x5
    | [x; x0; x1; x2; x3; x4; x5; x6] => frame8 x x0 x1 x2 x3 x4 x5 x6
    | [x; x0; x1; x2; x3; x4; x5; x6; x7] => frame9 x x0 x1 x2 x3 x4 x5 x6 x7
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] =>
        frame10 x x0 x1 x2 x3 x4 x5 x6 x7 x8
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] =>
        frame11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] =>
        frame12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] =>
        frame13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] =>
        frame14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] =>
        frame15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 
    | x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l =>
        pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (of_list l)
    end.
   *)
  
  
  Lemma cons15_to_list x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 l
    : x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l
      = to_list (pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (of_list l)).
  Proof.
    rewrite <- to_list_of_list with (l:=l).
    cbn.
    rewrite !to_list_of_list.
    reflexivity.
  Qed.

  (*
  Require Import Derive.
  Derive frame_cons
    SuchThat (forall (f:frame) (l : plist),
                 to_list (frame_cons f l) = frame_to_list f ++ to_list l)
    As frame_cons_spec.
  Proof.
    Unshelve.
    2:{
      refine (fix frame_cons f l : plist := _).
      destruct f, l.
      all:shelve.
    }
    compute in frame_cons.
    destruct f,l;
      basic_goal_prep.
    all: lazymatch goal with
         | l : plist |- _ => idtac
         | |- _ = ?lst =>
             rewrite <- to_list_of_list with (l:=lst);
             apply f_equal
         end.
    all: cbn[of_list].
    all: try reflexivity.
    all: rewrite cons15_to_list with (x:=a).
    all: apply f_equal.
    all: apply f_equal.
    all: instantiate(1:= frame_cons _ _).
    TODO: need induction l
          *)

  (*
  (* TODO: how to abstract out this match? *)
  Definition list_cons l pl :=
    match l with
    | [] => pl
    | [x] => tuple1 x
    | [x; x0] => tuple2 x x0
    | [x; x0; x1] => tuple3 x x0 x1
    | [x; x0; x1; x2] => tuple4 x x0 x1 x2 
    | [x; x0; x1; x2; x3] => tuple5 x x0 x1 x2 x3
    | [x; x0; x1; x2; x3; x4] => tuple6 x x0 x1 x2 x3 x4
    | [x; x0; x1; x2; x3; x4; x5] => tuple7 x x0 x1 x2 x3 x4 x5
    | [x; x0; x1; x2; x3; x4; x5; x6] => tuple8 x x0 x1 x2 x3 x4 x5 x6
    | [x; x0; x1; x2; x3; x4; x5; x6; x7] => tuple9 x x0 x1 x2 x3 x4 x5 x6 x7
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8] =>
        tuple10 x x0 x1 x2 x3 x4 x5 x6 x7 x8
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] =>
        tuple11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10] =>
        tuple12 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11] =>
        tuple13 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12] =>
        tuple14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 
    | [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13] =>
        tuple15 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 
    | x::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::l =>
        pcons' x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (of_list l)
    end.
    
  
  Definition papp (l m : plist) :=
    Eval compute in
      prec m list_cons l.
  
  (* O(nm) *)
  Fixpoint papp (l m : plist) {struct l} : plist :=
    match l with
    | pnil => m
    | (a :: l1)%list => (a :: app l1 m)%list
    end.
*)

End __.

Arguments plist : clear implicits.
#[export] Hint Constructors frame plist : utils.

Section __.
  Context {A B} (f : A -> B).

  Definition pmap (l : plist A) : plist B :=
    (*TODO: need frame cons/papp. Question:
      is there a way to spec things using n-tuples
      to reduce duplication?
     *)
    Eval compute in
        prec pnil (fun pre acc => (map f pre) ++ acc).
    match l with
    | pnil => pnil
    | tuple1 x => tuple1 (f x)
    | tuple2 x x0 => tuple2 (f x) (f x0)
    | tuple3 x x0 x1 => tuple3 (f x) (f x0) (f x1)
    | tuple4 x x0 x1 x2 => tuple4 (f x) (f x0) (f x1) (f x2)
    | tuple5 x x0 x1 x2 x3 => tuple5 (f x) (f x0) (f x1) (f x2) (f x3)
    | tuple6 x x0 x1 x2 x3 x4 => tuple6 (f x) (f x0) (f x1) (f x2) (f x3) (f x4)
    | pcons' x x0 x1 x2 x3 x4 x5 x6 =>
        pcons' (f x) (f x0) (f x1) (f x2) (f x3) (f x4) (f x5) (pmap x6)
    | _ => pnil
    end.
End __.
