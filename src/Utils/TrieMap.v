Require Import ZArith.
Require Import coqutil.Map.Interface.
Require Import Tries.Canonical.
Import PTree.

Require Utils.ArrayList.
From Utils Require Import Base ExtraMaps Default.

(* TODO: move this somewhere? *)
(*reverses the bits in a positive number*)
Fixpoint pos_rev' p acc :=
  match p with
  | xH => acc
  | xO p => pos_rev' p (xO acc)
  | xI p => pos_rev' p (xI acc)
  end.
Definition pos_rev p := pos_rev' p xH.

Section Folds.
  Context {B A : Type}.

  Section __.
    Context (f : A -> positive -> B -> A).
    
    (* positives consed when they should be appended

    TODO: to make folds more efficient at the cost of space,
    can just include each key at the leaf.
    To do so: implement map.map positive v for PTree.tree (positive*v)?
     *)
    Fixpoint trie_fold' (acc : A) (m : PTree.tree' B)
      (*TODO: find a better way?*)
      (revnum : positive) : A :=
      match m with
      | Node001 r => trie_fold' acc r (xI revnum)
      | Node010 y => f acc (pos_rev revnum) y
      | Node011 y r =>
          let acc := f acc (pos_rev revnum) y in
          trie_fold' acc r (xI revnum)
      | Node100 l => trie_fold' acc l (xO revnum)
      | Node101 l r =>      
          let acc := trie_fold' acc r (xI revnum) in
          trie_fold' acc l (xO revnum)
      | Node110 l y => 
          let acc := f acc (pos_rev revnum) y in
          trie_fold' acc l (xO revnum)
      | Node111 l y r =>
          let acc := f acc (pos_rev revnum) y in
          let acc := trie_fold' acc r (xI revnum) in
          trie_fold' acc l (xO revnum)
      end.


    Definition trie_fold (acc : A) (m : PTree.t B) : A :=
      match m with
      | Empty => acc
      | Nodes m' => trie_fold' acc m' xH
      end.

  End __.
  

  Section __.
    Context (f : B -> A -> A).

    (* A fold over just the values, avoids the issues of rebuilding the keys *)
    Fixpoint map_fold_values' (m : PTree.tree' B) (acc : A) :=
      match m with
      | Node001 r => map_fold_values' r acc
      | Node010 y => f y acc
      | Node011 y r =>
          let acc := f y acc in
          map_fold_values' r acc
      | Node100 l => map_fold_values' l acc
      | Node101 l r =>      
          let acc := map_fold_values' r acc in
          map_fold_values' l acc
      | Node110 l y => 
          let acc := f y acc in
          map_fold_values' l acc
      | Node111 l y r =>
          let acc := f y acc in
          let acc := map_fold_values' r acc in
          map_fold_values' l acc
      end.
                                                               
    Definition map_fold_values (m : PTree.tree B) (acc : A) : A :=
      match m with
      | Empty => acc
      | Nodes m' => map_fold_values' m' acc
      end.
  End __.

End Folds.

Section __.

  
  Context (value : Type).

  Definition trie_map : map.map positive value :=
    {|
      map.rep := PTree.t value;
      map.empty := PTree.empty value;
      map.get m k := PTree.get k m;
      map.put m k v := PTree.set k v m;
      map.remove m k := PTree.remove k m;
      map.fold := @trie_fold value;
    |}.

  (* TODO: prove map.ok *)
  #[export] Instance trie_map_ok : map.ok trie_map.
  Proof.
    constructor; basic_goal_prep.
    { eapply extensionality; eauto. }
    { reflexivity. }
    { eapply gss. }
    { eapply gso; eauto. }
    { eapply grs; eauto. }
    { eapply gro; eauto. }
    {
      revert m.
      eapply tree_ind;
        basic_goal_prep;
        basic_utils_crush.
      destruct l, o, r;
        basic_goal_prep; try tauto.
  Abort.
  
End __.

(* Binary intersection. To intersect ntrees t1...tm in time min(|ti|) instead of min(|t1|,|t2|)
     use ntree_intersect_list instead.
 *)
Section MapIntersect.
  Context {A B C} (elt_intersect : A -> B -> C).

  Import Canonical.PTree.
  Arguments empty {A}%type_scope.
                                            
  Fixpoint intersect' m1 m2 : tree _ :=
    match m1, m2 with
    (* just an element*)                                            
    | Node010 a, Node010 b
    | Node010 a, Node011 b _
    | Node010 a, Node110 _ b
    | Node010 a, Node111 _ b _                                            
    | Node011 a _, Node010 b                                            
    | Node110 _ a, Node010 b                                            
    | Node111 _ a _, Node010 b                                       
    | Node110 _ a, Node011 b _                                       
    | Node011 a _, Node110 _ b => Node empty (Some (elt_intersect a b)) empty
                                                  
    (* RHS only in result*)
    | Node001 r1, Node001 r2
    | Node001 r1, Node011 _ r2
    | Node001 r1, Node101 _ r2
    | Node001 r1, Node111 _ _ r2
    | Node011 _ r1, Node001 r2
    | Node101 _ r1, Node001 r2
    | Node111 _ _ r1, Node001 r2
    | Node011 _ r1, Node101 _ r2
    | Node101 _ r1, Node011 _ r2 => Node empty None (intersect' r1 r2)
                                            
    (* LHS only in result*)
    | Node100 l1, Node100 l2
    | Node100 l1, Node110 l2 _
    | Node100 l1, Node101 l2 _
    | Node100 l1, Node111 l2 _ _
    | Node110 l1 _, Node100 l2
    | Node101 l1 _, Node100 l2
    | Node111 l1 _ _, Node100 l2
    | Node110 l1 _, Node101 l2 _
    | Node101 l1 _, Node110 l2 _ => Node (intersect' l1 l2) None empty

    (* RHS + element *)
    | Node011 a r1, Node011 b r2
    | Node011 a r1, Node111 _ b r2
    | Node111 _ a r1, Node011 b r2 => Node empty (Some (elt_intersect a b)) (intersect' r1 r2)
                                                
    (* LHS + element *)
    | Node110 l1 a, Node110 l2 b
    | Node110 l1 a, Node111 l2 b _
    | Node111 l1 a _, Node110 l2 b => Node (intersect' l1 l2) (Some (elt_intersect a b)) empty

    (* everything *)
    | Node111 l1 a r1, Node111 l2 b r2 => Node (intersect' l1 l2) (Some (elt_intersect a b)) (intersect' r1 r2)
     
    (* No overlap *)
    | _, _ => empty
    end.

  Definition intersect m1 m2 :=
    match m1, m2 with
    | Empty, _
    | _, Empty => empty
    | Nodes m1', Nodes m2' => intersect' m1' m2'
    end.
End MapIntersect.

(* Designed to avoid as much work as possible by short-circuiting.
   Assumes that (elt_intersect _ x) commutes
 *)
Section MapIntersectList.
  Context {B} (elt_intersect : B -> B -> B).

  Import Lists.List.
  Import Canonical.PTree List.ListNotations.
  Arguments empty {A}%type_scope.

  (* Accumulators allow short-circuiting.
     We define separate functions to encode what branches to short-circuit
     in the instruction pointer.
   *)


  (*TODO: is there a way to generalize all of these fns and only write once?*)

  Section __.
    Context (D E F : Type).
  
  Definition i_type' lb cb rb : Type :=
    match lb, cb, rb with
    | false, false, false => unit
    | true, false, false => D
    | false, false, true => F
    | false, true, false => E
    | true, false, true => D * F
    | true, true, false => D * E
    | false, true, true => E * F
    | true, true, true => D * E * F
    end.

  
  Definition mk_i lb cb rb l1 l2 l3 : i_type' lb cb rb :=
    match lb, cb, rb with
    | false, false, false => tt
    | true, false, false => l1
    | false, false, true => l3
    | false, true, false => l2
    | true, false, true => (l1,l3)
    | true, true, false => (l1,l2)
    | false, true, true => (l2,l3)
    | true, true, true => (l1,l2,l3)
    end.
  
  Definition open_i lb cb rb : i_type' lb cb rb -> option _ * option _ * option _ :=
    match lb, cb, rb with
    | false, false, false => fun i => (None, None,None)
    | true, false, false => fun i => (Some i, None,None)
    | false, false, true => fun i => (None, None, Some i)
    | false, true, false => fun i => (None, Some i, None)
    | true, false, true => fun i => (Some (fst i), None, Some (snd i))
    | true, true, false => fun i => (Some (fst i), Some (snd i), None)
    | false, true, true => fun i => (None, Some (fst i), Some (snd i))
    | true, true, true => fun i => (Some (fst (fst i)), Some (snd (fst i)), Some (snd i))
    end.

  Definition ieta lb cb rb {R} lb' cb' rb'
    : (i_type' lb cb rb -> forall a b c : bool, R a b c) -> i_type' lb cb rb -> R lb' cb' rb' :=
    match lb, cb, rb with
    | false, false, false => fun k 'tt => k tt lb' cb' rb'
    | true, false, false => fun k i => k i lb' cb' rb'
    | false, false, true => fun k i => k i lb' cb' rb'
    | false, true, false => fun k i => k i lb' cb' rb'
    | true, false, true => fun k '(l,r) => k (l,r) lb' cb' rb'
    | true, true, false => fun k '(l,c) => k (l,c) lb' cb' rb'
    | false, true, true => fun k '(c,r) => k (c,r) lb' cb' rb'
    | true, true, true => fun k '(l,c,r) => k (l,c,r) lb' cb' rb'
    end.

  End __.
  
  Arguments open_i {D E F}%type_scope {lb cb rb}%bool_scope _.
  Arguments mk_i {D E F}%type_scope (lb cb rb)%bool_scope l1 l2 l3.
  Arguments ieta {D E F}%type_scope {lb cb rb}%bool_scope {R}%type_scope _ _ _
    _%function_scope _.

  Notation i_type := (i_type' (tree' B) B (tree' B)).
  Notation i_list_type := (i_type' (list (tree' B)) (list B) (list (tree' B))).

  Definition mcons {A} (h : option A) l :=
    match h, l with
    | Some h', Some l' => h'::l'
    | _, _ => []
    end.
  
  Open Scope bool.
  Definition i_cons {lb cb rb} (h:i_type lb cb rb)
    {lb' cb' rb'} (acc : i_list_type lb' cb' rb') : i_list_type (lb&&lb') (cb&&cb') (rb&&rb') :=
    let '(ml,mc,mr) := open_i acc in
    let '(mlh,mch,mrh) := open_i h in
    mk_i (lb&&lb') (cb&&cb') (rb&&rb')
      (mcons mlh ml) (mcons mch mc) (mcons mrh mr).

  Definition open_node' (n : tree' B) {R} (k : _ -> R) : R :=
    match n with
    | Node001 r => k (None, None, Some r)
    | Node010 c => k (None, Some c, None)
    | Node011 c r => k (None, Some c, Some r)
    | Node100 l => k (Some l, None, None)
    | Node101 l r => k (Some l, None, Some r)
    | Node110 l c => k (Some l, Some c, None)
    | Node111 l c r => k (Some l, Some c, Some r)
    end.

  Definition is_some {A} (o : option A) := if o then true else false.
  Local Coercion is_some : option >-> bool.

  
  Import Utils.Lists.
  (* Used to avoid dealing with type equations in code that will disappear after eval *)
  Definition icast {lb cb rb} (acc : i_list_type lb cb rb)
    {lb' cb' rb'} : i_list_type lb' cb' rb' :=
    let '(accl, accc, accr) := open_i acc in
    mk_i lb' cb' rb'
      (unwrap_with_default accl)
      (unwrap_with_default accc)
      (unwrap_with_default accr).

  Section __.

  (* TODO: should rec take in-params and out-params?*)
  Context (rec : forall {lb cb rb}, list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb).
  Arguments rec {lb cb rb}%bool_scope _%list_scope _.
  Definition i' lb cb rb tl (acc : i_list_type lb cb rb) : i_list_type lb cb rb :=
    match tl with
    | [] => acc
    | n::tl' =>
        let '(accl, accc, accr) := open_i acc in
        open_node' n
          (fun '(nl, nc, nr) =>
             let lb' := nl && lb in
             let cb' := nc&&cb in
             let rb' := nr&&rb in
        let acc' := mk_i lb' cb' rb'
                      (mcons nl accl) (mcons nc accc) (mcons nr accr) in
        (*short-circuit when possible *)
        (* use ieta to avoid duplication of recursive calls *)
        if lb' || cb' || rb' then (ieta _ _ _ icast (rec tl' acc'))
        else (*equivalent to tt*) mk_i lb cb rb [] [] [])
    end.
  End __.

  (* [i' open_i open_node' mcons mk_i orb andb is_some icast]*)
  Definition lefts := Eval cbv -[fst snd] in
      (fix lefts tl :=
         let rec lb cb rb : list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb  :=
           match lb, cb, rb with
           | true, false, false => lefts
           | lb', cb', rb' => fun _ _ => mk_i lb' cb' rb' [] [] []
           end in
         i' rec true false false tl).
  Definition rights := Eval cbv -[fst snd lefts] in
      (fix rights tl :=
         let rec lb cb rb : list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb  :=
           match lb, cb, rb with
           | false, false, true => rights
           | lb', cb', rb' => fun _ _ => mk_i lb' cb' rb' [] [] []
           end in
         i' rec false false true tl).
  Definition centers := Eval cbv -[fst snd lefts rights] in
      (fix centers tl :=
         let rec lb cb rb : list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb  :=
           match lb, cb, rb with
           | false, true, false => centers
           | lb', cb', rb' => fun _ _ => mk_i lb' cb' rb' [] [] []
           end in
         i' rec false true false tl).
  Definition sides :=
    Eval cbv -[lefts rights centers] in
      (fix sides tl :=
         let rec lb cb rb : list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb  :=
           match lb, cb, rb with
           | true, false, false => lefts
           | false, true, false => centers
           | false, false, true => rights
           | true, false, true => sides
           | lb', cb', rb' => fun _ _ => mk_i lb' cb' rb' [] [] []
           end in
         i' rec true false true tl).
  Definition lcs :=
    Eval cbv -[lefts rights centers] in
      (fix lcs tl :=
         let rec lb cb rb : list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb  :=
           match lb, cb, rb with
           | true, false, false => lefts
           | false, true, false => centers
           | false, false, true => rights
           | true, true, false => lcs
           | lb', cb', rb' => fun _ _ => mk_i lb' cb' rb' [] [] []
           end in
         i' rec true true false tl).
  Definition crs :=
    Eval cbv -[lefts rights centers] in
      (fix crs tl :=
         let rec lb cb rb : list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb  :=
           match lb, cb, rb with
           | true, false, false => lefts
           | false, true, false => centers
           | false, false, true => rights
           | false, true, true => crs
           | lb', cb', rb' => fun _ _ => mk_i lb' cb' rb' [] [] []
           end in
         i' rec false true true tl).
  Definition lcrs :=
    Eval cbv -[lefts rights centers lcs crs sides] in
      (fix lcrs tl :=
         let rec lb cb rb : list (tree' B) -> i_list_type lb cb rb -> i_list_type lb cb rb  :=
           match lb, cb, rb with
           | true, false, false => lefts
           | false, true, false => centers
           | false, false, true => rights
           | false, true, true => crs
           | true, false, true => sides
           | true, true, false => lcs
           | true, true, true => lcrs
           | lb', cb', rb' => fun _ _ => mk_i lb' cb' rb' [] [] []
           end in
         i' rec true true true tl).

  Definition elts_intersect c l :=
    Some (fold_left elt_intersect l c).
    
  (* Note: termination argument is tricky.
     Duplicate code for destruction of the head to make it structural.
     TODO: eval some calls to Node
   *)
  Fixpoint list_intersect' (hd : tree' B) (args : list (tree' B)) : tree B :=
    match hd with
    | Node001 r => 
        let rs := rights args [] in
        Node Empty None (list_intersect' r rs)
    | Node010 c =>
        let cs := centers args [] in
        Node Empty (elts_intersect c cs) Empty
    | Node011 c r => 
        let '(cs,rs) := crs args ([],[]) in
        Node Empty (elts_intersect c cs) (list_intersect' r rs)
    | Node100 l => 
        let ls := lefts args [] in
        Node (list_intersect' l ls) None Empty
    | Node101 l r => 
        let '(ls,rs) := sides args ([],[]) in
        Node (list_intersect' l ls) None (list_intersect' r rs)
    | Node110 l c => 
        let '(ls,cs) := lcs args ([],[]) in
        Node (list_intersect' l ls) (elts_intersect c cs) Empty
    | Node111 l c r => 
        let '(ls,cs,rs) := lcrs args ([],[],[]) in
        Node (list_intersect' l ls) (elts_intersect c cs) (list_intersect' r rs)
    end.

  Definition list_intersect'_cbv :=
    Eval cbv [list_intersect' Node] in list_intersect'.

  Fixpoint acc_tree'_list (l : list (tree B)) acc k : tree B :=
    match l with
    | [] => k acc
    | Empty::_ => Empty
    | Nodes t :: l' => acc_tree'_list l' (t::acc) k
    end.

  (* takes the first `hd` since the intersection of an empty list of trees isn't finitely defined.*)
  Definition list_intersect (hd : tree B) (tl : list (tree B)) : tree B :=
    match hd with
    | Empty => Empty
    | Nodes hd' => acc_tree'_list tl [] (list_intersect'_cbv hd')
    end.

  Context (elt_intersect_comm : forall a b, elt_intersect a b = elt_intersect b a).
  
  Lemma list_intersect'_nil
    : forall t0 : tree' B, Nodes t0 = list_intersect'_cbv t0 [].
  Proof.
    induction t0;
      basic_goal_prep;
      repeat match goal with
        | H : Nodes _ = _ |- _ =>
            rewrite <- ?H; clear H
        end;
      basic_utils_crush.
  Qed.

  Lemma fold_intersect_empty l
    : fold_left (intersect elt_intersect) l Empty = Empty.
  Proof.
    unfold intersect.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  #[local] Hint Rewrite fold_intersect_empty : utils.

  Definition i'_spec tl (acc : i_list_type true true true) : i_list_type true true true :=
    match tl with
    | [] => acc
    | n::tl' =>
        let '(accl, accc, accr) := acc in
        open_node' n
          (fun '(nl, nc, nr) => (mcons nl (Some accl), mcons nc (Some accc), mcons nr (Some accr)))
    end.
  
  Local Definition i'' m2 m1' :=
    match m2 with
    | Empty => empty
    | Nodes m2' => intersect' elt_intersect m1' m2'
    end.

  
  Lemma list_intersect'_cons_correct tl' hd a
    : list_intersect' hd (a::tl')
      = match intersect' elt_intersect hd a with
        | Empty => Empty
        | Nodes hd' => (list_intersect' hd' tl')
        end.
  Proof.
    revert a tl'.
    induction hd; basic_goal_prep.
    {
      destruct a.
(*
      
      Nodes (rights tl a::tl') ~ tl' `intersect` (map Node001 (a::tl')) 
    list_intersect' hd (rights tl tl') ~ fold intersect (map Node001 (hd::tl'))++tl
                               
      TODO: what to do with (rights ...)?
    unfold i''.
 *)
  Abort.

  Lemma list_intersect'_correct tl' hd
    :  fold_left i'' tl' (Nodes hd) = list_intersect'_cbv hd tl'.
  Proof.
    revert hd.
    unfold i''.
    induction tl';
      basic_goal_prep;
      basic_utils_crush.
    {
      eapply list_intersect'_nil.
    }
    (*rewrite <- IHtl'.
    *)
  Admitted.

   
  Lemma intersect_empty_r A (f : A -> A -> A) t
    : intersect f t Empty = Empty.
  Proof.
    destruct t; reflexivity.
  Qed.
  Hint Rewrite intersect_empty_r : utils.
    
  Lemma acc_tree'_list_helper tl tl' hd
    : List.fold_left (intersect elt_intersect) tl
        (List.fold_left i'' tl' (Nodes hd))
      = acc_tree'_list tl tl' (list_intersect'_cbv hd).
  Proof.
    revert tl' hd;
      induction tl;
      basic_goal_prep;
      eauto using list_intersect'_correct.
    destruct a;
      basic_goal_prep;
      basic_utils_crush.
    rewrite <- IHtl.
    f_equal.
    cbn.
    admit (*comm*).
  Admitted.
  
  Lemma list_intersect_correct hd l
    : List.fold_left (intersect elt_intersect) l hd = list_intersect hd l.
  Proof.
    destruct hd;
      basic_goal_prep;
      basic_utils_crush.
    revert t0.
    induction l; [eapply list_intersect'_nil|].

    basic_goal_prep;
      destruct a.
    1:basic_utils_crush.
    replace (intersect' elt_intersect t0 t1) with
      (List.fold_left i'' [t1] (Nodes t0)).
    2: cbn; admit (*comm*).
    eapply acc_tree'_list_helper.
  Admitted.
  
End  MapIntersectList.

#[export] Instance ptree_map_plus : map_plus trie_map :=
  {
    map_intersect := @intersect;
    map_fold_values := @map_fold_values;
    (* TODO: check whether the filter overhead is detectable *)
    map_map _ _ f := map_filter (fun x => Some (f x));
  }.

Module TrieArrayList.

  Open Scope positive.

  Definition trie_array A : Type := positive * (trie_map A) * A.
  #[global] Instance trie_arraylist : ArrayList.ArrayList positive trie_array :=
    {
      make _ a := (1, map.empty, a);
      get _ '(_,m,a) i := match map.get m i with Some a' => a' | None => a end;
      set _ '(p,m,a) i a' := (Pos.max p (i+1), map.put m p a', a);
      length _ '(p,_,_) := p;
    (*TODO: wrong since positive has no true zero. Should be p-1.
      Use N instead of positive?
     *)
      alloc _ '(p,m,a) a' := (p,(p+1, map.put m p a',a));
    }.

End TrieArrayList.
