Require Import ZArith Lists.List Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import coqutil.Map.Interface coqutil.Sorting.Permutation.
Require Import Tries.Canonical.
Import PTree.

Require Utils.ArrayList.
From Utils Require Import Booleans Base Lists Options ExtraMaps Default Monad.

(* TODO: move this somewhere? *)
(*reverses the bits in a positive number*)
Fixpoint pos_rev' p acc :=
  match p with
  | xH => acc
  | xO p => pos_rev' p (xO acc)
  | xI p => pos_rev' p (xI acc)
  end.
Definition pos_rev p := pos_rev' p xH.


(*TODO: move to List utils*)
Lemma all2_map_l A B C (R : A -> B -> Prop) (f : C -> A) l1 l2
  : all2 R (map f l1) l2 <-> all2 (fun x y => R (f x) y) l1 l2.
Proof.
  revert l2; induction l1; destruct l2;
    basic_goal_prep;
    basic_utils_crush.
  all: eapply IHl1; eauto.
Qed.
(*TODO: is this a good generic rewrite hint?*)
#[local] Hint Rewrite all2_map_l : utils.  
(*TODO: move to List utils*)
Lemma all2_map_r A B C (R : A -> B -> Prop) (f : C -> B) l1 l2
  : all2 R l1 (map f l2) <-> all2 (fun x y => R x (f y)) l1 l2.
Proof.
  revert l2; induction l1; destruct l2;
    basic_goal_prep;
    basic_utils_crush.
  all: eapply IHl1; eauto.
Qed.
(*TODO: is this a good generic rewrite hint?*)
#[local] Hint Rewrite all2_map_r : utils.


Lemma Mmap_option_all A B (f : A -> option B) l
  : list_Mmap f l = option_all (map f l).
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
  rewrite IHl; reflexivity.
Qed.

(*
Lemma match_match_option A B R (k : B -> R) o (case_1 : A -> B) case_2
  : k (match o with Some x => case_1 x | None => case_2 end)
    = match o with Some x => k (case_1 x) | None => k case_2 end.
Proof. destruct o; reflexivity. Qed.
*)


(*TODO: move to right file*)
Definition pair_map {A B C D}
  (f : A -> B) (g : C -> D) p :=
  (f (fst p), g (snd p)).

(*TODO: move to right file*)
Definition pair_map2 {A1 A2 B C1 C2 D}
  (f : A1 -> A2 -> B) (g : C1 -> C2 -> D) p1 p2 :=
  (f (fst p1) (fst p2), g (snd p1) (snd p2)).

Definition rezip3 {A B C} (p : list A * list B * list C) : list (A * B * C) :=
  List.combine (List.combine (fst (fst p)) (snd (fst p))) (snd p).


Definition split3 {A B C} (p : list (A * B * C)) : list A * list B * list C :=
  pair_map (@split A B) id (split p).

Lemma split_map A B (l : list (A * B))
  : split l = (map fst l, map snd l).
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
  rewrite IHl.
  reflexivity.
Qed.

Definition otree {A} (mt : option (tree' A)) :=
  match mt with None => Empty | Some t => Nodes t end.

Definition option_map2 {A B C} (f : A -> B -> C) ma mb :=
  @! let a <- ma in
    let b <- mb in
    ret f a b.

Lemma option_all_app A (l1 l2 : list (option A))
  : option_all (l1++l2)
    = option_map2 (app (A:=_)) (option_all l1) (option_all l2).
Proof.
  unfold option_map2.
  induction l1;
    basic_goal_prep;
    basic_utils_crush.
  { case_match; eauto. }
  {
    rewrite !IHl1.
    repeat case_match; eauto.
  }
Qed.
Hint Rewrite option_all_app : utils.


Lemma option_map2_None_r A B C (f : A -> B -> C) ma
  : option_map2 f ma None = None.
Proof. destruct ma; reflexivity. Qed.
Hint Rewrite option_map2_None_r : utils.


Lemma option_map2_Some_r A B C (f : A -> B -> C) ma b
  : option_map2 f ma (Some b) = Datatypes.option_map (fun a => f a b) ma.
Proof. destruct ma; reflexivity. Qed.
Hint Rewrite option_map2_Some_r : utils.

Lemma option_map_option_map A B C (f : B -> C) (g : A -> B) ma
  : Datatypes.option_map f (Datatypes.option_map g ma)
    = Datatypes.option_map (fun x => (f (g x))) ma.
Proof. destruct ma; reflexivity. Qed.
Hint Rewrite option_map_option_map : utils.

Lemma option_all_rev A (l : list (option A))
  : option_all (rev l) = Datatypes.option_map (rev (A:=_)) (option_all l).
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
  rewrite !IHl.
  repeat (case_match; basic_goal_prep; subst; eauto).
  basic_utils_crush.
Qed.
Hint Rewrite option_all_rev : utils.

(*TODO: move these somewhere?*)
Section __.
  Context {A B C D : Type}.

  Definition option_eta {R} (k : option A -> R) ma :=
    match ma with
    | None => k None
    | Some a => k (Some a)
    end.

  Lemma option_eta_equiv R (k : option A -> R) o
    : k o = option_eta k o.
  Proof. destruct o; reflexivity. Qed.
    

  Variant hfin2 := None2 | Some21 (a:A) | Some22 (a:A) (b:B).
  Definition op21 o :=
    match o with
    | None2 => None
    | Some21 a => Some a
    | Some22 a _ => Some a
    end.
  Definition op22 o :=
    match o with
    | None2 => None
    | Some21 _ => None
    | Some22 _ b => Some b
    end.
  
  Definition hfin2_eta {R} (k : hfin2 -> R) o :=
    match o with
    | None2 => k None2
    | Some21 a => k (Some21 a)
    | Some22 a b => k (Some22 a b)
    end.
  
  Record triple := mk3 { p31 :A; p32 : B; p33 : C }.
  Variant hfin3 :=
    | None3
    | Some31 (a:A)
    | Some32 (b:B)
    | Some33 (c:C)
    | Some312 (a:A) (b:B)
    | Some313 (a:A) (c:C)
    | Some323 (b:B) (c:C)
    | Some3123 (a:A) (b:B) (c:C).
  
  Definition hfin3_to_tuple_k o {R} (k : _ -> R) :=
    match o with
    | None3 => k (None, None, None)
    | Some31 a => k (Some a, None, None)
    | Some32 b => k (None, Some b, None)
    | Some33 c => k (None, None, Some c)
    | Some312 a b => k (Some a, Some b, None)
    | Some313 a c => k (Some a, None, Some c)
    | Some323 b c => k (None, Some b, Some c)
    | Some3123 a b c => k (Some a, Some b, Some c)
    end.
  
  Definition hfin3_to_tuple o :=
    Eval cbv in hfin3_to_tuple_k o id.

  Lemma hfin3_to_tuple_un_k o R (k : _ -> R)
    : hfin3_to_tuple_k o k = k (hfin3_to_tuple o).
  Proof. destruct o; reflexivity. Qed.

  Definition op31 o :=
    Eval cbv in hfin3_to_tuple_k o (fun p => fst (fst p)).
  Definition op32 o :=
    Eval cbv in hfin3_to_tuple_k o (fun p => snd (fst p)).
  Definition op33 o :=
    Eval cbv in hfin3_to_tuple_k o snd.

  
  Definition is_None3 a :=
    match a with
    | None3 => true
    | _ => false
    end.

  
  Definition hfin3_of_tuple o :=    
    match o with
    | (None, None, None) => None3
    | (Some a, None, None) => Some31 a
    | (None, Some b, None) => Some32 b
    | (None, None, Some c) => Some33 c
    | (Some a, Some b, None) => Some312 a b
    | (Some a, None, Some c) => Some313 a c
    | (None, Some b, Some c) => Some323 b c
    | (Some a, Some b, Some c) => Some3123 a b c
    end.

  Lemma hfin3_tuple_inverse o
    : hfin3_of_tuple (hfin3_to_tuple o) = o.
  Proof. destruct o; reflexivity. Qed.

  Lemma hfin3_tuple_inverse' o
    : hfin3_to_tuple (hfin3_of_tuple o) = o.
  Proof. cbv; repeat case_match; reflexivity. Qed.
  
  Record quad := mk4 { p41 :A; p42 : B; p43 : C; p44 : D }.
  
End __.
Arguments triple : clear implicits.
Arguments quad : clear implicits.
Arguments hfin2 : clear implicits.
Arguments hfin3 : clear implicits.


Definition rev3 {A B C} (hf : hfin3 (list A) (list B) (list C)) :=
  let r {X} := Datatypes.option_map (rev (A:=X)) in
  hfin3_of_tuple (pair_map (pair_map r r) r (hfin3_to_tuple hf)).

Lemma rev3_rev3 [A B C] (x :  hfin3 (list A) (list B) (list C)) : rev3 (rev3 x) = x.
Proof.
  unfold rev3.
  destruct x;
    basic_goal_prep;
    rewrite ?rev_involutive;
    reflexivity.
Qed.
#[export] Hint Rewrite rev3_rev3 : utils.  

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

    (* RHS and LHS *)
    | Node101 l1 r1, Node101 l2 r2 => Node (intersect' l1 l2) None (intersect' r1 r2)
    | Node101 l1 r1, Node111 l2 _ r2 => Node (intersect' l1 l2) None (intersect' r1 r2)
    | Node111 l1 _ r1, Node101 l2 r2 => Node (intersect' l1 l2) None (intersect' r1 r2)

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
  Context {B C} (elts_intersect : bool -> B -> list B -> option C)
    (elts_intersect_rev
      : forall b x l, elts_intersect b x (rev l)
                      = elts_intersect (negb b) x l).

  Import Lists.List.
  Import Canonical.PTree List.ListNotations.
  Arguments empty {A}%type_scope.
  
  Section __.
    Context {A : Type}.
    
    Definition tree'_tuple_k (t:tree' A) {R} (k : _ -> R) :=
      match t with
      | Node001 x => k (None, None, Some x)
      | Node010 x => k (None, Some x, None)
      | Node011 x x0 => k (None, Some x, Some x0)
      | Node100 x => k (Some x, None, None)
      | Node101 x x0 => k (Some x, None, Some x0)
      | Node110 x x0 => k (Some x, Some x0, None)
      | Node111 x x0 x1 => k (Some x, Some x0, Some x1)
      end.

    Definition tree'_tuple t := Eval cbv in tree'_tuple_k t id.

    
    Lemma tree'_tuple_un_k o R (k : _ -> R)
      : tree'_tuple_k o k = k (tree'_tuple o).
    Proof. destruct o; reflexivity. Qed.

    Definition tree'_of_tuple_k p {R} (k : tree' A -> R) k_None :=
      match p with
      | (None, None, None) => k_None
      | (None, None, Some x) => k (Node001 x)
      | (None, Some x, None) => k (Node010 x)
      | (None, Some x, Some x0) => k (Node011 x x0)
      | (Some x, None, None) => k (Node100 x)
      | (Some x, None, Some x0) => k (Node101 x x0)
      | (Some x, Some x0, None) => k (Node110 x x0)
      | (Some x, Some x0, Some x1) => k (Node111 x x0 x1)
      end.
    
  End __.
  

  Definition mcons {A} (h : option A) l :=
    match h, l with
    | Some h', Some l' => Some (h'::l')
    | _, _ => None
    end.

  Definition acc_ty :=
     hfin3 (list (tree' B)) (list B) (list(tree' B)).
  
  (*TODO: redo accumulator upacking w/ multiple functions *)
  Definition gather_tries'F gather_tries (tl : list (tree' B)) (acc : acc_ty) :=
    match tl with
    | [] => acc
    | t::tl' =>
        tree'_tuple_k t (fun p1 =>
        hfin3_to_tuple_k acc (fun p_acc =>
        let p12 := pair_map2 (pair_map2 mcons mcons) mcons p1 p_acc in
        gather_tries tl' (hfin3_of_tuple p12)))
    end.

  
  Definition gather_triesF gather_tries :=
    gather_tries'F (fun tl acc => if is_None3 acc then None3
                                  else gather_tries tl acc).

  Definition gather_tries_no_short :=
    (fix gather_tries tl := gather_tries'F gather_tries tl).
  
  Definition gather_tries_pre_cbv :=
    (fix gather_tries tl := gather_triesF gather_tries tl).
  
  Definition gather_tries :=
    Eval cbv in (fix gather_tries tl := gather_triesF gather_tries tl).

  Definition initial_acc {A B C} (hd_tuple : option A * option B * option C) :=
    let to_acc_list {A} := Mbind (M:=option) (fun _ => Mret (@nil A)) in
    hfin3_of_tuple (pair_map (pair_map to_acc_list to_acc_list) to_acc_list hd_tuple).

  Definition list_intersect'F (list_intersect' : tree' B -> bool -> list (tree' B) -> option (tree' C))
    (hd : tree' B) (is_rev : bool) (args : list (tree' B)) : option (tree' C) :=
    tree'_tuple_k hd (fun p1 =>
    hfin3_to_tuple_k (gather_tries args (initial_acc p1)) (fun p_acc =>
    let maybe_intersect m1 m2 : option (tree' C) := 
      @! let x <- m1 in
        let y <- m2 in
        (list_intersect' x (negb is_rev) y)
    in
    let p12 := pair_map2 (pair_map2 maybe_intersect
                            (fun c cs =>
                               @! let c <- c in
                                 let cs <- cs in
                                 (elts_intersect is_rev c cs)))
                 maybe_intersect
                 p1 p_acc
    in
    tree'_of_tuple_k p12 Some None)).

  #[local] Definition list_intersect'_pre_cbv :=
    (fix list_intersect' hd := list_intersect'F list_intersect' hd).
  
  Definition list_intersect' :=
    Eval cbv -[gather_tries] in
      (fix list_intersect hd := list_intersect'F list_intersect hd).

  Definition list_intersect hd := list_intersect' hd false.
  
  Lemma gather_tries_no_short_None3 tl
    :  gather_tries_no_short tl None3 = None3.
  Proof using.
    clear elts_intersect elts_intersect_rev.
    induction tl;
      basic_goal_prep;
      eauto.
    destruct a;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma gather_no_short tl acc
    : gather_tries tl acc = gather_tries_no_short tl acc.
  Proof using.
    clear elts_intersect elts_intersect_rev.
    revert acc;
      induction tl;
      basic_goal_prep;
      eauto.
    destruct a, acc;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite gather_tries_no_short_None3; eauto.
  Qed.
  
  Lemma Mmap_get_pos_trie x (l : list (tree B)) l'
    : Some l' = list_Mmap (get x) l ->
      exists l0, l = map Nodes (l0).
  Proof.
    revert l'; induction l;
      basic_goal_prep;
      basic_utils_crush.
    { exists []; eauto. }
    {
      revert H; repeat (case_match; try congruence).
      specialize (IHl _ eq_refl).
      basic_goal_prep;
        basic_utils_crush.
      destruct a; cbn in *; try congruence.
      exists (t0::x0).
      auto.
    }
  Qed.
  
  Definition opt_ord {A} (o1 o2 : option A) :=
    match o1, o2 with
    | None, None
    | None, Some _ => True
    | Some _, None  => False
    | Some x, Some y => x = y
    end.
  
  Section __.
    Context {A : Type}.

    (* A relation that holds when (at the top level) all subterms in the left
     are in the right.
     *)
    Definition subtree1 (t1 t2 : tree' A) :=
      let '(l1,c1,r1) := tree'_tuple t1 in
      let '(l2,c2,r2) := tree'_tuple t2 in
      (opt_ord l1 l2)
      /\ (opt_ord c1 c2)
      /\ (opt_ord r1 r2).

    Definition no_right t :=
      let '(l,c,r) := tree'_tuple (A:=A) t in
      r = None.
    
    Definition no_left t :=
      let '(l,c,r) := tree'_tuple (A:=A) t in
      l = None.
    
    Definition no_center t :=
      let '(l,c,r) := tree'_tuple (A:=A) t in
      c = None.
    
    Lemma subtree1_refl a : subtree1 a a.
    Proof. destruct a; cbn; intuition eauto. Qed.
    
    Lemma subtree1_trans : Transitive subtree1.
    Proof. intros a b c; destruct a,b,c; cbn; intuition subst; eauto. Qed.
      
  End __.
  Hint Resolve subtree1_refl : utils.
  Existing Instance subtree1_trans.

  
  Definition gather_tries_simple (tl : list (tree' B)) (acc : acc_ty) :=
    let oa_rev {A} (l : list (option A)) := option_all (rev l) in
    let h31 := pair_map (pair_map oa_rev oa_rev) oa_rev
                 (split3(map tree'_tuple tl))
    in
    pair_map2 (pair_map2 (option_map2 (app (A:=_))) (option_map2 (app (A:=_))))
      (option_map2 (app (A:=_)))
      h31 (hfin3_to_tuple acc).
  
  Lemma gather_tries_spec tl acc
    : hfin3_to_tuple (gather_tries tl acc) = gather_tries_simple tl acc.
  Proof.
    rewrite gather_no_short.
    revert acc.
    induction tl;      
      basic_goal_prep.
    { destruct acc; reflexivity. }
    {
      rewrite tree'_tuple_un_k.
      rewrite hfin3_to_tuple_un_k.
      rewrite IHtl; clear IHtl.
      unfold gather_tries_simple, pair_map, pair_map2, id.
      cbn.
      destruct (hfin3_to_tuple acc); clear acc;
        basic_goal_prep.
      destruct (tree'_tuple a); clear a;
        basic_goal_prep.
      unfold split3; cbn.
      destruct (split (map tree'_tuple tl)); clear tl;
        basic_goal_prep.
      destruct (split l); clear l;
        basic_goal_prep.
      rewrite !option_all_app.
      unfold id.
      basic_goal_prep.
      destruct o, o0, o1, o2, o3, o4, (option_all (rev l0)), (option_all (rev l1)), (option_all (rev l2));
        clear l0 l1 l2;
        basic_goal_prep.
      all: rewrite <- ?app_assoc.
      all: reflexivity.
    }
  Qed.
  
  Lemma get'_inner_map tl
    : map
        (fun m : tree' B =>
           match m with
           | Node010 x | Node011 x _ | Node110 _ x | Node111 _ x _ => Some x
           | _ => None
           end) tl
      = (snd (fst (split3 (map tree'_tuple tl)))).
  Proof.
    induction tl;
      unfold split3;
      repeat (basic_goal_prep; eauto; try case_match);
      basic_utils_crush.
  Qed.

  
  Definition tree_proj_001_k {A R} (k : tree' A -> R) k0 t :=
    match t with
    | Node001 x => k x
    | Node010 x => k0
    | Node011 x x0 => k x0
    | Node100 x => k0
    | Node101 x x0 => k x0
    | Node110 x x0 => k0
    | Node111 x x0 x1 => k x1
    end.

  Definition tree_proj_001 {A} := tree_proj_001_k (A:=A) Some None.

  
  Definition tree_proj_010_k {A R} (k : A -> R) k0 t :=
    match t with
    | Node001 x => k0
    | Node010 x => k x
    | Node011 x x0 => k x
    | Node100 x => k0
    | Node101 x x0 => k0
    | Node110 x x0 => k x0
    | Node111 x x0 x1 => k x0
    end.

  Definition tree_proj_010 {A} := tree_proj_010_k (A:=A) Some None.

  
  
  Definition tree_proj_100_k {A R} (k : tree' A -> R) k0 t :=
    match t with
    | Node001 x => k0
    | Node010 x => k0
    | Node011 x x0 => k0
    | Node100 x => k x
    | Node101 x x0 => k x
    | Node110 x x0 => k x
    | Node111 x x0 x1 => k x
    end.

  Definition tree_proj_100 {A} := tree_proj_100_k (A:=A) Some None.

  Lemma tree'_tuple_to_proj {A} (t : tree' A)
    : tree'_tuple t = (tree_proj_100 t, tree_proj_010 t,tree_proj_001 t).
  Proof.
    destruct t; reflexivity.
  Qed.
  
  Lemma get'_1 {A} x (t : tree' A)
    : get' x~1 t = Mbind (get' x) (tree_proj_001 t).
  Proof. destruct t; reflexivity. Qed.
  
  
  Lemma Mmap_Mbind A A' (f : A -> option A') l
    : list_Mmap (Mbind f) l = Mbind (list_Mmap f) (option_all l).
  Proof.
    induction l;
      repeat (basic_goal_prep; try case_match);
      basic_utils_crush.
  Qed.

  (*TODO: move to right place *)
  Lemma fst_split A1 A2 (l : list (A1*A2)): fst (split l) = map fst l.
  Proof.
    induction l;
      repeat (basic_goal_prep; try case_match);
      basic_utils_crush.
  Qed.
  
  (*TODO: move to right place *)
  Lemma snd_split A1 A2 (l : list (A1*A2)): snd (split l) = map snd l.
  Proof.
    induction l;
      repeat (basic_goal_prep; try case_match);
      basic_utils_crush.
  Qed.

  Instance opt_trans {A} {R : A -> A -> Prop} `{Transitive A R}
    : Transitive (Option.option_relation R).
  Proof.
    intros x y z.
    destruct x, y, z;
      cbn; try congruence.
    apply H.
  Qed.

  Lemma option_all_perm_Proper A
    : Proper (Permutation (A:=_) ==> Option.option_relation (Permutation (A:=A)))
        option_all.
  Proof.
    intros l l' Hl.
    induction Hl;
     repeat (basic_goal_prep;
             try case_match);
      basic_utils_crush.
    { apply perm_swap. }
    { eapply opt_trans; eauto. }
  Qed.
  
  Lemma gather_tries_none l
    : gather_tries l None3 = None3.
  Proof.
    induction l; 
      basic_goal_prep;
      try case_match;
      basic_utils_crush.
  Qed.
  Hint Rewrite gather_tries_none : utils.

  
  (* TODO: duplicated; should be a part of Monad_ok at some point*)
  Lemma option_Mbind_assoc T1 T2 T3 (f : T1 -> option T2) (g : T2 -> option T3) ma
    : Mbind (fun a => Mbind g (f a)) ma = Mbind g (Mbind f ma).
  Proof.
    destruct ma; cbn; eauto.
  Qed.

  Lemma option_map_ext [T1 T2] (f g : T1 -> T2) m
    : (forall x, m = Some x -> f x = g x) ->
      Datatypes.option_map f m = Datatypes.option_map g m.
  Proof.
    destruct m; cbn; try congruence.
    intro H; rewrite H; auto.
  Qed.

  Lemma option_map_id_ext [T] (m : option T) f
    : (forall x, m = Some x -> f x = x) ->
      Datatypes.option_map f m = m.
  Proof.
    destruct m; cbn; try congruence.
    intro H; rewrite H; auto.
  Qed.
    

  Lemma option_map_rev_option_all [T1 T2] (f : T1 -> option T2) l
    : Datatypes.option_map (rev (A:=T2))
        (option_all (map f l))
      = option_all (map f (rev l)).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite map_app.
    rewrite option_all_app.
    rewrite <- IHl.
    basic_goal_prep.
    repeat (case_match; basic_goal_prep);
      basic_utils_crush.
  Qed.
    
  
  (*TODO: move to list hints?*)
  #[local] Hint Rewrite rev_involutive : utils.
  Lemma gather_tries_rev x l
    :  gather_tries (rev l) (initial_acc x)
      = rev3 (gather_tries l (initial_acc x)).
  Proof.
    unfold rev3.
    rewrite <- hfin3_tuple_inverse with (o:= gather_tries (rev l) _).
    f_equal.
    rewrite !gather_tries_spec.
    (*rewrite <- hfin3_tuple_inverse with (o:= initial_acc x).*)
    unfold gather_tries_simple.
    (*rewrite ? hfin3_tuple_inverse, ? hfin3_tuple_inverse'.*)
    cbv [pair_map2 pair_map split3 pair_map id].
    cbn [fst snd].
    rewrite ! fst_split, ! snd_split, ! map_map.
    rewrite <- ! map_rev.
    rewrite !rev_involutive.
    
    f_equal; [f_equal| ].
    all:destruct x as [ [ [] [] ] [] ];
      cbn.
    all: change (match ?c with 
                 | Some a => Some (a ++ [])
                 | None => None
                 end)
      with (Datatypes.option_map (fun x => app x []) c).
    all: try now (repeat case_match; reflexivity).
    all: rewrite ?option_map_id_ext with (f:= (fun x => x ++ []))
      by (intros; cbn; apply app_nil_r).    
    all: rewrite ?option_map_rev_option_all,
        ?rev_involutive; try reflexivity.
  Qed.

  
  (*TODO: duplicated *)
  Lemma Mbind_option_ext T1 T2 (f g : T1 -> option T2) ma
    : (forall a, ma = Some a -> f a = g a) ->
      Mbind f ma = Mbind g ma.
  Proof. destruct ma; cbn in *; firstorder congruence. Qed.

  (*TODO: duplicated*)
  Lemma Mbind_option_map A1 A2 A3 (f : A2 -> option A3) (g : A1 -> A2) ma
    : Mbind f (Datatypes.option_map g ma)
      = Mbind (fun a => f (g a)) ma.
  Proof. destruct ma; reflexivity. Qed.
  Hint Rewrite Mbind_option_map : utils.


  
  Lemma list_intersect_rev t1 is_rev l0
    : list_intersect'_pre_cbv t1 is_rev (rev l0)
      = list_intersect'_pre_cbv t1 (negb is_rev) l0.
  Proof.
    revert is_rev l0.
    induction t1;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite ?gather_tries_rev.
    all: unfold rev3.
    all: rewrite !hfin3_to_tuple_un_k.
    all: rewrite hfin3_tuple_inverse'.
    all: change (if (?x : bool) then false else true) with (negb x) in *.
    all: autorewrite with utils bool in *.
    all: cbv [pair_map2 pair_map split3 pair_map id].
    all: cbn [fst snd].

    Ltac option_focus k :=
      match goal with
        |- context c [match ?e with Some x => @?branchS x | None => ?branchN end] =>
          lazymatch e with k ?t =>
                             let new_goal := context c [option_eta (fun o => match k o with
                                                                             | Some x => branchS x
                                                                             | None => branchN
                                                                             end) t] in
                             let HG := fresh "Heta" in
                             enough new_goal as HG;
                             [rewrite <- option_eta_equiv in HG; assumption
                             | cbv [option_eta] ]
          end
      end.
    all: first [option_focus (Datatypes.option_map (rev (A:=B)))
               |option_focus (Datatypes.option_map (rev (A:=tree' B)))];
      cbn;
      repeat 
        change (match ?m with
                | Some a => @?f a
                | None => None
                end)
      with (Mbind f m).
    all: rewrite <- ?option_Mbind_assoc.
    all: rewrite ? Mbind_option_map.
    all: try apply Mbind_option_ext; intros.
    all: rewrite ?IHt1, ?elts_intersect_rev,?negb_involutive.
    all: try reflexivity.
    all: repeat (lazymatch goal with
                   |- match ?c1 with _ => _ end = match ?c2 with _ => _ end =>
                     replace c1 with c2;[case_match|]
                 end;
                 try (apply Mbind_option_ext; intros);
                 rewrite ?IHt1, ?IHt1_1, ?IHt1_2, ?elts_intersect_rev,?negb_involutive;
                 try reflexivity).
  Qed.
   
  (*TODO: Issue for list intersect! Uses permutation!
    The `rev` in gather_tries_simple causes problems.
    Options:
    -rev the acc to preserve order
    -rev the cil in the caller
    -pass the cils through these functions and maintain pairness to support permutation
   *)
  Lemma list_intersect_correct' x mhd mtl is_rev
    : match list_Mmap (Mbind (get' x)) (mhd::mtl) with
      | Some (e::es) => 
          (@! let hd <- mhd in
             let tl <- option_all mtl in
             let li <- (list_intersect' hd is_rev tl) in
             ((get' x) li)) = (elts_intersect is_rev e (rev es))
      | Some [] => False
      | None =>
          (@! let hd <- mhd in
             let tl <- option_all mtl in
             let li <- (list_intersect' hd is_rev tl) in
             ((get' x) li)) = None
      end.
  Proof using elts_intersect_rev.
    change list_intersect' with list_intersect'_pre_cbv.
    generalize dependent mtl.
    revert mhd.
    induction x; intros.
    all:rewrite !Mmap_option_all.
    all:erewrite map_ext; intros.
    2:instantiate (1:= fun a => @!let a' <- a in
                                  let a1 <- tree_proj_001 a' in
                                  (get' x a1));
    destruct a; cbn; auto;
    destruct t0; reflexivity.
    3:instantiate (1:= fun a => @!let a' <- a in
                                  let a1 <- tree_proj_100 a' in
                                  (get' x a1));
    destruct a; cbn; auto;
    destruct t0; reflexivity.
    4:{
      instantiate (1:= fun a => @!let a' <- a in
                                  (tree_proj_010 a'));
      destruct a; cbn; auto;
      destruct t0; reflexivity.
    }
    all:change (fun x => ?f x) with f.
    all:rewrite <- Mmap_option_all.
    all:rewrite Mmap_Mbind.
    all:destruct mhd; cbn -[get']; eauto; [].
    all:case_match; cbn-[get']; eauto; [].
    1:specialize (IHx (tree_proj_001 t0) (map tree_proj_001 l)).
    2:specialize (IHx (tree_proj_100 t0) (map tree_proj_100 l)).
    1,2:rewrite Mmap_Mbind in IHx.
    all:cbn-[get'] in *.
    all:case_match; cbn -[get']; eauto.
    2:{
      destruct t0; cbn in *; try congruence.
      all: rewrite hfin3_to_tuple_un_k.
      all: rewrite gather_tries_spec.
      all: unfold gather_tries_simple.
      all: cbn.
      all:repeat case_match; cbn;eauto.
    }
    3:{
      destruct t0; cbn in *; try congruence.
      all: rewrite hfin3_to_tuple_un_k.
      all: rewrite gather_tries_spec.
      all: unfold gather_tries_simple.
      all: cbn.
      all:repeat case_match; cbn;eauto.
    }
    4:{
      destruct t0; cbn in *; try congruence.
      all: rewrite hfin3_to_tuple_un_k.
      all: rewrite gather_tries_spec.
      all: unfold gather_tries_simple.
      all: cbn.
      all:repeat case_match; cbn;eauto.
    }
    1:change (list_Mmap (fun a' : tree' B =>
             match tree_proj_001 a' with
             | Some a0 => get' x a0
             | None => None
             end) l)
          with (list_Mmap (fun a => Mbind (M:=option) (get' x) (tree_proj_001 a)) l).
    2:change (list_Mmap (fun a' : tree' B =>
             match tree_proj_100 a' with
             | Some a0 => get' x a0
             | None => None
             end) l)
          with (list_Mmap (fun a => Mbind (M:=option) (get' x) (tree_proj_100 a)) l).
    all:rewrite Mmap_option_all.
    1:rewrite <- map_map with (f:= tree_proj_001).
    2:rewrite <- map_map with (f:= tree_proj_100).
    all: change (fun x => ?f x) with f in *.
    all:rewrite <- Mmap_option_all.
    all:rewrite ?Mmap_Mbind.
    all:rewrite <- ?Mmap_option_all in *.
    all:destruct t0; cbn -[get'] in *;eauto.
    all: rewrite hfin3_to_tuple_un_k.
    all: rewrite gather_tries_spec.
    all: unfold gather_tries_simple.
    all: progress autorewrite with inversion rw_prop utils in *; subst.
    all: try erewrite map_ext by apply tree'_tuple_to_proj.
    all: unfold split3.
    all: rewrite !split_map.
    all: rewrite ?map_map in *.
    all: cbn -[get'] in *.
    all: rewrite !option_all_rev.
    all: rewrite <- ?Mmap_option_all.
    all: rewrite ?split_map.
    all: rewrite ?map_map in *.
    all: cbn -[get'] in *.
    all: rewrite <- ?Mmap_option_all.
    all: repeat (case_match; cbn -[get'] in *;eauto).
    all: rewrite ?get'_1.
    all: cbn.
    all: try tauto.
    all: autorewrite with inversion in *; subst.
    all: try assumption.
    all: try tauto.
    all: autorewrite with inversion utils in *; subst.
    all:rewrite ?list_intersect_rev, ?elts_intersect'_rev in *.
    all: rewrite ?negb_involutive in *.
    all: congruence.
  Qed.
    
  Lemma option_all_Some A (l : list A) : option_all (map Some l) = Some l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma list_intersect_correct x hd tl
    : get x (otree (list_intersect hd tl))
      = @!let hd_x <- get' x hd in
          let tl_x <- list_Mmap (get' x) tl in
          (elts_intersect false hd_x (rev tl_x)).
  Proof.
    pose proof (list_intersect_correct' x (Some hd) (map Some tl)) false.
    unfold list_intersect.
    change (Some hd :: map Some tl) with (map Some (hd::tl)) in *.
    rewrite Mmap_Mbind in *.
    rewrite option_all_Some in *.
    cbn in *.
    revert H; repeat (case_match; cbn).
    all:rewrite !option_all_Some in *.
    all: intros; basic_utils_crush.
    all:  repeat lazymatch goal with
           | HNone : ?a = None |- context [?a] =>
               rewrite HNone
           | HSome : ?a =  Some _ |- context [?a] =>
               rewrite HSome
           end.
    all:cbn in *; eauto.
  Qed.

  (*
  (* TODO: might want a stronger property, that the first argument can be permuted
     with the rest.
     This isn't as convenient though.
   *)
  Context (elts_intersect_Proper : Proper (eq ==> @Permutation _ ==> eq) elts_intersect).
  
  #[local] Instance list_intersect'_Proper
    : Proper (eq ==> Permutation (A:=_) ==> eq) list_intersect'_pre_cbv.
  Proof.
    intros hd' hd Hhd; subst.
    induction hd;
      intros;
      intros tl tl' Htl;
      basic_goal_prep.
    all: rewrite !hfin3_to_tuple_un_k.
    all: rewrite !gather_tries_spec.
    all: unfold gather_tries_simple.
    all: unfold pair_map2, pair_map; cbn.
    all: cbv [id].
    all: rewrite !split_map.
    all: cbn.
    all: rewrite !(map_ext _ _ tree'_tuple_to_proj).
    all: rewrite !map_map.
    all: cbn.
    all:change (fun x => ?f x) with f.
    all: 
      pose proof (option_all_perm_Proper _ _ _
                    (Permutation_rev' (Permutation_map' tree_proj_001 Htl)));
      pose proof (option_all_perm_Proper _ _ _
                    (Permutation_rev' (Permutation_map' tree_proj_010 Htl)));
      pose proof (option_all_perm_Proper _ _ _
                    (Permutation_rev' (Permutation_map' tree_proj_100 Htl))).
    all: repeat case_match; cbn; eauto; cbn in *.
    all: rewrite ?app_nil_r in *.
    all: try tauto.
    all: try congruence.
    all: repeat lazymatch goal with
           | H1 : list_intersect'_pre_cbv ?hd ?l = _,
               H2 : list_intersect'_pre_cbv ?hd ?l' = _,
                 Hperm : Permutation ?l ?l',
                   IHhd : (Permutation (A:=tree' B) ==> eq)%signature
                            (list_intersect'_pre_cbv ?hd)
                            (list_intersect'_pre_cbv ?hd)
             |- _ =>
               erewrite IHhd in H1; try eassumption; clear Hperm
           end;
      try lazymatch goal with
        | H1 : elts_intersect ?e ?l = _,
            H2 : elts_intersect ?e ?l' =_ |- _ =>
            erewrite elts_intersect_Proper in H1;
            try apply perm_skip;
            try (eassumption || symmetry; eassumption || reflexivity)
        end;
      congruence.
  Qed.
  
  
  #[export] Instance list_intersect_Proper
    : Proper (eq ==> Permutation (A:=_) ==> eq) list_intersect
    := list_intersect'_Proper.
  
   *)
   
  Lemma intersect_empty_r A (f : A -> A -> A) t
    : intersect f t Empty = Empty.
  Proof.
    destruct t; reflexivity.
  Qed.
  Hint Rewrite intersect_empty_r : utils.

  (*  
  Lemma list_intersect_correct hd l
    : List.fold_left (intersect elt_intersect) l hd = list_intersect hd l.
  Proof.
    destruct hd;
      basic_goal_prep;
      basic_utils_crush.
    (*revert t0.
    induction l; [eapply list_intersect'_nil|].

    basic_goal_prep;
      destruct a.
    1:basic_utils_crush.
    replace (intersect' elt_intersect t0 t1) with
      (List.fold_left i'' [t1] (Nodes t0)).
    2: cbn; admit (*comm*).
    eapply acc_tree'_list_helper.*)
  Admitted.
   *)
  
End MapIntersectList.

#[export] Instance ptree_map_plus : map_plus trie_map :=
  {
    map_intersect := @intersect;
    map_fold_values := @map_fold_values;
    (* TODO: check whether the filter overhead is detectable *)
    map_map _ _ f := map_filter (fun x => Some (f x));
  }.

#[export] Hint Rewrite gempty : utils.
#[export] Hint Rewrite @gNode : utils.

#[export] Instance ptree_map_plus_ok : map_plus_ok trie_map.
Proof.
  constructor.
  {
    intros.
    destruct t1, t2; basic_goal_prep; try now intuition eauto.
    { case_match; eauto. }
    {
      revert t1 k;
        induction t0;
        destruct t1;
        basic_goal_prep;
        repeat case_match;
        basic_goal_prep;
        try congruence.
      all:repeat lazymatch goal with
            | H : get' ?k (?f ?t0) = _ |- _ =>
                destruct k; basic_goal_prep
            | H : intersect' ?t0 ?t1 = _
              |- _ =>
                rewrite H
            end.
      all:autorewrite with bool utils in *.
      all: try congruence.
      all: repeat lazymatch goal with
             | Hi : intersect' ?f ?t0 ?t1 = _,
                 Hg0 : get' ?k ?t0 = _,
                   IH : forall t1 k,
                     get k (intersect' ?f ?t0 t1) = _
                     |- _ =>
                 specialize (IH t1 k);
                 rewrite Hi, Hg0 in IH;
                             cbn in *;
                             try congruence
    |  Hg0 : get' ?k ?t0 = _,
        IH : forall t1 k,
          get k (intersect' ?f ?t0 t1) = _
          |- get ?k (intersect' ?f ?t0 ?t1) = _ =>
         specialize (IH t1 k);
         rewrite Hg0 in IH;
         cbn in *;
         try congruence
    |  Hg1 : get' ?k ?t1 = _,
        Hg0 : get' ?k ?t0 = _,
          IH : forall t1 k,
            get k (intersect' ?f ?t0 t1) = _
            |- _ =>
         specialize (IH t1 k);
         rewrite Hg1, Hg0 in IH;
                      cbn in *;
                      try congruence
    | Hg1 : get' ?k ?t1 = _,
        IH : context [get' ?k ?t1]
      |- _ =>
        rewrite Hg1 in IH;
        cbn in *;
        try congruence
      end.
    }
  }
  {
    intros.
    apply gmap_filter.
  }
Qed.

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



    
