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
  
  Record quad := mk4 { p41 :A; p42 : B; p43 : C; p44 : D }.
  
End __.
Arguments triple : clear implicits.
Arguments quad : clear implicits.
Arguments hfin2 : clear implicits.
Arguments hfin3 : clear implicits.



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
  (* The argument to elts_intersect must be non-empty
     for the result to be well-defined
   *)
  Context {B C} (elts_intersect : list B -> option C).

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

  Definition list_intersect'F (list_intersect' : tree' B -> list (tree' B) -> option (tree' C))
    (hd : tree' B) (args : list (tree' B)) : option (tree' C) :=
    tree'_tuple_k hd (fun p1 =>
    hfin3_to_tuple_k (gather_tries args (initial_acc p1)) (fun p_acc =>
    let maybe_intersect m1 m2 : option (tree' C) := 
      @! let x <- m1 in
        let y <- m2 in
        (list_intersect' x y)
    in
    let p12 := pair_map2 (pair_map2 maybe_intersect
                            (fun c cs => Mbind (M:=option) elts_intersect (mcons c cs)))
                 maybe_intersect
                 p1 p_acc
    in
    tree'_of_tuple_k p12 Some None)).

  #[local] Definition list_intersect'_pre_cbv :=
    (fix list_intersect' hd := list_intersect'F list_intersect' hd).
  
  Definition list_intersect' :=
    Eval cbv -[gather_tries] in
      (fix list_intersect' hd := list_intersect'F list_intersect' hd).

  
  Fixpoint acc_tree'_list (l : list (tree B)) acc k : tree C :=
    match l with
    | [] => k acc
    | Empty::_ => Empty
    | Nodes t :: l' => acc_tree'_list l' (t::acc) k
    end.

  (* TODO: mediatw tree vs option
  (* takes the first `hd` since the intersection of an empty list of trees isn't finitely defined.*)
  Definition list_intersect (hd : tree B) (tl : list (tree B)) : tree C :=
    (* ensures that the tail is nonempty in the else branch.
       TODO: is there a way to hide this check in an existing match?
     *)
    if tl then map_filter (fun x => elts_intersect [x]) hd else
      match hd with
      | Empty => Empty
      | Nodes hd' => acc_tree'_list tl [] (fun args => list_intersect' hd')
      end.
   *)

  
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
  
  Lemma acc_tree'_list_Nodes x0 acc k
    : acc_tree'_list (map Nodes x0) acc k = k (rev x0 ++ acc).
  Proof.
    revert acc.
    induction x0;
      basic_goal_prep;
      basic_utils_crush.
    rewrite IHx0.
    f_equal.
    rewrite <- app_assoc.
    reflexivity.
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

  
  (*
  (*TODO: generalize to dependent version/other fns *)
  Lemma rights_correct tl acc
    : tl <> [] \/ acc <> [] ->
      match rights tl acc with
      | [] => Exists no_right tl
      | _ as rs =>
          all2 subtree1 (map Node001 rs) (rev tl ++ map Node001 acc)
      end.
  Proof.
    revert acc.
    induction tl;
      [destruct acc |];
      basic_goal_prep;
      basic_utils_crush.
    all: destruct a;
      basic_goal_prep;
      basic_utils_crush.
    all: try eapply Exists_cons_hd;
      unfold no_right;
      basic_goal_prep;
      basic_utils_crush.
    all: match goal with
           |- context [rights _ ?acc] =>
             specialize (IHtl acc)
         end.
    all: intuition try congruence.
    all: case_match.
    all: try eapply Exists_cons_tl;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite <- ?app_assoc; cbn [app]; eauto.
    all: my_case Hrev (rev tl); cbn in *; try tauto.
    all: repeat (case_match;subst;[]).
    all: intuition eauto.
    all: destruct o; cbn in *; subst; try tauto.
    all: eapply all2_Transitive; try typeclasses eauto.
    all: try eassumption.
    all: apply all2_app_shared_head; eauto with utils.
    all: cbn; intuition eauto with utils.
  Qed.
  
  Lemma lefts_correct tl acc
    : tl <> [] \/ acc <> [] ->
      match lefts tl acc with
      | [] => Exists no_left tl
      | _ as rs =>
          all2 subtree1 (map Node100 rs) (rev tl ++ map Node100 acc)
      end.
  Proof.
    revert acc.
    induction tl;
      [destruct acc |];
      basic_goal_prep;
      basic_utils_crush.
    all: destruct a;
      basic_goal_prep;
      basic_utils_crush.
    all: try eapply Exists_cons_hd;
      unfold no_left;
      basic_goal_prep;
      basic_utils_crush.
    all: match goal with
           |- context [lefts _ ?acc] =>
             specialize (IHtl acc)
         end.
    all: intuition try congruence.
    all: case_match.
    all: try eapply Exists_cons_tl;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite <- ?app_assoc; cbn [app]; eauto.
    all: my_case Hrev (rev tl); cbn in *; try tauto.
    all: repeat (case_match;subst;[]).
    all: intuition eauto.
    all: destruct o; cbn in *; subst; try tauto.
    all: eapply all2_Transitive; try typeclasses eauto.
    all: try eassumption.
    all: apply all2_app_shared_head; eauto with utils.
    all: cbn; intuition eauto with utils.
  Qed.

  
  Lemma side_correct_l tl acc
    : tl <> [] \/ fst acc <> [] ->
      match fst (sides tl acc) with
      | [] => Exists no_left tl
      | _ as rs =>
          all2 subtree1 (map Node100 rs) (rev tl ++ map Node100 (fst acc))
      end.
  Proof.
    destruct acc as [acc acc'].
    revert acc acc'.
    induction tl;
      [destruct acc |];
      basic_goal_prep;
      basic_utils_crush.
    all: destruct a;
      basic_goal_prep;
      basic_utils_crush.
    all: try eapply Exists_cons_hd;
      unfold no_left;
      basic_goal_prep;
      basic_utils_crush.
    all: match goal with
           | |- context [sides _ (?acc,?acc')] =>
             specialize (IHtl acc acc')
           | |- context [lefts ?tl ?acc] =>
             pose proof (lefts_correct tl acc)
         end.
    all: intuition try congruence.
    all: case_match.
    all: try eapply Exists_cons_tl;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite <- ?app_assoc; cbn [app]; eauto.
    all: my_case Hrev (rev tl); cbn in *; try tauto.
    all: repeat (case_match;subst;[]).
    all: intuition eauto.
    all: repeat (case_match; cbn in *; subst; try tauto).
    all: cbn; intuition subst; eauto with utils.
    all: destruct tl; basic_goal_prep; try congruence.
    all: intuition try congruence.
    all: eapply all2_Transitive; try typeclasses eauto.
    all: try eassumption.
    all: apply all2_app_shared_head; eauto with utils.
    all: cbn; intuition eauto with utils.
  Qed.

  
  Lemma side_subtree tl acc
    : all2 subtree1
        (map2 Node101 (rezip (sides tl acc)))
        (rev tl ++ map2 Node101 (rezip acc)).
  Proof.
    revert acc.
    induction tl;
      try destruct a;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite <- ? app_assoc; basic_goal_prep.
    {
      TODO: where is the node001 from?
      .
      I should have an option layer.
      In the 2-3 branch cases it is free.
      is this what happens when one list out of 2 is empty?
      TODO: goal is false. why?

    tl <> [] \/ fst acc <> [] ->
      match fst (sides tl acc) with
      | [] => Exists no_left tl
      | _ as rs =>
          all2 subtree1 (map Node100 rs) (rev tl ++ map Node100 (fst acc))
      end.
  Proof.

  Lemma side_correct_r tl acc
    : let (ls,rs) := sides tl acc in
      (tl 


    tl <> [] \/ snd acc <> [] ->
      match (sides tl acc) with
      | [] => Exists no_right tl
      | _ as rs =>
          all2 subtree1 (map Node001 rs) (rev tl ++ map Node001 (fst acc))
      end.
    
    Lemma side_correct_r tl acc
    : tl <> [] \/ snd acc <> [] ->
      match snd (sides tl acc) with
      | [] => Exists no_right tl
      | _ as rs =>
          all2 subtree1 (map Node001 rs) (rev tl ++ map Node001 (fst acc))
      end.
  Proof.
    destruct acc as [acc' acc].
    revert acc' acc.
    induction tl;
      [destruct acc |];
      basic_goal_prep;
      basic_utils_crush.
    all: destruct a;
      basic_goal_prep;
      basic_utils_crush.
    all: try eapply Exists_cons_hd;
      unfold no_right;
      basic_goal_prep;
      basic_utils_crush.
    all: match goal with
           | |- context [sides _ (?acc,?acc')] =>
             specialize (IHtl acc acc')
           | |- context [rights ?tl ?acc] =>
             pose proof (rights_correct tl acc)
         end.
    all: intuition try congruence.
    all: case_match.
    all: try eapply Exists_cons_tl;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite <- ?app_assoc; cbn [app]; eauto.
    all: my_case Hrev (rev tl); cbn in *; try tauto.
    all: repeat (case_match;subst;[]).
    all: intuition eauto.
    all: repeat (case_match; cbn in *; subst; try tauto).
    all: cbn; intuition subst; eauto with utils.
    all: destruct tl; basic_goal_prep; try congruence.
    all: intuition try congruence.
    all: eapply all2_Transitive; try typeclasses eauto.
    all: try eassumption.
    all: apply all2_app_shared_head; eauto with utils.
    all: cbn; intuition eauto with utils.
  Qed.

   *)

  Lemma gather_tries_no_short_None3 tl
    :  gather_tries_no_short tl None3 = None3.
  Proof.
    induction tl;
      basic_goal_prep;
      eauto.
    destruct a;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma gather_no_short tl acc
    : gather_tries tl acc = gather_tries_no_short tl acc.
  Proof.
    revert acc;
      induction tl;
      basic_goal_prep;
      eauto.
    destruct a, acc;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite gather_tries_no_short_None3; eauto.
  Qed.

  
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
  
  Context (elts_intersect_Proper : Proper (@Permutation _ ==> eq) elts_intersect).

  
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
  (*
  Lemma list_intersect'_proj_001 l l0 l1 t0 t1
    : list_Mmap tree_proj_001 l = Some l0 ->
      Some t1 = tree_proj_001 t0 ->
      list_intersect'_pre_cbv t0 l = Some l1 ->
      list_intersect'_pre_cbv t1 l0 = tree_proj_001 l1.
  Proof.
    destruct t0; cbn.
   *)

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
  
  Instance list_intersect'_Proper
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
        | H1 : elts_intersect (?e::?l) = _,
            H2 : elts_intersect (?e::?l') =_ |- _ =>
            erewrite elts_intersect_Proper in H1;
            try apply perm_skip;
            try (eassumption || symmetry; eassumption)
        end;
      congruence.
  Qed.
    
    
  Lemma list_intersect'_correct' x mhd mtl
    : match list_Mmap (Mbind (get' x)) (mhd::mtl) with
      | Some es => 
          (@! let hd <- mhd in
             let tl <- option_all mtl in
             let li <- (list_intersect' hd tl) in
             ((get' x) li)) = (elts_intersect es)
      | None =>
          (@! let hd <- mhd in
             let tl <- option_all mtl in
             let li <- (list_intersect' hd tl) in
             ((get' x) li)) = None
      end.
  Proof using elts_intersect_Proper.
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
    all: autorewrite with inversion utils in *; subst.
    all: rewrite <- ?Permutation_rev in *.
    all: try match goal with
         | H1 : ?A = ?B, H2 : ?A = ?C |- _ =>
             rewrite H1 in H2
         end.
    all: autorewrite with inversion utils in *; subst.
    all: try assumption.
    all: try tauto.    
    all: repeat lazymatch goal with
           | HNone : ?a = None |- _ =>
               rewrite HNone
           | HSome : ?a = Some _ |- _ =>
               rewrite HSome
           end; auto.
  Qed.
  
  Lemma option_all_Some A (l : list A) : option_all (map Some l) = Some l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
    rewrite IHl.
    reflexivity.
  Qed.
    
  Lemma list_intersect'_correct x hd tl
    : get x (otree (list_intersect' hd tl))
      = option_map elts_intersect (list_Mmap (get' x) (hd::tl)).
  Proof using elts_intersect_Proper.
    pose proof (list_intersect'_correct' x (Some hd) (map Some tl)).
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

  (*TODO: revive?
  (*TODO: not quite right if elts_intersect is not injective.
    Forward implication is true,
    backward is not
   *)
  Lemma list_intersect_correct x hd tl
    : match list_Mmap (get x) (hd::tl) with
      | Some es => get x (list_intersect hd tl) = (elts_intersect es)
      | None => get x (list_intersect hd tl) = None
      end.
  Proof.
    case_match.
    {
      pose proof HeqH as HeqH'.
      eapply Mmap_get_pos_trie in HeqH'.
      break.
      destruct x0; cbn in *; try congruence.
      basic_utils_crush.
      unfold list_intersect. 
      cbn -[map_filter ]in *.
      revert HeqH; case_match; cbn -[map_filter] in *; try congruence.
      case_match; cbn -[map_filter] in *; try congruence.
      intros;basic_utils_crush.
      destruct x0.
      {
        cbn -[map_filter] in *;
        rewrite ?gmap_filter, ?gempty in *.
        basic_utils_crush.
        cbn.
        rewrite <- HeqH.
        reflexivity.
      }
      rewrite acc_tree'_list_Nodes.
      cbn [map].
      change list_intersect'_cbv with list_intersect'.
(*
        get x (list_intersect' t0 t_lst)
        
      
      TODO: need an elts_intersect commutativity lemma to deal w/ the rev
      TODO: lemma about acc_tree'_list
               
        cbn.
      
      TODO: unwrap all the ptrees in hd::tl
      unfold list_intersect.
      destruct hd;
        cbn [option_map list_Mmap Mbind option_monad] in *;
        rewrite ?gmap_filter, ?gempty in *;
        cbv [get ] in *;
        try congruence.
      { revert HeqH; case_match; cbn in *; congruence. }
      {
        generalize (tl_1::tl_tl).
        revert HeqH; case_match; try congruence.
        case_match; subst; try congruence.
        case_match; subst; try congruence.
      }
        Cbn.
    }
    my_case Hget (get x (list_intersect hd tl)).
    2:case_match; eauto.
    2:{
    case_match.
    
    unfold list_intersect.
    destruct tl, hd; cbn -[map_filter] in *; eauto.
    {
      case_match; cbn -[map_filter]; eauto;
        rewrite !gmap_filter;
        cbv [get];
        rewrite <- ?HeqH;
        cbn;
        eauto.
    }
    {
      case_match; cbn -[map_filter]; eauto;
        cbv [get];
        destruct t0; eauto;
        rewrite <- ?HeqH.
      {
        case_match; cbn -[map_filter]; eauto;
          cbv [get].
        2:{
          TODO: prperties of acc_tree'_list
        cbn;
        eauto.
        
        

End.
       *)
  Abort.
   *)

  (*
  Context (elt_intersect_comm : forall a b, elt_intersect a b = elt_intersect b a).
   *)

  (*
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
   *)

  (*
  Lemma fold_intersect_empty l
    : fold_left (intersect elt_intersect) l Empty = Empty.
  Proof.
    unfold intersect.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  #[local] Hint Rewrite fold_intersect_empty : utils.
  *)


  (*
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
   *)

   
  Lemma intersect_empty_r A (f : A -> A -> A) t
    : intersect f t Empty = Empty.
  Proof.
    destruct t; reflexivity.
  Qed.
  Hint Rewrite intersect_empty_r : utils.

  (*
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
    (*rewrite <- IHtl.
    f_equal.
    cbn.
    admit (*comm*).*)
  Admitted.
  
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



    
