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


Lemma option_Mmap_Mmap A B C (g : A -> option B) (f : B -> option C) l
  : list_Mmap (fun x => Mbind f (g x)) l = Mbind (list_Mmap f) (list_Mmap g l).
Proof.
  induction l;
    basic_goal_prep;
    repeat (case_match;
            basic_goal_prep);
    basic_utils_crush.
Qed.


Lemma option_Mbind_comm A B C (f : A -> B -> option C) v1 v2
  : Mbind (fun x => Mbind (f x) v1) v2
    = Mbind (fun y => Mbind (fun x => f x y) v2) v1.
Proof. destruct v1, v2; cbn; reflexivity. Qed.

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
    (* (* represents the number of maps being intersected.
       Necessary to instantiate elts_intersect_rev how we need to.
       TODO: come up with a better way to do this   
     *)
    (arity : nat)*)
    (elts_wf : bool -> B -> list B -> Prop)
    (elts_wf_rev : forall b v l, elts_wf b v (rev l) <-> elts_wf (negb b) v l)
    (elts_intersect_rev
      : forall b x l, (*length l = arity ->*)
                      elts_wf b x (rev l) ->
                      elts_intersect b x (rev l)
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
                                 (* note: the argument to elts_intersect
                                    is interpreted as is_forward.
                                    Since cs will have been reversed from the args input,
                                    going from is_rev to is_forward removes the need to negate it here.
                                  *)
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
    clear elts_intersect elts_intersect_rev elts_wf elts_wf_rev.
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

  Lemma list_get'_1 {A} x (l : list (tree' A))
    : list_Mmap (get' x~1) l = list_Mmap (fun t => Mbind (get' x) (tree_proj_001 t)) l.
  Proof.
    rewrite !Mmap_option_all.
    f_equal.
    apply map_ext; intros; eauto using get'_1.
  Qed.

  
  Lemma get'_0 {A} x (t : tree' A)
    : get' x~0 t = Mbind (get' x) (tree_proj_100 t).
  Proof. destruct t; reflexivity. Qed.

  Lemma list_get'_0 {A} x (l : list (tree' A))
    : list_Mmap (get' x~0) l = list_Mmap (fun t => Mbind (get' x) (tree_proj_100 t)) l.
  Proof.
    rewrite !Mmap_option_all.
    f_equal.
    apply map_ext; intros; eauto using get'_0.
  Qed.

  
  Lemma get'_xH {A} (t : tree' A)
    : get' 1 t = tree_proj_010 t.
  Proof. reflexivity. Qed.

  Lemma list_get'_xH {A} (l : list (tree' A))
    : list_Mmap (get' 1) l = list_Mmap tree_proj_010 l.
  Proof. reflexivity. Qed.
  
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

  #[local] Hint Rewrite rev_length : utils.

  Fixpoint flip_by_length i b :=
    match i with
    | xI x 
    | xO x => flip_by_length x (negb b)
    | xH => b
    end.

  
  Lemma flip_by_length_xI i acc
    : flip_by_length (xI i) (negb acc) = flip_by_length i acc.
  Proof. cbn; rewrite negb_involutive; reflexivity. Qed.
  
  Lemma flip_by_length_xO i acc
    : flip_by_length (xO i) (negb acc) = flip_by_length i acc.
  Proof. cbn; rewrite negb_involutive; reflexivity. Qed.

  
  Lemma flip_by_length_negb i acc
    : flip_by_length i (negb acc) = negb (flip_by_length i  acc).
  Proof.
    revert acc.
    induction i;
      basic_goal_prep;
      basic_utils_crush.
    all: rewrite IHi.
    all: basic_utils_crush.
  Qed.
  
  (*TODO: problem! the reversal is forgotten here!
it's dependent on the length of i. use flip_by_length (could be backwards?)

     b t l -> b (next t) (rev (next l)) ~ (negb b) (next t) (next l)
   *)
  Definition map_elts_wf b t l :=
    forall i x l', PTree.get' i t = Some x ->
                   list_Mmap (PTree.get' i) l = Some l' ->
                 elts_wf (negb b) (*(flip_by_length i b)*) x l'.

  Lemma map_elts_wf_rev' is_rev x a
    : map_elts_wf is_rev x (rev a) -> map_elts_wf (negb is_rev) x a.
  Proof.
    unfold map_elts_wf.
    intros.
    rewrite ?flip_by_length_negb.
    rewrite <- elts_wf_rev.
    eapply H; eauto.
    
    rewrite Mmap_option_all,
      map_rev,
      option_all_rev,
      <- Mmap_option_all in *.
    rewrite H1.
    reflexivity.
  Qed.
    
  Lemma map_elts_wf_rev is_rev t a
    : map_elts_wf (negb is_rev) t a <-> map_elts_wf is_rev t (rev a).
  Proof.
    split; eauto using map_elts_wf_rev'.
    intros.
    rewrite <- negb_involutive with (b:=is_rev).
    apply  map_elts_wf_rev'.
    rewrite rev_involutive; auto.
  Qed.    

 
  Lemma tree'_tuple_center_elts_wf b t l0 v a0
    : map_elts_wf b t l0 ->
      snd (fst (tree'_tuple t)) = Some v ->
      option_all (map (fun x : tree' B => snd (fst (tree'_tuple x))) l0) = Some a0 ->
      elts_wf b v (rev a0).
  Proof.
    unfold map_elts_wf, tree'_tuple.
    rewrite elts_wf_rev.
    erewrite map_ext.
    2:{
      intros.
      Unshelve.
      2: refine (fun a => match a with Node001 x => _ | _ => _ end).
      2-8:shelve.
      cbn;destruct a; cbn.
      all: reflexivity.
    }
    intros.
    specialize (H xH v a0).
    rewrite <- Mmap_option_all in *.
    cbn in *.
    destruct t; cbn in *; try congruence.
    all:apply H in H1.
    all:basic_utils_crush.
  Qed.

  Lemma tree'_tuple_right_elts_wf b t l0 t' a0
    : map_elts_wf b t l0 ->
      snd (tree'_tuple t) = Some t' ->
      option_all (map (fun x : tree' B => snd (tree'_tuple x)) l0) = Some a0 ->
      map_elts_wf b t' a0.
  Proof.
    unfold map_elts_wf, tree'_tuple.
    destruct t; basic_goal_prep; try congruence.
    all: autorewrite with inversion in *; subst.
    all:specialize (H (xI i) x l'); cbn in H;
    rewrite ?negb_involutive in H; apply H; clear H; auto;
    change (list_Mmap (get' i) a0)
        with (Mbind (list_Mmap (get' i)) (Some a0)) in *;
      rewrite <- H1 in *; clear H1;
      rewrite <- Mmap_Mbind in *;
      rewrite Mmap_option_all in *;
      rewrite map_map in *;
      rewrite <- H3; clear H3;
      f_equal;
      apply map_ext;
      intros; case_match; basic_goal_prep; auto.
  Qed.
  
  
  Lemma tree'_tuple_left_elts_wf b t l0 t' a0
    : map_elts_wf b t l0 ->
      fst (fst (tree'_tuple t)) = Some t' ->
      option_all (map (fun x : tree' B => fst (fst (tree'_tuple x))) l0) = Some a0 ->
      map_elts_wf b t' a0.
  Proof.
    unfold map_elts_wf, tree'_tuple.
    destruct t; basic_goal_prep; try congruence.
    all: autorewrite with inversion in *; subst.
    all:specialize (H (xO i) x l'); cbn in H;
    rewrite ?negb_involutive in H; apply H; clear H; auto;
    change (list_Mmap (get' i) a0)
        with (Mbind (list_Mmap (get' i)) (Some a0)) in *;
      rewrite <- H1 in *; clear H1;
      rewrite <- Mmap_Mbind in *;
      rewrite Mmap_option_all in *;
      rewrite map_map in *;
      rewrite <- H3; clear H3;
      f_equal;
      apply map_ext;
      intros; case_match; basic_goal_prep; auto.
  Qed.

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

  (*
  Lemma negated_excluded_middle A
    : ~~(A \/ ~A).
  Proof. intuition. Qed.
  
  Lemma list_intersect_rev_ex (b1 b2:B) is_rev
    : (*length l0 = arity -> *)
    
    (*elts_wf is_rev b1 [b1;b2] ->*)
    let t1 := (Node001 (Node001 (Node010 b1))) in
    let t2 := (Node001 (Node001 (Node010 b2))) in
    let l0 := [t1;t2 ] in
    map_elts_wf is_rev t1 (rev l0) ->
      list_intersect'_pre_cbv t1 is_rev (rev l0)
      = list_intersect'_pre_cbv t1 (negb is_rev) l0.
  Proof.
    cbn in *.
    intros.
    rewrite ?negb_involutive in *.
    
    rewrite <- elts_intersect_rev, negb_involutive in *; cbn in *;eauto.
    specialize (H (xI xH)); cbn in *.
    rewrite ?negb_involutive in *.
    rewrite (*<- negb_involutive with (b:=is_rev),*) <- elts_wf_rev.
    apply H; auto.
    TODO: backward at this level, right at the next. why is that?cu
  Qed.
    apply (negated_excluded_middle (map_elts_wf true (Node001 (Node010 b1)) [Node001 (Node010 b2); Node001 (Node010 b1)])).
    intro.
    destruct H0.
    {
      apply Thm in H0.
      clear Thm.
      cbn in *.
    
  Lemma not_list_intersect_rev (b1 b2:B)
    : (*length l0 = arity -> *)
    
    elts_wf true b1 [b1;b2] ->
    b1 <> b2 ->
      ~( forall t1 is_rev l0, map_elts_wf is_rev t1 (rev l0) ->
      list_intersect'_pre_cbv t1 is_rev (rev l0)
      = list_intersect'_pre_cbv t1 (negb is_rev) l0).
  Proof.
    intros ? Hneq Thm.
    specialize (Thm (Node001 (Node010 b1)) true
                  [(Node001 (Node010 b1)) ;(Node001 (Node010 b2)) ]).
    cbn in *.
    change false with (negb true) in *.
    rewrite <- elts_intersect_rev in *; eauto.
    apply (negated_excluded_middle (map_elts_wf true (Node001 (Node010 b1)) [Node001 (Node010 b2); Node001 (Node010 b1)])).
    intro.
    destruct H0.
    {
      apply Thm in H0.
      clear Thm.
      cbn in *.
    2:{
    }
    revert is_rev l0.
    induction t1;
      basic_goal_prep;
      basic_utils_crush.    
    all: rewrite ?gather_tries_rev in *;
                 unfold rev3 in *;
                 rewrite ?hfin3_to_tuple_un_k, ?hfin3_tuple_inverse' in *;
                 cbv [pair_map2 pair_map split3 pair_map id] in *;
      cbn[fst snd] in *.
    all: rewrite !gather_tries_spec in *;
      unfold gather_tries_simple in *;
      basic_goal_prep;
      rewrite ?option_map2_Some_r in *;
      cbv [id] in *;
      autorewrite with utils in *;
      erewrite option_map_ext in *
        by (basic_goal_prep; rewrite app_nil_r; reflexivity).
    all: erewrite option_map_ext in *
        by (basic_goal_prep; rewrite rev_involutive; reflexivity).
    all:rewrite option_map_id_ext in *
        by (basic_goal_prep; reflexivity).
    all: try erewrite option_map_ext in *
        by (basic_goal_prep; apply app_nil_r).
    {
      case_match; cbn in *; eauto.
      2:{
    all: rewrite !split_map in *; cbn in *.
    all: rewrite ?map_map in *.
    all: rewrite option_map_rev_option_all in *.
    *)
  
  Lemma list_intersect_rev t1 is_rev l0
    : (*length l0 = arity -> *)
      map_elts_wf is_rev t1 (rev l0) ->
      list_intersect'_pre_cbv t1 is_rev (rev l0)
      = list_intersect'_pre_cbv t1 (negb is_rev) l0.
  Proof.
    revert is_rev l0.
    induction t1;
      basic_goal_prep;
      basic_utils_crush.    
    all: rewrite ?gather_tries_rev;
                 unfold rev3;
                 rewrite ?hfin3_to_tuple_un_k, ?hfin3_tuple_inverse';
                 cbv [pair_map2 pair_map split3 pair_map id];
      cbn[fst snd].
    all:
      first [option_focus (Datatypes.option_map (rev (A:=B)))
               |option_focus (Datatypes.option_map (rev (A:=tree' B)))];
      cbn;
      repeat 
        change (match ?m with
                | Some a => @?f a
                | None => None
                end)
      with (Mbind f m);
      rewrite <- ?option_Mbind_assoc;
      rewrite ? Mbind_option_map;
      try apply Mbind_option_ext; intros;
      try apply f_equal.
    
    all: rewrite gather_tries_spec in *;
      unfold gather_tries_simple in *;
      basic_goal_prep;
      rewrite ?option_map2_Some_r in *;
      cbv [id] in *;
      autorewrite with utils in *;
      erewrite option_map_ext in *
        by (basic_goal_prep; rewrite app_nil_r; reflexivity).
    all: rewrite !split_map in *; cbn in *.
    all: rewrite ?map_map in *.
    all: rewrite option_map_rev_option_all in *.
    all: unshelve (repeat (try case_match; basic_goal_prep;
      rewrite ?elts_intersect_rev by ((erewrite !length_option_all by eauto;
                                          basic_utils_crush) || shelve);

    
      rewrite ?gather_tries_spec in *;
      unfold gather_tries_simple in *;
      basic_goal_prep;
      rewrite ?option_map2_Some_r in *;
      cbv [id] in *;
      autorewrite with utils in *;
      try erewrite option_map_ext in *
        by (basic_goal_prep; rewrite app_nil_r; reflexivity);
      rewrite ?split_map in *; cbn in *;
    rewrite ?map_map in *;
      rewrite ?option_map_rev_option_all in *;
      (*TODO: hardcoded names*)
      try rewrite IHt1 by shelve;
    try rewrite IHt1_1 by shelve;
    try rewrite IHt1_2 by shelve;
      try (first [option_focus (Datatypes.option_map (rev (A:=B)))
                 |option_focus (Datatypes.option_map (rev (A:=tree' B)))];
           cbn;
           repeat 
             change (match ?m with
                     | Some a => @?f a
                     | None => None
                     end)
             with (Mbind f m);
           rewrite <- ?option_Mbind_assoc;
           rewrite ? Mbind_option_map;
           try apply Mbind_option_ext; intros;
           try apply f_equal);
                           rewrite ?negb_involutive, ?rev_involutive; auto)).
    all: try now (eapply tree'_tuple_center_elts_wf; cycle 1; eauto; cbn; eauto).
    all:rewrite <- map_elts_wf_rev, negb_involutive.
    all: try now (eapply tree'_tuple_right_elts_wf; cycle 1; eauto; cbn; eauto).
    all: try now (eapply tree'_tuple_left_elts_wf; cycle 1; eauto; cbn; eauto).
  Qed.

  Lemma list_Mmap_length T T' (f : T -> option T') l l'
    : list_Mmap f l = Some l' ->
      length l = length l'.
  Proof.
    revert l'.
    induction l;
      basic_goal_prep;
      repeat case_match;
      basic_goal_prep;
      basic_utils_crush.
    basic_goal_prep;
      basic_utils_crush.
  Qed.

  Definition uncons {T T'} f (l : list T) : option T' :=
    match l with
    | [] => None
    | x::l => f x l
    end.

  Lemma tree_proj_tuple_r {T} (a : (tree' T))
    :tree_proj_001 a = snd (tree'_tuple a).
  Proof. destruct a; reflexivity. Qed.
  
  Lemma list_tree_proj_tuple_r {T} (tl : list (tree' T))
    :  list_Mmap tree_proj_001 tl = option_all (snd (split (map tree'_tuple tl))).
  Proof.
    induction tl; auto.
    rewrite !snd_split, map_map in *.
    cbn [list_Mmap map].
    rewrite tree_proj_tuple_r, IHtl;
    reflexivity.
  Qed.

  
  Lemma tree_proj_tuple_l {T} (a : (tree' T))
    :tree_proj_100 a = fst (fst (tree'_tuple a)).
  Proof. destruct a; reflexivity. Qed.
  
  Lemma list_tree_proj_tuple_l {T} (tl : list (tree' T))
    :  list_Mmap tree_proj_100 tl = option_all (fst  (split(fst (split (map tree'_tuple tl))))).
  Proof.
    induction tl; auto.
    rewrite !fst_split, map_map in *.
    cbn [list_Mmap map].
    rewrite tree_proj_tuple_l, IHtl;
    reflexivity.
  Qed.

  
  Lemma tree_proj_tuple_c {T} (a : (tree' T))
    :tree_proj_010 a = snd (fst (tree'_tuple a)).
  Proof. destruct a; reflexivity. Qed.
  
  Lemma list_tree_proj_tuple_c {T} (tl : list (tree' T))
    :  list_Mmap tree_proj_010 tl = option_all (snd  (split(fst (split (map tree'_tuple tl))))).
  Proof.
    induction tl; auto.
    rewrite !snd_split, !fst_split, map_map in *.
    cbn [list_Mmap map].
    rewrite tree_proj_tuple_c, IHtl;
    reflexivity.
  Qed.

  Ltac option_match_comm :=
    lazymatch goal with
        |- context [match match ?ma with Some x => @?f x | None => ?y end with
                      | Some x' => @?f' x'
                      | None => ?y'
                      end] =>
          rewrite option_eta_equiv
          with (o := ma)
               (k:= fun c => match match c with Some x => f x | None => y end with
                      | Some x' => f' x'
                      | None => y'
                             end);
          cbv [option_eta]
      end.
  
  Lemma list_intersect'_get1 x is_rev hd tl
    :  map_elts_wf is_rev hd tl ->
       Mbind (get' x~1) (list_intersect'_pre_cbv hd is_rev tl)
      = @!let hd <- tree_proj_001 hd in
          let tl <- list_Mmap tree_proj_001 tl in
          (Mbind (get' x) (list_intersect'_pre_cbv hd is_rev tl)).
  Proof.
    destruct hd; cbn.
    all: rewrite ?tree'_tuple_un_k, ?hfin3_to_tuple_un_k.
    all: cbn.
    all: rewrite !gather_tries_spec; unfold gather_tries_simple; cbn.
    all: cbv [id].
    all: rewrite !option_all_rev.
    all: rewrite ?list_tree_proj_tuple_r.
    all: repeat rewrite ?fst_split, ?snd_split, ?map_map.
    all: try now (repeat case_match; auto).
    all: repeat change (match ?m with
                        | Some a => @?f a
                        | None => None
                        end)
      with (Mbind f m);
      rewrite !Mbind_option_map;
      basic_goal_prep.
    all:repeat (case_match; cbn; auto;
              autorewrite with utils in *;
              try rewrite !list_intersect_rev, !negb_involutive in *;
              rewrite ?map_elts_wf_rev, ?rev_involutive).
    all: try now (eapply tree'_tuple_right_elts_wf; eauto).
    all: try now (eapply tree'_tuple_left_elts_wf; eauto).
  Qed.

  
  Lemma list_intersect'_get0 x is_rev hd tl
    :  map_elts_wf is_rev hd tl ->
       Mbind (get' x~0) (list_intersect'_pre_cbv hd is_rev tl)
      = @!let hd <- tree_proj_100 hd in
          let tl <- list_Mmap tree_proj_100 tl in
          (Mbind (get' x) (list_intersect'_pre_cbv hd is_rev tl)).
  Proof.
    destruct hd; cbn.
    all: rewrite ?tree'_tuple_un_k, ?hfin3_to_tuple_un_k.
    all: cbn.
    all: rewrite !gather_tries_spec; unfold gather_tries_simple; cbn.
    all: cbv [id].
    all: rewrite !option_all_rev.
    all: try now (repeat case_match; auto).
    all: rewrite ?list_tree_proj_tuple_l.
    all: repeat rewrite ?fst_split, ?snd_split, ?map_map.
    all: try now (repeat case_match; auto).
    all: repeat change (match ?m with
                        | Some a => @?f a
                        | None => None
                        end)
      with (Mbind f m);
      rewrite !Mbind_option_map;
      basic_goal_prep.
    all:repeat (case_match; cbn; auto;
              autorewrite with utils in *;
              try rewrite !list_intersect_rev, !negb_involutive in *;
              rewrite ?map_elts_wf_rev, ?rev_involutive).
    all: try now (eapply tree'_tuple_right_elts_wf; eauto).
    all: try now (eapply tree'_tuple_left_elts_wf; eauto).
  Qed.

  
  Lemma list_intersect'_getxH is_rev hd tl
    :  map_elts_wf is_rev hd tl ->
       Mbind (get' 1) (list_intersect'_pre_cbv hd is_rev tl)
      = @!let hd <- tree_proj_010 hd in
          let tl <- list_Mmap tree_proj_010 tl in
          (elts_intersect (negb is_rev) hd tl).
  Proof.
    destruct hd; cbn.
    all: rewrite ?tree'_tuple_un_k, ?hfin3_to_tuple_un_k.
    all: cbn.
    all: rewrite !gather_tries_spec; unfold gather_tries_simple; cbn.
    all: cbv [id].
    all: rewrite !option_all_rev.
    all: try now (repeat case_match; auto).
    all: rewrite ?list_tree_proj_tuple_c.
    all: repeat rewrite ?fst_split, ?snd_split, ?map_map.
    all: repeat change (match ?m with
                        | Some a => @?f a
                        | None => None
                        end)
      with (Mbind f m);
      rewrite !Mbind_option_map;
      basic_goal_prep.
    all:repeat (case_match; cbn; auto;
              autorewrite with utils in *;
              try rewrite !list_intersect_rev, !negb_involutive in *;
                rewrite ?map_elts_wf_rev, ?rev_involutive).
    all: rewrite ? elts_intersect_rev in *; try congruence.
    all: try now (eapply tree'_tuple_center_elts_wf; eauto).
    all: try now (eapply tree'_tuple_left_elts_wf; eauto).
    all: try now (eapply tree'_tuple_right_elts_wf; eauto).
  Qed.

  
  Arguments get' {A}%type_scope !p%positive_scope !m.
  
  Lemma list_intersect_correct' x hd tl is_rev
    : map_elts_wf is_rev hd tl ->
      Mbind (get' x) (list_intersect' hd is_rev tl)
      = @!let hd' <- get' x hd in
          let tl' <- list_Mmap (get' x) tl in
          (elts_intersect (negb is_rev) hd' tl').
  Proof using elts_intersect_rev elts_wf_rev.
    change list_intersect' with list_intersect'_pre_cbv.
    revert hd is_rev tl.
    induction x; destruct hd; intros;
      basic_utils_crush.
    all: cbn [get'].
    all: try rewrite list_intersect'_get1 by auto.
    all: try rewrite list_intersect'_get0 by auto.
    all: try rewrite list_intersect'_getxH by auto.
    all: try (cbn; reflexivity).      
    all: cbn -[Mbind].
    all: change (Mbind ?f (Some ?v)) with (f v) in *.
    all: cbn beta.
    all: rewrite option_Mbind_comm;
      rewrite ?list_get'_1, ?list_get'_0;
      rewrite option_Mmap_Mmap, <- !option_Mbind_assoc;
      eapply Mbind_option_ext;
      intros.
    all: try (rewrite IHx by
             ((eapply tree'_tuple_right_elts_wf
               +eapply tree'_tuple_left_elts_wf); eauto; cbn;
         rewrite ?list_tree_proj_tuple_l, ?list_tree_proj_tuple_r,
           ?snd_split, ? fst_split, ?map_map in *;
              auto); rewrite option_Mbind_comm; reflexivity).
  Qed.
         
  Lemma option_all_Some A (l : list A) : option_all (map Some l) = Some l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma list_intersect_correct x hd tl
    : map_elts_wf false hd tl ->
      get x (otree (list_intersect hd tl))
      = @!let hd_x <- get' x hd in
          let tl_x <- list_Mmap (get' x) tl in
          (elts_intersect false hd_x (rev tl_x)).
  Proof.
    intro.
    unfold list_intersect, get, otree.
    etransitivity.
    {
      Unshelve.
      2: refine (_ (list_intersect' hd false tl)).
      2: intro x'; destruct x'; shelve.
      cbn.
      destruct (list_intersect' hd false tl); reflexivity.
    }
    cbn.
    repeat change (match ?m with
                   | Some a => @?f a
                   | None => None
                   end)
      with (Mbind f m).
    rewrite list_intersect_correct'; auto.
    eapply Mbind_option_ext; intros.
    repeat change (match ?m with
                   | Some a => @?f a
                   | None => None
                   end)
      with (Mbind f m).
    eapply Mbind_option_ext; intros.
    rewrite elts_intersect_rev; auto.
    eapply H in H1; eauto.
    eapply  elts_wf_rev; eauto.
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



    
