Require Import NArith Tries.Canonical Lists.List Sorting.Permutation.
Require Import Coq.Classes.Morphisms.
Require Ascii.
Import ListNotations.

From coqutil Require Import Map.Interface.

From Utils Require Import Utils Monad TrieMap.
Import Monad.StateMonad.



(*TODO: duplicated; move to Eqb or sim. location *)
#[export] Instance positive_Eqb : Eqb positive := Pos.eqb.

#[export] Instance positive_default : WithDefault positive := xH.


(*TODO: duplicated *)
#[local] Notation ne_list A := (A * list A)%type.


    
Lemma all2_len T1 T2 (R : T1 -> T2 -> Prop) l1 l2
  : all2 R l1 l2 -> length l1 = length l2.
Proof using.
  revert l2; induction l1; destruct l2;
    basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Resolve all2_len : utils.


Lemma all2_impl_l A B (R : A -> B -> Prop) P l1 l2
  : (forall x y, In x l1 -> In y l2 -> R x y -> P x) ->
    all2 R l1 l2 -> all P l1.
Proof.
  intro Himpl.
  enough (forall l1' l2', incl l1' l1 -> incl l2' l2 ->
                          all2 R l1' l2' -> all P l1')
    by eauto with utils.
  induction l1'; destruct l2';
    basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Resolve all2_impl_l : utils.

Lemma all2_impl_r A B (R : A -> B -> Prop) P l1 l2
  : (forall x y, In x l1 -> In y l2 -> R x y -> P y) ->
    all2 R l1 l2 -> all P l2.
Proof.
  intro Himpl.
  enough (forall l1' l2', incl l1' l1 -> incl l2' l2 ->
                          all2 R l1' l2' -> all P l2')
    by eauto with utils.
  induction l1'; destruct l2';
    basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Resolve all2_impl_r : utils.
    

Lemma filter_false_In:
  forall (B : Type) (f : B -> bool) (l : list B),
    (forall x : B, In x l -> f x = false) -> filter f l = [].
Proof using.
  intros.
  assert (exists l', incl l l' /\ forall x : B, In x l' -> f x = false)
    by (exists l; basic_utils_crush).
  clear H.
  destruct H0 as [l' [H0 ?] ].
  revert H0.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
  case_match; eauto.
  firstorder congruence.
Qed.



Lemma filter_true_In:
  forall (B : Type) (f : B -> bool) (l : list B),
    (forall x : B, In x l -> f x = true) -> filter f l = l.
Proof using .
  intros.
  assert (exists l', incl l l' /\ forall x : B, In x l' -> f x = true)
    by (exists l; basic_utils_crush).
  clear H.
  destruct H0 as [l' [H0 ?] ].
  revert H0.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
  case_match; try congruence.
  firstorder congruence.
Qed.


    
Lemma all_impl T (P Q : T -> Prop) l
  : (forall x, In x l -> P x -> Q x) -> all P l -> all Q l.
Proof.
  intros.
  assert (exists l', incl l l' /\ forall x : T, In x l' -> P x -> Q x)
    by (exists l; basic_utils_crush).
  clear H.
  destruct H1 as [l' [H1 ?] ].
  revert H0 H1.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
Qed.


(*TODO: move all to the right files *)

Lemma option_all_empty C (l : list (option C))
  : Some [] = option_all l <-> l = [].
Proof.
  induction l; 
    basic_goal_prep;
    repeat case_match;
    basic_utils_crush.
Qed.
Hint Rewrite option_all_empty : utils.

Hint Rewrite length_app : utils.

Lemma rev_eq_nil C (l : list C)
  : rev l = [] <-> l = [].
Proof. 
  induction l; 
    basic_goal_prep;
    basic_utils_crush.
  assert (length (rev l ++ [a]) = length (@nil C)) by congruence.
  cbn in *; basic_utils_crush.
  cbn in *; Lia.lia.
Qed.
Hint Rewrite rev_eq_nil : utils.

Hint Rewrite combine_nil : utils.


Lemma map_id C (l : list C)
  : map id l = l.
Proof using. unfold id; induction l; cbn; congruence. Qed.

Lemma Mbind_option_map A1 A2 A3 (f : A2 -> option A3) (g : A1 -> A2) ma
  : Mbind f (option_map g ma)
    = Mbind (fun a => f (g a)) ma.
Proof. destruct ma; reflexivity. Qed.
Hint Rewrite Mbind_option_map : utils.


Lemma all2_empty_r A1 A2 (R : A1 -> A2 -> Prop) l1
  : all2 R l1 [] <-> l1 = [].
Proof.
  destruct l1; basic_goal_prep; basic_utils_crush.
Qed.
Hint Rewrite all2_empty_r : utils.

Lemma all2_empty_l A1 A2 (R : A1 -> A2 -> Prop) l2
  : all2 R [] l2 <-> l2 = [].
  destruct l2; basic_goal_prep; basic_utils_crush.
Qed.
Hint Rewrite all2_empty_l : utils.


(*TODO: put this in utils?*)
#[local] Arguments combine_app [A B]%type_scope (lA lA' lB lB')%list_scope _.
#[local] Hint Rewrite combine_app : utils.

(*TODO: put this in utils *)
#[local] Hint Rewrite length_rev : utils.
    
Lemma rev_combine T1 T2 (l1: list T1) (l2 : list T2)
  : length l1 = length l2 ->
    rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof using.
  revert l2;
    induction l1;
    destruct l2;
    basic_goal_prep;
    basic_utils_crush.  
Qed.



Lemma Permutation_combine_l T1 T2 (l1 l1' : list T1) (l2 l2' : list T2)
  : length l1 = length l2 ->
    length l1' = length l2' ->
    Permutation (combine l1 l2) (combine l1' l2') ->
    Permutation l1 l1'.
Proof.
  intros.
  apply Permutation_map with (f:= fst) in H1.
  rewrite !map_combine_fst in * by eauto.
  auto.
Qed.

Lemma Permutation_combine_r T1 T2 (l1 l1' : list T1) (l2 l2' : list T2)
  : length l1 = length l2 ->
    length l1' = length l2' ->
    Permutation (combine l1 l2) (combine l1' l2') ->
    Permutation l2 l2'.
Proof.
  intros.
  apply Permutation_map with (f:= snd) in H1.
  rewrite !map_combine_snd in * by eauto.
  auto.
Qed.



Lemma hd_In [A] (d:A) l
  : In (hd d l) (d::l).
Proof. destruct l; basic_goal_prep; basic_utils_crush. Qed.


(*TODO: this is probably already defined somewhere. Move to utils and dedup.*)
Definition option_rel {X Y} (R : X -> Y -> Prop) mx my :=
  match mx, my with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.

Instance Mbind_Proper {T1 T2} {R : T1 -> _} {R' : option T2 -> _} `{Reflexive _ R'}
  : Proper ((R ==> R') ==> option_rel R ==> R') Mbind.
Proof.
  intros f1 f2 Hf x1 x2 Hx.
  unfold option_rel in *.
  destruct x1, x2; cbn in *; try reflexivity; try tauto.
  apply Hf; auto.
Qed.

(*TODO: add to utils?*)
#[local] Hint Immediate perm_swap : utils.

Instance list_Mmap_Permutation_Proper [A B] (f : A -> option B)
  : Proper (Permutation (A:=_) ==> option_rel (Permutation (A:=_))) (list_Mmap f).
Proof.
  unfold option_rel.
  intros l1 l2 Hp.
  induction Hp;
    basic_goal_prep;
    repeat case_match;
    basic_utils_crush.
  etransitivity; eauto.
Qed.


(*TODO: move these somewhere?*)
Section ListEta.
  Context {A B C D : Type}.

  Definition list_eta {R} (k : list A -> R) l :=
    match l with
    | [] => k []
    | (a::l') => k (a::l')
    end.

  Lemma list_eta_equiv R (k : list A -> R) o
    : k o = list_eta k o.
  Proof. destruct o; reflexivity. Qed.

End ListEta.


  


Section __.
  Context {A : Type}.
  Inductive pos_trie' :=
  | pos_trie_leaf (a:A)
  | pos_trie_node (m : PTree.tree' pos_trie').

  (*None is empty *)
  Definition pos_trie := option pos_trie'.

  Definition of_ptree (t : PTree.tree pos_trie') : pos_trie :=
    match t with
    | PTree.Empty => None
    | PTree.Nodes m => Some (pos_trie_node m)
    end.

  (*TODO: check for pre-computation optimizations *)
  (* Note: assumes the key is the right length. *)
  Fixpoint pt_get' pt k {struct k} : option A :=
    match pt, k with
    | pos_trie_leaf a, [] => Some a
    | pos_trie_node m, p::k' =>
        match PTree.get' p m with
        | Some pt' => pt_get' pt' k'
        | None => None
        end
    | _, _ => None        
    end.

  Definition pt_get pt k : option A :=
    match pt with    
    | None => None
    | Some pt => pt_get' pt k
    end.

  Fixpoint pt_singleton k v :=
    match k with
    | [] => pos_trie_leaf v
    | p::k' =>
        pos_trie_node (PTree.set0 p (pt_singleton k' v))
    end.
  
  Fixpoint pt_put' pt k v {struct k} :=
    match pt, k with
    | pos_trie_leaf _, _ => pos_trie_leaf v
    (*this case shouldn't happen:
        | pos_trie_leaf a, p::k' => _
     *)
    (*this case shouldn't happen *)
    | pos_trie_node m, [] => pos_trie_node m
    | pos_trie_node m, p::k' =>
        (* TODO: can do 1 traversal instead of 2*)
        match PTree.get' p m with
        | Some pt' => pos_trie_node (PTree.set' p (pt_put' pt' k' v) m)
        | None => pos_trie_node (PTree.set' p (pt_singleton k' v) m)
        end
    end.
  
  Definition pt_put pt k v :=
    match pt with
    | None => Some (pt_singleton k v)
    | Some pt => Some (pt_put' pt k v)
    end.
  
  Fixpoint pt_remove' pt k {struct k} :=
    match pt, k with
    | pos_trie_leaf _, _ => None
    (*this case shouldn't happen:
        | pos_trie_leaf a, p::k' => _
     *)
    (*this case shouldn't happen *)
    | pos_trie_node m, [] => None
    | pos_trie_node m, p::k' =>
        (* TODO: can do 1 traversal instead of 2*)
        match PTree.get' p m with
        | Some pt' =>
            match pt_remove' pt' k' with
            | None => of_ptree (PTree.remove' p m)
            | Some ptr => Some (pos_trie_node (PTree.set' p ptr m))
            end
        | None => Some (pos_trie_node m)
        end
    end.
  
  Definition pt_remove pt k :=
    match pt with
    | None => None
    | Some ptr => pt_remove' ptr k
    end.

  (*TODO: check; probably wrong
      TODO: can probably be made faster, if it's the bottleneck
   *)
  Fixpoint pt_fold' {R} (f : R -> _ -> _ -> R) (acc : R) pt stack : R :=
    match pt with
    | pos_trie_leaf a => f acc (rev stack) a
    | pos_trie_node m =>
        let f' acc p pt :=
          pt_fold' f acc pt (p::stack)
        in
        trie_fold' f' acc m 1
    end.

  Definition pt_fold {R} (f : R -> _ -> _ -> R) (acc : R) pt : R :=
    match pt with
    | None => acc
    | Some pt => pt_fold' f acc pt []
    end.
  
  (*TODO: temporary? *)
  #[export] Instance pos_trie_map : map.map (list positive) A :=
    {
      rep := pos_trie;
      get := pt_get;
      empty := None;
      put := pt_put;
      remove := pt_remove;
      fold _ := pt_fold;
    }.

  (* Helper function for projecting the inner map when we assume the node case.
     Should not be called on other cases.
   *)
  Definition proj_node_map' p : PTree.tree pos_trie' :=
    match p with
    | pos_trie_leaf a => PTree.Empty
    | pos_trie_node m => PTree.Nodes m
    end.
  
  Definition proj_node_map p : PTree.tree pos_trie' :=
    match p with
    | None => PTree.Empty
    | Some m => proj_node_map' m
    end.

  
  Definition proj_node_map_unchecked `{WithDefault A} p : PTree.tree' pos_trie' :=
    match p with
    | pos_trie_leaf a => PTree.Node010 (pos_trie_leaf default)
    | pos_trie_node m => m
    end.
  
  Section __.
    Context `{WithDefault A}.
    (*TODO: make this an option or no?*)
    Context (merge : A -> A -> A).

    (* assumes all elements of ptl are leaves *)
    Fixpoint leaf_intersect (a:A) ptl : A :=
      match ptl with
      | [] => a
      | (pos_trie_leaf a')::ptl' => leaf_intersect (merge a a') ptl'
      | (pos_trie_node _)::ptl' =>
          (*should never happen. Implementation just for proof convenience *)
          leaf_intersect a ptl'
      end.

    (*
      Definition leaf_intersect ptl : option A :=
      match ptl with
      | (pos_trie_leaf a)::ptl => Some (leaf_intersect' a ptl)
      | _ => None (*should never happen*)
      end.
     *)
    
    (*
      Challenge: what if the first trie has a false for the next var?
                         not so easy to invoke intersection.
                       More generally, how to intersect n spaced things?.
                       
      Algorithm: (assume all var lists have the same depth and match their tries)
      Project trie's from tries. If any empty, return empty.
      With n spaced trie's with empty var lists, invoke leaf_intersect.
      Else, partition tries into those with true next vars and false next vars.
      list_intersect the true next vars.
      TODO: does that make sense? not really, since there is no good way to deal with the children.


      Algorithm v2: "
      "
      Else, partition tries into those with true next vars and false/no next vars.
      If no trues, assume all tries are leaves, use leaf_intersect (sound if the tries cover the var set)
      else, call list_intersect' on the trues, with recursive call appending the false tries to its argument

      Question: is it enough to generlize list_intersect to work w/ elts_intersect : A -> list A -> option A?
      Seems like it might not be b/c of children list.

      Also, the performance is wrong if we eagerly intersect the subtries?
      No, that seems ok; we don't eagerly intersect them
     *)

    
    Variant partition_result :=
      | just_false_part (ci0 : list bool) (pt0 : pos_trie')
          (cil : list (list bool)) (ptl : list pos_trie')
      | have_true_part 
          (f_cil : list (list bool)) (f_ptl : list pos_trie')
          (t_ci0 : list bool) (t_pt0 : pos_trie')
          (t_cil : list (list bool)) (t_ptl : list pos_trie').
      
    Fixpoint partition_tries (cil : list (list bool)) (ptl : list pos_trie')
      (acc : partition_result) :=
      (* assume both lists have the same length *)
      match cil, ptl, acc with
      | [], [], _ => acc
      | (false::l1)::cil, pt::ptl,
        just_false_part ci0 pt0 other_cil other_tries =>
          partition_tries cil ptl
            (just_false_part l1 pt (ci0::other_cil) (pt0::other_tries))
      | (false::l1)::cil, pt::ptl,
        have_true_part other_cil other_tries t_ci0 t_pt0 true_cil true_tries =>
          partition_tries cil ptl
            (have_true_part (l1::other_cil) (pt::other_tries)
               t_ci0 t_pt0 true_cil true_tries) 
      | (true::l1)::cil, pt::ptl,
        just_false_part ci0 pt0 other_cil other_tries =>
          partition_tries cil ptl
            (have_true_part (ci0::other_cil) (pt0::other_tries)
               l1 pt [] [])
      | (true::l1)::cil, pt::ptl,
        have_true_part other_cil other_tries t_ci0 t_pt0 true_cil true_tries =>
          partition_tries cil ptl
            (have_true_part other_cil other_tries
               l1 pt (t_ci0 ::true_cil) (t_pt0::true_tries))
      | []::_, _, _ (* should never happen. Written separately for documentation *)
      | _, _, _ => acc (*mk4 default default default default*) (*should never happen *)
      end.

    Definition true_lists acc :=
      match acc with
      | just_false_part ci0 pt0 cil ptl => []
      | have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl => combine (t_ci0::t_cil) (t_pt0::t_ptl)
      end.

    Definition false_lists acc :=
      match acc with
      | just_false_part ci0 pt0 cil ptl => combine (ci0::cil) (pt0::ptl)
      | have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl => combine f_cil f_ptl
      end.
    
    Lemma partition_tries_true_lists' width cil ptl acc
      : width > 0 ->
        all (fun p => length p = width) cil ->
        length cil = length ptl ->
        true_lists (partition_tries cil ptl acc)
        = let l := combine cil ptl in
          let true_filter := rev (map (fun p => (tl (fst p), snd p))
                                    (filter (fun p => hd false (fst p)) l)) in
          true_filter ++ (true_lists acc).
    Proof.
      intro Hwidth.
      revert ptl acc;
        induction cil;
        destruct ptl;
        basic_goal_prep;
        repeat (case_match;
                basic_goal_prep);
        basic_utils_crush;
        try Lia.lia.
      {
        rewrite IHcil; eauto.
        basic_goal_prep.
        rewrite <- ! app_assoc.
        reflexivity.
      }
      {
        rewrite IHcil; eauto.
        basic_goal_prep.
        basic_utils_crush.
      }
    Qed.
    
    Lemma partition_tries_true_lists width cil ptl acc
      : all (fun p => length p = S width) cil ->
        length cil = length ptl ->
        true_lists (partition_tries cil ptl acc)
        = let l := combine cil ptl in
          let true_filter := rev (map (fun p => (tl (fst p), snd p))
                                    (filter (fun p => hd false (fst p)) l)) in
          true_filter ++ (true_lists acc).
    Proof.
      intros; eapply partition_tries_true_lists'; try eassumption.
      Lia.lia.
    Qed.
    
    Lemma partition_tries_false_lists' width cil ptl acc
      : width > 0 ->
        all (fun p => length p = width) cil ->
        length cil = length ptl ->
        false_lists (partition_tries cil ptl acc)
        = let l := combine cil ptl in
          let false_filter := rev (map (fun p => (tl (fst p), snd p))
                                     (filter (fun p => negb (hd false (fst p))) l)) in
          false_filter ++ (false_lists acc).
    Proof.
      intro Hwidth.
      revert ptl acc;
        induction cil;
        destruct ptl;
        basic_goal_prep;
        repeat (case_match;
                basic_goal_prep);
        basic_utils_crush;
        try Lia.lia.
      {
        rewrite IHcil; eauto.
        basic_goal_prep.
        rewrite <- ! app_assoc.
        cbn.
        reflexivity.
      }
      {
        rewrite IHcil; eauto.
        basic_goal_prep.
        rewrite <- ! app_assoc.
        cbn.
        reflexivity.
      }
    Qed.
    
    Lemma partition_tries_false_lists width cil ptl acc
      : all (fun p => length p = S width) cil ->
        length cil = length ptl ->
        false_lists (partition_tries cil ptl acc)
        = let l := combine cil ptl in
          let false_filter := rev (map (fun p => (tl (fst p), snd p))
                                     (filter (fun p => negb (hd false (fst p))) l)) in
          false_filter ++ (false_lists acc).
    Proof.
      intros; eapply partition_tries_false_lists'; try eassumption.
      Lia.lia.
    Qed.

    Instance default_partition_result : WithDefault partition_result :=
      just_false_part default (pos_trie_leaf default) default default.
    
    Definition partition_result_of_lists f t :=
      match t with
      | [] =>
          match f with
          | (fc0,fp0)::f =>
          let (t_c,t_p) := split t in
          let (f_c,f_p) := split f in
          just_false_part fc0 fp0 f_c f_p
          | _ => default (* shouldn't happen on valid inputs *)
          end
      | (tc0,tp0)::t =>
          let (t_c,t_p) := split t in
          let (f_c,f_p) := split f in
          have_true_part f_c f_p tc0 tp0 t_c t_p
      end.

    
    Fixpoint has_depth' (n : nat) (t : pos_trie') :=
      match n, t with
      | O, pos_trie_leaf _ => true
      | S n, pos_trie_node m =>
          map.forallb (fun k => has_depth' n) (PTree.Nodes m : TrieMap.trie_map _)
      | _, _ => false
      end.
    
    (*TODO: separate or combine the 2 conjuncts?*)
    Definition rectangular_trie_list width cil ptl :=
      all2 (fun c t => Is_true (has_depth' (length (filter id c)) t)
                          /\ length c = width) cil ptl.

    
    (* we expect the true tries to be one size deeper than the cis after a partition *)
    Definition offset_rectangular_trie_list width cil ptl :=
      all2 (fun c t => Is_true (has_depth' (S (length (filter id c))) t)
                          /\ length c = width) cil ptl.

    Definition partition_result_wf width acc :=
      match acc with
      | just_false_part ci0 pt0 cil ptl =>
          rectangular_trie_list width (ci0::cil) (pt0::ptl)
      | have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl =>
          offset_rectangular_trie_list width (t_ci0::t_cil) (t_pt0::t_ptl)
          /\ rectangular_trie_list width f_cil f_ptl
      end.

    
    
            
    Lemma partition_left_inverse width acc
      : partition_result_wf width acc ->
        partition_result_of_lists (false_lists acc) (true_lists acc) = acc.
    Proof.
      destruct acc; cbn;
        intros;
        rewrite !combine_split;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma partition_result_empty_true acc
      : true_lists acc = [] <-> exists fc fcl fp fpl, acc = just_false_part fc fp fcl fpl.
    Proof.
      destruct acc; split; basic_goal_prep;
        repeat eexists; try congruence.
      Unshelve.
      all: eauto.
    Qed.
    Hint Resolve partition_result_empty_true : utils.
    
    Lemma partition_result_empty_false acc
      : false_lists acc = []
        -> exists f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl,
          acc = have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl.
    Proof.
      destruct acc; repeat eexists; try congruence.
      basic_goal_prep; basic_utils_crush.
      Unshelve.
      all: eauto.
    Qed.
    
    Lemma partition_result_nonempty acc
      : true_lists acc = [] ->
        false_lists acc = [] ->
        False.
    Proof.
      destruct acc; cbn; congruence.
    Qed.
    Hint Resolve partition_result_nonempty : utils.

    
    Lemma partition_tries_wf width acc cil ptl
      : rectangular_trie_list (S width) cil ptl ->
        partition_result_wf width acc ->
        partition_result_wf width (partition_tries cil ptl acc).
    Proof.
      revert ptl acc;
        induction cil;
        destruct ptl;
        basic_goal_prep;
        repeat (case_match; basic_goal_prep);
        basic_utils_crush.
      all: apply IHcil.
      all: cbn; basic_utils_crush.
    Qed.
    Hint Resolve partition_tries_wf : utils.

    Lemma partition_tries_spec cil ptl acc width          
      : rectangular_trie_list (S width) cil ptl ->
        partition_result_wf width acc ->
        partition_tries cil ptl acc
        = let l := combine cil ptl in
          let true_filter := rev (map (fun p => (tl (fst p), snd p))
                                    (filter (fun p => hd false (fst p)) l)) in
          let false_filter := rev (map (fun p => (tl (fst p), snd p))
                                     (filter (fun p => negb (hd false (fst p))) l)) in
          
          partition_result_of_lists (false_filter ++ (false_lists acc))
            (true_filter ++ (true_lists acc)).
    Proof.
      intros.
      cbv [id].
      erewrite <- partition_left_inverse with (acc:=partition_tries cil ptl acc);
        eauto with utils.
      erewrite partition_tries_true_lists, partition_tries_false_lists.
      all: unfold rectangular_trie_list in *;
        basic_goal_prep; basic_utils_crush.
      all: eapply all2_impl_l; eauto.
      all: basic_goal_prep; intuition eauto.
    Qed.

    (*TODO: move to utils*)
    Hint Rewrite map_rev : utils.
    
    (*TODO: move to utils?*)
    Hint Rewrite map_app : utils.
    Hint Rewrite split_map : utils.

    (*
    Lemma partition_tries_correct cil ptl acc
      : partition_tries cil ptl acc = partition_tries_spec cil ptl acc.
    Proof.
      unfold partition_tries_spec.
      revert acc ptl;
        induction cil;
        destruct ptl, acc;
        basic_goal_prep; eauto.
      { repeat case_match; eauto. }
      {
        do 2 case_match; 
        basic_goal_prep;
        basic_utils_crush.
        all: rewrite IHcil;
          basic_goal_prep;
          basic_utils_crush.
        all: f_equal.
        all: rewrite <- app_assoc.
        all: reflexivity.
      }
    Qed.

    Definition partition_tries_spec' (cil : list (list bool)) (ptl : list pos_trie')
      (acc : quad _ _ _ _) :=
      let l := combine cil ptl in
      let true_filter := (map (fun p => (tl (fst p), snd p))
                                (filter (fun p => hd false (fst p)) l)) in
      let false_filter := (map (fun p => (tl (fst p), snd p))
                                 (filter (fun p => negb (hd false (fst p))) l)) in
      let (true_cil, true_tries) := split true_filter in
      let (false_cil, false_tries) := split false_filter in
      mk4 (true_cil++acc.(p41))
        (true_tries++acc.(p42))
        (false_cil++acc.(p43))
        (false_tries++acc.(p44)).

    
    (*TODO: actually a pointwise permutation *)
    Lemma partition_tries_correct' cil ptl acc
      : eq (partition_tries cil ptl acc) (partition_tries_spec' cil ptl acc).
    Proof.
    Admitted.
     *)
    
    
    Lemma filter_complement_permutation C (l : list C) f
      : Permutation (filter f l ++ filter (fun x => negb (f x)) l) l.
    Proof using.
      clear merge.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      case_match; cbn; eauto.
      change (a:: ?l) with ([a] ++ l).
      rewrite Permutation_app_comm.
      rewrite <- !app_assoc.
      apply Permutation_app_head.
      rewrite Permutation_app_comm.
      eauto.
    Qed.

    (*
    Lemma partition_tries_ptl_perm cil ptl acc out
      : Datatypes.length cil = Datatypes.length ptl ->
        partition_tries cil ptl acc = out ->
        Permutation (ptl ++ acc.(p42) ++ acc.(p44))
          (out.(p42) ++ out.(p44)).
    Proof.
      rewrite partition_tries_correct.
      unfold partition_tries_spec.
      repeat (basic_goal_prep;
              basic_utils_crush).
      rewrite !app_assoc.
      apply Permutation_app_tail.
      apply Permutation_sym.
      rewrite Permutation_app_comm.
      rewrite !app_assoc.
      apply Permutation_app_tail.
      rewrite <- rev_app_distr.
      rewrite <- !map_app.
      rewrite <- Permutation_rev.
      rewrite List.map_map; cbn.
      change (fun x => ?f x) with f.
      rewrite filter_complement_permutation.
      rewrite map_combine_snd; eauto.
    Qed.
     *)
    
    (* Fuel makes sense here since it is likely to be small (5-20)
       and makes the recursion much more convenient.
       Fuel must be more than the length of the lists in cil.

       takes in two cil lists and two ptl lists to avoid appending them
       in the recursive call.
       It's exactly two because we separate the trues and the falses.
       Assumes cil++cil', and ptl++ptl' are nonempty.
       Question: can I effectively encode the above assumption to reduce the function size?



     *)
    
    Fixpoint pt_spaced_intersect' fuel cil ptl (ci0 : list bool) cil' pt0 ptl'
      : option pos_trie' :=
      match fuel, ci0, pt0 with
      | S _, [], pos_trie_node _
      | O, _, _ => None (* should never happen*)
      (* assume all ci have the same length, all ptls are leaves in this branch *)
      | S fuel, [], pos_trie_leaf a =>
          Some (pos_trie_leaf (leaf_intersect (leaf_intersect a ptl) ptl'))
      | S fuel, ci0_hd::ci0_tl, _ =>
          let initial_part :=            
            if ci0_hd then have_true_part [] [] ci0_tl pt0 [] []
            else just_false_part ci0_tl pt0 [] []
          in
          let part := partition_tries cil' ptl'
                        (partition_tries cil ptl initial_part)
          in
          match part with
          | just_false_part ci0 pt0 other_cil other_tries =>
              pt_spaced_intersect' fuel other_cil other_tries ci0 [] pt0 []
          | have_true_part other_cil other_tries t_ci0 t_pt0 true_cil true_tries =>
              let true_cil_rev := rev true_cil in
              let pt_intersect :=
                (*TODO: change the interface for list_intersect to avoid assume_ne_list?*)
                list_intersect
                  (* reverse true_cil to match the order of the tries
                     passed by list_intersect*)
                  (fun is_forward =>
                     pt_spaced_intersect' fuel other_cil other_tries t_ci0
                       (if is_forward then true_cil else true_cil_rev))
                  (*TODO: avoid map? it's hard to avoid given the possibility of
                  leaf_intersect.
                   *)
                  (proj_node_map_unchecked t_pt0)
                  (map proj_node_map_unchecked true_tries)
              in
              option_map pos_trie_node pt_intersect
          end
      end.
    
    Definition pt_spaced_intersect (tries : ne_list (pos_trie * list bool)) : pos_trie :=
      (*This split has to happen at some point, so here is fine*)
      let '(ptl, cil) := split (snd tries) in
      let '(pt0, ci0) := fst tries in
      let fuel := S (length (hd [] cil)) in
      @!let pt0' <- pt0 in
        let ptl' <- list_Mmap id ptl in
        (pt_spaced_intersect' fuel cil ptl' ci0 [] pt0' []).
    
    Definition spaced_get x (p : list bool * pos_trie) : option A :=
      let key := map fst (filter snd (combine x (fst p))) in
      pt_get (snd p) key.

    Inductive depth' : pos_trie' -> nat -> Prop :=
    | leaf_depth a : depth' (pos_trie_leaf a) 0
    | node_depth m n
      : (forall k v, PTree.get' k m = Some v ->
                     depth' v n) ->
        depth' (pos_trie_node m) (S n).

    Definition depth t n :=
      match t with
      | Some t' => depth' t' n
      | None => True
      end.

    
    Definition has_depth n (t : pos_trie) :=
      match t with
      | None => true
      | Some x => has_depth' n x
      end.

    (*
    (* TODO: provably false (by example). figure out the bug *)
    Example pt_spaced_intersect'1_false
      : exists l p,
        depth' p (Datatypes.length (filter id l))
        /\ pt_spaced_intersect' (S (Datatypes.length l)) [l] [p] [] [] = Some p.
    Proof.
      exists [false; true].
      eexists.
      split.
      2: cbn.
      instantiate (1:=[false])

    (* TODO: provably false (by example). figure out the bug *)
    Example pt_spaced_intersect1 t l
      : depth t (length (filter id l)) -> pt_spaced_intersect [(t,l)] = t.
    Proof.
      unfold pt_spaced_intersect.
      basic_utils_crush.
      cbn -[pt_spaced_intersect'] in *.
      destruct t; eauto.
      cbn in H0.
      cbn.
      cbn [Mbind].
      cbn [map fst snd hd list_Mmap id].
      cbv[id].
      cbn -[pt_spaced_intersect'].
      destruct t; auto.
      revert p.
      induction l.
      {
        basic_goal_prep.
        destruct p; cbn; eauto.
        safe_invert H0.
      }
      cbn [pt_spaced_intersect'] in *.
      intros.
      rewrite !partition_tries_correct in *.
      unfold partition_tries_spec.
      cbn.
      (* TODO: why is the 2nd partition_tries becoming visible?*)
      basic_utils_crush.
      destruct a; cbn.
      2:{
        specialize (IHl p).
        apply IHl in H0.
        clear IHl.
        rewrite !partition_tries_correct in *.
        unfold partition_tries_spec in *.
        repeat (basic_goal_prep;
                basic_utils_crush).
        destruct l; cbn in *; eauto.
        destruct b; cbn in *; eauto.
        (*
        list_intersect'_correct
        destruct p; cbn in *; eauto.
        safe_invert H0.
        assert (exists k v, PTree.get' k m = Some v) by admit.
        break.
        pose proof H0.
        eapply H3 in H0.
        specialize (IHl x0).
        destruct l.*)
    Admitted.
     *)

   
    Hint Rewrite PeanoNat.Nat.min_id : utils.
    Hint Rewrite map_repeat : utils.

    
    Hint Rewrite rev_repeat : utils.

    
    Lemma repeat_default_hd C (x:C) n
      : hd x (repeat x n) = x.
    Proof.
      destruct n; reflexivity.
    Qed.
    Hint Rewrite repeat_default_hd : utils.

    
    Hint Rewrite firstn_all : utils.
    Hint Rewrite repeat_length : utils.

    Lemma tl_repeat C (x:C) n
      : tl (repeat x n) = repeat x (pred n).
    Proof.
      destruct n; reflexivity.
    Qed.
    Hint Rewrite tl_repeat : utils.


    
    Lemma combine_eq_nil C D (l1 : list C) (l2 : list D)
      : combine l1 l2 = [] <-> l1 = [] \/ l2 = [].
    Proof.
      destruct l1; cbn; try now intuition eauto.
      destruct l2; cbn; try now intuition eauto.
    Qed.
    Hint Rewrite combine_eq_nil : utils.

    Lemma app_eq_nil' : forall [A : Type] (l l' : list A), l ++ l' = [] <-> l = [] /\ l' = [].
    Proof.
      split; eauto using app_eq_nil.
      intuition subst.
      reflexivity.
    Qed.
    Hint Rewrite app_eq_nil' : utils.

    Lemma map_eq_nil' : forall [A B : Type] (f : A -> B) (l : list A), map f l = [] <-> l = [].
    Proof.
      split; eauto using map_eq_nil.
      intuition subst.
      reflexivity.
    Qed.
    Hint Rewrite map_eq_nil' : utils.

    Hint Rewrite length_zero_iff_nil : utils.

    
(*
    Lemma filter_eq_nil : forall [A : Type] (f : A -> bool) (l : list A), filter f l = [] <-> l = [].
    Proof. Abort. (*FALSE!*)
    Hint Rewrite filter_eq_nil : utils.
 *)

    (*
    
     (* A simpler version to serve as an intermediate step, removing the double lists *)
    Fixpoint pt_spaced_intersect'_simple fuel l
      : option pos_trie' :=
      match fuel with
      | O => None (* should never happen*)
      | S fuel =>
          let (true_cil, true_tries, other_cil, other_tries) :=
            partition_tries_spec (map fst l) (map snd l) (mk4 [] [] [] []) in
          match true_tries with
          | [] =>
              if hd [] other_cil then option_map pos_trie_leaf (leaf_intersect other_tries)
              else pt_spaced_intersect'_simple fuel (combine other_cil other_tries)
          | pt1::true_tries =>
              option_map pos_trie_node
                (list_intersect'
                   (fun true_tries => pt_spaced_intersect'_simple fuel
                                        (combine (other_cil++true_cil) (other_tries++true_tries)))
                   (proj_node_map_unchecked pt1)
                   (map proj_node_map_unchecked true_tries))
          end
      end.
*)

    Hint Rewrite filter_app : utils.

    (*TODO: why isn't this in utils?*)
    #[local] Hint Rewrite invert_eq_cons_nil : utils.
    Lemma rectangular_trie_list_nil_cons width pt ptl
      : rectangular_trie_list width [] (pt::ptl) <-> False.
    Proof using. clear merge. prove_inversion_lemma. Qed.
    Hint Rewrite rectangular_trie_list_nil_cons : utils.
    
    Lemma rectangular_trie_list_cons_nil width ci cil
      : rectangular_trie_list width (ci::cil) [] <-> False.
    Proof using. clear merge. prove_inversion_lemma. Qed.
    Hint Rewrite rectangular_trie_list_cons_nil : utils.
    
    Lemma rectangular_trie_list_cons_cons width ci cil pt ptl
      : rectangular_trie_list width (ci::cil) (pt::ptl)
        <-> length ci = width
            /\  Is_true (has_depth' (length (filter id ci)) pt)
            /\ rectangular_trie_list width cil ptl.
    Proof. clear merge. prove_inversion_lemma. Qed.
    Hint Rewrite rectangular_trie_list_cons_cons : utils.

    Lemma rectangular_trie_list_app width cil1 cil2 ptl1 ptl2
      : rectangular_trie_list width cil1 ptl1 ->
        rectangular_trie_list width cil2 ptl2 ->
        rectangular_trie_list width (cil1++cil2) (ptl1++ptl2).
    Proof.
      unfold rectangular_trie_list.
      autorewrite with utils.
      intuition eauto using all2_app.
    Qed.      
      
    Lemma partition_tries_0 cil2 ptl2 acc
      : rectangular_trie_list 0 cil2 ptl2 ->
        partition_tries cil2 ptl2 acc = acc.
    Proof using.
      clear merge.
      unfold rectangular_trie_list.
      revert ptl2 acc.
      induction cil2;
        destruct ptl2;
        repeat (repeat(basic_goal_prep;
                       try case_match);
                basic_utils_crush).
    Qed.     

    Lemma partition_tries_app width cil1 cil2 ptl1 ptl2 acc
      : rectangular_trie_list width cil1 ptl1 ->
        rectangular_trie_list width cil2 ptl2 ->
        partition_tries cil2 ptl2 (partition_tries cil1 ptl1 acc)
        = partition_tries (cil1++cil2) (ptl1++ptl2) acc.
    Proof.
      intros H1 H2; revert ptl1 acc H1.
      induction cil1;
        destruct ptl1;
        repeat (repeat(basic_goal_prep;
                       try case_match);
                basic_utils_crush).
      apply partition_tries_0; auto.
    Qed.
    
    
    Definition merge_list l :=
      match l with
      | [] => None
      | e::es => Some (List.fold_left merge es e)
      end.

    
    Lemma Mbind_option_ext T1 T2 (f g : T1 -> option T2) ma
      : (forall a, ma = Some a -> f a = g a) ->
        Mbind f ma = Mbind g ma.
    Proof. destruct ma; cbn in *; firstorder congruence. Qed.

    
    (* should be a part of Monad_ok at some point*)
    Lemma option_Mbind_assoc T1 T2 T3 (f : T1 -> option T2) (g : T2 -> option T3) ma
      : Mbind (fun a => Mbind g (f a)) ma = Mbind g (Mbind f ma).
    Proof.
      destruct ma; cbn; eauto.
    Qed.
    
    Lemma otree_get_Mbind T k (ma : option (PTree.tree' T))
      : Mbind (PTree.get' k) ma = PTree.get k (otree ma).
    Proof. destruct ma; reflexivity. Qed.

    
    Hint Rewrite rev_length : utils.

    
    (*TODO: move to TrieMap.v*)    
    Lemma invert_eq_mk4 W X Y Z (w w':W) (x x':X) (y y' : Y) (z z' : Z)
      : mk4 w x y z = mk4 w' x' y' z' <-> w = w' /\ x = x' /\ y = y' /\ z = z'.
    Proof. prove_inversion_lemma. Qed.
    #[local] Hint Rewrite invert_eq_mk4 : utils.

    Hint Rewrite rev_unit : utils.
    
    Lemma map_combine T1 T2 T3 T4 (f : T1 -> T2) (g : T3 -> T4) l1 l2
      : map (pair_map f g) (combine l1 l2) = (combine (map f l1) (map g l2)).
    Proof using.
      clear merge.
      revert l2;
        induction l1;
        destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    (*TODO: move to Utils*)
    Definition nonempty {A} (l:list A) :=
      if l then False else True.    
    Definition empty {A} (l:list A) :=
      if l then True else False.

    (*
    Lemma partition_tries_spec_properties_empty cil ptl
      true_cil true_tries other_cil other_tries
      : Datatypes.length cil = Datatypes.length ptl ->
        mk4 true_cil true_tries other_cil other_tries
          = partition_tries_spec cil ptl (mk4 [] [] [] []) ->
          all empty cil ->
          let others := combine other_cil other_tries in
          true_cil = []
          /\ true_tries = []
          /\ Permutation (combine cil ptl) others
          /\ length other_cil = length other_tries.
    Proof.
      unfold partition_tries_spec.
      autorewrite with bool utils.
      intros H0 H'; break; subst.
      autorewrite with bool utils.
      rewrite !List.map_map.
      cbn.
      revert ptl H0;
        induction cil;
        destruct ptl;
        basic_goal_prep;
        try now basic_utils_crush.
      destruct a;
        basic_goal_prep;
        basic_utils_crush.
      1,2:rewrite !filter_false_In; eauto;
      basic_goal_prep;
      apply in_combine_l in H3;
      eapply in_all in H3; eauto.
      1,2: destruct l; cbn in *; tauto.
      cbn [combine].
      rewrite Permutation_app_comm.
      cbn.
      constructor.
      rewrite <- rev_combine.
      2:{
        autorewrite with bool utils.
        auto.
      }
      rewrite <- Permutation_rev.
      rewrite !filter_true_In.
      2:{
        basic_goal_prep;
        apply in_combine_l in H3;
        eapply in_all in H3; eauto.
        destruct l; cbn in *; tauto.
      }
      rewrite <- List.map_map.
      rewrite map_combine_fst, map_combine_snd by eauto.
      rewrite map_ext_in with (g:=id).
      2:{
        basic_goal_prep.
        eapply in_all in H2; eauto.
        destruct a; cbn in *; tauto.
      }
      rewrite map_id.
      reflexivity.
    Qed.
     *)

     
    Definition spaced_get1 x (b : bool) m : option _ :=
      if b then PTree.get' x m else Some (pos_trie_node m).

    Definition get_leaf t :=
      match t with
      | pos_trie_leaf a => Some a
      | pos_trie_node m => None
      end.
    
    Definition get_leaf_unchecked t :=
      match t with
      | pos_trie_leaf a => a
      | pos_trie_node _ => default
      end.      

    Definition get_map t :=
      match t with
      | pos_trie_leaf a => None
      | pos_trie_node m => Some m
      end.      


    Fixpoint spaced_get' x : list bool * pos_trie' -> option A :=
      match x with
      (* assumes list is also empty*)
      | [] => fun p => get_leaf (snd p)
      (*TODO: get the mbind outside the fun somehow?*)
      | n::x => fun p =>
                  @!let t' <- spaced_get1 n (hd false (fst p)) (proj_node_map_unchecked (snd p)) in
                    (spaced_get' x (tl (fst p), t'))       
      end.

    (*TODO: replace spaced_get w/ this?*)
    Definition spaced_get_ x (p : list bool * pos_trie) : option A :=
      Mbind (spaced_get' x) (option_map (fun t => (fst p, t)) (snd p)).

    Definition zip_bools (l : list _) :=
      List.fold_left
        (fun acc l => map2 orb (combine l acc))
        (tl l)
        (hd [] l).

    (*TODO: add to monad laws*)
    Lemma option_Mbind_Mret T (ma : option T)
      : Mbind Mret ma = ma.
    Proof. destruct ma; reflexivity. Qed.
    Hint Rewrite option_Mbind_Mret : utils.
    
    Lemma option_Mbind_Mret' T1 T2 (f : T1 -> option T2) a
      : Mbind f (Mret a) = f a.
    Proof. reflexivity. Qed.
    Hint Rewrite option_Mbind_Mret' : utils.


    
    Lemma list_Mmap_None T1 T2 (f : T1 -> option T2) l
      : None = list_Mmap f l ->
        exists x, In x l /\ f x = None.
    Proof.
      induction l;
        repeat (cbn; try case_match);       
        basic_goal_prep;
        basic_utils_crush.
    Qed.      
    
    Lemma leaf_intersect_correct a l
      : all (fun t => Is_true (has_depth' 0 t)) l ->
        leaf_intersect a l
        = fold_left merge (map get_leaf_unchecked l) a.
    Proof.
      revert a.
      induction l;
        basic_goal_prep;
        repeat case_match;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    Instance all_Permutation_Proper {T P} : Proper (@Permutation T ==> iff) (all P).
    Proof.
      intros l1 l2.
      induction 1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Lemma all2_impl T1 T2 (R R' : T1 -> T2 -> Prop) l1 l2
      : (forall x y, In (x,y) (combine l1 l2) -> R x y -> R' x y) ->
        all2 R l1 l2 -> all2 R' l1 l2.
    Proof.
      revert l2; induction l1; destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma all_all2_r T1 T2 (P : T2 -> Prop) l1 l2
      : all2 (fun _ : T1 => P) l1 l2 -> all P l2.
    Proof.
      revert l2; induction l1; destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    

    Lemma merge_list_fold_left l
      : let m' a b := match a with None => Some b | Some a => Some (merge a b) end in
        merge_list l = fold_left m' l None.
    Proof.
      unfold merge_list.
      destruct l; cbn; auto.
      revert a.
      induction l;
        try case_match;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Instance option_all_Permutation_Proper {T}
      : Proper (@Permutation _ ==> option_rel (@Permutation T)) option_all.
    Proof.
      intros x y Hp.
      unfold option_rel.
      induction Hp.
      { cbn; reflexivity. }
      {
        revert IHHp; cbn.
        repeat (case_match;cbn);
          basic_goal_prep;
          basic_utils_crush.
      }
      {
        repeat (case_match; subst; cbn in * );
          basic_goal_prep;
          basic_utils_crush.
      }
      {
        revert IHHp1 IHHp2; cbn.
        repeat (case_match;cbn);
          basic_goal_prep;
          basic_utils_crush.
        rewrite IHHp1.
        auto.
      }
    Qed.
    
    Context (merge_comm : forall a b, merge a b = merge b a).
    Context (merge_assoc : forall a b c, merge a (merge b c) = merge (merge a b) c).
  
    Lemma merge_n_opt_Permutation x y
      : Permutation x y ->
        let m' a b := match a with None => Some b | Some a => Some (merge a b) end in
        fold_left m' x None
        = fold_left m' y None.
    Proof.
      intro Hp.
      generalize dependent (@None A).
      induction Hp;
        basic_goal_prep;
        basic_utils_crush.
      all:subst m'.
      all:basic_goal_prep.
      all: try case_match;
        basic_goal_prep;
        basic_utils_crush.
      all: congruence.
    Qed.
    
    
    Instance merge_list_Proper
      : Proper (@Permutation _ ==> eq) merge_list.
    Proof.
      intros x y Hp.
      rewrite !merge_list_fold_left.
      apply merge_n_opt_Permutation; auto.
    Qed.

    
    
    Lemma all_app T (P : T -> Prop) l1 l2
      : all P (l1++l2) <-> all P l1 /\ all P l2.
    Proof.
      induction l1; 
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite all_app : utils.


    (* Note: probably not provable for an arbitrary monad
       without funext.
     *)
    Lemma list_Mfoldl_map_option T1 T2 T3
      (f : T1 -> T2 -> option T1)
      (g : T3 -> T2) l acc
      : list_Mfoldl f (map g l) acc
        = list_Mfoldl (fun acc x => f acc (g x)) l acc.
    Proof using.
      revert acc;
        induction l;
        basic_goal_prep;
        try case_match;
        basic_utils_crush.
    Qed.

    
    Lemma list_Mfoldl_option_map T1 T2 T3
      (f : T1 -> T2 -> T1)
      (g : T3 -> option T2) l a
      : option_map (fun l => fold_left f l a)
          (list_Mmap g l)
        = list_Mfoldl (fun acc x => option_map (f acc) (g x)) l a.
    Proof.
      revert a;
        induction l;
        basic_goal_prep;
        repeat case_match;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma get_leaf_is_unchecked pt
      : Is_true (has_depth' 0 pt) ->
        get_leaf pt = Some (get_leaf_unchecked pt).
    Proof using.
      destruct pt;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    Lemma map_get_leaf_is_unchecked ptl
      : all (fun t => Is_true (has_depth' 0 t)) ptl ->
        (list_Mmap get_leaf ptl)
        = Some (map get_leaf_unchecked ptl).
    Proof using.
      induction ptl;
        basic_goal_prep;
        rewrite ?get_leaf_is_unchecked;
        basic_goal_prep;
        basic_utils_crush.
      rewrite H2.
      reflexivity.
    Qed.

    Section __.
      Context T (f : T -> T -> T)
        (f_associative : forall a b c, f (f a b) c = f a (f b c))
        (f_commutative : forall a b, f a b = f b a).
      
      Lemma fold_left_Permutation_Proper
        : Proper ((Permutation (A:=_)) ==> eq ==> eq) (fold_left f).
      Proof.
        intros l l' HP.
        induction HP;
          cbv [respectful] in *;
          basic_goal_prep;
          basic_utils_crush.
        { congruence. }
        { erewrite IHHP1; eauto. }
      Qed.

      Lemma fold_left_permuted a1 a2 l1 l2
        : Permutation (a1::l1) (a2::l2) ->
          fold_left f l1 a1 = fold_left f l2 a2.
      Proof.
        remember (a1 :: l1) as l1'.
        remember (a2 :: l2) as l2'.
        intro HP.
        revert a1 l1 Heql1' a2 l2 Heql2'.
        induction HP;
          basic_goal_prep;
          basic_utils_crush.
        { apply fold_left_Permutation_Proper; auto. }
        {
          cbn.
          congruence.
        }
        {
          destruct l'.
          {
            apply Permutation_nil in HP2;
              congruence.
          }
          erewrite IHHP1, IHHP2; eauto.
        }
      Qed.

      Lemma map2_commutative : forall a b, map2 f (combine a b) = map2 f (combine b a).
      Proof.
        induction a; destruct b;
          basic_goal_prep;
          basic_utils_crush;
          congruence.
      Qed.
      
      
      Lemma map2_associative
        : forall a b c,
          map2 f (combine c (map2 f (combine b a)))
          = map2 f (combine (map2 f (combine c b)) a).
      Proof.
        induction a; destruct b, c;
          basic_goal_prep;
          basic_utils_crush;
          congruence.
      Qed.
      
    End __.
    
    Instance zip_bools_Permutation_Proper : Proper ((Permutation (A:=_)) ==> eq) zip_bools.
    Proof.
      unfold zip_bools.
      intros l l' HP.
      destruct l, l';
        basic_goal_prep;
        basic_utils_crush.
      {
        apply Permutation_nil in HP;
          congruence.
      }
      {
        symmetry in HP;
        apply Permutation_nil in HP;
          congruence.
      }
      {
        apply fold_left_permuted; eauto.
        {
          apply map2_associative.
          destruct a, b, c; reflexivity.
        }
        {
          intros.
          apply map2_commutative.
          destruct a0, b0; reflexivity.
        }
      }
    Qed.

    Lemma zip_bools_map_cons b l
      : l <> [] -> zip_bools (map (cons b) l) = b::(zip_bools l).
    Proof.
      unfold zip_bools.
      destruct l;
        try congruence.
      intros _.
      cbn [tl hd map].
      revert l.
      induction l0;
        basic_goal_prep;
        basic_utils_crush.
      rewrite orb_diag.
      congruence.
    Qed.
    
    Instance leaf_intersect_Permutation_Proper
      : Proper (eq ==> Permutation (A:=_) ==> eq)
          leaf_intersect.
    Proof.
      intros a a' ?; subst a'.
      intros l1 l2 HP.
      revert a.
      induction HP; basic_goal_prep;
        repeat case_match;
        basic_utils_crush;
        congruence.
    Qed.

    
    Definition part_res_Perm pr1 pr2 :=
      match pr1, pr2 with
      | just_false_part ci0 pt0 cil ptl,
        just_false_part ci0' pt0' cil' ptl' =>
          Permutation ((ci0,pt0)::(combine cil ptl))
            ((ci0',pt0')::(combine cil' ptl'))
      | have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl,
        have_true_part f_cil' f_ptl' t_ci0' t_pt0' t_cil' t_ptl' =>
          Permutation (combine f_cil f_ptl)
               (combine f_cil' f_ptl')
          /\ Permutation ((t_ci0,t_pt0)::(combine t_cil t_ptl))
               ((t_ci0',t_pt0')::(combine t_cil' t_ptl'))
      | _,_ => False
      end.

    Instance part_res_Perm_Reflexive : Reflexive part_res_Perm.
    Proof.
      intros a;
        destruct a;
        cbn;
        intuition eauto.
    Qed.

    Record pr_tuple :=
      {
        f_cil : list (list bool);
        f_ptl : list pos_trie';
        t_cil : list (list bool);
        t_ptl : list pos_trie';
      }.

    Definition pr_to_tuple pr :=
      match pr with
      | just_false_part ci0 pt0 cil ptl =>
          Build_pr_tuple (ci0::cil) (pt0::ptl) [] []
      | have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl => 
          Build_pr_tuple f_cil f_ptl (t_ci0::t_cil) (t_pt0::t_ptl)
      end.

    (*
    Lemma partition_tries_spec'
      : let acc_t := pr_t_tuple acc in
        let pt_t := partition_tries cil ptl acc in
        Permutation (combine pt_t.(f_cil) pt_t.(f_ptl))
          (combine f_cil' t_ptl')
        /\ Permutation (combine f_cil t_ptl)
             (combine f_cil' t_ptl')
      match partition_tries cil ptl acc, acc with
      | just_false_part ci0 pt0 cil ptl,
        just_false_part ci0' pt0' cil' ptl' =>
          ci0 = ci0'
          /\ pt0 = pt0'
          /\ Permutation (combine cil ptl)
                         (combine cil' ptl')
      | have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl,
        have_true_part f_cil' f_ptl' t_ci0' t_pt0' t_cil' t_ptl' =>
          t_ci0 = t_ci0'
          /\ t_pt0 = t_pt0'
          /\ Permutation (combine f_cil t_ptl)
                         (combine f_cil' t_ptl')
          /\ Permutation (combine t_cil t_ptl)
               (combine t_cil' t_ptl')
      | _,_ => False
      end.
        |
     *)

    Lemma Permutation_nil_cons_iff:
      forall [A : Type] (l : list A) (x : A), Permutation [] (x :: l) <-> False.
    Proof.
      intuition auto.
      eapply Permutation_nil_cons; eauto.
    Qed.
    Hint Rewrite Permutation_nil_cons_iff : utils.

    
    Lemma Permutation_cons_nil_iff:
      forall [A : Type] (l : list A) (x : A), Permutation (x :: l) [] <-> False.
    Proof.
      intuition auto.
      symmetry in H0.
      eapply Permutation_nil_cons; eauto.
    Qed.
    Hint Rewrite Permutation_cons_nil_iff : utils.

    Lemma combine_fst_snd [T1 T2] (x : list (T1 * T2)) 
      :  combine (map fst x) (map snd x) = x.
    Proof.
      induction x; 
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    Instance partition_result_of_lists_Perm
      : Proper (Permutation (A:=_) ==> (Permutation (A:=_)) ==> part_res_Perm)
          partition_result_of_lists.
    Proof.
      intros ? ? ? ? ? ?.
      unfold partition_result_of_lists, part_res_Perm.
      repeat case_match;
        basic_goal_prep;
        autorewrite with utils in *;
        intuition (subst; eauto);
        rewrite !combine_fst_snd;
        auto.
    Qed.

    Instance Permutation_filter'
      : forall (A : Type) (f : A -> bool),
        Proper (Permutation (A:=A) ==> Permutation (A:=_)) (filter f).
    Proof.
      intros A' f.
      intros l1 l2 HP.
      induction HP;
        basic_goal_prep;
        repeat (case_match; basic_goal_prep);
        basic_utils_crush.
      rewrite IHHP1.
      eauto.
    Qed.

    
    
    Instance false_lists_Perm
      : Proper (part_res_Perm ==> (Permutation (A:=_)))
          false_lists.
    Proof.
      intros acc1 acc2 HP.
      destruct acc1, acc2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    
    Instance true_lists_Perm
      : Proper (part_res_Perm ==> (Permutation (A:=_)))
          true_lists.
    Proof.
      intros acc1 acc2 HP.
      destruct acc1, acc2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    

    Hint Resolve all2_len : utils.

    Lemma partition_tries_Permutation cil ptl cil' ptl' acc acc' width
      : rectangular_trie_list (S width) cil ptl ->
        (*TODO: derivable from other assumptions*)
        rectangular_trie_list (S width) cil' ptl' ->
        partition_result_wf width acc ->
        partition_result_wf width acc' ->
        Permutation (combine cil ptl) (combine cil' ptl') ->
        part_res_Perm acc acc' ->
        part_res_Perm (partition_tries cil ptl acc) (partition_tries cil' ptl' acc').
    Proof.
      unfold rectangular_trie_list.
      intros ? ? ? Hacc Hacc' HP.
      erewrite <- partition_left_inverse
        with (acc:=(partition_tries cil ptl acc))
        by eauto with utils.
      erewrite <- partition_left_inverse
        with (acc:=(partition_tries cil' ptl' acc'))
        by eauto with utils.
      erewrite !partition_tries_false_lists,
        !partition_tries_true_lists;
        basic_utils_crush.
      
      all: [>| eapply all2_impl_l; eauto; basic_goal_prep; now intuition eauto..].
      apply partition_result_of_lists_Perm.
      all:rewrite <- !Permutation_rev.
      all: rewrite ?HP, ?Hacc'; apply Permutation_app; eauto.
    Qed.      

    (*
    Lemma pt_spaced_intersect_Permutation fuel f_cil f_ptl t_ci0 t_cil
      : Proper (Permutation (A:=_) =2=> Permutation (A:=_) ==> eq)
           (pt_spaced_intersect' fuel f_cil f_ptl t_ci0 t_cil).
    Proof.
      revert f_cil f_ptl t_ci0 t_cil.
      induction fuel;
        intros;
        intros ? ? ? ptl1 ptl2 HP;
        basic_goal_prep;
        basic_utils_crush.
      repeat case_match; eauto.
      {
        rewrite HP.
        reflexivity.
      }
      {
        TODO: false!
                   t_cil needs to be permuted with ptl!
        TODO: partition_tries permutation
      }
     *)

    Lemma all_rev_iff [T] [P : T -> Prop] l
      : all P (rev l) <-> all P l.
    Proof.
      rewrite <- Permutation_rev.
      reflexivity.
    Qed.
    Hint Rewrite all_rev_iff : utils.

    
    Lemma all2_rev [T1 T2] [R : T1 -> T2 -> Prop] l1 l2
      : all2 R l1 l2 -> all2 R (rev l1) (rev l2).
    Proof.
      revert l2;
        induction l1;
        destruct l2;
        basic_goal_prep;
        basic_utils_crush.
      apply all2_app; eauto.
      cbn.
      tauto.
    Qed.
      
    Lemma all2_rev_iff [T1 T2] [R : T1 -> T2 -> Prop] l1 l2
      : all2 R (rev l1) (rev l2) <-> all2 R l1 l2.
    Proof.
      split; eauto using all2_rev.
      rewrite <- rev_involutive with (l:= l1).
      rewrite <- rev_involutive with (l:= l2).
      intros.
      apply all2_rev.
      rewrite !rev_involutive in *; auto.
    Qed.
    Hint Rewrite all2_rev_iff : utils.
    
    Lemma rectangular_trie_list_rev_iff width t_cil l
      : rectangular_trie_list width (rev t_cil) (rev l)
        <-> rectangular_trie_list width t_cil l.
    Proof.
      unfold rectangular_trie_list;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite rectangular_trie_list_rev_iff : utils.

    
    Definition leaf_intersect_uncons l :=
      match l with
      | cons (pos_trie_leaf a) l => leaf_intersect a l
      | _ => default
      end.    

    Instance part_res_Perm_Trans : Transitive part_res_Perm.
    Proof.
      unfold part_res_Perm, Transitive;
        repeat (basic_goal_prep; try case_match);
        basic_utils_crush.
      { rewrite H0, H1; auto. }
      { rewrite H0, H1; auto. }
      { rewrite H3, H2; auto. }
    Qed.
    
    (*TODO: how to make a lemma that cares about which permutation?*)
    (*
    Lemma list_intersect_Perm
      : forall (p : Permutation (x::l) (x'::l')),
        (forall is_rev x l x' l' (p' : Permutation (x::l) (x'::l')),
            SamePermutation p p' ->
            f is_rev x l = g is_rev x' l') ->
        list_intersect f x l
        = list_intersect g x' l'.


(*TODO: too restrictive? we can have the same permutation 2 different ways...*)
Inductive SamePermutation {A B}
  : forall [l1 l2 : list A], Permutation l1 l2 ->
                             forall [l1' l2' : list B], Permutation l1' l2' -> Prop :=
| same_perm_nil : SamePermutation (perm_nil _) (perm_nil _)
| same_perm_skip x l1 l2 (p : Permutation l1 l2) x' l1' l2' (p' : Permutation l1' l2')
  : SamePermutation p p' -> SamePermutation (perm_skip x p) (perm_skip x' p')
| same_perm_swap (x y : A) (l : list A)
    (x' y' : B) (l' : list B)
  : SamePermutation (perm_swap x y l) (perm_swap x' y' l')
| same_perm_trans

  match p1, p2 with
  | perm_nil _, perm_nil _ => True
  | perm_skip x x0, perm_skip x1 x01 =>
      same_permutation x0 x01
  | perm_swap _ _ _, perm_swap _ _ _ => True
  | perm_trans x x0, perm_trans x1 x01 =>
      same_permutation x x1
      /\ same_permutation x0 x01
  | _, _ => False
  end.
     *)

    
      (*
    Lemma list_intersect'_Perm_combined D B C (x:PTree.tree' D) l x' l' (f g : _ -> _ -> _ -> _ -> _ -> option (PTree.tree' C))
      (c : B) cl c' cl' is_rev
      : Permutation (combine (c::cl) (x::l)) (combine (c'::cl') (x'::l')) ->
      (forall is_rev x l x' l'  c cl c' cl',
            Permutation (combine (c::cl) (x::l)) (combine (c'::cl') (x'::l')) ->
            f c cl is_rev x l = g c' cl' is_rev x' l') ->
        list_intersect' (f c cl) x is_rev l
        = list_intersect' (g c' cl') x' is_rev l'.
    Proof.
      intros.
      otree
      apply PTree.extensionality.
      option_ext
      map.map_ext
      TODO: map_ext
              pose proof (list_intersect_correct' _ _
       *)

    
    Lemma otree_injective B (a b : option (PTree.tree' B))
      : otree a = otree b -> a = b.
    Proof.
      destruct a,b; cbn; congruence.
    Qed.

    (*TODO: how to make a lemma that cares about which permutation?*)
    Lemma list_intersect_Perm_combined D B C (x:PTree.tree' D) l x' l' (f g : _ -> _ -> _ -> _ -> option (PTree.tree' C))
      (c : B) cl c' cl'
      : Permutation (combine (c::cl) (x::l)) (combine (c'::cl') (x'::l')) ->
      (forall x l x' l'  c cl c' cl',
            Permutation (combine (c::cl) (x::l)) (combine (c'::cl') (x'::l')) ->
            f c cl x l = g c' cl' x' l') ->
        list_intersect (fun is_forward : bool => f c (if is_forward then cl else rev cl)) x l
        = list_intersect (fun is_forward : bool => g c' (if is_forward then cl' else rev cl')) x' l'.
    Proof.
      intros H' Hext.
      apply otree_injective.
      apply PTree.extensionality.
      intros.
      rewrite !list_intersect_correct.
      2,3:admit.
      {
        apply Permutation_map with (f:= pair_map id (PTree.get' i)) in H'.
        rewrite !map_combine in H'.
        rewrite !map_id in H'.
         Definition uncons {T T'} f (l : list T) : option T' :=
          match l with
          | [] => None
          | x::l => f x l
          end.
        change_no_check (Mbind (fun x => Mbind (fun l => @?f x l) (list_Mmap ?g ?l)) (?g ?x))
          with (Mbind (uncons f) (list_Mmap g (x::l))).
        rewrite !Mmap_option_all.
        set (R:= fun {A} (x y : list A) => Permutation (combine (c::cl) x) (combine (c'::cl') y)).
        eapply @Mbind_Proper
          with (R:= R _);
          auto.
        2:{
          unfold R;
          unfold option_rel;
            repeat case_match;
            basic_goal_prep;
          auto.
          all:admit.
        }
        {
        cbv [respectful R].
        destruct x0, y; cbn;
          basic_utils_crush.
        eapply Hext.
        cbn in *.
        rewrite <- !rev_combine by admit.
        rewrite <- !Permutation_rev.
        auto.
        }
    Abort.
      
    
    Lemma pt_spaced_intersect'_perm fuel width f_cil f_ptl t_ci0 t_cil x0 l f_cil' f_ptl' t_ci0' t_cil' x0' l'
      : rectangular_trie_list width (t_ci0::t_cil) (x0::l) ->
        rectangular_trie_list width f_cil f_ptl ->
        rectangular_trie_list width (t_ci0'::t_cil') (x0'::l') ->
        rectangular_trie_list width f_cil' f_ptl' ->
        let cils := t_ci0::t_cil++f_cil in
        let cils' := t_ci0'::t_cil'++f_cil' in
        let ptls := x0::l++f_ptl in
        let ptls' := x0'::l'++f_ptl' in
        Permutation (combine cils ptls) (combine cils' ptls') ->
        pt_spaced_intersect' fuel f_cil f_ptl t_ci0 t_cil x0 l
        = pt_spaced_intersect' fuel f_cil' f_ptl' t_ci0' t_cil' x0' l'.
    Proof.
      revert width f_cil f_ptl t_ci0 t_cil x0 l
        f_cil' f_ptl' t_ci0' t_cil' x0' l'.
      induction fuel;
        basic_goal_prep;
        auto.
      destruct t_ci0, t_ci0'.
      {
        repeat case_match; basic_goal_prep; subst; intuition auto.
        rewrite !leaf_intersect_correct.
        2-5: unfold rectangular_trie_list in *;
          repeat basic_goal_prep;
          eapply all2_impl_r; eauto;
          repeat basic_goal_prep;
          destruct x, y; 
        basic_goal_prep; auto; congruence.
        rewrite <-!fold_left_app.
        f_equal.
        f_equal.
        apply fold_left_permuted; eauto.
        change (?a :: map get_leaf_unchecked ?l ++ ?l')
          with (map get_leaf_unchecked ((pos_trie_leaf a)::l) ++ l').
        change ((?a,?b) :: (combine ?la ?lb))
          with (combine (a::la) (b::lb)) in *.
        apply Permutation_combine_r in H4.
        2,3: basic_goal_prep;basic_utils_crush.
        rewrite Permutation_app_comm in H4.
        change (?a::(?l++?l')) with ((a::l) ++ l') in *.
        eapply Permutation_map in H4.
        rewrite !map_app in *.
        erewrite H4.
        cbn.
        rewrite Permutation_app_comm.
        reflexivity.
      }
      1,2:repeat case_match;
          unfold rectangular_trie_list in *;
          repeat basic_goal_prep;
          Lia.lia.
      destruct width as [| width].
      {
        repeat case_match;
          unfold rectangular_trie_list in *;
          repeat basic_goal_prep;
          Lia.lia.
      }
      {

      erewrite !partition_tries_app in *; eauto.
      all: [> | unfold rectangular_trie_list in *;
                repeat basic_goal_prep; now auto..].

      Ltac populate_pt_knowledge width l1 l2 acc :=
          let Hacc := fresh in
          let Hrect := fresh in
          assert (partition_result_wf width acc) as Hacc
              by (case_match;cbn; intuition auto);
          assert (rectangular_trie_list (S width) l1 l2) as Hrect
              by (unfold rectangular_trie_list in *;
                  repeat basic_goal_prep;
                  apply all2_app; eauto);
          pose proof (partition_tries_wf width acc l1 l2 Hrect Hacc).
       

      lazymatch goal with
        |- match partition_tries ?l1 ?l2 ?acc with _ => _ end
           = match partition_tries ?l1' ?l2' ?acc' with _ => _ end =>
          populate_pt_knowledge width l1 l2 acc;
          populate_pt_knowledge width l1' l2' acc';
          assert (part_res_Perm (partition_tries l1 l2 acc)
                    (partition_tries l1' l2' acc'))
      end.
      {
        erewrite !partition_tries_spec; eauto.
        basic_goal_prep.
        rewrite <- !Permutation_rev.
        apply partition_result_of_lists_Perm.
        {
          replace (false_lists (@! if b then (have_true_part [] [] t_ci0 x0 [] [])
                                  else (just_false_part t_ci0 x0 [] [])))
            with (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                    (filter (fun p : list bool * pos_trie' => negb (hd false (fst p))) [(b::t_ci0, x0)]))
            by (destruct b; basic_goal_prep; auto).
          replace (false_lists (@! if b0 then (have_true_part [] [] t_ci0' x0' [] [])
                                  else (just_false_part t_ci0' x0' [] [])))
            with (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                    (filter (fun p : list bool * pos_trie' => negb (hd false (fst p)))
                       [(b0::t_ci0',x0')]))
            by (destruct b0; basic_goal_prep; auto).
          rewrite <- !map_app, <- !filter_app.
          apply Permutation_map.
          apply Permutation_filter'.
          rewrite Permutation_app_comm; cbn.
          rewrite Permutation_app_comm with (l:=combine (f_cil' ++ t_cil') (f_ptl' ++ l')); cbn.
          rewrite !combine_app in *; basic_utils_crush.
          rewrite Permutation_app_comm.
          rewrite H4.
          rewrite Permutation_app_comm.
          reflexivity.
        }
        {
          replace (true_lists (@! if b then (have_true_part [] [] t_ci0 x0 [] [])
                                 else (just_false_part t_ci0 x0 [] [])))
            with (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                    (filter (fun p : list bool * pos_trie' => (hd false (fst p))) [(b::t_ci0, x0)]))
            by (destruct b; basic_goal_prep; auto).
          replace (true_lists (@! if b0 then (have_true_part [] [] t_ci0' x0' [] [])
                                 else (just_false_part t_ci0' x0' [] [])))
            with (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                    (filter (fun p : list bool * pos_trie' => (hd false (fst p)))
                       [(b0::t_ci0',x0')]))
            by (destruct b0; basic_goal_prep; auto).
          rewrite <- !map_app, <- !filter_app.
          apply Permutation_map.
          apply Permutation_filter'.
          rewrite Permutation_app_comm; cbn.
          rewrite Permutation_app_comm with (l:=combine (f_cil' ++ t_cil') (f_ptl' ++ l')); cbn.
          rewrite !combine_app in *; basic_utils_crush.
          rewrite Permutation_app_comm.
          rewrite H4.
          rewrite Permutation_app_comm.
          reflexivity.
        }
      }      
      lazymatch goal with
        |- match partition_tries ?l1 ?l2 ?acc with _ => _ end
           = match partition_tries ?l1' ?l2' ?acc' with _ => _ end =>
          let Heqpt := fresh "Heqpt" in
          destruct (partition_tries l1 l2 acc) eqn:Heqpt;
          let Heqpt' := fresh "Heqpt" in
          destruct (partition_tries l1' l2' acc') eqn:Heqpt'
      end.      
      {
        repeat basic_goal_prep.
        eapply IHfuel; eauto.        
        1,2:unfold rectangular_trie_list in *;
        repeat basic_goal_prep; intuition eauto.
      }
      1,2: repeat basic_goal_prep; intuition auto.
      {
        repeat basic_goal_prep.
        f_equal.
    Abort.

       
      (*
    Lemma pt_spaced_intersect'_rev fuel f_cil f_ptl t_ci0 t_cil x0 l width
      : width > 0 ->
        rectangular_trie_list width (t_ci0::t_cil) (x0::l) ->
        rectangular_trie_list width f_cil f_ptl ->
        Permutation
        pt_spaced_intersect' fuel f_cil f_ptl t_ci0 (rev t_cil) x0 (rev l)
        = pt_spaced_intersect' fuel f_cil f_ptl t_ci0 t_cil x0 l.
    Proof.
      revert f_cil f_ptl t_ci0 t_cil x0 l.
      induction fuel;
        basic_goal_prep;
        auto.
      case_match.
      {
        case_match; auto.
        rewrite <- Permutation_rev.
        reflexivity.
      }
      {
        remember (partition_tries f_cil0 f_ptl0
                    (@! if b then (have_true_part [] [] t_ci0 x0 [] []) else (just_false_part t_ci0 x0 [] [])))
          as acc.
        Note: IH won't be sufficient here. t_ci0 changes as well.
        erewrite !partition_tries_spec by admit.
        cbn.
       *)
        (*        TODO: fold 1st arg in somehow, deal w/ just a list?
        Lemma match_of_lists
          : match partition_result_of_lists l1 l2 with
            | just_false_part ci0 pt0 other_cil other_tries =>
                f_case ci0 pt0 other_cil other_tries
            | have_true_part other_cil other_tries t_ci1 t_pt0 true_cil true_tries =>
                t_case other_cil other_tries t_ci1 t_pt0 true_cil true_tries
            end
            = match l2 with
                [] =>
         *)
                  
                        (*                   
        Lemma partition_tries_rev:
  forall (cil : list (list bool)) (ptl : list pos_trie') (cil' : list (list bool)) (ptl' : list pos_trie')
    (acc acc' : partition_result) (width : nat),
  width > 0 ->
  rectangular_trie_list width cil ptl ->
  rectangular_trie_list width cil' ptl' ->
  partition_result_wf acc ->
  partition_result_wf acc' ->
  Permutation (combine cil ptl) (combine cil' ptl') ->
  partition_tries (rev cil) (rev ptl) acc
  = let fl := false_lists acc in
    let tl := true_lists acc in
    partition_result_of_lists ((combine cil ptl)
      
          
        lazymatch goal with
          |- match ?c1 with _ => _ end = match ?c2 with _ => _ end =>
            assert (part_res_Perm c1 c2);
            [| destruct c1 eqn:Hc1;
               destruct c2 eqn:Hc2]
           (* [| replace c1 with c2 by admit;
            destruct c2 eqn:Hc2; auto]*)
        end.
        {
          eapply partition_tries_Permutation; eauto.
          {
            unfold rectangular_trie_list in *;
              basic_goal_prep;
              basic_utils_crush.
          }
       
          {
            unfold rectangular_trie_list in *;
              basic_goal_prep;
              basic_utils_crush.
          }
          all: try now (apply partition_tries_wf;case_match; cbn; auto).
          {
            rewrite <- rev_combine, <- Permutation_rev; auto.
            unfold rectangular_trie_list in *;
              basic_goal_prep;
              basic_utils_crush.
          }
          { reflexivity. }
        }
        {
          unfold part_res_Perm in *.
          TODO: need to generalize thm statement to part_res_perm of the arguments?.
          ALternately, need to be more precise here.
          Probably a better option:
          push revs through partition_tries
          
        }
      }
    Qed.
        case_match.
        
        
        TODO: justify permuting partition
        rewrite <- Permutation_rev.
        destruct ((partition_tries f_cil f_ptl
                     (@! if b then (have_true_part [] [] t_ci0 x0 [] []) else (just_false_part t_ci0 x0 [] [])))).
        Lemma partition_tries_rev
          : partition_tries (rev t_cil) (rev l) acc
            = 
        TODO: partition_tries_rev
      }
    Qed.
*)
    
    Lemma pt_spaced_intersect'_correct fuel x cil1 cil2 ptl1 ptl2 ci0 pt0
      : (fuel > length x)%nat ->
        length ci0 = length x ->
        Is_true (has_depth' (length (filter id ci0)) pt0) ->
        rectangular_trie_list (length x) cil1 ptl1 ->
        rectangular_trie_list (length x) cil2 ptl2 ->
        spaced_get_ x (zip_bools (ci0::cil1++cil2),
            pt_spaced_intersect' fuel cil1 ptl1 ci0 cil2 pt0 ptl2)
        = Mbind (list_Mfoldl (fun acc p => option_map (merge acc) (spaced_get' x p))
                   (combine (cil1++cil2) (ptl1 ++ ptl2)))
            (spaced_get' x (ci0, pt0)).
    Proof.
      unfold spaced_get_.
      rewrite Mbind_option_map.
      cbn [fst snd].
      revert x cil1 cil2 ptl1 ptl2 ci0 pt0.
      induction fuel; intros; try Lia.lia.
      cbn [pt_spaced_intersect'].
      destruct x, ci0;
        basic_goal_prep;
        try congruence.
      {
        destruct pt0; basic_goal_prep; try tauto.
        rewrite !leaf_intersect_correct.
        2,3:admit.
        rewrite <- fold_left_app.
        rewrite <- map_app.
        rewrite <- list_Mfoldl_map_option
          with (g := snd)
               (f := fun acc x => option_map (merge acc) (get_leaf x)).
        rewrite map_combine_snd.
        2: admit.
        rewrite <- list_Mfoldl_option_map.
        rewrite map_get_leaf_is_unchecked; auto.
        basic_utils_crush.
        all: unfold rectangular_trie_list in *; break.
        all: eapply all_all2_r.
        all: eapply all2_impl; eauto.
        all:unfold empty.
        all:basic_goal_prep; case_match; subst; cbn in *; eauto.
        (*
        all: apply in_combine_l in H7.
        all: [>eapply in_all in H3 | eapply in_all in H4]; eauto.
        all: destruct x; cbn in *; congruence.
      }
      erewrite partition_tries_app; eauto.
      destruct (partition_tries (cil1 ++ cil2) (ptl1 ++ ptl2)
        (@!
         if b then (have_true_part [] [] ci0 pt0 [] [])
         else (just_false_part ci0 pt0 [] [])))
        eqn:Hpart;
        [ replace (hd false (zip_bools ((b :: ci0) :: cil1 ++ cil2))) with
          false by admit
        | replace (hd false (zip_bools ((b :: ci0) :: cil1 ++ cil2))) with
          true by admit];
        cbn [spaced_get1].
      2:{
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
          
          option_focus (option_map pos_trie_node).
          cbn.
          repeat 
          change (match ?m with
                  | Some a => @?f a
                  | None => None
                  end)
            with (Mbind f m).
          rewrite option_Mbind_assoc.
          rewrite otree_get_Mbind.
          rewrite list_intersect_correct.
          2:{
            intro b'; destruct b'; cbn.
            *)
            (*
            TODO: parallel rev lemma.
            TODO: goal 2 is false?
            reflexivity.
             *)
          (*
          
          cbn.
          rewrite!option_Mbind_assoc.
          
          {
            rewrite <- option_eta_equiv in H5.
            assumption.
          sumption.
        TODO: how to better option-eta
        list_intersect_correct
        
        cbn.
        replace (match
    option_map pos_trie_node
      (list_intersect (pt_spaced_intersect' fuel f_cil f_ptl t_ci0 t_cil) (proj_node_map_unchecked pt0)
         (map proj_node_map_unchecked t_ptl))
  with
  | Some a =>
      match PTree.get' p (proj_node_map_unchecked a) with
      | Some a0 =>
          spaced_get' x
            (tl
               (fold_left (fun acc l : list bool => map2 orb (combine l acc)) (cil1 ++ cil2) (b :: ci0)),
             a0)
      | None => None
      end
  | None => None
                  end)
          with
          (match(list_intersect (pt_spaced_intersect' fuel f_cil f_ptl t_ci0 t_cil) (proj_node_map_unchecked pt0)
         (map proj_node_map_unchecked t_ptl))
  with
  | Some a =>
      match PTree.get' p a with
      | Some a0 =>
          spaced_get' x
            (tl
               (fold_left (fun acc l : list bool => map2 orb (combine l acc)) (cil1 ++ cil2) (b :: ci0)),
             a0)
      | None => None
      end
  | None => None
  end) by admit.
        list_intersect_correct.
      }
      {
        assert (Permutation (combine ((b::ci0)::(cil1 ++ cil2))
                               (pt0::(ptl1 ++ ptl2)))
                  (combine (map (cons false) (ci1::cil))
                     (pt1::ptl))) by admit.
        
        specialize (IHfuel x cil [] ptl [] ci1 pt1 ltac:(Lia.lia)).
        case_match. 
        {
          pose proof H5 as H5l.
          apply Permutation_combine_l in H5l.
          2,3:admit.
          set (zip_bools ((b :: ci0) :: cil1 ++ cil2)) as tmp.
          remember tmp as tmp'.
          revert Heqtmp'.
          subst tmp.
          (*TODO: why can't I rewrite in the body of a let?*)
          rewrite H5l.
          intros ?; subst tmp'.
          rewrite !zip_bools_map_cons by congruence.
          cbn [hd tl map].
          rewrite ! app_nil_r in IHfuel.
          cbn -[zip_bools].
          replace (pos_trie_node (proj_node_map_unchecked p0)) with p0 by admit.
          rewrite IHfuel.
          2-5:admit.
          replace b with false by admit.
          cbn.
          change (match ?m with
                  | Some a => @?f a
                  | None => None
                  end)
            with (Mbind f m).
          erewrite Mbind_option_ext
            with (f:= (fun a : pos_trie' => spaced_get' x (zip_bools (ci1 :: cil), a))).
          2:{
            intros.
            TODO: p0 specialized. there's a missalignment
            rewrite IHfuel.
          
          change (Mbind (fun a : pos_trie' => spaced_get' x (pair (zip_bools (cons ci1 cil)) a))
                    (spaced_get1 p false (proj_node_map_unchecked p0)))
            with (spaced_get' (p::x) (false::(zip_bools (cons ci1 cil)), p0)).
          rewrite IHfuel.
          TODO: turn lhs into a spaced_get?
          
          TODO: rewrite rhs into mbind mfoldl
          TODO: b vs false. not the same get1!
                                    do I need permutation induction in the middle?
        }
        TODO: reconcile spaced_get versions.
        TODO: would it be easier to relate to a binary fn first? seems like.
        2:{
          
        intuition try Lia.lia.
      my_case 1.
      case_match.
      
      Lemma partition_tries_spec
        : partition_tries cil ptl acc = 
          ->
          
      
      2,3: unfold rectangular_trie_list
      
        
        rewrite <- fold_left_app.
        
        
        rewrite Mmap_option_all.
        rewrite map_map.
        cbn.
        rewrite <- map_map with (f:=snd).
        rewrite map_combine_snd.
        2:admit.
        unfold merge_list.
        rewrite <- fold_left_app.
        rewrite <- map_app.
        = list_Mfold (fun acc t => fmap merge (spaced_get_ x t))
        TODO: wrong! RHS doesn't include a/ci0/pt0
        
        TODO: leaf_intersect_spec.

      
      rewrite partition_tries_app.
      2:{ eapply all2_len; eauto. }
      rewrite partition_tries_correct.
      set (p := partition_tries_spec _ _ _).
      remember p as p'.
      subst p.
      destruct p' as [? ? ? ?].   
      destruct x.
      {
        clear IHfuel.
        apply partition_tries_spec_properties_empty in Heqp'.
        2:{
          autorewrite with utils.
          apply all2_len in H4, H3.
          rewrite H4, H3.
          reflexivity.
        }
        2:{
          basic_utils_crush.
          all:eapply all_impl; try eassumption.
          all:unfold empty.
          all:basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        basic_goal_prep; subst.
        replace (hd [] p43) with (@nil bool).
        2:{
          pose proof (fun H' => Permutation_combine_l _ _ _ _ _ _ H' H8 H7) as HPcl.
          autorewrite with utils in HPcl.
          pose proof (hd_In [] p43) as Hhd;
            cbn in Hhd.
          destruct Hhd as [Hhd | Hhd]; auto.
          assert (all (fun p : list bool => length p = 0%nat) (cil1++cil2))
            by (autorewrite with utils; intuition auto).
          rewrite HPcl in H5.
          {
            eapply in_all in H5; eauto.
            destruct (hd [] p43); cbn in *; auto; congruence.
          }
          {
            apply all2_len in H3, H4.
            Lia.lia.
          }
        }
        apply Permutation_combine_r in H7; eauto.
        2:{
          apply all2_len in H3, H4.
          autorewrite with utils.
          Lia.lia.
        }
        rewrite option_eta_equiv with
          (o:= (leaf_intersect p44))
          (k:= fun o => match option_map pos_trie_leaf o with
                        | Some a => get_leaf a
                        | None => None
                        end).
        unfold option_eta.
        cbn.
        change (match leaf_intersect p44 with
                 | Some a => Some a
                 | None => None
                end)
          with (option_eta id (leaf_intersect p44)).
        rewrite <- option_eta_equiv.
        cbv [id].
        rewrite leaf_intersect_correct.
        2:{
          rewrite <- H7.
          autorewrite with utils.
          split.
          all: eapply all_all2_r.
          all: eapply all2_impl; try eassumption.
          all: basic_goal_prep;
            case_match; cbn; eauto.
          all: apply in_combine_l in H5.
          all: eapply in_all in H5; eauto;
            basic_goal_prep.
          all: destruct x; basic_goal_prep; congruence.
        }
        change (match ?o with
                 | Some a => ?f a
                 | None => None
                end)
          with (Mbind f o).
        rewrite <- H7.
        clear p43 p44 H7 H8.
        rewrite !Mmap_option_all.
        rewrite map_ext
          with (l:= (combine (cil1 ++ cil2) (map Some (ptl1 ++ ptl2))))
               (g:= (fun p => Mbind get_leaf (snd p))).        
        2:{
          basic_goal_prep;
          repeat case_match;
          basic_goal_prep;
          basic_utils_crush.
        }
        rewrite <- map_map with (f:=snd).
        rewrite map_combine_snd.
        2:admit.
        change (map Some (ptl1 ++ ptl2))
          with (map (Mret (M:=option)) (ptl1 ++ ptl2)).
        rewrite map_map.
        erewrite map_ext 
          with (f:=(fun x : pos_trie' => @! let p <- @! ret x in (get_leaf p)))
        (g:= get_leaf ).
        2:{
          intros.
          change (fun x => ?f x) with f.
          rewrite option_Mbind_Mret'.
          reflexivity.
        }
        reflexivity.
      }
      {
        basic_goal_prep.
        replace (partition_tries_spec (cil1 ++ cil2) (ptl1 ++ ptl2))
          with (partition_tries_spec' (cil1 ++ cil2) (ptl1 ++ ptl2))
          in Heqp' by admit.
        unfold partition_tries_spec' in *.
        cbn in *.
        autorewrite with utils in Heqp'.
        2:admit.
        rewrite !map_map in Heqp'.
        cbn in *.
        rewrite <- !map_app in Heqp'.
        rewrite <- !filter_app in Heqp'.
        rewrite <- !combine_app in * by admit.
        assert (all (fun p : list bool => length p = S (length x)) (cil1 ++ cil2))
          by admit;
          clear H1 H2.
        assert (all2 (fun (c : list bool) (t : pos_trie') =>
                        Is_true (has_depth' (length (filter id c)) t))
                  (cil1 ++ cil2)
                  (ptl1 ++ ptl2))
          by admit;
          clear H3 H4.
        revert Heqp' H1 H5.
        generalize (cil1 ++ cil2).
        clear cil1 cil2.
        generalize (ptl1++ptl2).
        clear ptl1 ptl2.
        intros ptl cil.
        intros.
        replace (combine cil (map Some ptl))
          with (map (pair_map id Some) (combine cil ptl))
          by admit.
        rewrite Mmap_option_all.
        rewrite map_map.
        cbv [id].
        cbn.
        change (fun x => ?f x) with f in *.
        replace (zip_bools cil)
          with (zip_bools (map fst (combine cil ptl))) by admit.
        rewrite <- map_combine_fst with (lB := ptl) in H5 by admit.
        assert (all (fun '(c,t) => Is_true (has_depth' (length (filter id c)) t))
                  (combine cil ptl))
          by admit;
          clear H1.
        revert Heqp' H5 H2.
        generalize (combine cil ptl);
          clear cil ptl.
        intros.
        destruct p42.
        {
          replace (if hd [] p43 then (option_map pos_trie_leaf (leaf_intersect p44))
                   else (pt_spaced_intersect' fuel p43 p44 [] []))
            with (if p43 then (option_map pos_trie_leaf (leaf_intersect p44))
                  else (pt_spaced_intersect' fuel p43 p44 [] []))
            by admit.
          TODO: do I need leaf_intersect?.
                   seems like a complicating factor
  
          destruct p43.
          TODO: more destructs than i'd like
        }
        
        TODO: generalize combine ++?
        filter_app
        rewrite <-
        break; subst.
        
        TODO: remove the revs
        TODO
          




      unfold partition_tries_spec.
      cbn.
      autorewrite with bool utils.
      2,3:admit.
      replace (rev
        (map snd
           (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
              (filter (fun p : list bool * pos_trie' => hd false (fst p))
                 (combine cil1 ptl1))) ++
         map snd
           (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
              (filter (fun p : list bool * pos_trie' => hd false (fst p))
                 (combine cil2 ptl2)))))
        with (map snd
           (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
              (filter (fun p : list bool * pos_trie' => hd false (fst p))
                 (combine cil1 ptl1))) ++
         map snd
           (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
              (filter (fun p : list bool * pos_trie' => hd false (fst p))
                 (combine cil2 ptl2))))
        by admit (*TODO: permutation*).
      rewrite !map_map.
      cbn.
      let l :=
        constr:( map (fun x0 : list bool * pos_trie' => snd x0)
        (filter (fun p : list bool * pos_trie' => hd false (fst p)) (combine cil1 ptl1)) ++
      map (fun x0 : list bool * pos_trie' => snd x0)
      (filter (fun p : list bool * pos_trie' => hd false (fst p)) (combine cil2 ptl2)))
      in
      enough (match l 
      
      lazymatch goal with
        |- ?LHS = ?RHS =>
              pattern LHS;
              pattern l
          lazymatch LHS with
          | context c [l] =>
          end
      end.
      
      rewrite list_eta_equiv
        with
        
      list_eta_equiv
      TODO: list eta
: clear revs via up-to-permutation
        TODO: how to handle partition tries in the nonempty case?
        safe_invert H0.
      }


      


    Qed.
           *)
    Abort.

      
    
    Lemma all_const C P (x:C) l
      : all P l ->
        (forall y, P y -> y = x) ->
        l = repeat x (length l).
    Admitted.

    


    Lemma map_combine_fst' C D
      : forall (lA : list C) (lB : list D),
        map fst (combine lA lB) = (firstn (length lB) lA).
    Admitted.
    Hint Rewrite  map_combine_fst' : utils.
    
    Lemma map_combine_snd' C D
      : forall (lA : list C) (lB : list D),
        map snd (combine lA lB) = (firstn (length lA) lB).
    Admitted.
    Hint Rewrite  map_combine_snd' : utils.

    
    Lemma firstn_repeat m n C (x:C)
      : firstn m (repeat x n) = repeat x (min m n).
    Proof.
    Admitted.
    Hint Rewrite firstn_repeat : utils.

    
    Lemma fold_left_fix_In C D (f : C -> D -> C) l acc
      : (forall x, In x l -> f acc x = acc) -> fold_left f l acc = acc.
    Admitted.




    (*TODO: move?
    Lemma list_intersect'_ext A1 A2 (f g : list A1 -> option A2) t ts
      : (forall l, f l = g l) ->
        list_intersect' f t ts = list_intersect' g t ts.
    Admitted.
     *)

    
    (*
    Lemma pt_spaced_intersect'_simple_spec fuel cil1 cil2 ptl1 ptl2
      : Datatypes.length cil1 = Datatypes.length ptl1->
        pt_spaced_intersect' fuel cil1 ptl1 cil2 ptl2
        = pt_spaced_intersect'_simple fuel (combine (cil1 ++ cil2) (ptl1 ++ ptl2)).
    Proof.
      revert cil1 cil2 ptl1 ptl2.
      induction fuel;
        basic_goal_prep; eauto.
      rewrite partition_tries_app; auto.
      rewrite !partition_tries_correct.
      unfold partition_tries_spec; cbn [p41 p42 p43 p44].
      autorewrite with utils bool in *.
      repeat lazymatch goal with
               |- match ?c with _ => _ end
                  = match ?c with _ => _ end =>
                 case_match; auto
             end.
      (*erewrite list_intersect'_ext; eauto.
      intros.
      rewrite HeqH1.
      rewrite IHfuel; eauto.
      basic_utils_crush.
    Qed.*)
    Admitted.
*)
    
    Lemma with_names_from_map_snd A1 A2 (l : list (A1 * A2))
      : with_names_from l (map snd l) = l.
    Admitted.
    Hint Rewrite with_names_from_map_snd : utils.


    
    Lemma all_rev T (P : T -> Prop) l
      : all P (rev l) <-> all P l.
    Admitted.
    Hint Rewrite all_rev : utils.
    
    Lemma all_map T T' (f : T -> T') (P : T' -> Prop) l
      : all P (map f l) <-> all (fun x => P (f x)) l.
    Admitted.
    Hint Rewrite all_map : utils.
    
    Lemma all_filter T (P : T -> Prop) l f
      : all P (filter f l) <-> all (fun x => Is_true (f x) -> P x) l.
    Admitted.
    Hint Rewrite all_filter : utils.

    
    Definition not_leaf (p : pos_trie') := if p then False else True.
    Lemma not_leaves_map_proj l
      : all not_leaf l ->
        exists l', l = map pos_trie_node l'.
    Admitted.

    (*
    Lemma partition_tries_spec_properties_nonempty cil ptl
      true_cil true_tries other_cil other_tries
        : mk4 true_cil true_tries other_cil other_tries
          = partition_tries_spec cil ptl (mk4 [] [] [] []) ->
          all nonempty cil ->
          let trues := combine (map (cons true) true_cil) true_tries in
          let others := combine (map (cons false) other_cil) other_tries in
          Permutation (combine cil ptl) (trues ++ others)
          /\ length true_cil = length true_tries
          /\ length other_cil = length other_tries.
    Proof.
    Admitted.
*)

    
    
    Lemma combine_map_fst_snd T1 T2 (l : list (T1*T2))
      :  (combine (map fst l) (map snd l)) = l.
    Admitted.

   
    


   
    (*
    Lemma pt_spaced_intersect'_simple_correct fuel x cil1 cil2 ptl1 ptl2
      : (fuel > length x)%nat ->
        all (fun p => length p = length x) cil1 ->
        all (fun p => length p = length x) cil2 ->
        all2 (fun c t => Is_true (has_depth' (length (filter id c)) t)) cil1 ptl1 ->
        all2 (fun c t => Is_true (has_depth' (length (filter id c)) t)) cil2 ptl2 ->
        spaced_get_ x (zip_bools (cil1++cil2), pt_spaced_intersect' fuel cil1 ptl1 cil2 ptl2)
        = Mbind merge_list (list_Mmap (spaced_get_ x) (combine (cil1++cil2)
                                                         (map Some (ptl1 ++ ptl2)))).
    Proof.
      unfold spaced_get_.
      rewrite Mbind_option_map.
      cbn [fst snd].
      revert x cil1 cil2 ptl1 ptl2.
      induction fuel; intros; try Lia.lia.
      cbn [pt_spaced_intersect'].
      rewrite partition_tries_app.
      2:{ eapply all2_len; eauto. }
      rewrite partition_tries_correct.
      set (p := partition_tries_spec _ _ _).
      remember p as p'.
      subst p.
      destruct p' as [? ? ? ?].
      destruct x.
      {
        apply partition_tries_spec_properties_empty in Heqp'.
        2:{
          autorewrite with utils.
          apply all2_len in H4, H3.
          rewrite H4, H3.
          reflexivity.
        }
        2:{
          basic_utils_crush.
          all:eapply all_impl; try eassumption.
          all:unfold empty.
          all:basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        basic_goal_prep; subst.
        eapply all_const in H1, H2.
        2,3: intro y; destruct y; cbn in *; try Lia.lia; reflexivity.
        assert (p43 = repeat [] (Datatypes.length p44)) by admit. (*provable*)
        subst p43.
        rewrite repeat_default_hd.
        change (match ?c with
                | Some pt => @?f pt
                | None => None
                end)
          with (Mbind f c).
        rewrite Mbind_option_map.
        cbn -[Mbind].
        change (@Some ?A) with (@Mret option _ A).
        rewrite option_Mbind_Mret.
        rewrite leaf_intersect_correct.
        2:{
          symmetry in H7.
          apply Permutation_combine_r in H7.
          2: basic_utils_crush.
          rewrite H7.
          autorewrite with utils.
          split.
          all: eapply all_all2_r.
          all: eapply all2_impl; eauto.
          all: basic_goal_prep.
          {
            apply in_combine_l in H5.
            rewrite H1 in H5.
            apply repeat_spec in H5.
            subst.
            cbn in *; eauto.
          }
          {
            apply in_combine_l in H5.
            rewrite H2 in H5.
            apply repeat_spec in H5.
            subst.
            cbn in *; eauto.
          }
        }
        {
          eapply Mbind_Proper.
          1:eapply merge_list_Proper.
          rewrite !Mmap_option_all.
          apply option_all_Permutation_Proper.
          basic_utils_crush.
          apply Permutation_combine_r in H7.
          2:admit(*length*).
          rewrite <- H7.
          erewrite map_ext_in
            with (f:=(fun p : list bool * pos_trie =>
                        match option_map (fun t : pos_trie' => (fst p, t)) (snd p) with
                        | Some a => get_leaf (snd a)
                        | None => None
                        end)).
          2:{
            intros.
            replace (fst a) with (@nil bool) by admit.
            instantiate (1:= fun a => _ (snd a));
              cbn.
            instantiate (1:= Mbind get_leaf).
            destruct (snd a); reflexivity.
          }
    (*
          rewrite <- map_Mmap
          TODO: map 
    }
          replace p44 with (ptl1 ++ ptl2) by admit.
         Definitely true, just needs lemmas
                            Lemma all_Permutation_Proper P : Proper (Permutation ==> iff) (all P).
        Lemma merge_list_Permutation_Proper
        cil1,2 = repeat [].
        (map cons false p43) incl cil1,2, so p43 = []

                            
        replace 
        TODO: need to assert that p43 nonempty?
        rewrite leaf_intersect_correct.
        admit (*TODO leaf_intersect lemma*).
        }
      {
        apply partition_tries_spec_properties_nonempty in Heqp'.
        2:{
          basic_utils_crush.
          all:eapply all_impl; try eassumption.
          all:unfold nonempty.
          all:basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        break.
        replace (combine (cil1 ++ cil2) (map Some (ptl1 ++ ptl2)))
          with (map (pair_map id Some) (combine (cil1 ++ cil2) (ptl1 ++ ptl2)))
          by admit.
        replace (combine (cil1 ++ cil2) (ptl1 ++ ptl2))
        with (combine (map (cons true) p41) p42 ++ combine (map (cons false) p43) p44)
          by admit.
        replace (zip_bools (cil1 ++ cil2))
          with (zip_bools ((map (cons true) p41) ++ (map (cons false) p43)))
          by admit.
        destruct p42, p41; try (basic_goal_prep;congruence).
        {
          destruct (hd [] p43); [admit (*contradiction*)|].
          (*TODO: bools permutation
          rewrite IHfuel. *)
          cbn [map app].
          replace (zip_bools (map (cons false) p43)) with (cons false (zip_bools p43))
            by admit.
          cbn [spaced_get' fst snd hd tl spaced_get1].
          rewrite !option_Mbind_assoc.
          change (fun x => ?f x) with f in *.
          cbn [combine app].
          rewrite <- !option_Mbind_assoc.
          unfold Mbind at 3.
          cbn - [Mbind].
          unfold Mbind at 2.
          cbn - [Mbind].
          rewrite Mbind_option_ext
            with (g:= fun a => spaced_get' x (zip_bools p43, a)).
          2: admit (*TODO: depth reasoning*).
          change (match ?c with
                  | Some pt => @?f pt
                  | None => None
                  end)
            with (Mbind f c).
          replace (zip_bools p43) with (zip_bools (p43 ++[])) by basic_utils_crush.
          rewrite IHfuel by admit.
          f_equal.
          basic_utils_crush.
          replace (map (pair_map id Some) (combine (map (cons false) p43) p44))
            with (map (pair_map (cons false) Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          replace (combine p43 (map Some p44))
            with (map (pair_map id Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          rewrite !Mmap_option_all.
          rewrite !List.map_map.
          f_equal.
          eapply map_ext.
          basic_goal_prep.
          (*TODO: remember that p0 has positive depth, i.e. is a map*)
          replace (pos_trie_node (proj_node_map_unchecked p0)) with p0 by admit.
          reflexivity.
        }
        {
          change (match ?c with
                  | Some pt => @?f pt
                  | None => None
                  end)
            with (Mbind f c).
          replace (zip_bools (map (cons true) (l :: p41) ++ map (cons false) p43))
            with (true::(zip_bools (l :: p41 ++ p43))) by admit.
          cbn [spaced_get' fst snd hd tl spaced_get1].
          rewrite !option_Mbind_assoc.
          change (fun x => ?f x) with f in *.
          rewrite <- !option_Mbind_assoc.
          change (@Some ?A)
            with (@Mret option _ A).
          change (Mbind ?f (Mret ?a)) with (f a).
          cbn beta.
          rewrite !option_Mbind_assoc.
          rewrite otree_get_Mbind.
          rewrite list_intersect'_correct.
          2:admit.
          change (@PTree.option_map) with (@Mbind option _).
          rewrite !Mmap_option_all.
          rewrite <- !option_Mbind_assoc.
          (*TODO: flip order to make this a change?*)
          replace (zip_bools (l :: p41 ++ p43))
            with (zip_bools (p43 ++ l :: p41)) by admit.
          erewrite Mbind_option_ext.
          2:{
            intros.
            apply IHfuel; admit.
          }
          rewrite !option_Mbind_assoc.
          f_equal.
          rewrite <- !Mmap_option_all.
          TODO: pile of permute/ get goop.
          Mbind f (option_all l)
          = 
          

          Fail.
          rewrite !List.map_map.
          unfold id.
          remember (l::p41) as p41'.
          remember (p0::p42) as p42'.
          cbn -[Mbind option_all].
          change (Mbind ?f (Some ?a)) with (f a).
          cbn -[Mbind option_all].
          cbn beta.
          rewrite <- !option_Mbind_assoc.
          
          rewrite <- surjective_pairing.
          TODO: manage get' on both sides
          rewrite !option_Mbind_assoc.
          









          
          change (match ?c with
                  | Some pt => @?f pt
                  | None => None
                  end)
            with (Mbind f c).
          replace (zip_bools p43) with (zip_bools (p43 ++[])) by basic_utils_crush.
          rewrite IHfuel by admit.
          f_equal.
          basic_utils_crush.
          replace (map (pair_map id Some) (combine (map (cons false) p43) p44))
            with (map (pair_map (cons false) Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          replace (combine p43 (map Some p44))
            with (map (pair_map id Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          rewrite !Mmap_option_all.
          rewrite !List.map_map.
          f_equal.
          eapply map_ext.
          basic_goal_prep.
          (*TODO: remember that p0 has positive depth, i.e. is a map*)
          replace (pos_trie_node (proj_node_map_unchecked p0)) with p0 by admit.
          reflexivity.
        }

      
    Lemma pt_spaced_intersect'_simple_correct fuel x l
      : (fuel > length x)%nat ->
          all (fun p => length (fst p) = length x) l ->
          all (fun p => Is_true (has_depth' (length (filter id (fst p))) (snd p))) l ->
          spaced_get_ x (zip_bools l, pt_spaced_intersect'_simple fuel l)
          = Mbind merge_list (list_Mmap (spaced_get_ x) (map (pair_map id Some) l)).
    Proof.
      unfold spaced_get_.
      rewrite Mbind_option_map.
      cbn [fst snd].
      revert x l.
      induction fuel; intros; try Lia.lia.
      cbn [pt_spaced_intersect'_simple].
      set (p := partition_tries_spec _ _ _).
      remember p as p'.
      subst p.
      destruct p' as [? ? ? ?].
      destruct x.
      {
        apply partition_tries_spec_properties_empty in Heqp'.
        2:{
          rewrite all_map.
          eapply all_impl; try apply H1.
          unfold empty.
          basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        basic_goal_prep; subst.
        admit (*TODO leaf_intersect lemma*).
      }
      {
        apply partition_tries_spec_properties_nonempty in Heqp'.
        2:{
          rewrite all_map.
          eapply all_impl; try apply H1.
          unfold nonempty.
          basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        break.
        rewrite combine_map_fst_snd in *.
        destruct p42, p41; try (basic_goal_prep;congruence).
        {
          destruct (hd [] p43); [admit (*contradiction*)|].
          (*TODO: bools permutation
          rewrite IHfuel. *)
          admit.
        }
        {
          rewrite !Mbind_option_map.
          cbn [spaced_get'].
          cbn [fst snd].
          rewrite !option_Mbind_assoc.
          cbn [get_map].
          change (fun x => ?f x) with f in *.
          change (Mbind (A:=(PTree.tree' pos_trie')) Some)
            with (Mbind (M:=option) (A:=(PTree.tree' pos_trie')) Mret).
          rewrite option_Mbind_Mret.
          (*TODO: because the true list is nonempty*)
          replace (hd false (zip_bools l)) with true by admit.
          cbv [spaced_get1].
          change (fun x => ?f x) with f in *.
          rewrite otree_get_Mbind.
          rewrite list_intersect'_correct.
          2:admit.
          change (@PTree.option_map) with (@Mbind option _).
          rewrite Mmap_option_all with (l:=(map (pair_map id Some) l)).
          erewrite map_ext with (l:=(map (pair_map id Some) l)).
          2:{
            intros.
            rewrite Mbind_option_map.
            cbn [fst snd].
            rewrite option_Mbind_assoc.
            instantiate (1:= fun a => Mbind _ (snd a)).
            cbn beta.
            destruct a; cbn.
            destruct o; cbn; [|reflexivity].
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            rewrite option_Mbind_assoc.
            instantiate (1:= fun a2 => Mbind _ (get_map a2)).
            instantiate (1:= fun a2m => if hd false (fst a) then _ else _).
            cbn.
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            destruct (hd false l1).
            {
              rewrite <- option_Mbind_assoc.
              destruct (get_map p1); cbn; auto.
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            instantiate (1:= Mbind (fun a' : pos_trie' => spaced_get' x (tl (fst a), a')) (PTree.get' p a2m)).
            reflexivity.
            }
            {
              rewrite <- option_Mbind_assoc.
              destruct (get_map p1); cbn; auto.
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            instantiate (1:= spaced_get' x (tl (fst a), pos_trie_node a2m)).
            reflexivity.
            }
          }
          rewrite <- Mmap_option_all with (l:=(map (pair_map id Some) l)).
          
          unfold spaced_get.
          cbn [pt_get].
          TODO: destruct 
                  (list_Mmap (PTree.get' p) (cons (proj_node_map_unchecked p0) (map proj_node_map_unchecked p42)))
                  and the map spaced_gets
          replace (tl (zip_bools l))
            with (combine (app p43 (cons l0 p41)) (app p44 true_tries)).
          rewrite <- !option_Mbind_assoc.
          Unset Printing Notations.
          rewrite !Mbind_option_map.
          
          Fail.
      change (match ?c with
              | Some pt => Some (?f pt)
              | None => None
              end)
        with (option_map f c) in *.
      cbn [fst snd].
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c) in *.
      rewrite !Mbind_option_map.
      cbn [fst snd].
      rewrite !option_Mbind_assoc.
      replace (hd false (zip_bools l)) with true by admit.
      cbv [spaced_get1].
      rewrite <- !option_Mbind_assoc.
      cbn.
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      cbn [Datatypes.length] in *.
      subst mout.
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      rewrite !option_Mbind_assoc.
      rewrite otree_get_Mbind.
      rewrite list_intersect'_correct.
      2: admit.
      change (@PTree.option_map) with (@Mbind option _).
      rewrite <- !option_Mbind_assoc.
      cbn.
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      rewrite <- !option_Mbind_assoc.
      
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      
      answer: this is the false case?
      TODO: spaced get of list_intersect'?
                   why is x not a cons?
      list_intersect'_correct
      specialize (IHfuel x (tl l) ltac:(Lia.lia)).
      cbn [fst snd] in IHfuel.
      rewrite Mbind_option_map in IHfuel.
      subst mout.
      TODO: list intersect
      (combine (p43 ++ p41) (p44 ++ true_tries))
      TODO: IH doesn't have the append
      rewrite IHfuel.
      
          destruct mout; cbn -[Mbind].
          {
            unfold Mbind at 1.
            cbn -[Mbind].
            rewrite !option_Mbind_assoc.
z            TODO: fold mbind
            replace (hd false
                     (fold_left (fun acc l0 : list bool => map2 orb (combine l0 acc)) (tl (map fst l)) (hd [] (map fst l))))
              with true by admit.
            cbn.
            TODO:
          rewrite <- !option_Mbind_assoc.
          rewrite option_eta_equiv with
            (k:=fun mout => spaced_get (p :: x)
                               (bools, match mout with
                                       | Some pt => Some (pos_trie_node pt)
                                       | None => None
                                       end)) (o:=mout).
          subst mout.
          unfold option_eta; cbn.
          unfold 
          spaced_get (p::k) := Mbind (spaced_get k) (get p (project m)).
          TODO: spaced_get should eval on cons key?.
          alt unfold everywhere
          end.
          option_eta
          list_intersect'_correct
        }

      Fail.



      
      unfold spaced_get.
      subst bools.
      cbn [pt_spaced_intersect'_simple].
      unfold partition_tries_spec.
      cbn [p41 p42 p43 p44 fst snd].
      autorewrite with utils bool.
      cbn [p41 p42 p43 p44 fst snd].
      case_match.
      {
        symmetry in HeqH3.
        autorewrite with utils bool in *.
        intuition subst;
          autorewrite with utils bool in *;
          subst;
          eauto.
        shelve.
      }
      unfold pt_get.
      change (match ?c with
              | Some pt => Some (?f pt)
              | None => None
              end)
        with (option_map f c).
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      autorewrite with utils bool.
      assert (all not_leaf (p::H3)).
      {
        rewrite HeqH3.
        autorewrite with utils bool.
        eapply all_impl; eauto.
        basic_goal_prep.
        destruct l0 as [| [] ?];
          basic_goal_prep;
          try tauto.
        destruct p0;
          tauto.
      }
      apply not_leaves_map_proj in H4.
      break.
      destruct x0; cbn in H4; try congruence.
      safe_invert H4.
      rewrite List.map_map with (f:=pos_trie_node).
      cbn [proj_node_map_unchecked].
      rewrite map_id.
      rewrite List.map_map in HeqH3.
      cbn in HeqH3.
      change (fun x => ?f x) with f in *.
      destruct x.
      {
        basic_goal_prep.
        assert (l = combine (repeat [] (length l)) (map snd l)).
        {
          revert H1; clear.
          induction l;
            basic_goal_prep;
            basic_utils_crush.
        }
        rewrite H3 in HeqH3.
        basic_utils_crush.
        rewrite filter_false_In in HeqH3.
        2:{
          basic_goal_prep.
          apply in_combine_l in H4.
          apply repeat_spec in H4.
          subst.
          reflexivity.
        }
        basic_goal_prep.
        congruence.
      }
      remember ((fold_left (fun acc l0 : list bool => map2 orb (combine l0 acc)) (tl (map fst l))
                   (hd [] (map fst l)))) as bools.
      destruct bools.
      1: admit (*TODO: contradiction *).
      cbn [combine filter map fst snd].
      destruct b.
      {
        cbn [map fst pt_get'].
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      rewrite option_Mbind_assoc.
      rewrite otree_get_Mbind.
      erewrite list_intersect'_correct.
      2:admit (*TODO*).
      change (@PTree.option_map) with (@Mbind option _).
      rewrite <- option_Mbind_assoc.
      cbn.
      TODO: top-level thought:
          would it be better to prove a list-of-lists induction principle?.
      would it be sufficient to have a destructor since we induct on fuel?.
      note: could replace l im bools w/ output of partition via perm
      TODO: IH
      basic_utils_crush.

      Proof sketch:
        input splits into 


      
      TODO: Mbind_assoc
      TODO: may be n falses, need the first true!
      TODO: have to pull the first bool out of map2 orb.
      Question: can I transpose the listoflists?. probably not
      have it be a list of tuples, rather than a tuple of lists?.
      might be easier to work with.
        contradiction.
        cbn.
        rewrite H3 in HeqH3.
        
      TODO: evaluation blocked on x. if empty, behaves diff.x
      erewrite Mbind_option_ext.
      2:{
        intros.
        TODO: x empty?
        cbn.
      cbv [pt_get'].

      Lemma pt_get'_PTree_get'
        :   pt_get

      TODO: need the PTree.get'
        
      TODO: what do I know here?
      TODO: need to know that there's a 'true' in the bools list?.
      QUestion: should bools be constrained propositinally rather than defined?.
      TODO: apply H1,h2 in p::H3?
      
      TODO: pt_get' to PTree.get x0 (otree 
      rewrite !List.map_map; cbn [fst snd].
      TODO: what's the diff between H3, H4/ l0,p?
                                                Why does l0 show up, but not p?
        TODO: simplify further: have 1 combined list!
        TODO: list_intersect'_correct
       *)
    Abort.
    *)

    (*TODO: update
      Lemma pt_spaced_intersect'_correct fuel x cil1 cil2 ptl1 ptl2
        : (fuel > length x)%nat ->
          all (fun l => length l = length x) cil1 ->
          all (fun l => length l = length x) cil2 ->
          all2 (fun l t => Is_true (has_depth' (length (filter id l)) t)) cil1 ptl1 ->
          all2 (fun l t => Is_true (has_depth' (length (filter id l)) t)) cil2 ptl2 ->
          
          let bools := List.fold_left
                         (fun acc l => map2 orb (combine l acc))
                         (tl (cil1++cil2))
                         (hd [] (cil1++cil2))
          in
          spaced_get x (pt_spaced_intersect' fuel cil1 ptl1 cil2 ptl2, bools)
          = Mbind merge_list (list_Mmap (spaced_get x) (combine (map Some (ptl1++ptl2)) (cil1 ++ cil2))).
      Proof.
        revert x cil1 cil2 ptl1 ptl2.
        induction fuel; intros; try Lia.lia.
        unfold spaced_get.
        subst bools.
        cbn [pt_spaced_intersect'].
        rewrite ! partition_tries_correct.
        unfold partition_tries_spec.
        cbn [p41 p42 p43 p44 fst snd].
        autorewrite with utils bool.
        cbn [p41 p42 p43 p44 fst snd].
        case_match.
        {
          symmetry in HeqH5.
          autorewrite with utils bool in *.
          intuition subst;
            autorewrite with utils bool in *;
            subst;
            eauto.
        }
        case_match.
        {
          symmetry in HeqH5, HeqH6.
          autorewrite with utils bool in *.
          intuition subst;
            autorewrite with utils bool in *;
            subst;
            eauto.
        }
        assert (combine (l::H5) (p::H6)
                = rev (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                         (filter (fun p : list bool * pos_trie' => hd false (fst p)) (combine cil2 ptl2)))
                    ++
                    rev
                    (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                       (filter (fun p : list bool * pos_trie' => hd false (fst p)) (combine cil1 ptl1))))
          by admit.
        clear H7 (*TODO: we might need this*).

        
        unfold pt_get.
        change (match ?c with
                | Some pt => Some (?f pt)
                | None => None
                end)
          with (option_map f c).
        change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
          with (Mbind f c).
        autorewrite with utils bool.

        TODO: simplify things: get rid of cil1,2
        list_intersect'_correct
                    
        cbn.

        
        destruct x; cbn in *.








        
        case_match.
        1:case_match.
        all:unfold spaced_get.
        all: subst.
        all: cbn [fst snd].
        {
          revert HeqH6.
          rewrite Mmap_option_all.
          autorewrite with utils bool.
          intuition subst; cbn in *; eauto.
          all:autorewrite with utils bool in *; eauto.
          symmetry in H5.
          autorewrite with utils bool in *; eauto.
        }
        all: cbn [pt_spaced_intersect'].
        all:rewrite ! partition_tries_correct.
        all:unfold partition_tries_spec.
        all: autorewrite with utils bool.
        all: cbn.
        all:rewrite !List.map_map.
        all: cbn.
        all: case_match.
        all: try symmetry in HeqH7.
        all: autorewrite with utils bool in *.
        all:break.
        {
          intuition subst; cbn in *.
          all:autorewrite with utils bool in *.
          all: subst.
          all:autorewrite with utils bool in *.
          all: cbn in *.
          all: try congruence.
          symmetry in H5.
          all:autorewrite with utils bool in *.
          subst.
          cbn in *.
          congruence.
        }
        2:{
          symmetry in HeqH0.
          autorewrite with utils bool in *.
          intuition subst; cbn in *.
          all:autorewrite with utils bool in *.
          all: subst.
          all:autorewrite with utils bool in *.
          all: cbn in *.
          all: try congruence.
        }
        all: case_match.
        1,3:exfalso.
        1,2:[>symmetry in HeqH8 | symmetry in HeqH7];
        autorewrite with utils bool in *;
        intuition subst; cbn; eauto;
        autorewrite with utils bool in *;
        cbn in *; congruence.
        all: unfold pt_get.
        all:change (match ?c with
                | Some pt => Some (?f pt)
                | None => None
                end)
          with (option_map f c).
        all:change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
          with (Mbind f c).
        all:autorewrite with utils bool in *.
        TODO: issue: want goal to have 1 true at the front of bools
        rewrite list_intersect'_correct.
        ....
        
        2:{
          
          }
            
        }
        {
          rewrite Mmap_option_all in HeqH6.
          rewrite <- map_app in HeqH6.
          rewrite <- map_id with (l:= (cil1 ++ cil2)) in HeqH6.
          rewrite <- map_combine_separated in HeqH6.
          cbv [id] in HeqH6.
          rewrite List.map_map in HeqH6.
          cbn in *.
        }
        
        3:{
        TODO: relate a H6, l h7?


        }
        {
          rewrite <- rev_app_distr in HeqH7.
          rewrite <- rev_involutive with (l:=l::H7) in HeqH7.
          apply rev_inj in HeqH7.
          
        basic_utils_crush.
        {
        }
        all: autorewrite with utils bool.
        2:{
        cbn [fst snd].
        set (key:=(map fst (filter snd (combine x bools)))).
        subst bools.
        
        revert x len cil1 cil2 ptl1 ptl2.
        induction fuel; intros; try Lia.lia.
        cbn [pt_spaced_intersect'].
        rewrite ! partition_tries_correct.
        unfold partition_tries_spec.
        basic_utils_crush.
        rewrite !List.map_map.
        cbn.
        unfold spaced_get.
        cbn.
        destruct len.
        {
          eapply all_const with (x:=[]) in H1, H2.
          2,3: destruct y; cbn; intros; congruence.
          generalize dependent (Datatypes.length cil1).
          generalize dependent (Datatypes.length cil2).
          intros; subst.
          autorewrite with utils bool.
          rewrite !filter_false_In with (f:=(fun p : list bool * pos_trie' => hd false (fst p))).
          2,3:destruct x0; intro Hcom;
            apply in_combine_l in Hcom;
            apply repeat_spec in Hcom;
            subst;
            reflexivity.
          rewrite !Permutation.filter_true_In
            with (f:=(fun p : list bool * pos_trie' => negb (hd false (fst p)))).
          2,3:destruct x0; intro Hcom;
            apply in_combine_l in Hcom;
            apply repeat_spec in Hcom;
          subst; reflexivity.
          repeat change (fun x => ?f x) with f.
          autorewrite with utils bool.
          rewrite <- !List.map_map with (f :=fst).
          autorewrite with utils bool.
          autorewrite with utils bool.
          subst bools.
          cbn.
          rewrite <- !repeat_app.
          autorewrite with utils bool.
          rewrite fold_left_fix_In.
          2:{
            intros l Hin.
            apply repeat_spec in Hin; subst.
            reflexivity.
          }
          unfold spaced_get.
          cbn.
          Hint Rewrite combine_nil : utils.
          autorewrite with utils bool.
          cbn.
          TODO: did I case too early on the len?
     *)

    (*
    Lemma leaf_intersect_correct l
      : 
      spaced_get x
        (option_map pos_trie_leaf (leaf_intersect l), [])
        = Mbind (fun es => match es with
                           | [] => None
                           | e :: es0 => Some (fold_left merge es0 e)
                           end)
            (list_Mmap (spaced_get x) (combine l (repeat [] (length l)))).
      
          
          TODO: leaf intersect lemma
          
          Lemma repeat_default_hd
            : hd x (repeat x n) = x.


            rev_app_distr
          rewrite !map_combine_fst'.
          rewrite !firstn_repeat.
          Lemma 
          rewrite !H1, !H2.
        cbn beta.
     *)

    (*TODO update
    (*TODO: how to do this other than by matching on p?*)
      Lemma pt_spaced_intersect_correct x p
        : let bools := List.fold_left
                         (fun acc p => map2 orb (combine (snd p) acc))
                         (tl p)
                         (hd [] (map snd p))
          in
        match list_Mmap (spaced_get x) p with
        | Some es => spaced_get x (pt_spaced_intersect p, bools)
                     = match es with
                       | [] => None
                       | e::es => Some (List.fold_left merge es e)
                       end
        | _ => spaced_get x (pt_spaced_intersect p, bools) = None
        end.
      Proof.
     *)
        

        (*
      Lemma pt_spaced_intersect'_correct x p
        : all (fun l => len = length l) cil ->
          all (fun l => len = length l) ptl ->
        let bools := List.fold_left
                         (fun acc l => map2 orb (combine l  acc))
                         cil
                         (repeat true len)
          in
        match list_Mmap (spaced_get x) p with
        | Some es => spaced_get x (pt_spaced_intersect p, bools)
                     = match es with
                       | [] => None
                       | e::es => Some (List.fold_left merge es e)
                       end
        | _ => spaced_get x (pt_spaced_intersect p, bools) = None
        end.
      Proof.
        todo: lemma about intersect'
              *)
        
    (*TODO: ditch this compat layer *)
    Definition compat_intersect (p : ne_list (pos_trie * list bool)) : pos_trie :=
      pt_spaced_intersect p.

    (*TODO: update
      Lemma compat_intersect_correct x p
        : let bools := List.fold_left
                         (fun acc p => map2 orb (combine (snd p) acc))
                         (snd p)
                         (snd (fst p))
          in
        match spaced_get x (fst p), list_Mmap (spaced_get x) (snd p) with
        | Some e, Some es => spaced_get x (compat_intersect p, bools)
                             = Some (List.fold_left merge es e)
        | _,_ => spaced_get x (compat_intersect p, bools) = None
        end.
      Proof.
        (*
        TODO: to avoid unrolling, write one for pt_spaced_intersect
        
        revert p.
        (*TODO: should work, but might need to do induction on cil*)
        induction x.
        {
          unfold spaced_get, compat_intersect, pt_spaced_intersect.
          basic_goal_prep.
          destruct (split  l) as [ptl cil] eqn:Hsplit.
          cbn.
          cbv [id].
          destruct p; cbn;
            repeat (case_match; subst; cbn in 
                    2:{
          
        unfold compat_intersect.
        unfold pt_spaced_intersect.
        destruct p.
        cbn [fst snd].
        destruct (split (p :: l)) as [ptl cil] eqn:Hsplit.
        generalize dependent ptl.
        revert x p l.
        
        TODO: induction on distinguished elt cil?
              *)
      Abort.
     *)
    
  End __.

End __.

Definition sort_of := xH.
