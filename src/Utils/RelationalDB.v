(* A relational database implementation with conjunctive queries,
   for use in e-matching.
   TODO: profile, optimize performance.
   Use PArrays instead of lists in various spots 
   (can be fixed size, so don't need ArrayList, but that might be easiest first)
*)
Require Import Equalities Orders ZArith List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.
From Utils Require Import Utils Natlike ArrayList ExtraMaps NatlikePos.
From Utils Require TrieMap.
Import Sets.


Open Scope positive.

  
  (*TODO: determine whether to generalize idx/elt or just use positive*)
  (* PTree has positive keys, which means elt = positive to use it
   Then idx = positive with the only instantiation I intend to use
   *)
  (*TODO: use something other than list? for our uses list might be optimal,
    depending on how it's generated
   *)
Inductive query_trie :=
  (*Necessary for when a variable does not appear in a clause *)
  | qt_unconstrained : query_trie -> query_trie
  (* need to expose map impl or inductive is not strictly positive *)
  | qt_tree : TrieMap.map query_trie -> query_trie.

  Notation qt_nil := (qt_tree (PTree.Empty)).


Instance trie_set : set positive :=
  {
    set_as_map := TrieMap.map _;
    intersection := PTree.combine (fun a b => if a then b else None);
    union := PTree.combine (fun a b => if a then Some tt else b);
  }.

(* Includes top element, isomorphic to option *)
Variant pos_set := finite_set (m : trie_set) | all_positives.

Definition pos_set_intersection p1 p2 :=
  match p1, p2 with
  | finite_set s1, finite_set s2 => finite_set (intersection s1 s2)
  | finite_set s1, all_positives => finite_set s1
  | all_positives, finite_set s2 => finite_set s2
  | all_positives, all_positives => all_positives
  end.

Definition values_of_next_var (t : query_trie) : pos_set :=
  match t with
  | qt_tree m => finite_set (PTree.map_filter (fun _ => Some tt) m)
  | qt_unconstrained _ => all_positives
  end.
  
  Definition choose_next_val (v:positive) (t : query_trie) : query_trie :=
  match t with
  | qt_tree m => 
    match map.get m v with Some t => t | None => qt_nil end
  | qt_unconstrained t => t 
  end.   

  Fixpoint list_compare l1 l2 :=
    match l1, l2 with
    | [],[] => Eq
    | [], _ => Lt
    | _, [] => Gt
    | x1::l1, x2::l2 =>
        match BinPosDef.Pos.compare x1 x2 with
        | Eq => list_compare l1 l2
        | c => c
        end
    end.

  Axiom TODO: forall {A},A.
  
  Definition list_ltb l1 l2 :=
    match list_compare l1 l2 with
    | Lt => true
    | _ => false
    end.
  
  (* Make this an instance so we can use single-curly-braces so we don't need to qualify field-names with [SortedList.parameters.] *)
  Local Instance list_strict_order: @SortedList.parameters.strict_order _ list_ltb
    := { ltb_antirefl := TODO
       ; ltb_trans := TODO
       ; ltb_total := TODO }.

  
  Definition relation_map : map.map (list positive) unit :=
    SortedList.map (SortedList.parameters.Build_parameters (list positive) unit list_ltb)
                   list_strict_order.


  Definition relation : set (list positive) := set_from_map relation_map.

  Definition db : map.map positive relation := TrieMap.map _.

  Definition arg_map : map.map positive positive := TrieMap.map _.

  Definition Idx := positive.
  Definition elt := positive.

  (* We establish a type for conjunctive queries *)

  (*TODO: use primitive pair?*)
  Definition atom : Type := Idx (*Relation id*) * list Idx.
  Record query :=
    {
      free_vars : list Idx;
      (*TODO: list or set?*)
      clauses : list atom;
    }.



  (* TODO: figure out whether this can have duplicates
     {subst_set : set arg_map}.
   *)
Definition subst_set := list arg_map.

(*TODO: move to extramaps/Triemap *)
Definition as_list {A} :=
  TrieMap.trie_fold (B:=A) (fun m k v => (k,v)::m) [].

  

Fixpoint generic_join' (tries : @named_list Idx query_trie)
         (vars : list Idx) (acc : arg_map) : subst_set :=
  match vars with
  | [] => [acc]
  | (x::vars') =>
      let Rxs : list pos_set :=
        map (fun '(_,v) => values_of_next_var v) tries in
      let Dx := fold_left pos_set_intersection Rxs all_positives in
      (*
        If Dx is all_positives, then the variable is unconstrained.
        We will probably only guarentee the behavior of generic_join
        when all free variables appear, so the result in this case doesn't matter
       *)
      match Dx with
      | finite_set Dx =>
          flat_map (fun v => generic_join' (named_map (choose_next_val v) tries) vars'
                                           (map.put acc x v))
                   (map fst (as_list Dx))
      | all_positives => []
      end
  end.
  

  (* we need constants for residual queries in generic_join *)
  Variant argument := const_arg (c : elt) | var_arg (x : Idx).

Require Import Utils.Monad.
Fixpoint match_args args tuple : option arg_map :=
  match args, tuple with
  | [], _ => Some map.empty
  | _,[] => Some map.empty
  | (var_arg x)::args, e::tuple =>
      @! let m <- match_args args tuple in
         match map.get m x with
         | Some e' => if eqb e e' then Some m else None
         | None => Some (map.put m x e)
         end
  | (const_arg c)::args, e::tuple =>
      if eqb c e then match_args args tuple else None
  end.

Goal match_args [var_arg 1;var_arg 1;var_arg 1] [2; 3; 4] = None.
  reflexivity.
Qed.

Goal (Mbind (fun m => map.get m 1) (match_args [var_arg 1;var_arg 1;var_arg 1] [3; 3; 3]) = Some 3).
  reflexivity.
Qed.


Definition match_args_and_lookup args tuple (x : Idx) : option elt :=
  @! let m <- match_args args tuple in
     let e <- map.get m x in
     ret e.

  Definition find_values_in_relation' (x : Idx) (rel : relation) args :=
    map.fold (fun acc tuple _ =>
                match match_args_and_lookup args tuple x with
                | Some e => e::acc
                | None => acc
                end) [] rel.

#[refine]
Instance eqb_argument : Eqb argument :=
  {
    eqb a b :=
    match a,b with
    | var_arg ax, var_arg bx => eqb ax bx
    | const_arg ac, const_arg bc => eqb ac bc
    | _,_ => false
    end;
  }.
all: eapply TODO.
Defined.

(*handle unconstrained variables*)
Definition find_values_in_relation (x : Idx) (rel : relation) args :=
  if existsb (eqb (var_arg x)) args
  then Some (find_values_in_relation' x rel args)
  else None.

  Definition arg_subst v x a :=
    match a with
    | const_arg c => const_arg c
    | var_arg x' =>
        if eqb x x' then const_arg v else var_arg x'
    end.

Goal (arg_subst 2 1 (var_arg 1) = const_arg 2). reflexivity. Qed.
Goal (arg_subst 2 1 (var_arg 3) = var_arg 3). reflexivity. Qed.
Goal (arg_subst 2 1 (const_arg 1) = const_arg 1). reflexivity. Qed.
  
(*TODO: filter rel on recursive calls?*)
(* TODO: if a variable is unconstrained, need to handle it specially *)
Fixpoint build_trie' (rel: relation) (vars : list Idx) (args : list argument)
  : query_trie :=
    match vars with
    | [] => qt_nil
    | x::vars' =>
        let vs := find_values_in_relation x rel args in
        match vs with
        | Some vs =>
            qt_tree (fold_left
                       (fun m v =>
                          map.put m v (build_trie' rel vars' (map (arg_subst v x) args)))
                       vs
                       map.empty)
        | None  =>
            qt_unconstrained (build_trie' rel vars' args)
        end
    end.

  Definition build_trie (d:db) (vars : list Idx) (clause : atom) : Idx * query_trie :=
    let rel_id := fst clause in
    match map.get d rel_id with
    | Some rel => (rel_id,build_trie' rel vars (map var_arg (snd clause)))
    | None => (rel_id, qt_nil)
    end.
  
Definition build_tries (d:db) (vars : list Idx) (clauses : list atom)
  : @named_list Idx query_trie :=
    map (build_trie d vars) clauses.
           
  Definition generic_join (d : db) (q : query) : subst_set :=
    let tries := build_tries d q.(free_vars) q.(clauses) in
    generic_join' tries q.(free_vars) map.empty.
  
  Module Examples.
    Open Scope positive.

    Definition r1 : relation :=
      Sets.add_elt
        (Sets.add_elt
           map.empty
           [10; 20; 20])
        [6; 4; 5].


    Goal find_values_in_relation 1 r1 [var_arg 1; var_arg 2; var_arg 1] = Some [].
      Proof. reflexivity. Qed.
    Goal find_values_in_relation 1 r1 [var_arg 1; var_arg 2; var_arg 3] = Some [6; 10].
      Proof. reflexivity. Qed.
    Goal find_values_in_relation 1 r1 [var_arg 2; var_arg 1; var_arg 1] = Some [20].
      Proof. reflexivity. Qed.
    Goal find_values_in_relation 1 r1 [var_arg 1; var_arg 1; var_arg 2] = Some [].
      Proof. reflexivity. Qed.
    Goal find_values_in_relation 1 r1 [var_arg 1; var_arg 1; var_arg 1] = Some [].
      Proof. reflexivity. Qed.
    
    Definition r2 : relation :=
      Sets.add_elt
        (Sets.add_elt
           (Sets.add_elt
              map.empty
              [4; 56])
           [4; 52])
        [7; 65].

    
    Definition r3 : relation :=
      Sets.add_elt
        (Sets.add_elt
           map.empty
           [10; 20; 30])
        [4; 4; 5].
    
    Definition db_ex : db :=
      Eval compute in (map.put
                         (map.put
                            (map.put
                               map.empty
                               1 r1)
                            2 r2)
                         3 r3).

    Definition q1 : query :=
      Build_query [1;2;3]
                  [(1,[1;2;3]);(3,[2;2;3])].
 
    

    Definition tries := Eval compute in  (build_tries db_ex q1.(free_vars) q1.(clauses)).

    Compute (map as_list (generic_join' tries q1.(free_vars) map.empty)). 
    
    Compute (map as_list (generic_join db_ex q1)).

    (*TODO: for debugging only*)
    Definition pos_set_as_list (p:pos_set) :=
      match p with
      | all_positives => None (*TODO: change if causes debugging confusion*)
      | finite_set m => Some (map fst (as_list m))
      end.

    (*TODO: 3 should be unconstrained*)
    (* tries seem to be generated correctly *)
    Compute (named_map (fun t =>
                          (pos_set_as_list (values_of_next_var t
                       )))
                       tries). 

    Compute (intersection (set:=trie_set) (map.singleton 2 tt) (map.singleton 2 tt)).

    Let vars := Eval compute in q1.(free_vars).
    Let acc:arg_map := map.empty.

    Let Rxs := Eval compute in (map (fun '(_,v) => values_of_next_var v) tries).
    Compute (map as_list Rxs).
    Let Dx := Eval compute in ( fold_left intersection Rxs map.empty).

  Fixpoint generic_join' (tries : @named_list Idx query_trie)
           (vars : list Idx) (acc : arg_map) : subst_set :=
    match vars with
    | [] => [acc]
    | (x::vars') =>
        let Rxs : list trie_set :=
          map (fun '(_,v) => values_of_next_var v) tries in
        (*If Rxs is empty then there are no tries, i.e. no clauses
          In theory, this should allow the variables to range over all values
          This is impractical with an infinite set.
          TODO: determine what to do in this case based on what makes the proof easy
         *)
        match Rxs with
        | [] => []
        | Rx1::Rxs =>
            let Dx := fold_left intersection Rxs Rx1 in
            flat_map (fun v => generic_join' (named_map (choose_next_val v) tries) vars'
                                             (map.put acc x v))
                     (map fst (as_list Dx))
        end
    end.
