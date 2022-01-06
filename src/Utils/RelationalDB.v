(* A relational database implementation with conjunctive queries,
   for use in e-matching.
   TODO: profile, optimize performance.
   Use PArrays instead of lists in various spots 
   (can be fixed size, so don't need ArrayList, but that might be easiest first)
*)
Require Import Equalities Orders ZArith List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils Natlike ArrayList ExtraMaps.
Import Sets.

Section QueryTrie.

  Context (A : Type).
  
  (*TODO: determine whether to generalize idx/elt or just use positive*)
  (* PTree has positive keys, which means elt = positive to use it
   Then idx = positive with the only instantiation I intend to use
   *)
  (*TODO: use something other than list? for our uses list might be optimal,
    depending on how it's generated
   *)
  Inductive query_trie :=
  | qt_nil
  (* TODO: use map from A to tries?
     Currently includes duplication
     TODO: need to expose map impl or inductive is not strictly positive
   *)
  | qt_tree : @named_list A query_trie -> query_trie.

  
  Definition values_of_next_var (t : query_trie) : list A :=
    match t with
    | qt_tree l => map fst l
    | _ => []
    end.

  Context `{Eqb A}.
  
  Definition choose_next_val (v:A) (t : query_trie) : query_trie :=
    match t with
    | qt_nil => qt_nil
    | qt_tree l => named_list_lookup qt_nil l v
    end.

End QueryTrie.

Arguments values_of_next_var {_}.
Arguments choose_next_val {_}%type {_}.

Arguments qt_nil {_}%type_scope.
Arguments qt_tree {_}%type_scope _.


Section WithIdx.
  (*Idx type used for relation ids and variables *)
  Context (Idx : Type) {natlike_idx : Natlike Idx}.
  (* elt is the type of elements of a relation *)
  Context (elt : Type) {elt_eqb : Eqb elt}
          {elt_default : WithDefault elt (*not necessary, just convenient*)}.

  (*invariant: all lists have the same length
   *)
  Context {relation : set (list elt)}.

  (* We distinguish the relation id as a key for efficiency *)
  Context {db : map.map Idx relation}.

  (* We establish a type for conjunctive queries *)

  (*TODO: use primitive pair?*)
  Definition atom : Type := Idx (*Relation id*) * list Idx.
  Record query :=
    {
      free_vars : list Idx;
      (*TODO: list or set?*)
      clauses : list atom;
    }.



  Context {arg_map : map.map Idx elt}
          {id_set : set Idx}
          {elt_set : set elt}.
  (* TODO: figure out whether this can have duplicates
     {subst_set : set arg_map}.
   *)
  Definition subst_set := list arg_map.


  Fixpoint generic_join' (tries : @named_list Idx (query_trie elt))
           (vars : list Idx) (acc : arg_map) : subst_set :=
    match vars with
    | [] => [acc]
    | (x::vars') =>
        let Dx := fold_left (fun l '(_,v) => (values_of_next_var v)++l) tries [] in
        flat_map (fun v => generic_join' (named_map (choose_next_val v) tries) vars'
                                         (map.put acc x v))
                 Dx
    end.
  

  (* we need constants for residual queries in generic_join *)
  Variant argument := const_arg (c : elt) | var_arg (x : Idx).

  Fixpoint match_args_put (x : Idx) (e : elt) l :=
    match l with
    | [] => [(x,e)]
    | (x',e') ::l =>
        if eqb x x' then if eqb e e' then (x',e')::l else []
        else (x',e')::(match_args_put x e l)
    end.
  
  Fixpoint match_args args tuple :=
    match args, tuple with
    | [], _ => []
    | _,[] => []
    | (var_arg x)::args, e::tuple =>
        match_args_put x e (match_args args tuple)
    | (const_arg c)::args, e::tuple =>
        if eqb c e then match_args args tuple else []
    end.


  Definition find_values_in_relation x (rel : relation) args :=
    map.fold (fun acc tuple _ =>
                match named_list_lookup_err (match_args args tuple) x with
                | Some e => e::acc
                | _ => acc
                end) [] rel.

  Definition arg_subst v x a :=
    match a with
    | const_arg c => const_arg c
    | var_arg x' =>
        if eqb x x' then const_arg v else var_arg x'
    end.
  
  (*TODO: filter rel on recursive calls?*)
  Fixpoint build_trie' (rel: relation) (vars : list Idx) (args : list argument) : (query_trie elt) :=
    match vars with
    | [] => qt_nil
    | x::vars' =>
        let vs := find_values_in_relation x rel args in
        qt_tree (map (fun v => (v, build_trie' rel vars' (map (arg_subst v x) args))) vs)
    end.

  Definition build_trie (d:db) (vars : list Idx) (clause : atom) : Idx * (query_trie elt) :=
    let rel_id := fst clause in
    match map.get d rel_id with
    | Some rel => (rel_id,build_trie' rel vars (map var_arg (snd clause)))
    | None => (rel_id, qt_nil)
    end.
  
  Definition build_tries (d:db) (vars : list Idx) (clauses : list atom) : @named_list Idx (query_trie elt) :=
    map (build_trie d vars) clauses.
           
  Definition generic_join (d : db) (q : query) : subst_set :=
    let tries := build_tries d q.(free_vars) q.(clauses) in
    generic_join' tries q.(free_vars) map.empty.
  
End WithIdx. 

Arguments generic_join {_}%type {_} {_}%type {_ _ _ _} _ _.
Arguments free_vars {_}%type.
Arguments clauses {_}%type.


From coqutil Require Map.SortedList.
From Utils Require TrieMap NatlikePos.

Module MinimalPositiveInstantiation.

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

  Notation query := (query positive).

  Definition arg_map : map.map positive positive := TrieMap.map _.
  
  Definition generic_join : db -> query -> list arg_map :=
    @generic_join _ _ _ _ _ _ _.

  Module Examples.
    Open Scope positive.

    Definition r1 : relation :=
      Sets.add_elt
        (Sets.add_elt
           map.empty
           [10; 20; 20])
        [6; 4; 5].

    
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
        [4; 4; 8].
    
    Definition db_ex : db :=
      Eval compute in (map.put
                         (map.put
                            (map.put
                               map.empty
                               1 r1)
                            2 r2)
                         3 r3).

    Definition q1 : query :=
      Build_query _
                  [(*1; 2; 3;*) 1; 2]
                  [(*(1,[1;2;3]); *)(2, [1;2])].


    Compute (build_tries _ _ db_ex q1.(free_vars) q1.(clauses)). 
    
    Definition as_list {A} :=
      TrieMap.trie_fold (B:=A) (fun m k v => (k,v)::m) [].
    (*TODO: duplicates some results; should actually use a set?*)
    (*TODO: seems bugged on 2nd clause*)
    Compute (map as_list (generic_join db_ex q1)).

  End Examples.
           
  
End MinimalPositiveInstantiation.

