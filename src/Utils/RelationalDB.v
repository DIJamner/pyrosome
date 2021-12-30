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
  (* an optimization for cases where the variable doesn't appear in the relation
     TODO: use or no? it's a bit tricky
  | qt_unconstrained : query_trie -> query_trie
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
          {elt_set : set elt}
          {subst_set : set arg_map}.


  Fixpoint generic_join' (tries : @named_list Idx (query_trie elt))
           (vars : list Idx) (acc : arg_map) : subst_set :=
    match vars with
    | [] => map.singleton acc tt
    | (x::vars') =>
        let Dx := fold_left (fun l '(_,v) => (values_of_next_var v)++l) tries [] in
        fold_left union
            (map (fun v => generic_join' (named_map (choose_next_val v) tries) vars' (map.put acc x v)) Dx)
            map.empty
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

Arguments generic_join {_}%type {_} {_}%type {_ _ _ _ _} _ _.
