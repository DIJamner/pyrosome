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
From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps NatlikePos.
From Utils Require TrieMap.
Import Sets.

Section SetWithTop.
  Context {A : Type}
          {A_set : set A}.
  (* Includes top element, isomorphic to option *)
  Variant set_with_top := finite_set (m : A_set) | all_elements.

  Definition set_with_top_intersection p1 p2 :=
    match p1, p2 with
    | finite_set s1, finite_set s2 => finite_set (intersection s1 s2)
    | finite_set s1, all_elements => finite_set s1
    | all_elements, finite_set s2 => finite_set s2
    | all_elements, all_elements => all_elements
    end.
End SetWithTop.

Arguments set_with_top {A}%type_scope A_set.


(* We need to expose the map implelementation or query_trie is not strictly positive.
   We cordon it off into its own module so that the rest can be parametric over idx and elt.
 *)
Module PositiveQueryTrie.
  
  Open Scope positive.
  Inductive query_trie :=
  (*Necessary for when a variable does not appear in a clause *)
  | qt_unconstrained : query_trie -> query_trie
  (* need to expose map impl or inductive is not strictly positive *)
  | qt_tree : TrieMap.map query_trie -> query_trie.

  Notation qt_nil := (qt_tree (PTree.Empty)).

  #[export] Instance trie_set : set positive :=
    {
      set_as_map := TrieMap.map _;
      intersection := PTree.combine (fun a b => if a then b else None);
      union := PTree.combine (fun a b => if a then Some tt else b);
    }.

  Definition values_of_next_var (t : query_trie) : set_with_top trie_set :=
    match t with
    | qt_tree m => finite_set (PTree.map_filter (fun _ => Some tt) m)
    | qt_unconstrained _ => all_elements
    end.

  Definition choose_next_val (v:positive) (t : query_trie) : query_trie :=
    match t with
    | qt_tree m => 
        match map.get m v with Some t => t | None => qt_nil end
    | qt_unconstrained t => t 
    end.
End PositiveQueryTrie.


(* Make all functions parametric over the indices and elements *)
Section __.
  (*Idx type used for relation ids and variables *)
  Context (idx : Type) {natlike_idx : Natlike idx}.
  (* elt is the type of elements of a relation *)
  Context (elt : Type) {elt_eqb : Eqb elt}
          {elt_default : WithDefault elt (*not necessary, just convenient*)}.

  Context (elt_set : set elt).

  (*Parameterize by query trie since the inductive can't be defined generically *)
  Context (query_trie : Type)
          (qt_unconstrained : query_trie -> query_trie)
          (trie_map : map.map elt query_trie)
          (qt_tree : trie_map -> query_trie)
          (values_of_next_var : query_trie -> set_with_top elt_set)
          (choose_next_val : elt -> query_trie -> query_trie).

  Notation qt_nil := (qt_tree map.empty).

  Context (relation : set (list elt))
          (db : map.map idx relation)
          (arg_map : map.map idx elt).


  (* We establish a type for conjunctive queries *)

  (*TODO: use primitive pair?*)
  Definition atom : Type := idx (*Relation id*) * list idx.
  Record query :=
    {
      free_vars : list idx;
      (*TODO: list or set?*)
      clauses : list atom;
    }.


(* TODO: figure out whether this can have duplicates
     {subst_set : set arg_map}.
 *)
Definition subst_set := list arg_map.

Fixpoint generic_join' (tries : @named_list idx query_trie)
         (vars : list idx) (acc : arg_map) : subst_set :=
  match vars with
  | [] => [acc]
  | (x::vars') =>
      let Rxs :=
        map (fun '(_,v) => values_of_next_var v) tries in
      let Dx := fold_left set_with_top_intersection Rxs all_elements in
      (*
        If Dx is all_positives, then the variable is unconstrained.
        We will probably only guarentee the behavior of generic_join
        when all free variables appear, so the result in this case doesn't matter
       *)
      match Dx with
      | finite_set Dx =>
          map.fold
            (fun l v _ =>
               (generic_join' (named_map (choose_next_val v) tries) vars'
                              (map.put acc x v))
                 ++l)
            []
            Dx
      | all_positives => []
      end
  end.


(* we need constants for residual queries in generic_join *)
Variant argument := const_arg (c : elt) | var_arg (x : idx).

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

Definition match_args_and_lookup args tuple (x : idx) : option elt :=
  @! let m <- match_args args tuple in
     let e <- map.get m x in
     ret e.

Definition find_values_in_relation' (x : idx) (rel : relation) args :=
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
Definition find_values_in_relation (x : idx) (rel : relation) args :=
  if existsb (eqb (var_arg x)) args
  then Some (find_values_in_relation' x rel args)
  else None.

Definition arg_subst v x a :=
  match a with
  | const_arg c => const_arg c
  | var_arg x' =>
      if eqb x x' then const_arg v else var_arg x'
  end.


(*TODO: filter rel on recursive calls?*)
(* TODO: if a variable is unconstrained, need to handle it specially *)
Fixpoint build_trie' (rel: relation) (vars : list idx) (args : list argument)
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

Definition build_trie (d:db) (vars : list idx) (clause : atom) : idx * query_trie :=
  let rel_id := fst clause in
  match map.get d rel_id with
  | Some rel => (rel_id,build_trie' rel vars (map var_arg (snd clause)))
  | None => (rel_id, qt_nil)
  end.

Definition build_tries (d:db) (vars : list idx) (clauses : list atom)
  : @named_list idx query_trie :=
  map (build_trie d vars) clauses.

Definition generic_join (d : db) (q : query) : subst_set :=
  let tries := build_tries d q.(free_vars) q.(clauses) in
  generic_join' tries q.(free_vars) map.empty.

End __.

Module PositiveInstantiation.
  
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

Export PositiveQueryTrie.

Definition generic_join (d : db) (q : query _) : subst_set _ _ arg_map :=
  generic_join positive positive
               trie_set query_trie qt_unconstrained _ qt_tree
               values_of_next_var choose_next_val relation db arg_map d q.

#[global] Notation atom := (atom positive).
#[global] Notation query := (query positive).
#[global] Notation Build_query := (Build_query positive).

End PositiveInstantiation.

  
Module Examples.
  Open Scope positive.
  Import PositiveInstantiation.

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
  
End Examples.
