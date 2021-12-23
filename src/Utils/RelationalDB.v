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

  (* we need constants for residual queries in generic_join *)
  Variant argument := const_arg (c : elt) | var_arg (x : Idx).
  (*TODO: use primitive pair?*)
  Definition atom : Type := Idx (*Relation id*) * list argument.
  Record query :=
    {
      free_vars : list Idx;
      (*TODO: list or set?*)
      clauses : list atom;
    }.


  
  Lemma invert_const_const x y
    : const_arg x = const_arg y <-> x = y.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_const_const : utils.
  Lemma invert_const_var x y
    : const_arg x = var_arg y <-> False.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_const_var : utils.
  Lemma invert_var_const x y
    : var_arg x = const_arg y <-> False.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_var_const : utils.
  Lemma invert_var_var x y
    : var_arg x = var_arg y <-> x = y.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_var_var : utils.
  
  #[refine]
   Instance eqb_argument : Eqb argument :=
    {|
      eqb a b := match a, b with
                 | const_arg ca, const_arg cb => eqb ca cb
                 | var_arg xa, var_arg xb => eqb xa xb
                 | _ , _ => false
                 end
    |}.
  {
    destruct n; destruct m; simpl; basic_utils_crush.
  }
  {
    destruct x; destruct y; simpl; basic_utils_crush.
  }
  {
    destruct x; simpl; basic_utils_crush.
  }
  Admitted.

  Context {arg_map : map.map Idx elt}
          {id_set : set Idx}
          {elt_set : set elt}
          {subst_set : set arg_map}.

  Axiom (trie : Type).
  Context (trie_map : map.map Idx trie).

  Axiom value_of_next_var : trie -> elt.

  Axiom choose_next_val : elt -> trie -> trie.
  Axiom union : subst_set -> subst_set -> subst_set.

  Axiom trie_map_map : (trie -> trie) -> trie_map -> trie_map.

  Fixpoint generic_join' (tries : trie_map) (vars : list Idx) (acc : arg_map) : subst_set :=
    match vars with
    | [] => map.singleton acc tt
    | (x::vars') =>
        let Dx := map.fold (fun l _ v => (value_of_next_var v)::l) [] tries in
        fold_left union
            (map (fun v => generic_join' (trie_map_map (choose_next_val v) tries) vars' (map.put acc x v)) Dx)
            map.empty
    end.

  Axiom build_tries : list Idx -> list atom -> trie_map.
           
  Definition generic_join (d : db) (q : query) : subst_set :=
    let tries := build_tries q.(free_vars) q.(clauses) in
    generic_join' tries q.(free_vars) map.empty.
  
End WithIdx.

Arguments generic_join {_ _}%type {_ _ _ _}.
