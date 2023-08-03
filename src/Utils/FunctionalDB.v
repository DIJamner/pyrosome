(* An implementation of the core of egglog
   TODO: figure out how to make the fixpoint-trie generic
 *)
Require Import Equalities Orders ZArith Lists.List Int63.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

Require Std.Sorting.Mergesort.
Module Merge := Std.Sorting.Mergesort.Sectioned.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind MapTree.
From Utils Require TrieMap TrieMapInt63.
(*From Pyrosome.Theory Require Import Core.*)
Import Sets.

Section WithMap.
  Context
    (* these first 3 types may all be the same *)
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)
      (counter : Type)
      (*TODO: any reason to have separate from idx?*)
    (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
    (allocated : counter -> idx -> Prop)
    (fresh : counter -> idx)
    (* TODO: forces idx to be infinite *)
    (fresh_is_new : forall c, ~ allocated c (fresh c))
    (incr : counter -> counter)
    (fresh_is_next : forall c, allocated (incr c) (fresh c))
    (* the type of values in the table. TODO: generalize to a symbol-dependent signature.
    (elt : Type)
    We use idx as the sole output type for now since it behaves specially wrt matching
     *).
  (*(term_args_map : map.map (list idx) elt).*)

  Definition table := (named_list (list idx) idx).
  
  (* TODO: is maintaining this as an assoc list be better? queries all perform folds, not gets *)
 Context (node_map : map.map symbol table).

  Context 
      (idx_map : forall A, map.map idx A)
      (idx_map_ok : forall A, map.ok (idx_map A)).

  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).
  
  Record instance := {
      DB : node_map;
      sort_map : idx_map idx;
      equiv : union_find;
    }.

  (* we need constants for residual queries in generic_join *)
  Variant argument := const_arg (c : idx) | var_arg (x : idx).

  (* assumption a = const_arg x *)
  Definition resolve_arg a :=
    match a with const_arg x => Some x | var_arg _ => None end.

  
  (* args_locs represents the indices of the arguments we want to match.
     for functions of the form f(x0..xn) |-> x_n+1, the index i refers to xi.
     For simplicity, we assume that any index >= n+1 refers to out.
     (Alternately, this function should only be called w/ indices up to n+1)

     Returns `Some i` if this row has i at indices l0::args_locs,
     and None if those locations do not all have the same value.
   *)
  Definition match_args (args : list idx) (out : idx) '(l0,args_locs) : option _ :=
    let v := nth l0 args out in
    if forallb (fun i => eqb v (nth i args out)) args_locs then Some v else None. 
  
  (*
  Require Import Coq.Sorting.Mergesort.
  Import NatSort. *)
  
  (*
    `split_by` sorts the table into subtables where all key indices in 'is' have the same value
    Split up into a call to mergesort and a second filter/split pass.
    This increases runtime (but not complexity), but lets us use the library mergesort.
   *)
  (*Fail Context (sort : ((list idx) * idx -> (list idx) * idx -> bool) -> table -> table).*)

  Fixpoint filter_split_sorted' (args_locs : nat * list nat) (tab : table)
    out current current_idx
    : named_list idx (named_list (list idx) idx) :=
    match tab with
    | [] => (current_idx,current)::out
    | (args,e)::tab' =>
        match match_args args e args_locs with
        | Some i =>
            if eqb i current_idx
            then filter_split_sorted' args_locs tab' out ((args,e)::current) current_idx
            else filter_split_sorted' args_locs tab' ((current_idx, current)::out) [(args,e)] i
        | None => filter_split_sorted' args_locs tab' out current current_idx
        end
    end.

  Definition filter_split_sorted args_locs tab :=
    match tab with
    | [] => []
    | (args,e)::tab' =>
        match match_args args e args_locs with
        | Some i => filter_split_sorted' args_locs tab' [] [(args,e)] i
        (* TODO: Silences errors. Consider proper error propagation *)
        | None => []
        end
    end.

  (*TODO: move to Booloeans/WithDefault*)
  Instance default_bool : WithDefault bool := false.

  Context (idx_leb : idx -> idx -> bool).
  
  Definition args_order loc0 : list idx * idx -> list idx * idx -> bool :=
    fun l1 l2 =>
      let v1 := nth loc0 (fst l1) (snd l1) in 
      let v2 := nth loc0 (fst l2) (snd l2) in 
      idx_leb v1 v2.

  Definition split_by (args_locs : nat * list nat) (tab : table)
    : named_list idx table :=
    let table' := Merge.sort (args_order (fst args_locs)) tab in
    filter_split_sorted args_locs table'.

  (*TODO: move to list utils?*)
  Fixpoint indices_of' {A} `{Eqb A} (a : A) offset l : list nat :=
    match l with
    | [] => []
    | b::l' => if eqb a b then offset::(indices_of' a (S offset) l')
               else indices_of' a (S offset) l'
    end.

  Definition indices_of {A} `{Eqb A} (a : A) l : list nat :=
     indices_of' a 0 l.

  Context (tree : map_tree idx_map).

  Definition ne_table : Type := ((list idx) * idx) * table.

  Definition ne_as_table (n : ne_table) := cons (fst n) (snd n).
  
  Coercion ne_as_table : ne_table >-> list.

  

  Definition arg_subst v x a :=
    match a with
    | const_arg c => const_arg c
    | var_arg x' =>
        if eqb x x' then const_arg v else var_arg x'
    end.

  Instance eqb_argument : Eqb argument :=
    fun a b =>
      match a,b with
      | var_arg ax, var_arg bx => eqb ax bx
      | const_arg ac, const_arg bc => eqb ac bc
      | _,_ => false
      end.


  
  Instance eqb_argument_ok : Eqb_ok eqb_argument.
  Proof using Eqb_idx_ok.
    unfold Eqb_ok, eqb, eqb_argument.
    intros a b;
      my_case Ha a;
      my_case Hb b;
      basic_goal_prep;
      try congruence.
    { eqb_case c c0; congruence. }
    { eqb_case x x0; congruence. }
  Qed.
  
  Fixpoint build_trie' (tab : ne_table) (vars : list idx) (args : list argument)
    : tree _ :=
    match vars with
    | [] =>
        (* Assumes that all arguments must be constant here.
           Implied by fvs(args) <= vars.

           Further assumes that the table is functional,
           i.e. that each key (arg list) appears at most once.
           TODO: figure out whether we need to relax this assumption,
           e.g. for semi-naive evaluation.
         *)
        leaf (m:= idx_map) (snd (fst tab))
    | x::vars' =>
        match indices_of (var_arg x) args with
        (* unconstrained *)
        | [] => top_node (build_trie' tab vars' args)
        | loc0::arg_locs =>
            let split_tab := split_by (loc0,arg_locs) tab in
            let trie_map :=
              fold_left
                (fun trie_map '(i, tab) =>
                   match tab with
                   (* Short-circuit if there are no more entries.
                      TODO: check whether this can happen.
                      If so, it means that map.get can return None on the output
                      in normal operation
                    *)
                   | [] => trie_map
                   | r1::tab' =>
                       let im := build_trie' (r1,tab') vars' (map (arg_subst i x) args) in
                       map.put trie_map i im
                   end)
                split_tab
                map.empty in
            node trie_map
        end
    end.

  (*
    clauses have the form R(x1,...xn) (|-> xn+1)?
    where xn+1, if provided, binds the output.
    atom_args should be of length either arity(R) or arity(R)+1
   *)
  Record atom :Type :=
    {
      atom_fn : symbol;
      atom_args : list idx;
    }.
  
  (* Returns None only if the clause doesn't match any rows.
     Note: may still return Some in such cases.
   *)
  Definition build_trie (nodes:node_map) (vars : list idx) (clause : atom) : option _ :=
    @!let (r1::tab) <?- map.get nodes clause.(atom_fn) in
      ret (build_trie' (r1,tab) vars (map var_arg clause.(atom_args))).

  (* Returns None only if some clause doesn't match any rows.
     Note: may still return Some in such cases.
   *)
  Definition build_tries (nodes : node_map) (vars : list idx) (clauses : list atom)
    : option (list (tree _)) :=
    list_Mmap (build_trie nodes vars) clauses.

(*
TODO: what is best wrt intersection?

Seems like the sorted-list-style map might be the best here.
- arrays (when available) are best when the keys are dense
- Sorted list is better than ptree when you have to iterate over the whole map
- ptree is better than sorted list when you need to get or to set possibly exisitng keys

Issue: building trie performs unordered insertions
Question: what dominates: unordered insertions or iteration? probably insertion
Alternately: should I build a tree then convert to a list?
2nd alt: can I define an intersection that directly builds sorted lists?
 *)
  Context (intersect : forall {A B C}, (A -> B -> C) -> tree A -> tree B -> tree C).
  Arguments intersect {A B C}%type_scope _%function_scope _ _.

  (*
    Folding over just the values of a tree map can avoid the overhead of calculating the keys.
    TODO: add this to an appropriate interface.
   *)
  Context (map_tree_fold_values : forall {A B}, (A -> B -> B) -> tree A -> B -> B).
  Arguments map_tree_fold_values {A B}%type_scope _%function_scope _ _.
  
  Fixpoint top_tree {A} var_count : tree (list A) :=
    match var_count with
    | 0 => leaf []
    | S n => top_node (top_tree n)
    end.
  
  (* We implement a simplified generic join by just iteratively intersecting the tries.
     The primary difference from standard generic join is that we do not record the full
     substitutions that satisfy the query, only the output of the functions in the query.
     This should be sufficient for our use-cases and greatly simplifies things.
   *)                                                              
  Definition generic_join' {A} (tries : list (tree A)) var_count : list _ :=
    map_tree_fold_values cons (List.fold_right (intersect cons) (top_tree var_count) tries) [].

  
  Record query :=
    {
      free_vars : list idx;
      clauses : list atom;
    }.

  (* Returns a list of all possible outputs of the query's clauses
     such that the query matches.
     Note: duplicates are possible.
   *)
  Definition generic_join (nodes : node_map) q : list (list idx) :=
    match build_tries nodes q.(free_vars) q.(clauses) with
    | None => [] (* short-circuit: includes an empty trie *)
    | Some tries => generic_join' tries (List.length q.(free_vars))
    end.

  (* Properties *)

  (*TODO: use this here? *)
  Context `{WithDefault idx}.
  
  Definition atom_args_subst args_in fvs : list idx -> list idx :=
    map (named_list_lookup default (combine args_in fvs)).
  
  Definition query_subst (args : list idx) q : list (symbol * list idx) :=
    List.map (fun clause => (clause.(atom_fn),atom_args_subst args q.(free_vars) clause.(atom_args))) q.(clauses).

  (*TODO: handles the return variable in a somewhat hacky way.
          Maybe the query should keep it separate at spec-level?
   *)  
  Definition nodes_lookup (n : node_map) '(has_ret,(s,args)) : idx :=
    let table_key := if has_ret : bool then removelast args else args in
    unwrap_with_default
      (@! let tab <- map.get n s in
         (named_list_lookup_err tab table_key)).


  (* Note: We don't need completeness for our purposes, but it should hold. *)
  Theorem generic_join_sound nodes q results
    : (*wf_query q -> (probably necessary) *)
    In results (generic_join nodes q) ->
    exists has_rets args, results = map (nodes_lookup nodes) (combine has_rets (query_subst args q)).
  Abort.

  Section __.
    Context (tab : table).
  Inductive trie_satisfies_clause' : list idx -> list argument -> _ -> Prop :=
  | empty_satisfies_no_result_match key a atom_args
    : In (key, a) tab ->
      atom_args = map const_arg key ->
      trie_satisfies_clause' [] atom_args (leaf a)
  | empty_satisfies_result_match key a atom_args
    : In (key, a) tab ->
      atom_args = map const_arg (key++[a]) ->
      trie_satisfies_clause' [] atom_args (leaf a)
  | cons_satisfies_top x fvs atom_args t
    (* rather than quantify over an arbitrary v here,
       we require that x is not in atom_args.
     *)
    : trie_satisfies_clause' fvs atom_args t ->
      trie_satisfies_clause' (x::fvs) atom_args (top_node t)
  | cons_satisfies_node x fvs atom_args m
    : (forall v t, map.get m v = Some t -> trie_satisfies_clause' fvs (map (arg_subst x v) atom_args) t) ->
      trie_satisfies_clause' (x::fvs) atom_args (node m).
  End __.
  Hint Constructors trie_satisfies_clause' : utils.
  
  Definition trie_satisfies_clause nodes fvs clause trie : Prop :=
    match map.get nodes clause.(atom_fn) with
    | Some tab => trie_satisfies_clause' tab fvs (map var_arg clause.(atom_args)) trie
    | None => False
    end.

  Definition subst_all_args s args : list argument :=
    List.fold_right (fun '(x,v) => map (arg_subst x v)) args s.
  
  (* has two disjuncts, one for including the result and one for not *)
  Definition row_can_match (args : list argument) '(key,v) :=
    exists s, (subst_all_args s args) = map const_arg (key++[v])
              \/ (subst_all_args s args) = map const_arg key.

  Definition arg_vars :=
    flat_map (fun x =>
                match x with
                | const_arg c => []
                | var_arg x' => [x']
                end).
  
  Lemma no_vars_means_all_const args
    :  incl (arg_vars args) [] ->
       exists cs, args = map const_arg cs.
  Proof.
    induction args;
      basic_goal_prep;
      [exists []
       | destruct a (*
         let x := open_constr:(_::_) in
         exists x*)];
      basic_goal_prep;
      basic_utils_crush.
    exists (c::x).
    reflexivity.
  Qed.
  
  Lemma subst_all_args_const x x0
    : subst_all_args x (map const_arg x0) = (map const_arg x0).
  Proof.
    unfold subst_all_args.
    revert x0.
    induction x;
      basic_goal_prep;
      basic_utils_crush.
    rewrite IHx.
    rewrite map_map.
    eapply map_ext.
    intros; reflexivity.
  Qed.

  (*TODO: move to List.v*)
  Lemma map_inj A B (f : A -> B)
    : (forall a a', f a = f a' -> a = a') ->
      forall l l', map f l = map f l' -> l = l'.
  Proof.
    induction l;
      destruct l';
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  (*TODO: move to Utils*)
  Hint Resolve incl_tl : utils.

  (*TODO: move to List.v*)
  Lemma incl_strengthen {A} (a:A) l1 l2
    : ~ In a l1 ->
      incl l1 (a::l2) ->
      incl l1 l2.
  Proof.
    unfold incl;
      basic_goal_prep.
    pose proof H2.
    eapply H1 in H2;
      basic_utils_crush.
  Qed.

  Lemma not_in_arg_vars a args
    : ~ In (var_arg a) args ->
      ~ In a (arg_vars args).
  Proof.
    unfold arg_vars.
    induction args;
      try case_match;
      basic_goal_prep;
      basic_utils_crush.
    revert H5;
      case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma indices_of_empty A  `{Eqb_ok A} (a:A) l
    : [] = indices_of a l ->
      ~ In a l.
  Proof.
    unfold indices_of.
    generalize 0.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    eqb_case a a0;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Require Import Coq.Sorting.Permutation.
  Import Mergesort.Sectioned.

  
  Lemma filter_split_sorted_sound i0 idxs tab v t
    : (*TODO: use regular or strong sort? (have both)*)
    Sorted.Sorted (fun x x0 => is_true (args_order i0 x x0)) tab ->
    In (v,t) (filter_split_sorted (i0, idxs) tab) ->
    incl t tab
    /\ all (fun row => all (fun i => nth i (fst row) (snd row) = v) (i0::idxs)) t.
  Proof.
    unfold filter_split_sorted;
      case_match.
    {
      basic_utils_crush.
    }
    {
      subst; break; cbn.
      set (forallb _ _) as b;
        my_case Hforallb b;
        subst b.
      2:{ basic_utils_crush. }
      basic_goal_prep.
      (*TODO: induction invariants for filter_split_sorted'*)
  Admitted.

  
  Context (idx_leb_total : forall x y, idx_leb x y = true \/ idx_leb y x = true).

    
  Lemma args_order_total x y i0
    : args_order i0 x y = true \/ args_order i0 y x = true.
  Proof.
    unfold args_order.
    eapply idx_leb_total.
  Qed.
  
  Lemma split_by_sound i0 idxs tab v t
    : In (v,t) (split_by (i0,idxs) tab) ->
      incl t tab
      /\ all (fun row => all (fun i => nth i (fst row) (snd row) = v) (i0::idxs)) t.
  Proof.
    unfold split_by.
    set (Merge.sort _ _) as l.
    assert (Permutation l tab).
    {
      symmetry.
      eapply Permuted_sort.
    }
    intro H'.
    eapply filter_split_sorted_sound in H'.
    2:{
      subst l.
      eapply Merge.Sorted_sort.
      intros; eapply args_order_total.
    }
    intuition eauto.
    unfold incl.
    intro.
    rewrite <- H0.
    eapply H1.
  Qed.
  
  Lemma row_can_match_subst a v l i args
    : (forall j, In j (indices_of (var_arg a) args) ->
                 nth j (l++[i]) v = v) ->
      row_can_match args (l, i) ->
      row_can_match (map (arg_subst a v) args) (l, i).
  Proof.
    revert l.
    induction args;
      destruct l;
      unfold row_can_match;
      basic_goal_prep.
    { exists x; eauto. }
    {
      exfalso.
      revert H1.
      (*unfold subst_all_args.
      cbv [fold_right].
      cbn.
      cbn in H1. intuition congruence. }
    
      basic_utils_crush.*)
  Admitted.
    
    
  Lemma build_trie'_sound r1 tab fvs args
    : incl (arg_vars args) fvs ->
      all (row_can_match args) (r1::tab) ->
      trie_satisfies_clause' (r1::tab) fvs args (build_trie' (r1,tab) fvs args).
  Proof.
    revert r1 tab args.
    induction fvs;
      basic_goal_prep.
    {
      break.
      
      eapply no_vars_means_all_const in H0; break; subst.
      rewrite ! subst_all_args_const in H1.
      destruct H1 as [H1 | H1];
        eapply map_inj in H1; subst;
        basic_goal_prep;
        try congruence;
        basic_utils_crush.
    }
    {
      case_match; subst; basic_goal_prep.
      {
        econstructor.
        assert (incl (arg_vars args) fvs).
        {
          eapply incl_strengthen; eauto.
          eapply not_in_arg_vars.
          eapply indices_of_empty; eauto.
          typeclasses eauto.
        }
        eapply IHfvs; basic_utils_crush.
        all: unfold row_can_match;
          exists x.
        all: [>left | right]; eauto.
      }
      {
        econstructor;
          basic_goal_prep.
        assert (t = build_trie' ((l,i), tab) fvs (map (arg_subst a v) args))
          by admit.
        {
          break;subst.
          eapply IHfvs.
          1:admit (*arg_vars lemma*).
          (* TODO:use row_can_match_subst *)
       (*   
        revert H4.
        lazymatch goal with
        | |- context [split_by (?i0, ?idxs) ?tab] =>
            pose proof (split_by_sound i0 idxs tab) as H';
            revert H';
            set (split_by _ _)
        end.
        intros.
        intro H4.
        Set Printing Coercions.
        cbv in n0.
        eapply split_by_sound in 

        TODO: nested ind on the split_by?
        revert t H4.
        eapply Properties.map.map_ind.
        TODO: nested map induction
        eapply IHfvs.
      }
    }
  Qed.*)
  Admitted.
    
  Lemma build_trie_sound nodes fvs clause tries
    : incl (arg_vars (map var_arg clause.(atom_args))) fvs ->
      (forall tab, map.get nodes clause.(atom_fn) = Some tab ->
                   all (row_can_match (map var_arg clause.(atom_args))) tab) ->
      build_trie nodes fvs clause = Some tries ->
      trie_satisfies_clause nodes fvs clause tries.
  Proof.
    unfold build_trie, trie_satisfies_clause.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
    revert H2;
    case_match;
      basic_goal_prep;
      basic_utils_crush.
    eapply build_trie'_sound; eauto.
  Qed.     
  
  (* Only the Some case is necessary in the soundness direction *)
  Lemma build_tries_sound nodes fvs clauses tries
    : all (fun c => incl (arg_vars (map var_arg c.(atom_args))) fvs) clauses ->
      all (fun c => forall tab, map.get nodes c.(atom_fn) = Some tab ->
                                all (row_can_match (map var_arg c.(atom_args))) tab)
        clauses ->
    build_tries nodes fvs clauses = Some tries ->
      all2 (trie_satisfies_clause nodes fvs) clauses tries.
  Proof.
    revert tries; induction clauses;
      basic_goal_prep;
      basic_utils_crush.
    revert H2; case_match;
      basic_utils_crush.
    revert H2; case_match;
      basic_utils_crush.
    eapply build_trie_sound; eauto.
  Qed.

End WithMap.

Module PositiveIdx.

  (*TODO: move to Eqb or sim. locaion *)
  Instance positive_Eqb : Eqb positive := Pos.eqb.

  

  Definition generic_join_pos :=
    generic_join positive _ positive (TrieMap.map _)
      TrieMap.map Pos.leb positive_map_tree (@map_tree_intersect)
      (@map_tree_fold_values).

  Local Open Scope positive.
  Example db1 : TrieMap.map (table _) :=
    map.put
      (map.put map.empty 1 [([2;2;3], 1); ([2;3;3], 10)])
      2 [([8;4], 3); ([3;1], 2)].

  Local Notation query := (query positive positive).

  Example query1 : query :=
    Build_query _ _ [3;1;2;4;5;6]
      [
        Build_atom _ _ 1 [4;5;6];
        Build_atom _ _ 2 [2;3];
        Build_atom _ _ 1 [1;1;2;3]
      ].
  Compute (generic_join_pos db1 query1).
  
  Example query2 : query :=
    Build_query _ _ [1;2;3]
      [
        (*TODO: bug w/ non-first arg as dup? the atom below should match 2;3;3 -> 10*)
        Build_atom _ _ 1 [1;2;2;3]
      ].

  Compute (generic_join_pos db1 query2).
End PositiveIdx.

  

 (* (*TODO: Does reachable being reflexive cause a problem?
    Really want a PER since malformed terms shouldn't count? *)

  Axiom lookup : term symbol -> instance -> option idx.
  Axiom sort_of : forall {V}, lang V -> ctx V -> term V -> sort V.

  (* TODO: extend to support existentials *)
  (* Assumes no sort eqns in l (and so does not store sorts in instance) *)
  Definition valid_instance l c (i : instance) :=
    (forall i' t, lookup t i = Some i' -> interp_uf (equiv i) i' i')
    /\ (forall t1 i1 t2 i2, interp_uf (equiv i) i1 i2 ->
                            lookup t1 i = Some i1 ->
                           lookup t2 i = Some i2 ->
                           eq_term l c (sort_of l c t1) t1 t2).
  *)
