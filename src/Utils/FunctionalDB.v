(* An implementation of the core of egglog
 *)
Require Import Equalities Orders ZArith Lists.List Int63.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

Require Std.Sorting.Mergesort.
Module Merge := Std.Sorting.Mergesort.Sectioned.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind MapTreeN.
From Utils Require TrieMap TrieMapInt63.
(*From Pyrosome.Theory Require Import Core.*)
Import Sets.
  

Section WithMap.
  Context
    (* these first 3 types may all be the same *)
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)
      (*TODO: any reason to have separate from idx?*)
    (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
    (* the type of values in the table. TODO: generalize to a symbol-dependent signature.
    (elt : Type)
    We use idx as the sole output type for now since it behaves specially wrt matching
     *).
  (*(term_args_map : map.map (list idx) elt).*)

  Definition table := (named_list (list idx) idx).
  
 Context (symbol_map : forall A, map.map symbol A).

  Context 
      (idx_map : forall A, map.map idx A)
      (idx_map_ok : forall A, map.ok (idx_map A)).

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
    : ntree idx idx (List.length vars) :=
    match vars as v' return ntree idx idx (List.length v') with
    | [] =>
        (* Assumes that all arguments must be constant here.
           Implied by fvs(args) <= vars.

           Further assumes that the table is functional,
           i.e. that each key (arg list) appears at most once.
           TODO: figure out whether we need to relax this assumption,
           e.g. for semi-naive evaluation.
         *)
        snd (fst tab)
    | x::vars' =>
        match indices_of (var_arg x) args with
        (* unconstrained *)
        | [] => inr (build_trie' tab vars' args)
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
            inl trie_map
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
      (* TODO: should I keep this separate? atom_conclusion : idx; *)
    }.

  Definition node_map := symbol_map table.
  
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
    : option (list _) :=
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

  
  Fixpoint top_tree {A} var_count : ntree idx (list A) var_count :=
    match var_count with
    | 0 => []
    | S n => inr (top_tree n)
    end.

  Context `{@map_plus idx idx_map}.
  
  (* We implement a simplified generic join by just iteratively intersecting the tries.
     Note: the running time here is proportional to the second-largest trie in the worst case,
     whereas it should be proportional to the smallest.
     Potential solutions: lazy tries &/or special nary-intersect (second seems easier than first)
   *)                                                              
  Definition generic_join' {A} var_count (tries : list (ntree idx A var_count)) : list _ :=
    ntree_fold _ (fun acc k _ => cons k acc)
      var_count
      (List.fold_right (ntree_intersect cons var_count) (top_tree var_count) tries) [].

  
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
    | Some tries => generic_join' (List.length q.(free_vars)) tries
    end.

  (* Properties *)

  (*TODO: use this here? *)
  Context `{WithDefault idx}.

  (*TODO: is the combine in the right order?*)
  Definition atom_args_subst args_in fvs : list idx -> list idx :=
    map (named_list_lookup default (combine fvs args_in)).
  
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

  (*
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
*)

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

  (*
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
*)
(*
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
 *)

  Definition db_map := symbol_map {n & (ntree idx idx n)}.

  Context `{@map_plus symbol symbol_map}.

  Definition flatten_db : db_map -> node_map :=
    map_map (fun p => ntree_to_tuples _ (projT1 p) (projT2 p)).
    
  
  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).

  
  Record instance := {
      db : db_map;
      (*sort_map : idx_map idx;*)
      equiv : union_find;
      (* TODO: maintain an upper bound on the number of rows in db
         for the purpose of ensuring termination?
       
      size : nat;*)
    }.

  Import StateMonad.

  Definition table_put n (t : ntree idx idx n) uf ks v :=
     match ntree_get _ n t ks with
     | Some v1 =>
         (*TODO: union shouldn't ever fail? check this &/or make non-option union *)
         match UnionFind.union _ _ _ _ uf v v1 with
         | Some (uf',v') =>
            (* Note: needs rebuilding*)
             (v', t, uf')
         | None => (*should never happen if v in uf *) (v, t, uf)  
         end
        | None =>
            let t' := ntree_set _ n t ks v in
            (v, t', uf)            
        end.

  (* TODO: assumes idx merge fn. Generalize.
     TODO: why the option out?
   *)
  Definition db_put s ks v i : idx * instance :=
    match map.get i.(db) s with
    | Some (existT _ n t) =>
        let '(v', t', uf') := table_put _ t i.(equiv) ks v in
        let db' := map.put i.(db) s (existT _ n t') in
        (v,Build_instance db' uf')
    | None =>
        let s_ntree := ntree_singleton _ (List.length ks) ks v in
        let db' := map.put i.(db) s (existT _ (List.length ks) s_ntree) in
        (v, Build_instance db' i.(equiv))
    end.

  Context (idx_succ : idx -> idx).
  
  Definition db_get s ks : stateT instance option idx :=
    fun i =>
      (* TODO: abstact out the 'mutate value' pattern? *)
      @! let (existT _ n t) <- map.get i.(db) s in
        match ntree_get _ n t ks with
        | Some v => Some (v, i)
        | None =>
            let (uf',v) := alloc _ _ _ idx_succ i.(equiv) in
            let t' := ntree_set _ n t ks v in
            let db' := map.put i.(db) s (existT _ n t') in
            Some (v,Build_instance db' uf')            
        end.

  Definition find' (v : idx) : stateT _ option idx :=
    fun uf => @!let p <- UnionFind.find _ _ _ _ uf v in ret (snd p, fst p).
  
  (*TODO: write instead in terms of node_map?*)
  Definition rebuild_ntree' (uf : union_find) n (t : ntree idx idx (S n))
    : (ntree idx idx (S n) * union_find * bool) :=
    ntree_fold (key:=idx) _ (fun '(t,uf, changed) keys v =>
                    unwrap_with_default (H:=(t,uf,changed))
                      (@! let {option} (keys',uf1) <- list_Mmap (M:= stateT _ option) find' keys uf in
                         let {option} (v', uf2) <- find' v uf1 in
                         let (_,t', uf') := table_put _ t uf keys' v' in
                         let changed' := (changed || eqb v v')%bool in
                         ret {option} (t',uf',changed')))
       (S n) t (inl map.empty : ntree idx idx (S n),uf,false).
    
  (*TODO: `unwrap_with_default` assumes presence in uf. Is this the best way to handle things? *)
  Definition rebuild_ntree (uf : union_find) n : ntree idx idx n -> (ntree idx idx n * union_find*bool) :=
    match n with
    (* can always mark changed as false here, since rebuilding a tree0 needs at most one update *)
    | 0 => fun x => unwrap_with_default (H:=(x,uf,false)) (Mfmap (fun x => (x,false)) (find' x uf))
    | S n' => rebuild_ntree' uf n'
    end.
                               
  Definition rebuild_once i : instance * bool :=
      map.fold (fun '(acc, has_changed) k '(existT _ n v) =>
                  let '(v', uf', v_has_changed) := rebuild_ntree acc.(equiv) n v in
                  (Build_instance (map.put acc.(db) k (existT _ n v')) uf',
                    (has_changed || v_has_changed)%bool))
        (Build_instance map.empty i.(equiv),false) i.(db).

  Fixpoint rebuild' limit (i : instance) : instance :=
    match limit with
    | 0 => i
    | S n =>
        let '(i',changed) := rebuild_once i in
        if changed then rebuild' n i' else i'
    end.

  (* Note: partial rebuilding is sound but not complete.
         We use a bound of 100 for now.
         On strange match failures, check this.
   *)
  Definition rebuild (i : instance) : instance := rebuild' 100 i.
  
  (*TODO: rebuilding process requires non-functional dbs at intermediate steps
    once we use non-idx merges
   *)
  (*
    TODO: do I want to support let_query? I don't have a use for it right now
    and generally, multiple queries is a bad idea since they should be bundled into one
    instead: log_exp an upd_exp
   *)
  Inductive log_upd : Type :=
  | put_row : atom -> idx (* var *) -> log_upd -> log_upd
  | let_row : atom -> idx (* binder *) -> log_upd -> log_upd
  | unify : idx -> idx -> log_upd -> log_upd
  | done : log_upd.

  Record op_state : Type :=
   Mk_state {
      data : instance;
      env : idx_map idx;
      changed : bool;
     }.
  
  Definition do_unify a b : state op_state unit :=
    fun s =>
      (* shortcut when equal so that changed remains false *)
      if eqb a b then (tt,s) else
      match UnionFind.union _ _ _ _ s.(data).(equiv) a b with
      | Some (uf,_) => (tt,Mk_state (Build_instance s.(data).(db) uf) s.(env) true)
      | None => (tt,s) (* shouldn't happen *)
      end.

  (* assumes the input is in the domain *)
  Definition sub (env : idx_map idx) i : idx :=
    unwrap_with_default (map.get env i).

  Definition do_put_row a i : state op_state unit :=
    fun s =>
      let f := a.(atom_fn) in
      let args := map (sub s.(env)) a.(atom_args) in
      let val := sub s.(env) i in
      let (_, d) := db_put f args val s.(data) in
      (tt, Mk_state d s.(env) true).

  (* Assumes that the symbol of a corresponds to a real table *)
  Definition do_let_row a x : state op_state unit :=
    fun s =>
      let f := a.(atom_fn) in
      let args := map (sub s.(env)) a.(atom_args) in
      match db_get f args s.(data) with
      | Some (i, d) =>
          (tt, Mk_state d (map.put s.(env) x i) true)          
      | None => (tt,s) (* shouldn't happen *)
      end.
  
  (* TODO: generate differential instance?
   *)
  Fixpoint apply_upd (l : log_upd) : state op_state unit :=
      match l with
      | unify i1 i2 k =>
          @! let _ <- do_unify i1 i2 in
            (apply_upd k)
      | put_row a i k => 
          @! let _ <- do_put_row a i in
            (apply_upd k)
      | let_row a x k => 
          @! let _ <- do_let_row a x in
            (apply_upd k)
      | done => Mret tt
      end.
        
  
  (*
    Note: should be able to generate terms (e.g. proofs of internal facts like neq) in addition to equalities!
   *)
  Record log_op : Type :=
    {
      (*
        We generalized the conclusion :- assumption ... pattern from core egglog
        to better support multiple operations being performed on the results of a single match.
        log_ops behave as follows:
        - run `assumptions` query
        - for each substitution in the result, run the update program

       This is useful for things like recording `sort_of` entries at the same time as terms are added to the db

       TODO: w/ advanced enough optimization, it will be worth generalizing further to a program
       made up of an (ordered) sequence of queries and conclusions, to take advantage of subqueries.
       Note: Use the var/const split for this
       *)
      update : log_upd;
      assumptions : query;
    }.
  
  Definition log_program : Type := list log_op.

  Definition opt_to_list {A} o : list A :=
    match o with Some x => [x] | None => [] end.

  (*
  Definition make_query l :=
    let c_vars := (opt_to_list (snd l.(conclusion)) ++ atom_args (fst l.(conclusion))) in
    let vars := List.dedup (eqb (A:=_))
                  (List.fold_left (app (A:=_))
                     (map atom_args l.(assumptions)) c_vars) in
    Build_query vars l.(assumptions).
   *)

  (*
  (*TODO: how to tell arity of conclusion to differentiate val var and no val var?*)
  Definition apply_join_sub c fvs s : atom * option idx :=
    let '(Build_atom f args,out) := c in
    let args' := atom_args_subst s fvs args in
    (Build_atom f args',Mfmap (named_list_lookup default (combine fvs s)) out).*)

  Definition db_alloc '(Build_instance db equiv) : idx * instance :=
    let '(equiv',v):= alloc _ _ _ idx_succ equiv in
    (v, Build_instance db equiv').

  (* TODO: move to Monad.v *)
  Section __.
    Context {M : Type -> Type} `{Monad M} {A B : Type} (f : A -> M (list B)).
    Fixpoint list_Mflatmap (l : list A) : M (list B) :=
      match l with
      | [] => @! ret []
      | a::al' =>
          @! let b <- f a in
            let bl' <- list_Mflatmap al' in
            ret (b++bl')
      end.
  End __.

  Definition state_upd {S} (f : S -> S) : state S unit := fun s => (tt, f s).

  Fixpoint fold_updates has_changed upd subs : state instance bool :=
    match subs with
    | [] => Mret has_changed
    | s::subs' =>
        @! let s_changed <- fun i =>
                            let (_,op_s) := apply_upd upd (Mk_state i s has_changed) in
                            (op_s.(changed), op_s.(data)) in
          let subs'_changed <- fold_updates has_changed upd subs' in
          ret orb s_changed subs'_changed
    end.

  (* TODO: generate differential instance? *)
  Definition apply_op changed (l : log_op) : state instance bool :=
    fun i =>
      (* TODO: precompute, choose a good var order as part of query optimization *)
      let q := l.(assumptions) in
      let subs := generic_join (flatten_db i.(db)) q in
      let sub_maps := map (fun s => map.of_list (combine q.(free_vars) s)) subs in
      (fold_updates changed l.(update) sub_maps i).
    
  Definition run_once (p : log_program) : state instance bool :=
    list_Mfoldl apply_op p false.    
  
  Fixpoint run (p : log_program) n i : instance :=
    match n with
    | 0 => i
    | S n =>
        let (changed,i') := run_once p i in
        if changed then run p n (rebuild i') else i
    end.


End WithMap.

Module PositiveIdx.

  (*TODO: move to Eqb or sim. locaion *)
  Instance positive_Eqb : Eqb positive := Pos.eqb.

  Definition generic_join_pos :=
    generic_join positive _ positive (TrieMap.trie_map)
      TrieMap.trie_map Pos.leb (H:=TrieMap.ptree_map_plus).

  Local Open Scope positive.
  Example db1 : TrieMap.trie_map (table _) :=
    map.put
      (map.put map.empty 10 [([7;7;3], 1); ([7;3;3], 9)])
      20 [([8;4], 3); ([3;1], 7)].

  Local Notation query := (query positive positive).

  Example query1 : query :=
    Build_query _ _ [3;1;2;4;5;6]
      [
        Build_atom _ _ 10 [4;5;6];
        Build_atom _ _ 20 [2;3];
        Build_atom _ _ 10 [1;1;2;3]
      ].
  Time Compute (generic_join_pos db1 query1).
  
  Example query2 : query :=
    Build_query _ _ [1;2;3]
      [
        Build_atom _ _ 10 [1;2;2;3]
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
