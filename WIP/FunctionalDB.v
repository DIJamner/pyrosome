(* An implementation of the core of egglog
   TODO: figure out how to make the fixpoint-trie generic
 *)
Require Import Equalities Orders ZArith Lists.List Int63.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.
From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind MapTree.
From Utils Require TrieMap TrieMapInt63.
From Pyrosome.Theory Require Import Core.
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
    (elt : Type).
  (*(term_args_map : map.map (list idx) elt).*)

  Definition table := (named_list (list idx) elt).
  
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

  (*Note: map.fold might be slow.
    TODO: make sure I have an efficient fold available

    Idea: go from var : list var, DB : cargs |-> id and a : arguments to
    t : map_tree arg_id id
    Process of using t: (lazy?) intersect w/ other clauses

   *)

  Definition match_args (args : list idx) '(loc0,args_locs) : option _ :=
    @! let (v::vals) <?- list_Mmap (nth_error args) (loc0::args_locs) in
      let! forallb (eqb v) vals in
      ret v.
  
  (*
  Require Import Coq.Sorting.Mergesort.
  Import NatSort. *)
  
  (*
    `split_by` sorts the table into subtables where all key indices in 'is' have the same value
    Split up into a call to mergesort and a second filter/split pass.
    This increases runtime (but not complexity), but lets us use the library mergesort.

    Unfortunately the standard library sort is defined in a (Module) functor,
    so we can neither use it in a section, nor instantiate it with an `args_locs`-dependent comparison.
    TODO: copy & modify the stdlib mergesort to use section variables.
    NOTE: to avoid forcing an overly strict comparison, may as well also generalize the proofs
    to be wrt an equivalence.
   *)
  Context (sort : ((list idx) * elt -> (list idx) * elt -> bool) -> table -> table).

  Fixpoint filter_split_sorted' (args_locs : nat * list nat) (tab : table)
    out current current_idx
    : named_list idx (named_list (list idx) elt) :=
    match tab with
    | [] => (current_idx,current)::out
    | (args,e)::tab' =>
        match match_args args args_locs with
        | Some i =>
            if eqb i current_idx
            then filter_split_sorted' args_locs tab' out ((args,e)::current) current_idx
            else filter_split_sorted' args_locs tab' ((current_idx, current)::out) [(args,e)] i
        (* TODO: may return None for multiple reasons.
           This match does not properly handle errors (although they aren't supposed to happen)
         *)
        | None => filter_split_sorted' args_locs tab' out current current_idx
        end
    end.

  Definition filter_split_sorted args_locs tab :=
    match tab with
    | [] => []
    | (args,e)::tab' =>
        match match_args args args_locs with
        | Some i => filter_split_sorted' args_locs tab' [] [(args,e)] i
        (* TODO: Silences errors. Consider proper error propagation *)
        | None => []
        end
    end.

  (*TODO: move to Booloeans/WithDefault*)
  Instance default_bool : WithDefault bool := false.

  Context (idx_leb : idx -> idx -> bool).
  
  Definition args_order loc0 : list idx * elt -> list idx * elt -> bool :=
     fun l1 l2 =>
          unwrap_with_default
            (@! let idx1 <- nth_error (fst l1) loc0 in
            let idx2 <- nth_error (fst l2) loc0 in
            ret (idx_leb idx1 idx2)).

  Definition split_by (args_locs : nat * list nat) (tab : table)
    : named_list idx table :=
    let table' := sort (args_order (fst args_locs)) tab in
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

  Context (tree : map_tree idx_map elt).
  
  (* TODO: check these *)
  #[local] Arguments leaf {key}%type_scope {m}%function_scope {A}%type_scope {map_tree} _.
  #[local] Arguments top_node {key}%type_scope {m}%function_scope {A}%type_scope {map_tree} _.
  #[local] Arguments node {key}%type_scope {m}%function_scope {A}%type_scope {map_tree} _.

  Definition ne_table : Type := ((list idx) * elt) * named_list (list idx) elt.

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
  
  Fixpoint build_trie' (tab : ne_table) (vars : list idx) (args : list argument)
    : tree :=
    match vars with
    | [] =>
        (* Assumes that all arguments must be constant here.
           Implied by fvs(args) <= vars.

           Further assumes that the table is functional,
           i.e. that each key (arg list) appears at most once
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

  Definition atom :Type := symbol * list idx.

  (* Returns None only if the clause doesn't match any rows.
     Note: may still return Some in such cases.
   *)
  Definition build_trie (nodes:node_map) (vars : list idx) (clause : atom) : option _ :=
    @! let rel_id := fst clause in
      let (r1::tab) <?- map.get nodes rel_id in
      ret (rel_id, build_trie' (r1,tab) vars (map var_arg (snd clause))).

  Definition build_tries (nodes : node_map) (vars : list idx) (clauses : list atom)
    : option _ :=
    list_Mmap (build_trie nodes vars) clauses.


  

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
  
  

(*TODO: move to utils*)
Lemma invert_Forall2_nil_nil {A B} (f : A -> B -> Prop)
  : Forall2 f [] [] <-> True.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_nil_nil : utils.

Lemma invert_Forall2_nil_cons {A B} (f : A -> B -> Prop) e x
  : Forall2 f [] (e :: x) <-> False.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_nil_cons : utils.

Lemma invert_Forall2_cons_nil {A B} (f : A -> B -> Prop) e x
  : Forall2 f (e :: x) [] <-> False.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_cons_nil : utils.

Lemma invert_Forall2_cons_cons {A B} (f : A -> B -> Prop) e x e' x'
  : Forall2 f (e :: x) (e'::x')
    <-> (f e e') /\ Forall2 f x x'.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_cons_cons : utils.

Lemma Forall2_combine {A B} (op : A -> B -> Prop) l1 l2
  : List.length l1 = List.length l2 -> Forall2 op l1 l2 <-> all (fun '(a,b) => op a b) (combine l1 l2).
Proof using.
  revert l2; induction l1; destruct l2;
    basic_goal_prep;
    basic_utils_crush.
  all: eapply IHl1; eauto.
Qed.

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


(*TODO: move to sets*)
Lemma member_empty {A} {m : set A} {_ :map.ok m} (e : A)
  : member (map.empty (map:=m)) e = false.
Proof.
  unfold member.
  erewrite map.get_empty.
  reflexivity.    
Qed.
Hint Rewrite @member_empty : utils.

Lemma member_add_elt {A} `{Eqb A} {S : set A} {_ :map.ok S} (s : S) (e e' : A)
  : member (add_elt s e) e' = ((eqb e e') || (member s e'))%bool.
Proof.
  unfold member.
  unfold add_elt.
  my_case Heqb (eqb e e');
    basic_goal_prep;
    basic_utils_crush.
  { rewrite map.get_put_same; reflexivity. }
  { rewrite map.get_put_diff; auto. }
Qed.
Hint Rewrite @member_add_elt : utils.

(*TODO: do I want this in utils?*)
Hint Rewrite Bool.orb_true_iff : utils.

Definition set_flat_map {A B} {S : set A} (f : A -> list B) (s : S) : list B :=
  map.fold (fun l v _ => f v ++ l) [] s.


(* We need to expose the map implementation or query_trie is not strictly positive.
   We cordon it off into its own module so that the rest can be parametric over idx and elt.
 *)
Module PositiveQueryTrie.
  
  Open Scope positive.
  Inductive query_trie :=
  (*Necessary for when a variable does not appear in a clause *)
  | qt_unconstrained : query_trie -> query_trie
  (* need to expose map impl or inductive is not strictly positive *)
  | qt_tree : TrieMap.map query_trie -> query_trie
  (* used when there are no more variables left *)
  | qt_nil : query_trie.

  (* used when there are no possible instantiations *)
  Notation qt_empty := (qt_tree (PTree.Empty)).

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
    (* shouldn't normally hit this case *)
    | qt_nil => finite_set map.empty
    end.

  Definition choose_next_val (v:positive) (t : query_trie) : query_trie :=
    match t with
    | qt_tree m => 
        match map.get m v with Some t => t | None => qt_empty end
    | qt_unconstrained t => t 
    (* shouldn't normally hit this case *)
    | qt_nil => qt_empty
    end.

  
End PositiveQueryTrie.

Module Int63QueryTrie.
  
  Open Scope int63.
  Inductive query_trie :=
  (*Necessary for when a variable does not appear in a clause *)
  | qt_unconstrained : query_trie -> query_trie
  (* need to expose map impl or inductive is not strictly positive *)
  | qt_tree : TrieMapInt63.map query_trie -> query_trie
  (* used when there are no more variables left *)
  | qt_nil : query_trie.

  (* used when there are no possible instantiations *)
  Notation qt_empty := (qt_tree (PTree.Empty)).

  #[export] Instance trie_set : set int :=
    {
      set_as_map := TrieMapInt63.map _;
      intersection := PTree.combine (fun a b => if a then b else None);
      union := PTree.combine (fun a b => if a then Some tt else b);
    }.

  Definition values_of_next_var (t : query_trie) : set_with_top trie_set :=
    match t with
    | qt_tree m => finite_set (PTree.map_filter (fun _ => Some tt) m)
    | qt_unconstrained _ => all_elements
    (* shouldn't normally hit this case *)
    | qt_nil => finite_set map.empty
    end.

  Definition choose_next_val (v:int) (t : query_trie) : query_trie :=
    match t with
    | qt_tree m => 
        match map.get m v with Some t => t | None => qt_empty end
    | qt_unconstrained t => t 
    (* shouldn't normally hit this case *)
    | qt_nil => qt_empty
    end.

  
End Int63QueryTrie.


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
          (trie_map_ok : map.ok trie_map)
          (qt_tree : trie_map -> query_trie)
          (qt_nil : query_trie)
          (values_of_next_var : query_trie -> set_with_top elt_set)
          (choose_next_val : elt -> query_trie -> query_trie).

  Axiom (query_trie_ind
     : forall P : query_trie -> Prop,
       (forall q : query_trie, P q -> P (qt_unconstrained q)) ->
       (forall r : trie_map, P (qt_tree r)) -> P qt_nil -> forall q : query_trie, P q).
  Axiom (query_trie_rec
     : forall P : query_trie -> Type,
       (forall q : query_trie, P q -> P (qt_unconstrained q)) ->
       (forall r : trie_map, P (qt_tree r)) -> P qt_nil -> forall q : query_trie, P q).
  
  Notation qt_empty := (qt_tree map.empty).
  
  (*TODO: move the abstraction boundary?*)
  Context (get_keys : trie_map -> elt_set).
  Axiom member_get_keys
    : forall r x, member (get_keys r) x = true <-> if map.get r x then True else False.
  
  Axiom (values_of_next_var_tree
            : forall m, values_of_next_var (qt_tree m) = finite_set (get_keys m)).
  Axiom (values_of_next_var_unconstrained
            : forall t, values_of_next_var (qt_unconstrained t) = all_elements).
  Axiom (values_of_next_var_nil
          : values_of_next_var qt_nil = finite_set map.empty).

  Axiom (choose_next_val_tree
          : forall v m, choose_next_val v (qt_tree m) = match map.get m v with Some t => t | None => qt_empty end).
  Axiom (choose_next_val_unconstrained
          : forall v t, choose_next_val v (qt_unconstrained t) = t).
  Axiom (choose_next_val_nil
          : forall v, choose_next_val v qt_nil = qt_empty).

  Hint Rewrite values_of_next_var_tree : utils.
  Hint Rewrite values_of_next_var_unconstrained : utils.
  Hint Rewrite values_of_next_var_nil : utils.
  Hint Rewrite choose_next_val_tree : utils.
  Hint Rewrite choose_next_val_unconstrained : utils.
  Hint Rewrite choose_next_val_nil : utils.

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
    (* Note: can function incorrectly on trivial clauses (e.g. (1,[])).
       We don't use trivial clauses in the egraph solver, so they
       are just disallowed in the theorems.
     *)
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
            set_flat_map (fun v => generic_join' (named_map (choose_next_val v) tries) vars'
                                                 (map.put acc x v))
                         Dx
        | all_positives => []
        end
    end.



  Fixpoint match_args args tuple : option arg_map :=
    match args, tuple with
    | [], [] => Some map.empty
    | _,[] => None
    | [],_ => None
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

  Definition find_values_in_relation' (x : idx) (rel : relation) args
    : elt_set :=
    map.fold (fun acc tuple _ =>
                match match_args_and_lookup args tuple x with
                | Some e => add_elt acc e
                | None => acc
                end) map.empty rel.

  Axiom TODO:forall {A} ,A.
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


  Definition match_one_const a e :=
    match a with const_arg e' => eqb e e' | _ => false end.

  Definition args_in_rel  (rel: relation) (args : list argument) :=
    map.fold (fun acc tuple _ => acc || (all2 match_one_const args tuple))%bool false rel.
  
  (*TODO: filter rel on recursive calls?*)
  (* TODO: if a variable is unconstrained, need to handle it specially *)
  Fixpoint build_trie' (rel: relation) (vars : list idx) (args : list argument)
    : query_trie :=
    match vars with
    | [] => if args_in_rel rel args then qt_nil else qt_empty
    | x::vars' =>
        let vs := find_values_in_relation x rel args in
        match vs with
        | Some vs =>
            qt_tree (map.fold
                       (fun m v _ =>
                          map.put m v (build_trie' rel vars' (map (arg_subst v x) args)))
                       map.empty
                       vs)
        | None  =>
            qt_unconstrained (build_trie' rel vars' args)
        end
    end.

  Definition build_trie (d:db) (vars : list idx) (clause : atom) : idx * query_trie :=
    let rel_id := fst clause in
    match map.get d rel_id with
    | Some rel => (rel_id,build_trie' rel vars (map var_arg (snd clause)))
    | None => (rel_id, qt_empty)
    end.

  Definition build_tries (d:db) (vars : list idx) (clauses : list atom)
    : @named_list idx query_trie :=
    map (build_trie d vars) clauses.

  Definition generic_join (d : db) (q : query) : subst_set :=
    let tries := build_tries d q.(free_vars) q.(clauses) in
    (* require all queries to have at least one variable.
       This avoids edge cases with degenerate clauses,
       e.g. Q() = R() where R ={} in d

       TODO: implement the empty branch which decides whether the result should be [] or [empty]
     *)
    if q.(free_vars) then [] else generic_join' tries q.(free_vars) map.empty.

  (*Properties*)

  (*TODO: mention fvs? *)
  Definition satisfies_query d q (m : arg_map) :=
    forall i args,
      In (i,args) q.(clauses) ->
      exists R,
        map.get d i = Some R
        /\
        exists tuple,
          List.Forall2 (fun a e => map.get m a = Some e) args tuple
          /\
          member R tuple = true.

  
  Definition const_args_in_rel args (R : relation) :=
    exists tuple,
      map const_arg tuple = args
      /\ member R tuple = true.

  
  (* TODO: try using this? *)
  Inductive denote_query_trie : list idx -> query_trie -> arg_map -> Prop :=
  | denote_qt_nil : denote_query_trie [] qt_nil map.empty
  (* TODO: this does complicate things since it requires cross-trie reasoning
     To show that some trie fixes the value
   *)
  | denote_qt_unconstrained vars t m x v
    : denote_query_trie vars t m ->
      denote_query_trie (x::vars) (qt_unconstrained t) (map.put m x v)
  | denote_qt_cons vars t m x tm v
    : map.get tm v = Some t ->
      denote_query_trie vars t m ->
      denote_query_trie (x::vars) (qt_tree tm) (map.put m x v).
  (*TODO: new hintdb?*)
  Hint Constructors denote_query_trie : utils.

  (* TODO: still use anywhere?
  Inductive sound_trie_for_relation
            (R : relation) (args : _)
    : _ -> list idx -> Prop :=
  | sound_trie_qt_nil :
    const_args_in_rel args R ->
    sound_trie_for_relation R args qt_nil []
  | sound_trie_qt_empty :
    sound_trie_for_relation R args qt_empty []
  | sound_trie_qt_tree m x vars
    : (forall v t, map.get m v = Some t ->
                   sound_trie_for_relation R (map (arg_subst v x) args) t vars) ->
      sound_trie_for_relation R args (qt_tree m) (x::vars)
  | sound_trie_qt_unconstrained t x vars
    : (forall v, sound_trie_for_relation R (map (arg_subst v x) args) t vars) ->
      sound_trie_for_relation R args (qt_unconstrained t) (x::vars).

  (*TODO: new hintdb?*)
  Hint Constructors sound_trie_for_relation : utils. 

  
  Definition trie_sound_for_atom (d : db) vars '(i,t) '(i',args) :=
    i = i' /\
      exists R,
        map.get d i = Some R /\
        (sound_trie_for_relation R (map var_arg args) t vars).
*)

  Definition arg_from_vars vars a :=
    match a with
    | const_arg _ => True
    | var_arg x => In x vars
    end.

  Lemma all_args_from_empty_is_const args
    : all (arg_from_vars []) args ->
      exists tuple, map const_arg tuple = args.
  Proof.
    induction args; 
      basic_goal_prep; basic_utils_crush.
    - exists []; basic_utils_crush.
    - destruct a;
        basic_utils_crush.
      exists (c::x);
        basic_utils_crush.
  Qed.

  Definition one_arg_can_match a c :=
    match a with
    | var_arg _ => True
    | const_arg c' => c = c'
    end.

  Definition args_can_match R args :=
    exists tuple,
      member R tuple = true
      /\ Forall2 one_arg_can_match args tuple.

  (*
  Lemma args_match_const_eq tuple tuple'
    : Forall2 one_arg_can_match (map const_arg tuple') tuple ->
      tuple' = tuple.
  Proof.
    revert tuple;
      induction tuple';
      destruct tuple;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
*)

  (*TODO: move somewhere*)
  Hint Rewrite @map.get_empty : utils.

  Context (arg_map_ok : map.ok arg_map).

  
  Lemma match_args_sound' args tuple m
    : (*List.length args = List.length tuple ->*)
      Some m = match_args args tuple ->
      forall m',
        (forall x c, map.get m x = Some c -> map.get m' x = Some c) ->
      Forall2 (fun a c =>
                 match a with
                 | const_arg c' => c = c'
                 | var_arg x => map.get m' x = Some c
                 end)
              args
              tuple.
  Proof.
    revert m.
    revert tuple; induction args;
      destruct tuple;
      basic_goal_prep;
      autorewrite with utils in*;
      subst;
      auto 1.
    {
      destruct a;
        basic_goal_prep;
        congruence.
    }    
    destruct a;
      basic_goal_prep.
    {
      revert H; 
        case_match; [|congruence].
      basic_utils_crush.
    }
    {
      revert H; 
        case_match; [|congruence].
      case_match.
      {
        case_match; [|congruence].
        basic_goal_prep;
          basic_utils_crush.
      }
      {
        basic_goal_prep;
          basic_utils_crush.
        - apply H0.
          apply map.get_put_same.
        - eapply IHargs; eauto.
          intros; apply H0.
          rewrite map.get_put_diff; eauto.
          congruence.
      }
    }
  Qed.
  
  Lemma match_args_sound args tuple m
    : Some m = match_args args tuple ->
      Forall2 (fun a c =>
                 match a with
                 | const_arg c' => c = c'
                 | var_arg x => map.get m x = Some c
                 end)
              args
              tuple.
  Proof.
    intros; eapply match_args_sound'; eauto.
  Qed.
      
  
  Lemma match_args_and_lookup_sound args k i e
    : Some e = match_args_and_lookup args k i ->
      Forall2 one_arg_can_match (map (arg_subst e i) args) k.
  Proof.
    unfold match_args_and_lookup.
    simpl.
    case_match; [|congruence].
    case_match; [|congruence].
    intros H'; inversion H'; clear H'; subst.
    pose proof (match_args_sound _ _ _ HeqH) as H.
    revert H.
    clear HeqH.
    revert dependent r.
    revert dependent k.
    revert args.
    induction args;
      destruct k;
      basic_goal_prep;
      try destruct a;
      basic_goal_prep;
      basic_utils_crush.
    {
      case_match;
      basic_goal_prep;
        basic_utils_crush.
      congruence.
    }
  Qed.

  (*TODO: move to the right place*)
  Definition map_incl {A B} {m : map.map A B} (S S' : m) := forall x v, map.get S x = Some v -> map.get S' x = Some v.

  (*TODO: move to utils*)
  (*TODO: implement/import list eqb*)
  #[refine]
  Instance list_eqb {A} `{Eqb A} : Eqb (list A) :=
    {
      eqb := all2 eqb
    }.
  all: apply TODO.
  Defined.
  
  Definition set_incl S S' := forall x, member S x = true -> member S' x = true.

  Context {relation_ok : Sets.ok relation}.

  Lemma set_put_monotone m k
    : set_incl m (map.put m k tt).
  Proof.
    intro.
    unfold member in *.
    case_match; try congruence.
    intros _.
    my_case Heq (eqb x k).
    {
      basic_goal_prep;
        change (eqb x k = true) in Heq;
        basic_utils_crush.
      now erewrite map.get_put_same.
    }
    {
      basic_goal_prep;
      change (eqb x k = false) in Heq;
        basic_utils_crush.
      erewrite map.get_put_diff; auto.
      now rewrite <- HeqH.      
    }
  Qed.    

  (*TODO: move up?*)
  Context {elt_set_ok : Sets.ok elt_set}.
  
  Lemma find_values_in_relation_some_sound i R args elts
    : find_values_in_relation i R args = Some elts ->
      forall e, member elts e = true ->
                forall R', set_incl R R' ->
                args_can_match R' (map (arg_subst e i) args).
  Proof.
    unfold find_values_in_relation.
    case_match; try congruence.
    intros fv; inversion fv; clear fv.
    clear HeqH elts H0.
    intros e.
    unfold find_values_in_relation'.
    eapply map.fold_spec.
    { basic_utils_crush. }
    intros.
    revert H1.     
    case_match.
    {
      my_case Heqe (eqb e e0);
        basic_goal_prep;
        autorewrite with utils in *; subst.
      {
        clear H0 H1.
        eapply match_args_and_lookup_sound in HeqH1.
        {
          exists k;
            basic_goal_prep;
            basic_utils_crush.
          apply H2.
          unfold member; now erewrite map.get_put_same.
        }
      }
      {
        erewrite member_add_elt in H1.
        autorewrite with utils in *.
        destruct H1.
        1:now basic_utils_crush.
        apply H0; auto.
        intros x mem.
        eapply H2.
        now eapply set_put_monotone.
      }
    }
    {
      intros; eapply H0; eauto.
      intros x mem.
      eapply H2.
      destruct v.
      now eapply set_put_monotone.
    }
  Qed.

  (*TODO: what is the right property here?
  Lemma find_values_in_relation_none_sound i R args
    : find_values_in_relation i R args = None ->
      forall e, args_can_match R (map (arg_subst e i) args).
  Proof.
    unfold find_values_in_relation.
    case_match; try congruence.
    intros _.
    intros.
    assert (map (arg_subst e i) args = args) as Hargs_eq.
    {
      revert HeqH; induction args;
        basic_goal_prep; try destruct a; basic_utils_crush.
      {
        symmetry in HeqH.
        rewrite Bool.orb_false_iff in HeqH.
        basic_goal_prep; basic_utils_crush.
        case_match;
          basic_goal_prep; basic_utils_crush.
      }
      {
        symmetry in HeqH.
        rewrite Bool.orb_false_iff in HeqH.
        basic_goal_prep; basic_utils_crush.
      }
    }
    rewrite Hargs_eq.
    assumption.
  Qed.*)

  
  Lemma arg_from_vars_subst x a v vars
    : arg_from_vars (x :: vars) a ->
      arg_from_vars vars (arg_subst v x a).
  Proof.
    unfold arg_from_vars.
    destruct a; 
      basic_goal_prep; basic_utils_crush.
    case_match;
      basic_goal_prep; basic_utils_crush.
    revert HeqH.
    case_match;
      basic_goal_prep; basic_utils_crush.
    all:inversion HeqH0; subst; auto.
  Qed.
  Hint Resolve arg_from_vars_subst : utils.
  
  Lemma all_arg_from_vars_subst x args v vars
    : all (arg_from_vars (x :: vars)) args ->
      all (arg_from_vars vars) (map (arg_subst v x) args).
  Proof.
    induction args;
      basic_goal_prep; try now basic_utils_crush.
    destruct H.
    split; auto.
    apply arg_from_vars_subst; assumption.
  Qed.      

  (*TODO: move somewhere*)
  Hint Rewrite map.get_empty : utils.

  
  Lemma args_in_rel_sound R args
    : args_in_rel R args = true ->
      const_args_in_rel args R.
  Proof.
    unfold args_in_rel, const_args_in_rel.
    eapply map.fold_spec; try congruence.
    intros k v m r gmk IH.
    destruct r; simpl.
    {
      intros _; specialize (IH eq_refl);
        destruct IH as [tuple [? ?]].
      subst;
        eexists; split; eauto.
      destruct v;
        now eapply set_put_monotone.
    }
    {
      clear IH.
      intros; exists k.
      split; cycle 1.
      {
        destruct v;
          change ((map.put m k tt)) with (add_elt m k);
          erewrite member_add_elt;basic_utils_crush.
      }
      {
        revert H; clear.
        revert k;
          induction args;
          destruct k;
          basic_goal_prep; unfold  match_one_const in *;
          try destruct a; basic_utils_crush.
      }
    }
  Qed.

  Definition maps_arg_to (m : arg_map) a e :=
    match a with
    | const_arg e' => e = e'
    | var_arg x => map.get m x = Some e
    end.

  Definition arg_map_sound_for_relation (R : relation) args (m : arg_map) :=
    exists tuple,
      Forall2 (maps_arg_to m) args tuple
      /\ member R tuple = true.

  Definition trie_sound_for_relation (R : relation) vars args t :=
    forall m, denote_query_trie vars t m ->
              arg_map_sound_for_relation R args m.
    
  Lemma const_args_map x0 args m
    : map const_arg x0 = args -> Forall2 (maps_arg_to m) args x0.
  Proof.
    revert x0; induction args; destruct x0;
      basic_goal_prep; unfold  maps_arg_to; basic_utils_crush.
  Qed.
  Local Hint Resolve const_args_map : core.

  (*TODO: prove above*)
  Context (invert_qt_nil_tree : forall m, qt_nil = qt_tree m <-> False).
  Hint Rewrite invert_qt_nil_tree : utils.
  Context (invert_qt_unconstrained_tree : forall t m, qt_unconstrained t = qt_tree m <-> False).
  Hint Rewrite invert_qt_unconstrained_tree : utils.
  Context (invert_qt_tree_unconstrained : forall t m, qt_tree m = qt_unconstrained t <-> False).
  Hint Rewrite invert_qt_tree_unconstrained : utils.
  
  Context (invert_qt_tree_tree : forall m m', qt_tree m = qt_tree m' <-> m = m').
  Hint Rewrite invert_qt_tree_tree : utils.
  Context (invert_qt_unconstrained_unconstrained
            : forall t t', qt_unconstrained t = qt_unconstrained t' <-> t = t').
  Hint Rewrite invert_qt_unconstrained_unconstrained : utils.

  Lemma empty_trie_sound R vars args
    : trie_sound_for_relation R vars args qt_empty.
  Proof.
    unfold trie_sound_for_relation.
    intros m dqt.
    inversion dqt;
      autorewrite with utils in *;
      try tauto.
    subst.
    rewrite map.get_empty in H0.
    congruence.
  Qed.
  Local Hint Resolve empty_trie_sound : utils.

  
  Lemma arg_map_sound_subst R v x args m
    : arg_map_sound_for_relation R (map (arg_subst v x) args) m ->
      arg_map_sound_for_relation R args (map.put m x v).
  Proof.
    unfold arg_map_sound_for_relation.
    intro H'; destruct H' as [tuple [? ?]].
    exists tuple.
    split; auto.
    revert H.
    clear H0.
    unfold maps_arg_to.
    revert tuple; induction args;
      destruct tuple;
      basic_goal_prep;
      try destruct a;
      basic_utils_crush.
    clear IHargs H1.
    revert H0.
    unfold arg_subst.
    my_case Heqb (eqb x x0);
      basic_utils_crush.
    - now rewrite map.get_put_same.
    - rewrite map.get_put_diff; eauto.
  Qed.
  
  Lemma tree_trie_sound R vars args x m
    : (forall v t, map.get m v = Some t ->
                   trie_sound_for_relation R vars (map (arg_subst v x) args) t) ->
    trie_sound_for_relation R (x::vars) args
                              (qt_tree m).
  Proof.
    unfold trie_sound_for_relation.
    intros H m' dqt.
    inversion dqt;
      autorewrite with utils in *;
      try tauto; subst.
    apply  arg_map_sound_subst.
    eapply H; eauto.
  Qed.
  Local Hint Resolve tree_trie_sound : utils.

  Lemma unconstrained_trie_sound R vars args t a
    : ~ In a vars ->
      all (arg_from_vars vars) args ->
      trie_sound_for_relation R vars args t ->
      trie_sound_for_relation R (a :: vars) args (qt_unconstrained t).
  Proof.
    unfold trie_sound_for_relation.
    intros Hdup Hargs IH m' dqt.
    inversion dqt; clear dqt;
      autorewrite with utils in *;
      try tauto; subst.
    specialize (IH _ H3).
    destruct IH as [tuple [? ?]].
    exists tuple; split; auto.
    revert H.
    clear H0.
    revert tuple; induction args;
      destruct tuple;
      basic_goal_prep;
      basic_utils_crush.
    unfold maps_arg_to.
    destruct a0; auto; intros.
    
    assert (a <> x).
    {
      intro; subst.
      apply Hdup.
      apply H0.
    }
    rewrite map.get_put_diff; auto.
  Qed.
  Local Hint Resolve unconstrained_trie_sound : utils.

  (*TODO: move to Utils.v*)
  Lemma invert_NoDup_cons {A} x (a:A)
    : NoDup (a::x) <-> ~ In a x /\ NoDup x.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite @invert_NoDup_cons : utils.

  (* TODO: move to Utils.v*)
  Lemma invert_negb_true b
    : negb b = true <-> ~(b = true).
  Proof.
    destruct b; simpl; intuition congruence.
  Qed.
  Hint Rewrite invert_negb_true : utils.
  
  Lemma invert_existsb_true {A} P (l : list A)
    : existsb P l = true <-> exists x, In x l /\ P x = true.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.    
  Hint Rewrite @invert_existsb_true : utils. 
  
  Lemma args_from_vars_strengthen a R args vars
    : None = find_values_in_relation a R args ->
      all (arg_from_vars (a :: vars)) args ->
      all (arg_from_vars vars) args.
  Proof.
    unfold find_values_in_relation.
    case_match; [congruence|].
    intros.
    symmetry in HeqH.
    revert HeqH.
    rewrite <- Bool.negb_true_iff.
    rewrite invert_negb_true.
    rewrite invert_existsb_true.
    revert H0; induction args;
      basic_goal_prep;
      basic_utils_crush.
    revert HeqH H1.
    clear.
    unfold arg_from_vars.
    destruct a0; simpl;
      intuition.
    subst.
    exfalso.
    apply HeqH.
    exists (var_arg x).
    intuition.
    apply eqb_refl.
  Qed.

  
  Lemma build_trie'_sound R args vars
    : NoDup vars ->
      all (arg_from_vars vars) args ->
      trie_sound_for_relation R vars args (build_trie' R vars args).
  Proof.
    revert args; induction vars;
      basic_goal_prep.
    {
      eapply all_args_from_empty_is_const in H0;
        destruct H0.
      case_match.
      {
        symmetry in HeqH1.
        apply args_in_rel_sound in HeqH1.
        unfold trie_sound_for_relation.
        intros m dqt.
        unfold const_args_in_rel in *.
        unfold arg_map_sound_for_relation.
        destruct HeqH1 as [? [? ?]].
        exists x0; split; auto.
      }
      {
        eapply empty_trie_sound.
      }
    }
    case_match.
    {
      eapply tree_trie_sound.
      intros.
      enough (t=(build_trie' R vars (map (arg_subst v a) args)));[subst|].
      {
        autorewrite with utils in H; destruct H.
        eapply IHvars; eauto.
        eapply all_arg_from_vars_subst.
        auto.
      }
      {     
        revert H1.
        set map.empty.
        assert (map.get r0 v = None).
        {
          unfold r0.
          erewrite map.get_empty; auto.
        }
        revert H.
        eapply map.fold_spec.
        { basic_goal_prep; congruence. }
        {
          basic_goal_prep.
          intuition subst.
          my_case Heqk (eqb k v).
          { rewrite eqb_eq in Heqk; subst.
            erewrite map.get_put_same in H4.
            congruence.
          }
          {
            rewrite eqb_neq in Heqk.
            apply not_eq_sym in Heqk.
            erewrite map.get_put_diff in H4;
              tauto.
          }
        }
      }
    }
    {
      eapply unconstrained_trie_sound;
        autorewrite with utils in *; try now intuition.
      {
        eapply args_from_vars_strengthen; eauto.
      }
      eapply IHvars; eauto; try now intuition.
      {
        eapply args_from_vars_strengthen; eauto.
      }
    }
  Qed.

  (*TODO: move to utils*)
  Lemma all_map {A B} P (f : A -> B) l
    : all P (map f l) = all (fun x => P (f x)) l.
  Proof.
    induction l;
      basic_goal_prep; basic_utils_crush.
  Qed.
      
  
  Definition trie_sound_for_atom (d : db) vars '(i,t) '(i',args) :=
    i = i' /\
      let R := unwrap_with_default map.empty (map.get d i) in
      trie_sound_for_relation R vars (map var_arg args) t.
  
  Lemma build_trie_sound d vars a
    : NoDup vars ->
      all (fun x => In x vars) (snd a) ->
      trie_sound_for_atom d vars (build_trie d vars a) a.
  Proof.
    unfold build_trie, atom in *.
    basic_goal_prep.
    case_match;
      unfold trie_sound_for_atom;
      split; auto;
      unfold unwrap_with_default;
      rewrite <- HeqH1.
    {
      apply build_trie'_sound; auto.
      rewrite all_map.
      assumption.
    }
    {
      unfold unwrap_with_default.
      apply empty_trie_sound.
    }
  Qed.
  Local Hint Resolve build_trie_sound : utils.

  
  Lemma build_tries_sound d vars clauses
    : NoDup vars ->
      all (fun a => all (fun x => In x vars) (snd a)) clauses ->
      Forall2 (trie_sound_for_atom d vars) (build_tries d vars clauses) clauses.
  Proof.
    induction clauses;
      basic_goal_prep;
      try now basic_utils_crush.
    destruct H0.
    constructor; eauto with utils.
  Qed.
      

  Definition well_scoped_query (d:db) q :=
    NoDup q.(free_vars) /\
      all (fun a => all (fun x => In x q.(free_vars)) (snd a)
                    /\ exists R, map.get d (fst a) = Some R)
          q.(clauses).
                                     
  
  (*TODO: mention fvs? *)
  Definition might_satisfy_query d (clauses : list atom) (m : arg_map) :=
    forall i args,
      In (i,args) clauses ->
      exists R,
        map.get d i = Some R
        /\
          exists tuple,
            (*This line differs from satisfies_query*)
            List.Forall2 (fun a e => forall e', map.get m a = Some e' -> e = e') args tuple
            /\
              member R tuple = true.

  
  Definition no_trivial_clauses q :=
    all (fun p => Exists (fun _ => True) (snd p)) q.(clauses).

  Definition might_be_inhabited (d : db) (a : atom) :=
      exists R,
        map.get d (fst a) = Some R
        /\
          exists tuple,
            (*we include the length condition here since we aren't maintaining arity invariants yet*)
            Forall2 (fun _ _ => True) (snd a) tuple
            /\
              member R tuple = true.
  
  Definition all_clauses_might_be_inhabited d q :=
    all (might_be_inhabited d) q.(clauses).

  Lemma empty_might_satisfy d q
    : well_scoped_query d q ->
      all_clauses_might_be_inhabited d q ->
      might_satisfy_query d q.(clauses) map.empty.
  Proof.
    destruct q;
      unfold well_scoped_query, all_clauses_might_be_inhabited, might_satisfy_query;
      simpl;
      basic_goal_prep.
    pose proof (in_all _ _ H2 H1) as H'; simpl in H'; basic_goal_prep.
    pose proof (in_all _ _ H0 H1) as H'; unfold might_be_inhabited in H'; simpl in H'; basic_goal_prep.
    assert (x = x0) by congruence; subst.
    exists x0; split; auto.
    exists x1; split; auto.
    eapply List.Forall2_impl_strong.
    {
      intros x y P _ _ e.
      rewrite map.get_empty.
      congruence.
    }
    eassumption.
  Qed.
    
  
  Lemma might_satisfy_empty_vars_satisfies d q m
    : well_scoped_query d q ->
      q.(free_vars) = [] ->
      might_satisfy_query d q.(clauses) m ->
      satisfies_query d q m.
  Proof.
    unfold might_satisfy_query, satisfies_query, well_scoped_query.
    destruct q; basic_goal_prep; subst.
    specialize (H1 _ _ H2).
    break.

    exists x; split; auto.
    exists x0; split; auto.
    
    assert (args = []).
    {
      revert dependent clauses0.
      clear.
      induction clauses0; basic_goal_prep; intuition subst; simpl in *; eauto.
      destruct args; simpl in *; intuition.
    }
    subst.
    inversion H1; subst; clear H1; eauto.
  Qed.

  Lemma in_map_flat_map x f m
    :  In x
          (map.fold
             (fun (l : list arg_map) (v : elt) (_ : unit) =>
                f v ++ l) [] m) ->
       exists v, (member m v = true /\ In x (f v)).
  Proof.
    eapply map.fold_spec;
      basic_goal_prep;
      try now basic_utils_crush.
    autorewrite with utils in *.
    destruct H1.
    {
      exists k;
        intuition idtac.
      change ((map.put ?m ?k tt)) with (add_elt m k);
        erewrite member_add_elt;basic_utils_crush.
    }
    {
      destruct (H0 H1) as [v [? ?]].
      exists v; intuition.
      change ((map.put ?m ?k tt)) with (add_elt m k);
        erewrite member_add_elt;basic_utils_crush.
    }
  Qed.

  Definition member_with_top {A} {S : set A} (s : set_with_top S) v :=
    match s with
    | all_elements => true
    | finite_set s' => member s' v
    end.
  (*Axiom values_of_next_var_sound
    : forall t (v : elt) x vars m, member_with_top (values_of_next_var t) v = true ->
                  denote_query_trie (x::vars) t m ->
                  denote_query_trie vars (choose_next_val v t) (map.put m x v).*)


  (*TODO: move to Sets*)
  Lemma in_set_flat_map {A B} `{Eqb A} {S : set A} {S_ok : Sets.ok S} (f : A -> list B) b (s : S)
    : In b (set_flat_map f s) ->
      exists a, In b (f a) /\ member s a = true.
  Proof.
    unfold set_flat_map.
    eapply map.fold_spec;
      basic_goal_prep;
      basic_utils_crush.
    {
      exists k; simpl.
      change (map.put m k tt) with (add_elt m k).
      rewrite member_add_elt.
      basic_utils_crush.
    }
    {
      exists x; intuition.
      change (map.put m k tt) with (add_elt m k).
      rewrite member_add_elt.
      basic_utils_crush.
    }
  Qed.

  
    Lemma member_intersection_l (m m' : elt_set) x
      : member (intersection m m') x = true -> member m x = true.
  Proof using elt_set_ok.
    unfold member;
      case_match;
      try congruence.
    intros _.
    erewrite <- get_intersect_same.
    {
      erewrite <- HeqH; auto.
    }
    epose proof (Option.option_eq_dec _ (fun _ _ => true) _
                                          _ (map.get m x) (map.get m' x)) as H'.
    destruct H';auto.
    exfalso.
    erewrite get_intersect_diff in HeqH; eauto.
    congruence.
    Unshelve.
    {
      intros; break; reflexivity.
    }
    {
      intros; break; reflexivity.
    }
  Qed.

  
    Lemma member_intersection_r (m m' : elt_set) x
      : member (intersection m m') x = true -> member m' x = true.
  Proof using elt_set_ok.
    (*TODO: get_intersect_same is left-biased, need commutativity or stronger axiom*)
  Admitted.
    
  
  Lemma fold_left_intersect_subset s (m0 m1 : elt_set)
    : finite_set m0 = fold_left set_with_top_intersection s (finite_set m1) ->
      (forall x, member m0 x = true -> member m1 x = true).
  Proof using choose_next_val elt elt_default elt_set qt_nil query_trie relation values_of_next_var elt_set_ok.
    revert m0 m1;
      induction s;
      basic_goal_prep;
      basic_utils_crush.
    1:congruence.
    revert H; case_match; subst; eauto.
    intros.
    eapply member_intersection_l.
    eauto.
  Qed.
  
  Lemma in_fold_left_tries {A} m0 (tries : @named_list A query_trie) x base
    : finite_set m0 =
        fold_left set_with_top_intersection (map (fun '(_, v) => values_of_next_var v) tries) base ->
      member m0 x = true ->
      forall n m, In (n,m) tries -> member_with_top (values_of_next_var m) x = true.
  Proof.
    revert m0 base.
    induction tries;
      basic_goal_prep;
      try now basic_utils_crush.
    destruct H1; eauto.
    safe_invert H1.
    clear IHtries.
    unfold member_with_top;
      case_match; auto.
    destruct base; simpl in *;
      eapply fold_left_intersect_subset in H; eauto.
    eapply member_intersection_r; eauto.
  Qed.

  
  Lemma might_satisfy_cons_weaken d y l' acc
    : might_satisfy_query d (y :: l') acc ->
      might_satisfy_query d l' acc.
  Proof.
    unfold might_satisfy_query.
    simpl in *.
    firstorder.
  Qed.

  (*TODO: move to Utils.v?*)
  Lemma map_put_remove' {A B} `{Eqb A} {M : map.map A B} {ok : map.ok M} (m : M) a x
    : map.get m a = Some x ->
      map.put (map.remove m a) a x = m.
  Proof.
    intros.
    eapply map.map_ext; intros.
    destruct (Eqb_dec k a); subst.
    {
      rewrite map.get_put_same; auto.
    }
    {
      rewrite map.get_put_diff; auto.
      rewrite map.get_remove_diff; auto.
    }
  Qed.

  Lemma map_put_remove {A B} `{Eqb A} {M : map.map A B} {ok : map.ok M} (m : M) a x
    : map.put (map.remove m a) a x = map.put m a x.
  Proof.
    intros.
    eapply map.map_ext; intros.
    destruct (Eqb_dec k a); subst.
    {
      rewrite !map.get_put_same; auto.
    }
    {
      rewrite !map.get_put_diff; auto.
      rewrite map.get_remove_diff; auto.
    }
  Qed.

(*
  Lemma denote_query_trie_choose vars x q m a
    : denote_query_trie vars (choose_next_val x q) m ->
      denote_query_trie (a :: vars) q (map.remove m a).
  Proof.
    induction q using query_trie_ind;
      autorewrite with utils in *.
    {
      intros.
      constructor.*)

 
  Lemma next_val_sound_for_atom d a i q vars y x
    : ~ In a (snd y) ->
      trie_sound_for_atom d (a :: vars) (i, q) y ->
      member_with_top (values_of_next_var q) x = true ->
      trie_sound_for_atom d vars (i, choose_next_val x q) y.
  Proof.
    unfold trie_sound_for_atom.
    destruct y.
    intuition subst.
    unfold trie_sound_for_relation in *;
      intros.
    unfold arg_map_sound_for_relation in *.
    simpl in *.
    
    eassert (denote_query_trie (a :: vars) q _).
    {
      revert H1 H0; induction q using query_trie_ind;
        autorewrite with utils;
        basic_goal_prep.
      {
        constructor; eauto.
      }
      {
        apply member_get_keys in H1.
        revert H1; case_match; [intros _|tauto].
        econstructor; eauto.
      }
      {
        exfalso.
        rewrite member_empty in H1;
          inversion H1.
      }
    }
    specialize (H3 _ H2).
    break.
    eexists; split; eauto.
    clear H4.
    revert dependent x0.
    revert dependent l.
    induction l;
      destruct x0;
      basic_goal_prep;
      basic_utils_crush.
    {
      revert H6; unfold maps_arg_to;
        rewrite map.get_put_diff; eauto.
    }
  Qed.
(*    {
      eapply H; eauto.
      
      need a notin l

    
        unfold 
        compute in H0.
        constructor; eauto.
    eapply H2; clear H2.
    revert H0 H.
    induction q using query_trie_ind;
      simpl;
      autorewrite with utils;
      intros.
    {
      erewrite <- (map_put_remove m).
      {
        constructor; eauto.
        TODO: m -> m seems wrong, why aren't they different?
      let x := open_constr:(map.put (map.remove m a) a x) in
      enough (m = x) as Hmeq; [rewrite Hmeq|].
      {
        constructor.
        eauto.
      }
      TODO: where to go from here? 
      co
    }
    destruct q; simpl in *.
      unfold denote_query_trie in *.
 *)

  

  Definition might_map_arg_to (m : arg_map) a e :=
    match a with
    | const_arg e' => e = e'
    | var_arg x =>
        match map.get m x with
        | Some e' => e = e'
        | None => True
        end
    end.

  Definition arg_map_might_be_sound_for_relation (R : relation) args (m : arg_map) :=
    exists tuple,
      Forall2 (might_map_arg_to m) args tuple
      /\ member R tuple = true.


  Definition trie_might_be_sound_for_relation (R : relation) vars args t :=
    forall m m', denote_query_trie vars t m' ->
                 map_incl m m' ->
                 arg_map_might_be_sound_for_relation R args m.
  
  
  Definition trie_might_be_sound_for_atom (d : db) vars '(i,t) '(i',args) :=
    i = i' /\
      let R := unwrap_with_default map.empty (map.get d i) in
      trie_might_be_sound_for_relation R vars (map var_arg args) t.

  (*TOOD: replace case_match with this?*)
  Ltac case_match' :=
    try lazymatch goal with
          [ H :  context [ match ?e with
                           | _ => _
                           end] |- _ ] => revert H
        end;
    case_match.

  Lemma denote_empty vars m : denote_query_trie vars qt_empty m <-> False.
  Proof.
    intuition subst.
    inversion H; subst; basic_utils_crush.
  Qed.
  Hint Rewrite denote_empty : utils.

  Hint Rewrite member_get_keys : utils.
  
  Lemma denote_choose_next vars x q m a
    : denote_query_trie vars (choose_next_val x q) m ->
      member_with_top ( values_of_next_var q) x = true ->
      denote_query_trie (a :: vars) q (map.put m a x).
  Proof.
    unfold member_with_top.
    revert m.
    induction q using query_trie_ind;
      basic_goal_prep;
      autorewrite with utils in *;
      repeat case_match';
      basic_utils_crush.
  Qed.


  Lemma denote_query_trie_domain vars q m a x
    : denote_query_trie vars q m ->
      map.get m a = Some x ->
      In a vars.
  Proof.
    intro H; induction H; subst;
      basic_utils_crush.
    {
      destruct (Eqb_dec a x0);
        subst;
        basic_utils_crush.
      right.
      rewrite map.get_put_diff in H0; eauto.
    }
    {
      destruct (Eqb_dec a x0);
        subst;
        basic_utils_crush.
      right.
      rewrite map.get_put_diff in H1; eauto.
    }
  Qed.
  
  Lemma trie_might_be_sound_choose_next_val d a vars tries clauses x
    : Forall2 (trie_might_be_sound_for_atom d (a :: vars)) tries clauses ->
      ~ In a vars ->
      (*TODO: need values_of_next_var fact*)
      Forall2 (trie_might_be_sound_for_atom d vars) (named_map (choose_next_val x) tries) clauses.
  Proof.
    revert clauses;
      induction tries;
      intro clauses;
      destruct clauses;
      basic_goal_prep;
      try now basic_utils_crush.

    autorewrite with utils in *;
      break.
    split; try now basic_utils_crush.
    revert H.
    (*TODO: can't use intuition*)
    unfold trie_might_be_sound_for_atom;
      intros; break; subst; split; auto.

    revert H2.
    unfold trie_might_be_sound_for_relation;
      intros; break; subst.

    eapply H2.
    {
      eapply denote_choose_next; eauto.
      admit(*TODO: add add'l assumption*).
    }
    admit (*map reasoning*).
  Admitted.
    

  
(*TODO: move to Utils*)

Fixpoint all_unique {A} (l : list A) :=
  match l with
  | [] => True
  | n::l' => ~ In n l' /\ all_unique l'
  end.
Arguments all_unique {_} !_ /.

  Context (idx_dec : forall (a b : idx), {a=b}+{~a=b}).

  (*assumption too strong
  Lemma might_satisfy_query_put d clauses acc a x
    :  might_satisfy_query d clauses acc ->
       (forall c, In c clauses -> ~ In a (snd c)) ->
       (*map.get acc a = None ->*)
       (*TODO: what hyps?*)
       might_satisfy_query d clauses (map.put acc a x).
  Proof.
    unfold might_satisfy_query;
      intuition.
    specialize (H i args); intuition break; subst.
    exists x0; intuition.
    exists x1; intuition.
    revert H2.
    eapply List.Forall2_impl_strong.

    intros.
    eapply H2.
    rewrite map.get_put_diff in H6; auto.
    intro; subst.
    eapply H0; eauto.
  Qed.*)

  
  Definition elt_sound_for_query d (clauses : list atom) (x : idx) (e :elt) :=
    forall i args,
      In (i,args) clauses ->
      exists R,
        map.get d i = Some R
        /\
          forall tuple,
             member R tuple = true ->
            (*This line differs from satisfies_query*)
            List.Forall2 (fun a e' => a = x -> e = e') args tuple.

  Lemma Forall2_len_eq {A B} (op : A -> B -> Prop) l1 l2
    : Forall2 op l1 l2 -> List.length l1 = List.length l2.
  Proof.
    revert l2; induction l1; destruct l2; basic_goal_prep; basic_utils_crush.
  Qed.

  
  Lemma all_weaken {A} (l : list A) (P Q : _ -> Prop)
    : (forall x, In x l -> P x -> Q x) ->
      all P l -> all Q l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma might_satisfy_query_put d clauses acc a x
    :  might_satisfy_query d clauses acc ->
       elt_sound_for_query d clauses a x ->
       (*map.get acc a = None ->*)
       (*TODO: what hyps?*)
       might_satisfy_query d clauses (map.put acc a x).
  Proof.
    unfold might_satisfy_query;
      basic_goal_prep.
    specialize (H i args ltac:(auto)).
    break; subst.
    exists x0; intros; break; split; auto.
    exists x1; intros; break; split; auto.
    assert (List.length args = List.length x1) by eauto using Forall2_len_eq.      
    revert H2.
    rewrite !Forall2_combine by assumption.
    eapply all_weaken.
    basic_goal_prep.
    basic_goal_prep.
    destruct (idx_dec a i0); subst.
    {
      rewrite map.get_put_same in H6;
        inversion H6; subst; clear H6.
      specialize (H0 i args ltac:(auto)).
      break.
      assert (x = x0) by congruence; subst.
      specialize (H6 x1 H3).
      rewrite !Forall2_combine in H6 by assumption.
      pose proof (in_all _ _ H6 H2) as H'.
      simpl in H'.
      symmetry; auto.
    }
    {
      eapply H5.
      rewrite map.get_put_diff in H6; auto.
    }
  Qed.

  (*
  Lemma might_be_sound_clause_free_vars d vars trie clause
    : trie_might_be_sound_for_atom d vars trie clause ->
      forall x, In x (snd clause) -> In x vars.
  Proof.
    unfold trie_might_be_sound_for_atom; intuition (break;subst).
    simpl in *.
    unfold trie_might_be_sound_for_relation in *; intuition (break; subst).
   *)

  Definition well_scoped_clause vars (c : atom) :=
    all (fun x => In x vars) (snd c).

  
  Lemma next_var_sound_for_query d a vars tries clauses x m0
    : Forall2 (trie_might_be_sound_for_atom d (a :: vars)) tries clauses ->
      finite_set m0 =
        fold_left set_with_top_intersection (map (fun '(_, v) => values_of_next_var v) tries) all_elements ->
      member m0 x = true ->
      elt_sound_for_query d clauses a x.
  Proof.
    unfold elt_sound_for_query;
      basic_goal_prep.
  Admitted.
    
    
  Lemma generic_join'_sound d m tries vars clauses acc
      : (*well_scoped_query d (Build_query vars clauses) ->*)
    all_unique vars ->
      Forall2 (trie_might_be_sound_for_atom d vars) tries clauses ->
      In m (generic_join' tries vars acc) ->
      (*TODO: is this necessary?
      all_clauses_might_be_inhabited d (Build_query vars clauses) ->*)
      (*TODO: what do I need to know about acc? *)
      might_satisfy_query d clauses acc ->
      might_satisfy_query d clauses m.
    (*
      (*TODO: use single q for query?*)
      satisfies_query d (Build_query vars clauses) m.*)
  Proof.
    simpl.
    revert tries acc m.
    induction vars;
      basic_goal_prep;
      basic_utils_crush.
    
(*    destruct H.
    basic_goal_prep.
    inversion H; clear H; subst.
 *)
    
    case_match'.
    2: intro H'; now safe_invert H'.
    intro H'; apply in_set_flat_map in H'.
    break.
    eapply IHvars; eauto using trie_might_be_sound_choose_next_val.
    eapply might_satisfy_query_put; eauto using next_var_sound_for_query.
  Qed.
    
          (*


    
    apply IHvars in H0; auto.
    2:admit (*TODO: lemma*).
    {
      {
        pose proof (in_fold_left_tries _ _ _ _ HeqH0 H2).
        revert H3 H.
        clear m H0 IHvars HeqH0.
        revert clauses H1.
        induction tries;
          basic_goal_prep;
          basic_utils_crush.
        {
          safe_invert H; eauto.
          (*TODO: automate*)
        }
        {
          safe_invert H.
          constructor; eauto.
          2:{
            eapply IHtries; eauto.
            eapply might_satisfy_cons_weaken; eauto.
          }
          specialize (H3 i q ltac:(intuition)).
          TODO: missing subst on y/l' (need a notin?)
           next_val_sound_for_atom 
          TODO: choose_next_val invariant

        1,4: shelve.
        intros.

        unfold member_with_top.
    }
    TODO: use values_of_next_var_sound?
    Fail.
    {     (* 
      intro H'; apply in_map_flat_map in H'.
      basic_goal_prep.
      assert (forall i t, In (i,t) tries ->
                          member_with_top (values_of_next_var t) x = true).
      {
        revert HeqH0; clear; induction tries;
          basic_goal_prep; try now intuition.
        
          basic_utils_crush.
      (*TODO: show x in denotation of all tries*)
      eapply IHvars; eauto.
      1:(*TODO: show x in next vals of all tries*) idtac.
      2:{ (* same as above*)

    }
      intro H'; apply in_map_flat_map in H'.
      basic_goal_prep.
      inversion H; clear H; subst.
      eapply IHvars.
      { split; eauto.
      specialize (IHvars _ _ _ ltac:(eauto)).
      destruct H' as [v [? ?]].
      eapply IHvars in H3.

      TODO: generalize conclusion to something like might_satisfy_query before induction?
                       apply acc to clauses?

      Lemma satisfies_query_subst
        : (forall v, ??? -> satisfies_query d {| free_vars := vars; clauses := (clauses_subst a v clauses0) |} m) ->
        satisfies_query d {| free_vars := a :: vars; clauses := clauses0 |} m
      TODO: subst lemmas
    }
    }
      might_satisfy_empty_vars_satisfies
      specialize (H1 _ _ H2).
      destruct H1 as [R [? [tuple [? ?]]]].
      exists R; split; auto.
      exists tuple; split; auto.
      revert H1;

    }
      revert dependent tries.
      revert dependent clauses0.
      induction clauses0;
        destruct tries;
      basic_goal_prep;
        basic_utils_crush.
      destruct H1; subst.
      revert H0.
      simpl.
      clear tries clauses0 IHclauses0 H2.
      unfold unwrap_with_default.
      case_match; intros TS.
      2:{
        TODO: missing connection between m and q
        
      inversion TS.
      
      {
        destruct H2 as [? [? [? ?]]]; subst.
        assert (x = x0) by congruence; subst.
        exists x0; split; auto.
        inversion H2; subst.
        {
          destruct H as [? [? ?]].
          exists x; split; auto.
          destruct x; destruct args; simpl in *;
            now basic_utils_crush.
        }
        {
          
        }
                                               
        exists 
        TODO: forall vs exists; predicates don't agree
    }
    simpl.
    generalize (clauses q), (free_vars q).
    clear q.
    intros.
           *)*)
  
  Lemma NoDup_all_unique {A} (l : list A)
    : NoDup l <-> all_unique l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
    - constructor.
    - inversion H1; tauto.
    - inversion H1; tauto.
    - constructor; tauto.
  Qed.
    
  Theorem generic_join_sound d q m
    : well_scoped_query d q ->
      In m (generic_join d q) ->
      satisfies_query d q m.
  Proof.
    unfold generic_join, well_scoped_query.
    
    assert (all_clauses_might_be_inhabited d q) by admit.
    destruct q; simpl in *.
    destruct free_vars0; [basic_goal_prep; basic_utils_crush| generalize (i::free_vars0) as free_vars1].
    intros fvs [H_nodups Hwsq].
    match goal with
    | [Hwsq : all ?P ?clauses0 |- context[build_tries ?d ?vars ?a]] =>
        let Hwsq' := fresh Hwsq in
        assert (all (fun a : idx * list idx => all (fun x : idx => In x vars) (snd a)) clauses0) as Hwsq' by admit;
        pose proof (build_tries_sound d vars a ltac:(assumption) Hwsq')
    end.
    clear Hwsq (*TODO: is this needed anymore?*).
    revert H.
    generalize (build_tries d fvs clauses0).
    unfold satisfies_query.
    intros.
    simpl in *.
    rewrite NoDup_all_unique in H_nodups.
    assert (might_satisfy_query d clauses0 m).
    {
      eapply generic_join'_sound; eauto.
      2: {
        eapply empty_might_satisfy with (d:=d) (q:= {| free_vars := fvs; clauses := clauses0 |}).
        {
          unfold well_scoped_query.
          rewrite NoDup_all_unique; split; simpl; intuition auto.
          clear H2.
          revert dependent clauses0.
          induction clauses0; repeat basic_goal_prep;
            auto.
          inversion H0; subst; clear H0.
          unfold all_clauses_might_be_inhabited, might_be_inhabited in *.
          repeat basic_goal_prep.
          repeat (specialize (IHclauses0 ltac:(auto))).
          intuition subst.
          eexists; eauto.
        }
        {
          exact H.
        }
      }
      {
        (*
        TODO: what is n???
      }
        ; eauto.
    (*TODO: only use the latter*)
    
    pose proof (generic_join'_sound _ _ _ _ _ _ H_nodups ltac:(shelve) H1
                                    (empty_might_satisfy _ _ ltac:(eauto) H)).
    TODO: use lemma above
    (*TODO: reason about generic_join'

      forall i t,

        
        In (i,t) (build_tries d fv cls) ->
        exists R,
          mag.get d i = Some R
          /\ (forall args, (i,args
            sound_trie_for_relation R (map ? t ?


        *)*)
  Admitted.                     

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
               trie_set query_trie qt_unconstrained _ qt_tree qt_nil
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
