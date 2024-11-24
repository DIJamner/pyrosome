Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
From Utils.EGraph Require Import Defs.
Import Monad.StateMonad.

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)

      (*TODO: just extend to Natlike?*)
      (idx_succ : idx -> idx)
      (idx_zero : WithDefault idx)
      (*TODO: any reason to have separate from idx?*)
    (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
      (default_symbol : WithDefault symbol).

  Existing Instance idx_zero.
  Existing Instance default_symbol.
  
  Context (symbol_map : forall A, map.map symbol A)
        (symbol_map_plus : map_plus symbol_map).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_plus : map_plus idx_trie).

  Notation atom := (atom idx symbol).

  Notation hash_node := (hash_node idx_succ).
  
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie).

  (*TODO: move to semantics?
    Semantic interpretation of variables:
    - query_vars is a permutation of (fvs query_clauses)
    - elements of query_vars are universally quantified
    - elements of ((fvs write_clauses) - query_vars) are existentially quantified
    - no new variables in write_unifications
   *)
  Record log_rule : Type :=
  { query_vars : list idx;
    query_clauses : list atom;
    write_clauses : list atom;
    write_unifications : list (idx * idx);
  }.

  (*
    Normalization through congruence closure

    We can use egraph rebuilding to perform extensive rw rule optimization.
    Just adding all the atoms to the egraph deduplicates them in a simple sense,
    but it still leaves the situation where two identical atoms allocate separate output variables.
    However, rebuilding solves exactly this situation, so we can just call it to handle
    the job for us.

    TODO: what to do about input vs fresh vars in output clauses of query?
    also: split between query and coquery clauses
    - a chance for optimization to eliminate coquery clauses that are in the query
    - how to distinguish query and coquery in the same egraph: special fn table?

    Something that will definitely work:
    - rebuild-optimize just the query, building a map of variable -> egraph index at initialization
                     + Note: this map can be the identity map if the variables are dense and numbered right,
                             but that might be a bit too delicate for something with unimportant performance
    - unify like variables across the rule
    - rebuild-optimize the coquery independently, again w/ a var map to retain the exact names
                     + TODO: what to do about two query variables getting unified?
                             We can safely assume they are output vars.
                             This can be represented by adding a node twice, once for each var.
                             Could also add unification clauses, but that doesn't seem worth it

    Potential improvement:
    Given D  |- G, (f x^ |-> z) where (f x^ |-> y) in D and z not in fv(D), we can remove (f x^ |-> z)
    from the coquery and replace z with y everywhere.
    This could then lead to improvements via congruence, so it would be beneficial to do in the egraph.

    Idea: after optimizing the query, instead of starting from a fresh graph,
    add the coquery to the existing egraph, then rebuild.
    Take the output and subtract all query clauses.
    Question: is this sound & complete?
    - Seems like no: what if two query clauses get unified?
      Could happen when the coquery is supposed to generate a merge.
      Would either result in some query clauses migrating to the coquery,
      or if do really wrong, a rule that restricts the inputs instead of unifying the outputs

    Note: improving the coquery is nice, but not very important, so we'll skip this latter idea for now.


    Core implementation question: add vars as 0-arg constructors
    or 'pun' as ids? Punning makes rebuilding do the right thing automatically, but subtle.
    0-arg constructors requires rws for output.


    TODO: for punning:
    - add vars to union-find such that they are all valid ids
         (note: will benefit from vars being dense starting at 0)
    - add clauses as atoms (put rather than hash since the ids are preallocated)
    - run rebuild
    
    - for coquery, if a var isn't in the query vars, still pre-add it,
      but use hash_node to generate a value, then union them.
      Generates excess free vars the first time a clause is seen, but allows for proper deduplication

    
   *)    
  
  
  Local Notation "'ST'" := (state instance).
  
  (*TODO: is probably always id. Unify symbol & idx?*)
  Context (idx_as_symbol : idx -> symbol).
  Definition add_fundep_var v :=
    hash_node (idx_as_symbol v) [].

  Definition add_fundep_clause (a : atom) : ST unit :=
    @! let args' <- list_Mmap add_fundep_var a.(atom_args) in
      let out' <- add_fundep_var a.(atom_ret) in
      (*TODO: pick the right add_node fn*)
      let i <- hash_node_out _ _ _ _ _ _ (Build_atom a.(atom_fn) args' out') in
      let _ <- union i out' in
      ret tt.

  Fixpoint build_var_map' (vars : list idx) (g : instance) acc :=
    match vars with
    | [] => rev acc
    | x::vars =>
        let (x_id,_) := hash_node (idx_as_symbol x) [] g in
        build_var_map' vars g ((x_id,x)::acc)
    end.

  Definition build_var_map v g := build_var_map' v g [].

  Definition atom_fvs (a : atom) := a.(atom_ret)::a.(atom_args).

  Section Optimize.
    Context (fuel : nat) (lr : log_rule).

    Let g_query := snd (Mseq (list_Miter (M :=state instance) add_fundep_clause lr.(query_clauses))
        (rebuild _ _ _ _ _ _ _ fuel)
        (empty_egraph idx_zero)).

    Let vm_query := build_var_map lr.(query_vars) g_query.

    Let sub_q x := named_list_lookup x vm_query x.
    
    Let query_clauses' : list atom :=
          (flat_map (fun '(f,y) =>
                       map (fun p =>
                              Build_atom f (map sub_q (fst p)) (sub_q (snd (snd p))))
                         (map.tuples y))
             (* remove all atoms that are vars *)
             (filter (fun p => negb (inb (fst p) (map idx_as_symbol lr.(query_vars))))
                (map.tuples g_query.(db)))).
    
    Let in_query_clauses (v : idx) :=
          existsb (fun c => orb (inb v c.(atom_args)) (eqb v c.(atom_ret))) query_clauses'.

    Let query_vars' := filter in_query_clauses lr.(query_vars).

    Let g_write :=
          snd (Mseq (list_Miter (M :=state instance) add_fundep_clause lr.(write_clauses))
                 (rebuild _ _ _ _ _ _ _ fuel)
                 g_query).

    (* prepend query vars to make sure that they take precedence over fresh vars *)
    Let vars := (dedup (eqb (A:=_))
                           (lr.(query_vars) ++ (flat_map atom_fvs lr.(write_clauses)))).

    Let sub_w x := named_list_lookup x (build_var_map vars g_write) x.

    (* TODO: BUG. Need to sort so that fresh vars first appear in the conclusions.
     *)
    Let write_clauses' : list atom :=
          (* TODO: sort by existential var dependence *)
          (*(sort_by_var_deps *)
          (*remove all query clauses *)
          (filter
             (fun c => negb (inb c query_clauses'))
             (flat_map (fun '(f,y) =>
                          map (fun p =>
                                 Build_atom f (map sub_w (fst p)) (sub_w (snd (snd p))))
                            (map.tuples y))
                (* remove all atoms that are vars *)
                (filter (fun p => negb (inb (fst p) (map idx_as_symbol vars)))
                   (map.tuples g_write.(db))))).
    
    (*TODO: optimize unifications of fresh vars out*)
    Let write_unifications' :=
          (filter (fun p => negb (eqb (fst p) (snd p)))
             (dedup (eqb (A:=_)) (map (fun p => (sub_w (fst p), sub_w (snd p)))
                                    lr.(write_unifications)))).
    
    Definition optimize_log_rule :=
      Build_log_rule query_vars' query_clauses' write_clauses' write_unifications'.

  End Optimize.

  Notation rule_set := (rule_set idx symbol symbol_map idx_map).
  (* TODO: Using ST' instead of ST because of some weird namespacing *)
  Local Notation ST' := (state (symbol_map (idx * idx_map (list nat * nat)))).

  (* Sorts the elements in the first list, viewed as a set, by their position in the second.
     Assumes the second list has no duplicates.
   *)
  Definition sort_by_position_in (l1 l2 : list idx) :=
    filter (fun x => inb x l1) l2.

  (* Returns `Some k` for some k such that (k,v) is in m, if any such pair exists.
     Expect this to be slow. *)
  Definition map_inverse_get {key value} {map : map.map key value} `{Eqb value}
    (m : map) (v : value) : option key :=
    map.fold (fun acc k v' => if eqb v v' then Some k else acc) None m.

  Definition hash_clause (a : Defs.atom nat symbol) : ST' idx :=
    let (f, args, out) := a in
    fun S : symbol_map (idx * idx_map (list nat * nat)) =>
      match map.get S f with
      | Some (last, m) =>
          match map_inverse_get m (args,out) with
          | Some i => (i, S)
          | None =>
              let new_id := idx_succ last in
              let S' := map.put S f (new_id, map.put m new_id (args,out)) in
              (new_id, S')
          end
      | None => (idx_zero, map.put S f (idx_zero, map.singleton idx_zero (args,out)))
      end.

  Local Notation idx_of_nat := (idx_of_nat _ idx_succ idx_zero).

  Definition compile_query_clause (qvs : list idx) (a : atom) : ST' (symbol * idx * list idx) :=
    let (f, args, out) := a in
    let clause_vars := sort_by_position_in (out::args) qvs in
    let indices : list nat := (seq 0 (length clause_vars)) in
    let sub : named_list idx nat := combine clause_vars indices in
    let compiled_clause := Build_atom f (map (named_list_lookup 0 sub) args)
                             (named_list_lookup 0 sub out) in
    @! let i <- hash_clause compiled_clause in
      ret (f, i, clause_vars).

  Local Notation erule := (erule idx symbol).
  Local Notation const_rule := (const_rule idx symbol).

  
  Definition clauses_fvs l rem_list :=
    filter (fun x => negb (inb x rem_list))
      (dedup (eqb (A:=_)) (flat_map atom_fvs l)).
  
  Definition compile_rule (r  : log_rule) : ST' (erule + const_rule) :=
    let (qvs, qcls, wcls, wufs) := r in
    @! let qcls_ptrs <- list_Mmap (compile_query_clause qvs) qcls in
      (* Assume it must be nonempty to be useful.
         TODO: how to handle empty rules?
         essentially just add a term to the egraph, can be run once and discarded.
       *)
      match qcls_ptrs with
        (* assumes qvs empty *)
      | [] => Mret (inr (Build_const_rule _ _ (clauses_fvs wcls []) wcls wufs))
      | c::cs => Mret (inl (Build_erule _ _ qvs (c,cs) (clauses_fvs wcls qvs) wcls wufs))
      end.

  (*TODO: put in Utils.v*)
  Definition split_sum_list {A B} (l : list (A + B)) : (list A * list B) :=
    List.fold_right (fun e acc => match e with
                                  | inl e' => (e'::fst acc, snd acc)
                                  | inr e' => (fst acc,e'::snd acc)
                                  end) ([],[]) l.
  
  
  Definition build_rule_set (rules : list log_rule) : rule_set :=
    let opt_rules := map (optimize_log_rule 100 (*TODO: magic number*)) rules in
    let (crs, clauses_plus) := list_Mmap compile_rule opt_rules map.empty in
    let (erules, consts) := split_sum_list crs in
    Build_rule_set (map_map snd clauses_plus) erules consts.
 
End WithMap.


Arguments build_rule_set {idx}%type_scope {Eqb_idx} idx_succ%function_scope idx_zero 
  {symbol}%type_scope {Eqb_symbol} {symbol_map}%function_scope {symbol_map_plus} 
  {idx_map idx_trie}%function_scope idx_as_symbol%function_scope rules%list_scope.
