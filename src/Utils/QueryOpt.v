Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind FunctionalDB Monad ExtraMaps.
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

  
  

  Record uncompiled_rw_rule : Type :=
  { uc_query_vars : list idx;
    uc_query_clauses : list atom;
    uc_write_clauses : list atom;
    uc_write_unifications : list (idx * idx);
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

  (* We add the query vars
  Definition add_vars (l : list idx) : ST (named_list symbol idx) :=
    @!let idxs <- list_Mmap (fun x => hash_node x []) l in
      ret (combine l idxs).
  *)

  (* adds a rule clause, using its variables as unionfind indices
     Note: output idx unlikely to be used.
   *)
  Definition add_rule_clause '(Build_atom f args out) : ST unit :=
    (* TODO: make sure all vars are valid in the union-find*)
    @! (*let _ <- add_vars_to_uf (out::args) in*)
      (* this may create new vars!
         need to make sure all rule vars are already added.*)
      let out' <- @hash_node (f : symbol) args in
      let _ <- union out out' in
      ret tt.

  (*
  Definition initialize_uf r :=
    (*likely to dup a couple vars, but that's fine.
      Necessary to include coquery vars as well, even for query,
      so that the substitution doesn't identify new vars w/
      coquery vars.
     *)
    for_each (r.(query_vars)++(map atom_ret r.(coquery)))
             (fun x => add_to_uf x).
  
  Definition add_clauses (clauses : list atom) : ST unit :=
    list_Miter add_rule_clause clauses.

  Definition optimize_query r :=
    let (vars_out, i) := @! let _ <- initialize_uf r in
                    let _ <- add_clauses r.(query) in
                    let _ <- rebuild 1000 in
                    (list_Mmap find r.(query_vars))
    in
    let new_clauses := list_atoms i in
    let var_map := combine r.(query_vars) vars_out in
    (* TODO: rename var_map vars to be dense starting at 0.
       Will impact map performance at runtime.
     *)
    (dedup vars_out, new_clauses, rename_clauses var_map r.(coquery)).

  Definition optimize_coquery r :=
    (*TODO: pass for eliminating query-determined vars,
      where coquery contains an atom f args out where f args out'
      is in the query and out is fresh.
     *)
    let (vars_out, i) := @! let _ <- initialize_uf r in
                    let _ <- add_clauses r.(query) in
                    let _ <- rebuild 1000 in
                    (list_Mmap find r.(query_vars))
    in
    let new_clauses := list_atoms i in    
    let var_map := combine r.(query_vars) vars_out in
    let unification_clauses :=
      for each x such that x in r.(query_vars) and x->z (z!=x),
      let (f args z) in new_clauses in
      (f args x)
      
    in
    (dedup vars_out, new_clauses, rename_clauses var_map r.(coquery)).

   *)

  Notation rw_set := (rw_set idx symbol symbol_map idx_map).
  (* TODO: Using ST' instead of ST because of some weird namespacing *)
  Local Notation ST' := (state (symbol_map (idx * idx_map (list idx * idx)))).

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

  Definition hash_clause (a : atom) : ST' idx :=
    let (f, args, out) := a in
    fun S : symbol_map (idx * idx_map (list idx * idx)) =>
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
    let idxs := map idx_of_nat (seq 0 (length clause_vars)) in
    let sub := combine clause_vars idxs in
    let compiled_clause := Build_atom f (map (named_list_lookup default sub) args)
                             (named_list_lookup default sub out) in
    @! let i <- hash_clause compiled_clause in
      ret (f, i, clause_vars).

  Local Notation compiled_rw_rule := (compiled_rw_rule idx symbol).
  
  Definition compile_rw_rule (r  : uncompiled_rw_rule) : ST' compiled_rw_rule :=
    let (qvs, qcls, wcls, wufs) := r in
    @! let qcls_ptrs <- list_Mmap (compile_query_clause qvs) qcls in
      (* Assume it must be nonempty to be useful *)
      match qcls_ptrs with
      | [] => (*Should never happen if called corrrectly*)
          Mret (Build_compiled_rw_rule _ _ default default default default)
      | c::cs => Mret (Build_compiled_rw_rule _ _ qvs (c,cs) wcls wufs)
      end.

  
  Arguments Build_rw_set {idx symbol}%type_scope {symbol_map idx_map}%function_scope 
    query_clauses compiled_rules%list_scope.
  
  Definition build_rw_set (rules : list uncompiled_rw_rule) : rw_set :=
    let (crs, clauses_plus) := list_Mmap compile_rw_rule rules map.empty in
    Build_rw_set (map_map snd clauses_plus) crs.
 
End WithMap.
