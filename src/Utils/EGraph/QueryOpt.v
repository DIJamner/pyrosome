Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
From Utils.EGraph Require Import Defs Semantics.
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

  Existing Instance Eqb_idx.
  Existing Instance idx_zero.
  Existing Instance default_symbol.
  
  Context (symbol_map : forall A, map.map symbol A)
        (symbol_map_plus : map_plus symbol_map).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_plus : map_plus idx_trie).

  Notation atom := (atom idx symbol).
  Notation sequent := (sequent idx symbol).
  
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie).


  (*TODO: moved to semantics and edited
    Semantic interpretation of variables:
    - query_vars is a permutation of (fvs query_clauses)
    - elements of query_vars are universally quantified
    - elements of ((fvs write_clauses) - query_vars) are existentially quantified
    - no new variables in write_unifications
   
  Record log_rule : Type :=
  { query_vars : list idx;
    query_clauses : list atom;
    write_clauses : list atom;
    write_unifications : list (idx * idx);
  }.
*)

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

  Definition canonicalize_clause c {A} : state (instance A) (clause _ _) :=
    match c with
    | atom_clause a => Mfmap atom_clause (canonicalize a)
    | eq_clause x y =>
        @! let x' <- find x in
          let y' <- find y in
          ret (eq_clause x' y')
    end.
  
  (*TODO: duplicated. move*)
  #[local] Instance map_default {K V} `{m : map.map K V} : WithDefault m := map.empty.

  Definition remove_atom a {A} : state (instance A) unit :=
    fun '(Build_instance _ _ _ _ _ _ db equiv parents epoch wl an) =>
      let tbl_upd tbl := map.remove tbl a.(atom_args) in
      let db' := map_update db a.(atom_fn) tbl_upd in
      (tt,Build_instance _ _ _ _ _ _ db' equiv parents epoch wl an).

  
  Definition force_uf (uf : union_find idx (idx_map idx) (idx_map nat)) :=
    let force_parent x :=
      match UnionFind.find _ _ _ _ uf x with
      | Some y => snd y
      | None => (*never happens *) x
      end in
    let rank' := map_map (fun _ => 1) uf.(rank _ _ _) in
    let parent' := map_map force_parent uf.(parent _ _ _) in
    MkUF _ _ _ rank' parent' 1 uf.(next _ _ _).
    
  Definition force_equiv {X} : state (instance X) unit :=
    fun '(Build_instance _ _ _ _ _ _ db equiv parents epoch wl an) =>
      let equiv' := force_uf equiv in
      (tt,Build_instance _ _ _ _ _ _ db equiv' parents epoch wl an).

(* TODO: split in 2: egraph comps to sequent, and sequent to egraph comps *)
Section SequentOfStates.
  Context {X A} `{analysis idx symbol X}
    (assumptions : state (instance X) A)
    {B} (conclusions : A -> state (instance X) B).
  
  (* We keep around the egraph for use in the conclusion,
     but it suffices to discard the equations and just use the assumptions,
     since the atoms of the query will all use the canonical variables.

     TODO: make sure to take in a sufficient fuel.
     Must be an input to be sound.
   *)
  Let assumption_inst :=
        (@! let a <- assumptions in
           let _ <- rebuild 1000 in
           ret a)
          (empty_egraph idx_zero X).
  Let assumption_atoms := db_to_atoms (snd assumption_inst).(db).

  (*
    Start the conclusion egraph from the assumption one to handle collapsing
    any conclusion variables that were unified by assumption simplification.

    This will leave a bunch of excess equations in the conclusion,
    but we optimize them out later, and even if we didn't, reflexive & fresh unions are cheap.

    Note: force_equiv guarantees that the union-find is rank 1.
    This means that when eliminating dead equations later,
    we do not need to consider transitivity.
   *)
  Let conclusion_inst :=
        let comp a :=(@! let b <- conclusions a in
                        let _ <- rebuild 1000 in
                        let _ <- force_equiv in
                        ret b) in
        snd (uncurry comp assumption_inst).

  (* Remove the atoms of the assumptions.
     We remove them rather than not adding them in the first place
     because we also want to remove anything from the conclusion that duplicates
     an assumption.
   *)
  Let conclusion_inst_dedup :=
        snd (list_Miter
               (fun a => Mbind (fun a => remove_atom a (A:=X))
                           (canonicalize a))
               assumption_atoms
               conclusion_inst).

  (*
    Should be a correct conclusion, but contains a bunch of extra equations.
   *)
  Let conclusion_atoms := db_to_atoms conclusion_inst_dedup.(db).
  Let conclusion_eqs_verbose : list (_*_) :=
        map.tuples conclusion_inst.(equiv).(parent _ _ _).

  (* Check whether the variable is in any atoms (conclusion or assumptions) *)
  Let conclusion_var_in_atoms x :=
    existsb (fun a => orb (eqb a.(atom_ret) x)
                        (inb x a.(atom_args)))
      (assumption_atoms ++ conclusion_atoms).

  Let live_eqn x y :=
        (* filter out all reflexive equalities,
           as well as all equalities where one of the variables is not in the atomsz
         *)
        andb (andb (negb (eqb x y))
                   (*TODO: double check! should check query, not conclusion *)
                (conclusion_var_in_atoms x))
                (conclusion_var_in_atoms y).
  
  (*TODO: should be optimized more; current implementation unfinished*)
  Let conclusion_eqs_final :=
        (* filter out the obviously dead equations*)
       (*TODO: debug filter (fun '(x,y) => negb (can_erase y))  *)
        filter (fun '(x,y) => live_eqn x y)
          conclusion_eqs_verbose.

 
  (*A variant that preserves in the type that the assumption has no equations*)
  Definition sequent'_of_states := 
    (assumption_atoms, conclusion_atoms , conclusion_eqs_final).

  (* Generates an (optimized) sequent from two egraph state monad values *)
  Definition sequent_of_states := 
    Build_sequent _ _ (map atom_clause assumption_atoms)
      (map (uncurry eq_clause) conclusion_eqs_final++(map atom_clause conclusion_atoms)).

  (* Diagnostics. For debugging only*)

  Definition seq_of_S_assumption_atoms := assumption_atoms.
  Definition seq_of_S_assumption_eqns := map.tuples (snd assumption_inst).(equiv).(parent _ _ _).
  Definition seq_of_S_conclusion_atoms :=  db_to_atoms conclusion_inst.(db).
  Definition seq_of_S_live_eqn := live_eqn.
  Definition seq_of_S_in_atom := conclusion_var_in_atoms.
  Definition seq_of_S_verbose := conclusion_eqs_verbose.

  (************************)

End SequentOfStates.

Section Optimize.
  Context (s : sequent).

  
  (*TODO: make sure to choose sufficient fuel to totally rebuild.
    Also, if this is it, compute more efficiently.
   *)
  Let fuel :=
        let var_count :=
          (length (flat_map (clause_vars _ _) s.(seq_assumptions)
                   ++ flat_map (clause_vars _ _) s.(seq_conclusions)))
        in
        var_count * var_count.


  Notation clauses_to_instance :=
    (clauses_to_instance idx_succ (analysis_result:=unit)).
  
  Let sub_and_assumptions :=
        @! let (_,sub) <- clauses_to_instance s.(seq_assumptions) [] in
         (* let _ <- rebuild fuel in TODO: rebuilds above already *)
          ret sub.

  Let conclusions (p : named_list idx idx) : state (instance unit) _ :=
        (*Mseq *) (clauses_to_instance s.(seq_conclusions) p) (* (rebuild fuel) *). 
 
  (*A variant that preserves in the type that the assumption has no equations*)
  Definition optimize_sequent' := sequent'_of_states sub_and_assumptions conclusions.
  
  Definition optimize_sequent := sequent_of_states sub_and_assumptions conclusions.

  
  (* Diagnostics. For debugging only*)

  Definition opt_assumption_atoms := seq_of_S_assumption_atoms sub_and_assumptions.
  Definition opt_assumption_eqns := seq_of_S_assumption_eqns sub_and_assumptions.
  Definition opt_conclusion_atoms := seq_of_S_conclusion_atoms sub_and_assumptions conclusions.
  Definition opt_live_eqn := seq_of_S_live_eqn sub_and_assumptions conclusions.
  Definition opt_in_atom := seq_of_S_in_atom sub_and_assumptions conclusions.
  Definition opt_verbose := seq_of_S_verbose  sub_and_assumptions conclusions.

  (************************)

End Optimize.


  Definition atom_fvs (a : atom) := a.(atom_ret)::a.(atom_args).

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

  Definition compile_query_clause (qvs : list idx) (a : atom)
    : ST' (erule_query_ptr idx symbol) :=
    let (f, args, out) := a in
    let clause_vars := sort_by_position_in (out::args) qvs in
    let indices : list nat := (seq 0 (length clause_vars)) in
    let sub : named_list idx nat := combine clause_vars indices in
    let compiled_clause := Build_atom f (map (named_list_lookup 0 sub) args)
                             (named_list_lookup 0 sub out) in
    @! let i <- hash_clause compiled_clause in
      ret (Build_erule_query_ptr _ _ f i clause_vars).

  Local Notation erule := (erule idx symbol).
  Local Notation const_rule := (const_rule idx symbol).

  
  Definition clauses_fvs l rem_list :=
    filter (fun x => negb (inb x rem_list))
      (dedup (eqb (A:=_)) (flat_map (clause_vars idx symbol) l)).

  Definition compile_rule (r  : sequent) : ST' (erule + const_rule) :=
    let '(assumptions, conclusion_atoms, conclusion_eqs) :=
      optimize_sequent' r in
    (*TODO: optimize order somewhere*)
    let qvs := dedup (eqb (A:=_)) (flat_map atom_fvs assumptions) in
    (*TODO: simplify *)
    let conclusion_vars :=
      (clauses_fvs (map (uncurry eq_clause) conclusion_eqs
                      ++ map atom_clause conclusion_atoms) qvs) in
    @! let {ST'} qcls_ptrs <- list_Mmap (compile_query_clause qvs) assumptions in
      (* Assume it must be nonempty to be useful.
         TODO: how to handle empty rules?
         essentially just add a term to the egraph, can be run once and discarded.
       *)
      match qcls_ptrs with
      | [] => Mret (inr (Build_const_rule _ _ conclusion_vars
                           conclusion_atoms conclusion_eqs))
      | c::cs => Mret (M:=ST') (inl (Build_erule _ _ qvs (c,cs) conclusion_vars
                              conclusion_atoms conclusion_eqs))
      end.

  (*TODO: put in Utils.v*)
  Definition split_sum_list {A B} (l : list (A + B)) : (list A * list B) :=
    List.fold_right (fun e acc => match e with
                                  | inl e' => (e'::fst acc, snd acc)
                                  | inr e' => (fst acc,e'::snd acc)
                                  end) ([],[]) l.
  
  
  Definition build_rule_set (rules : list sequent) : rule_set :=
    let (crs, clauses_plus) := list_Mmap compile_rule rules map.empty in
    let (erules, consts) := split_sum_list crs in
    Build_rule_set (map_map snd clauses_plus) erules consts.
  
End WithMap.


Arguments build_rule_set {idx}%type_scope {Eqb_idx} idx_succ%function_scope idx_zero 
  {symbol}%type_scope {Eqb_symbol} {symbol_map}%function_scope {symbol_map_plus} 
  {idx_map}%function_scope {idx_map_plus} {idx_trie}%function_scope rules%list_scope.

Arguments QueryOpt.sequent_of_states {idx}%type_scope {Eqb_idx} 
  {idx_zero} {symbol}%type_scope {Eqb_symbol} {symbol_map idx_map}%function_scope
  {idx_map_plus} {idx_trie}%function_scope {X A}%type_scope {H} 
  assumptions {B}%type_scope conclusions%function_scope.
