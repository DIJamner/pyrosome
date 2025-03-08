(* An implementation of the core of egglog

   TODO: benchmark, then use plist everywhere feasible and retest
 *)
Require Import Equalities Orders ZArith Lists.List Uint63.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind (*SpacedMapTreeN*).
From Utils Require TrieMap TrieMapInt63.
Import Sets.
Import StateMonad.

Notation ne_list A := (A * list A)%type.
Definition ne_map {A B} (f : A -> B) (l : ne_list A) : ne_list B :=
  (f (fst l), map f (snd l)).

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)

      (*TODO: just extend to Natlike?*)
      (idx_succ : idx -> idx)
      (idx_zero : idx)
      (*TODO: any reason to have separate from idx?*)
    (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol).

  
  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_plus : map_plus symbol_map).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_plus : map_plus idx_trie).

  Context (analysis_result : Type).

  Record db_entry :=
    {
      entry_epoch : idx;
      entry_value : idx;
      (* Note: this is not a duplicate of the by-idx analyses.
         it is important that there is a result associated with each entry.
       *)
      entry_analysis : analysis_result;
    }.
  
  (*
    each symbol has an n-ary table of epoch-stamped entries.
    fst of result is epoch, snd is value
   *)
  Definition db_map := symbol_map (idx_trie db_entry).

  (*Context `{@map_plus symbol symbol_map}.*)

  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).

   (*
    clauses have the form R(x1,...xn) (|-> xn+1)?
    where xn+1, if provided, binds the output.
    atom_args should be of length either arity(R) or arity(R)+1
   *)
  Record atom :Type :=
    {
      atom_fn : symbol;
      atom_args : list idx;
      atom_ret : idx;
    }.

  #[export] Instance atom_eqb : Eqb atom :=
    fun a1 a2 =>
      (eqb a1.(atom_fn) a2.(atom_fn))
      && (eqb a1.(atom_args) a2.(atom_args))
      && (eqb a1.(atom_ret) a2.(atom_ret)).

  Class analysis : Type :=
    {
      (* gets an atom and the analyses of its children *)
      analyze : atom -> list analysis_result -> analysis_result;
      analysis_meet :  analysis_result -> analysis_result -> analysis_result;
      analysis_default :: WithDefault analysis_result;
    }.

  Context `{analysis}.
  
  Record instance := {
      db : db_map;
      equiv : union_find;
      parents : idx_map (list atom);
      (* Used to determine which entries belong to the frontier *)
      epoch : idx;
      (* used to delay unification until rebuilding *)
      worklist : list (idx * idx);
      (* TODO: maintain an upper bound on the number of rows in db
         for the purpose of ensuring termination?
       
      size : nat;*)
      (*
        Note: For saturation, need to maintain a 'changed' flag somewhere.
              (alternately, maintain the epoch of last edit)
              If we instead maintain one 'changed' flag per symbol,
              we can reuse tries from all tables that haven't changed.
              For pyrosome languages, this will frequently include type info.
              Probably worth doing, since the only cost is 'or'ing the 'changed'
              flags once per iteration
       *)
      analyses : idx_map analysis_result;
    }.

  Record erule_query_ptr :=
    {
      query_ptr_symbol : symbol;
      query_ptr_ptr : idx;
      query_ptr_args : list idx;
    }.
  
    (*
    each disjunct contains a free variable list and a list of clause info,
    where clause info consists of the idx of the clause and a substitution.
    The substitution must be monotonic, i.e. if n < m then s(n) < s(m)
   *)
  Record erule :=
    {
      query_vars : list idx;
      (* TODO: substitution could a named_list,
         or just be a list idx? but would require an injection
         nat -> idx
         Alternately, should it just be an idx map?

         We expect the substitution to be dense (actually total) on [0,n) for some n.
         but access is primarily ordered.

         symbol, clause id, clause variables (in query_vars order)
       *)
      query_clause_ptrs : ne_list erule_query_ptr;
      write_vars : list idx;
      (* The list of clauses to write for each assignment valid wrt the query.
         Uses the vars in query_vars, plus write_vars for fresh/unbound idxs.
       *)
      write_clauses : list atom;
      (*
        Can mostly be emulated with duplicate clauses,
        but is necessary for the case where we want to unify variables
        that only appear as functino inputs (e.g. the rule x : unit, y : unit |- x = y).
        Since we have to support it, we may as well allow them everywhere
        since it's a small improvement over adding the same clause twice with different outputs.
       *)
      write_unifications : list (idx * idx);
    }.

  (* Used for rules with no query.
     Such rules are valid, but only need to be run once
     and are incompatible with the nonempty assumptions of generic join.
   *)
  Record const_rule :=
    {
      const_vars : list idx;
      const_clauses : list atom;
      const_unifications : list (idx * idx);
    }.
  

  (*
    TODO: how to do clauses for output of rw_set?
    probably just makes sense to go by disjunct than try sharing,
    since adding is pretty cheap compared to trie creation.
   *)
  
  Record rule_set : Type :=
    {
      (* TODO: having nat recursion makes the implementation simpler.
         Either require nat recursion for idx or just implement a packed nat here,
         since most numbers will be 0-5 and essentially all will be <16
       *)
      query_clauses : symbol_map (idx_map (list nat * nat));
      compiled_rules : list erule;
      (* TODO: technically only need 1 const rule *)
      compiled_const_rules : list const_rule;
    }. 

  
  Local Notation ST := (state instance).

  
  (* does nothing if the arguments don't have analysis results already.
     TODO: does this design make sense?
     Analysis is not attached to the node anywhere
   *)
  Definition update_analyses a_ret new_a : ST unit :=
    fun i =>
      let meet_a := match map.get i.(analyses) a_ret with
                    | Some oa => analysis_meet new_a oa
                    | None => new_a
                    end
      in
      let analyses' := map.put i.(analyses) a_ret meet_a in
      (tt, Build_instance i.(db) i.(equiv) i.(parents) i.(epoch) i.(worklist) analyses').

  (* assumes the idxs in lst already have analysis results*)
  Definition get_analyses lst : ST (list analysis_result) :=
    fun i =>
      match list_Mmap (map.get i.(analyses)) lst with
      | Some al => (al, i)
      | _=> (default, i)
      end.
  
  (*TODO: propagate down the removal of the option and push to UnionFind file
    as an alternative
   *)
  Definition union (v v1 : idx) : ST idx :=
    fun d =>
      (*TODO: eqb duplicated in UF.union; how to reduce the work?*)
      if eqb v v1 then (v,d)
      else
        let new_analysis :=
          unwrap_with_default
            (@!let v_analysis <- map.get d.(analyses) v in
               let v1_analysis <- map.get d.(analyses) v1 in
               ret (analysis_meet v_analysis v1_analysis))
        in
        (*should always return Some if v in uf *)
        @unwrap_with_default _  (v,d)
        (@!let (uf', v') <- UnionFind.union _ _ _ _ d.(equiv) v v1 in
             let v_old := if eqb v v' then v1 else v in
             let analyses' :=
                   (*TODO: doesn't garbage collect right now *)
                   map.put (map.put d.(analyses) v new_analysis)
                     v' new_analysis in  
             ret {option} (v', Build_instance d.(db) uf' d.(parents)
                     d.(epoch) ((v_old,v')::d.(worklist)) analyses')).
    

  Definition alloc : ST idx :=
    (fun i =>
       let (equiv', x_fresh) := alloc _ _ _ idx_succ i.(equiv) in
       (x_fresh, Build_instance i.(db) equiv' i.(parents) i.(epoch) i.(worklist) i.(analyses))).
  
  (*TODO: move this somewhere?
    TODO: sometimes maps can implement this more efficiently
   *)
  Definition map_update {K V} `{WithDefault V} {mp : map.map K V} (m : mp) x (f : V -> V) :=
    match map.get m x with
    | Some v => map.put m x (f v)
    | None => map.put m x (f default)
    end.

  (*
  (*TODO: move this somewhere?
    TODO: sometimes maps can implement this more efficiently
   *)
  Definition map_update_if_exists {K V} {mp : map.map K V} (m : mp) x (f : V -> V) :=
    match map.get m x with
    | Some v => map.put m x (f v)
    | None => m
    end.
  *)

  (*TODO: move*)
  #[local] Instance map_default {K V} `{m : map.map K V} : WithDefault m := map.empty.
  
  Definition new_singleton_out' a out_a : ST idx :=
    fun i =>
      let tbl_upd tbl :=
        map.put tbl a.(atom_args)
                        (Build_db_entry i.(epoch) a.(atom_ret) out_a) in
      let db' := map_update i.(db) a.(atom_fn) tbl_upd in
      (* Add the node as a parent of its output.
         This is necessary to ensure output ids stay canonical,
         which matters for matching.

         Dedup the args to avoid adding a node twice.
       *)
      let parents' := fold_left (fun m x => map_update m x (cons a))
                        (dedup (eqb (A:=_)) (a.(atom_ret)::a.(atom_args))) i.(parents) in
      (a.(atom_ret), Build_instance db' i.(equiv) parents' i.(epoch) i.(worklist) i.(analyses)).

  Definition new_singleton_out a : ST idx :=
    @! let arg_as <- get_analyses a.(atom_args) in
      let out_a := analyze a arg_as in
      let _ <- update_analyses a.(atom_ret) out_a in
      (new_singleton_out' a out_a).
  
  (*TODO: propagate down the removal of the option and push to UnionFind file
    as an alternative
   *)
  Definition find a : ST idx :=
    fun d =>
      match UnionFind.find _ _ _ _ d.(equiv) a with
      | Some (uf',v') =>
          (v', Build_instance d.(db) uf' d.(parents)
                              d.(epoch) d.(worklist) d.(analyses))
      | None => (*should never happen if a in uf *) (a,d)  
      end.

  Definition canonicalize (a:atom) : ST atom :=
    let (f,args,o) := a in
    @!let args' <- list_Mmap find args in
      let o' <- find o in
      ret Build_atom f args' o'.

  
  (*
    takes in an idx that should be unified with the output (but doe no unification)
    Guarantees not to allocate a fresh idx
    TODO: move function boundary for a better spec
   *)
  Definition hash_node_out a : ST idx :=
    fun i =>
      match map.get i.(db) a.(atom_fn) with
      | Some tbl =>
          match map.get tbl a.(atom_args) with
          | Some (Build_db_entry _ x _) => (x, i)
          | None => new_singleton_out a i
          end
      | None => new_singleton_out a i
      end.

  
  (* accesses the egraph like a hashcons.
     If the node exists, return its id.
     Otherwise, generate a fresh id, store it, and return it
     TODO: generates extra idxs when the node already exists
   *)
  Definition hash_node (f : symbol) args : ST idx :=
    @! let out <- alloc in
      (hash_node_out (Build_atom f args out)).

  (* takes the current env as an accumulator for convenience *)
  Definition allocate_existential_vars (* write_vars env_acc *)
    : list idx -> idx_map idx -> ST (idx_map idx) :=
    list_Mfoldl (fun acc x =>
                   @! let v <- alloc in
                     ret (map.put acc x v)).
  
  (* writes the clause to the egraph, assuming env maps all free variables to idxs *)
  Definition exec_clause (env : idx_map idx) (c : atom) : ST _ :=
    (* assume: all idxs are keys in env *)
    let args_vals := map (fun x => unwrap_with_default (H:=idx_zero) (map.get env x)) c.(atom_args) in
    let out_val := unwrap_with_default (H:=idx_zero) (map.get env c.(atom_ret)) in
    @!let args_vals' <- list_Mmap find args_vals in
      let out_val' <- find out_val in
      let i <- hash_node_out (Build_atom c.(atom_fn) args_vals' out_val') in
      (* will be a noop if hash_node_out allocates a fresh singleton
         TODO: this union is suspicious
       *)
      (union i out_val').
   
  
  Definition exec_write r assignment : ST unit :=
    (* Note: the preallocation method here will do extra allocations
       if the nodes are already in the egraph.
       TODO: (partial?) solution:
       gc allocated idxs in the union  if they have no parents?
     *)
    @! let env <- allocate_existential_vars r.(write_vars)
                  (map.of_list (combine r.(query_vars) assignment)) in
      let _ <- list_Miter (exec_clause env) r.(write_clauses) in      
      (list_Miter (fun '(x,y) =>
                     (* assume: all x,y are keys in env *)
                     let xv := unwrap_with_default (H:=idx_zero) (map.get env x) in
                     let yv := unwrap_with_default (H:=idx_zero) (map.get env y) in
                     (union xv yv))
         r.(write_unifications)).

  (*TODO: avoid code duplication *)
  Definition exec_const r : ST unit :=
    (* Note: the preallocation method here will do extra allocations
       if the nodes are already in the egraph.
       TODO: (partial?) solution:
       gc allocated idxs in the union  if they have no parents?
     *)
    @! let env <- allocate_existential_vars r.(const_vars) map.empty in
      let _ <- list_Miter (exec_clause env) r.(const_clauses) in      
      (list_Miter (fun '(x,y) =>
                     (* assume: all x,y are keys in env *)
                     let xv := unwrap_with_default (H:=idx_zero) (map.get env x) in
                     let yv := unwrap_with_default (H:=idx_zero) (map.get env y) in
                     (union xv yv))
         r.(const_unifications)).

  Definition process_const_rules (rs : rule_set) : ST unit :=
    list_Miter exec_const rs.(compiled_const_rules).

  
  Fixpoint insert (acc : list (option idx)) n x : option _ :=
    match n,acc with
    | 0, [] => Some [Some x]
    | 0, None::acc' => Some ((Some x)::acc')
    | 0, (Some y)::acc' => if eqb x y then Some acc else None
    | S n, [] => option_map (cons None) (insert [] n x)
    | S n, my::acc' => option_map (cons my) (insert acc' n x)
    end.

  
  Fixpoint match_clause' cargs cv args v acc : option _ :=
    match cargs, args with
    | [], [] => insert acc cv v
    | x::cargs', y::args' => Mbind (match_clause' cargs' cv args' v) (insert acc x y)
    | _, _ => None (*shouldn't happen *)
    end.

  
  (*
    Returns `Some assignment` iff (cargs,cv)[/assignment/] = (args,v)
    where assignment has domain [0..max(cargs,cv)].
    Note that if it exists, the assignment is unique.

    TODO: there are definitely opportunities to speed up this function and its helpers

    Observation: a typical atom has 0-5 args.
    A (packed) list is probably faster than a ptree map.

    Note: will return None if not all consecutive cargs/cv nats have been instantiated
   *)
  Definition match_clause '(cargs, cv) args v : option _ :=
    Mbind option_all (match_clause' cargs cv args v []).
  
  (* build all the tries for a given symbol at once
     TODO: likely bug returning leaf in some cases
   *)
  Definition build_tries_for_symbol
    (current_epoch : idx)
    (q_clauses : idx_map (list nat * nat))
    (tbl : idx_trie db_entry)
    : idx_map (idx_trie unit * idx_trie unit) (* full * frontier *)
    :=    
    let upd_trie_pair (args : list idx) '(Build_db_entry epoch v a) '(full, frontier) clause :=
      match match_clause clause args v with
      | Some assignment =>
          (* TODO: possible issue w/ tuple ordering
             TODO: test match_clause
           *)
          let full' : idx_trie unit := map.put full assignment tt in
          if eqb epoch current_epoch
          then (full', map.put frontier assignment tt)
          else (full', frontier)
      | None => (full, frontier)
      end          
    in  
    map.fold (fun tries args vp => map_intersect (upd_trie_pair args vp) tries q_clauses)
      (map_map (fun _ => (map.empty, map.empty : idx_trie unit)) q_clauses) tbl.

  Definition build_tries (q : rule_set) : ST (symbol_map (idx_map (idx_trie unit * idx_trie unit))) :=
    fun i => (map_intersect (build_tries_for_symbol i.(epoch)) q.(query_clauses) i.(db), i).

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} `{WithDefault B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).
  Arguments spaced_list_intersect {B}%type_scope {_} merge%function_scope _.
                                                 
  Definition intersection_keys (tries : ne_list (idx_trie unit * list bool)) : list _ :=
    map.keys (spaced_list_intersect (fun _ _ => tt) tries).

  (* assumes `sublist cvs qvs` *)
  Fixpoint variable_flags (qvs cvs : list idx) :=
    match qvs, cvs with
    | [], _ (*assume cvs empty *) => []
    | qx::qvs', [] => false::(variable_flags qvs' [])
    | qx::qvs', cx::cvs' =>
        if eqb qx cx
        then true::(variable_flags qvs' cvs')
        else false::(variable_flags qvs' cvs)
    end.

  Definition trie_of_clause
    (query_vars : list idx)
    (* each trie pair is (total, frontier) *)
    (db_tries : symbol_map (idx_map (idx_trie unit * idx_trie unit)))
    (frontier_n : idx)
    '(Build_erule_query_ptr f n clause_vars) : idx_trie unit * list bool :=
    let flags := variable_flags query_vars clause_vars in
    (* If f is not in db_tries, it means the DB contains no matching nodes *)
    match map.get db_tries f with
    | Some trie_list =>
        let (total,frontier) := unwrap_with_default (map.get trie_list n) in
        let inner_trie := if eqb (n : idx) frontier_n then frontier else total in
        (inner_trie, flags)
    | None => (map.empty, flags)
    end.
  
  Definition process_erule'
    (* each trie pair is (total, frontier) *)
    (db_tries : symbol_map (idx_map (idx_trie unit * idx_trie unit)))
    (r : erule) (frontier_n : idx) : ST unit :=
    let tries : ne_list _ :=
      ne_map (trie_of_clause r.(query_vars) db_tries frontier_n)
        r.(query_clause_ptrs) in
    let assignments : list _ := (intersection_keys tries) in
    list_Miter (M:=ST) (exec_write r) assignments.

  (*TODO: avoid using this*)
  Fixpoint idx_of_nat n :=
    match n with
    | 0 => idx_zero
    | S n => idx_succ (idx_of_nat n)
    end.
  
  Definition process_erule db_tries r : ST unit :=
    (* TODO: don't construct the list of nats/idxs, just iterate directly *)
    list_Miter (fun n => process_erule' db_tries r (idx_of_nat n))
      (seq 0 (List.length (uncurry cons r.(query_clause_ptrs)))).

  (* TODO: return the new epoch?  *)
  Definition increment_epoch : ST unit :=
    fun '(Build_instance db equiv parents epoch worklist analyses) =>
      (tt,Build_instance db equiv parents (idx_succ epoch) worklist analyses).
  
  Definition pull_worklist : ST (list _) :=
    fun d => (d.(worklist),
               Build_instance d.(db) d.(equiv) d.(parents)
                              d.(epoch) [] d.(analyses)).

  (*
  (*optional addition: return value
    NOTE: removes only from data, not parents or frontier.
   *)
  Definition remove_node f args : ST unit :=
    fun i =>
      let d' := map_update_if_exists i.(db) f (fun tbl => map.remove tbl args) in
      (tt, Build_instance d' i.(equiv) i.(parents) i.(epoch) i.(worklist)).

  (* Note: should only be called with nodes not in the egraph! *)
  Definition put_node a : ST unit :=
    fun i =>
      let d' := map_update i.(db) a.(atom_fn)
                (fun tbl => map.put tbl a.(atom_args) (i.(epoch),a.(atom_ret))) in
      (tt, Build_instance d' i.(equiv) i.(parents) i.(epoch) i.(worklist)).
  *)

  (*
    Returns a as a convenience
    NOTE: removes only from data, not parents
   *)
  Definition update_node' a old_args out_a : ST atom :=
    fun i =>
      let tbl_update tbl :=
        match map.get tbl old_args with
        | Some entry =>
            (*TODO: can be done in 2 map traversals, not 3*)
            map.put (map.remove tbl old_args)
              a.(atom_args)
                  (Build_db_entry i.(epoch) a.(atom_ret) out_a)
        | None => 
            map.put tbl
              a.(atom_args)
                  (Build_db_entry i.(epoch) a.(atom_ret) out_a)
        end
      in
      let d' := map_update i.(db) a.(atom_fn) tbl_update in
      (a, Build_instance d' i.(equiv) i.(parents) i.(epoch) i.(worklist) i.(analyses)).

  Definition update_node a old_args : ST atom :=
    @! let arg_as <- get_analyses a.(atom_args) in
      let out_a := analyze a arg_as in
      let _ <- update_analyses a.(atom_ret) out_a in
      (update_node' a old_args out_a).

  Definition get_parents x : ST (list atom) :=
    fun s =>
      (* assume x exists *)
      (unwrap_with_default (map.get s.(parents) x), s).
  
  Definition set_parents x ps : ST unit :=
    fun d =>
      let p' := map.put d.(parents) x ps in
      (tt, Build_instance d.(db) d.(equiv) p' d.(epoch) d.(worklist)
      d.(analyses)).
  
  Definition remove_parents x : ST unit :=
    fun d =>
      let p' := map.remove d.(parents) x in
      (tt, Build_instance d.(db) d.(equiv) p' d.(epoch) d.(worklist)
      d.(analyses)).

  
  Fixpoint add_parent ps p : ST (list atom) :=
    match ps with
    | [] => Mret [p]
    | (Build_atom f' args' o' as p')::ps' =>
        let (f, args, o) := p in
        if (eqb f f') && (eqb args args')
        then @! let om <- union p.(atom_ret) p'.(atom_ret) in
               ret (Build_atom f args om)::ps'
        else @! let ps'' <- add_parent ps' p in ret p'::ps''
    end.

  (*TODO: move to Monad *)
  Definition pair_Mmap {A A' B B' M} `{Monad M}
    (f : A -> M A') (g : B -> M B') (p: A * B) : M (A' * B')%type :=
    @! let x <- f (fst p) in
      let y <- g (snd p) in
      ret (x,y).
  
  Definition repair '(x_old,x_canonical) : ST unit :=
    let repair_each a : ST atom :=
      @!let {ST} a' <- canonicalize a in
        (* Don't update if it's already canonical,
           to avoid falsely bumping the epoch
         *)
        if eqb a a'
        then ret {ST} a
        else (update_node a' a.(atom_args))
    in
    (* TODO: a one-op remove-and-return would be useful*)
    @! let old_ps <- get_parents x_old in
      let _ <- remove_parents x_old in
      let ps1 <- list_Mmap repair_each old_ps in
      let canon_ps <- get_parents x_canonical in
      let ps2 <- list_Mfoldl add_parent ps1 canon_ps in
      (set_parents x_canonical ps2).

  Fixpoint rebuild fuel : ST unit :=
    match fuel with
    | 0 => Mret tt
    | S fuel =>
        @! let todo <- pull_worklist in
          if todo : list (idx * idx) then ret tt
          else
            (* we canonicalize the canonical node, but not the old one
               Since this entry is responsible for adding the old parents
               to whatever the current canonical representative is
             *)
            let todo <- list_Mmap (pair_Mmap Mret find) todo in
            let todo := dedup (eqb (A:=_)) todo in
            let _ <- list_Miter repair todo in
            (rebuild fuel)
    end.

  Definition run1iter (rs : rule_set) rebuild_fuel : ST unit :=
    @! let tries <- build_tries rs in
      (* increment the epoch so that all added nodes are in the next frontier.
           TODO: check for off-by-one errors
       *)
      let _ <- increment_epoch in
      let _ <- list_Miter (process_erule tries) rs.(compiled_rules) in
      (* TODO: compute an adequate upper bound for fuel *)
      (rebuild rebuild_fuel).

  Fixpoint saturate_until' rs (P : ST bool) fuel rebuild_fuel : ST bool :=
    match fuel with
    | 0 => Mret false
    | S fuel =>
        @! let {ST} done <- P in
          if (done : bool) then ret true
          else (Mseq (run1iter rs rebuild_fuel)
                 (saturate_until' rs P fuel rebuild_fuel))
    end.

  (* run the const rules once before the saturation loop *)
  Definition saturate_until rs (P : ST bool) fuel : ST bool :=
    Mseq (process_const_rules rs)
      (*(Mseq increment_epoch*)
         (* TODO: is there a need to rebuild after const rules?
            In general: yes, for now.
            With optimal const rules: no
          *)
            (Mseq (rebuild 1000)
               (saturate_until' rs P fuel 1000)).
    
  
  Definition are_unified (x1 x2 : idx) : state instance bool :=
    @!let x1' <- find x1 in
      let x2' <- find x2 in
      ret eqb x1' x2'.

  Definition empty_egraph : instance :=
    Build_instance map.empty (empty _ _ _ idx_zero)
      map.empty idx_zero [] map.empty.


  
  Definition trie_of_clause'
    (query_vars : list idx)
    (* each trie pair is (total, frontier) *)
    (db_tries : symbol_map (idx_map (idx_trie unit * idx_trie unit)))
    '(Build_erule_query_ptr f n clause_vars) : idx_trie unit * list bool :=
    let flags := variable_flags query_vars clause_vars in
    match map.get db_tries f with
    | Some trie_list =>
        (* never use the frontier*)
        let (total,_) := unwrap_with_default (map.get trie_list n) in
        let flags := variable_flags query_vars clause_vars in
        (total, flags)
    | None => (map.empty, flags)
    end.
  (*TODO: name clash; rename QueryOpt?
    Runs the query side of the rules in a rule set, returning the computed assignments

    TODO: different interface?
   *)
  Definition run_query (rs : rule_set) n : ST _ :=
    match nth_error rs.(compiled_rules) n with
    | Some r =>
        @! let db_tries <- build_tries rs in
          (*TODO: frontier_n a hack*)
          let tries : ne_list _ := ne_map (trie_of_clause' r.(query_vars) db_tries)
                                     r.(query_clause_ptrs) in
          ret (Some (intersection_keys tries))
    | None => Mret None
    end.

  (* TODO: name clash. TODO: keep def? diagnostic only
     
   *)
  Definition run_query' (rs : rule_set) n : ST _ :=
    match nth_error rs.(compiled_rules) n with
    | Some r =>
        @! let db_tries <- build_tries rs in
          (*TODO: frontier_n a hack*)
          let tries : ne_list _ := ne_map (trie_of_clause' r.(query_vars) db_tries)
                                     r.(query_clause_ptrs) in
          ret (Some tries)
    | None => Mret None
    end.
               
  (*TODO:
    - fill in Context-hypothesized ops
    - prove properties of above
    - implement eqsatlog on top of this (relationship to terms)
   *)

  (*
  (* Properties *)

  
  Lemma ntree_intersect_length A B (merge : A -> B -> B) `{WithDefault B} t1 (t2: ntree B)
    : ntree_len_eq t1 t2 ->
      ntree_len_eq t1 (ntree_intersect_unchecked merge t1 t2).
  Proof.
    intro Hlen.
    unfold ntree_intersect_unchecked.
    unshelve erewrite compute_unchecked_eq; eauto.
    unfold ntree_intersect, ntree_len_eq, zip in *.
    basic_goal_prep;
      basic_utils_crush.
    rewrite combine_length.
    Lia.lia.
  Qed.

  Lemma ntree_len_eq_trans A B C (t1 : ntree A) (t12 : ntree (m:=idx_map) B) (t2 : ntree C)
    : ntree_len_eq t1 t12 ->
      ntree_len_eq t12 t2 ->
      ntree_len_eq t1 t2.
  Proof.
    unfold ntree_len_eq; basic_utils_crush.
    congruence.
  Qed.
  
  Lemma fold_ntree_intersect_length A B (merge : A -> B -> B) `{WithDefault B} l (t : ntree B)
    : all (fun t' : ntree A => ntree_len_eq t t') l ->
      ntree_len_eq t (fold_right (ntree_intersect_unchecked merge) t l).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    1: unfold ntree_len_eq; basic_utils_crush.
    eapply ntree_len_eq_trans.
    2:eapply ntree_intersect_length.
    all: eauto.
    unfold ntree_len_eq in *; basic_utils_crush.
    congruence.
  Qed.
    

  Lemma fold_ntree_intersect A B (merge : A -> B -> B) `{WithDefault B} l (t : ntree B) k
    : all (fun t' => ntree_len_eq t t') l ->
      let merge' (ma : option A) (mb : option B) :=
        @! let a <- ma in
          let b <- mb in
          ret merge a b
      in
      ntree_get (fold_right (ntree_intersect_unchecked merge) t l) k
      = fold_right merge' (ntree_get t k) (map (fun t => ntree_get t k) l).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite ntree_intersect_unchecked_spec; eauto.
    2:{
      revert H3 H4; clear.
      intros.
      eapply ntree_len_eq_trans.
      2: eapply fold_ntree_intersect_length; eauto.
      unfold ntree_len_eq in *;
        basic_utils_crush;
        congruence.
    }
    case_match; eauto.
    rewrite H2.
    reflexivity.
  Qed.

  Definition fully_constrained {A} (t : ntree (m:=idx_map) A) : Prop :=
    Is_true (forallb id t.(constrained_indices)).

  (*TODO: move to coqutil maybe?*)
  Lemma fold_right_flatmap X Y f (acc : list Y) (l : list X)
    : (forall x acc, f x acc = f x [] ++ acc) ->
      let f' x := f x [] in
      fold_right f acc l = flat_map f' l ++ acc.
  Proof.
    intro Hf.
    intro f'; subst f'.
    revert acc; induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite Hf.
    rewrite IHl.
    rewrite app_assoc.
    reflexivity.
  Qed.


  (*TODO: move to MapTreeN.v?*)
  Lemma ntree_fold'_monotone A len acc0 keystack n
    : MapTreeN.ntree_fold' A
    (fun (acc1 : list (list idx)) (k0 : list idx) (_ : A) => k0 :: acc1) len acc0
    keystack n =
        MapTreeN.ntree_fold' A
    (fun (acc1 : list (list idx)) (k0 : list idx) (_ : A) => k0 :: acc1) len []
    keystack n ++ acc0.
  Proof.
    revert acc0 keystack n.
    induction len;
      basic_goal_prep;
      basic_utils_crush.
    cbn.
    rewrite !Properties.map.fold_to_tuples_fold.
    
    unfold MapTreeN.ntree in *.
    generalize (map.tuples n) as l.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite IHlen.
    rewrite IHl.
    rewrite app_assoc.
    rewrite <- IHlen.
    reflexivity.
  Qed.
  
(* *)
  Lemma ntree_fold'_keys A (k:list idx) len t acc keystack
    : In k (MapTreeN.ntree_fold' A (fun acc k _ => k::acc) len acc keystack t)
      <-> (exists k_suff, k = rev keystack ++ k_suff
                          /\ Is_Some (MapTreeN.ntree_get t k_suff)
                          /\ List.length k_suff = len)
          \/ In k acc.
  Proof.
    revert t acc keystack.
    induction len;
      basic_goal_prep.
    {
      split;
      basic_goal_prep;
        basic_utils_crush.
      {
        left; exists [];
          basic_goal_prep;
          basic_utils_crush.
      }
      {
        destruct x;
          basic_goal_prep;
          basic_utils_crush.
      }
    }
    {
      match goal with
        |- context [(map.fold ?f ?acc ?m)] =>
          pose proof (Properties.map.fold_to_list f acc m)
      end.
      break.
      (*assert (all_fresh x) as Hxfr by admit.*)
      unfold MapTreeN.ntree in *.
      rewrite H1.
      clear H1.
      rewrite fold_right_flatmap.
      2:{
        basic_goal_prep.
        eapply ntree_fold'_monotone.
      }
      split;
        basic_goal_prep;
        basic_utils_crush.
      {
        rewrite in_flat_map in *.
        basic_goal_prep;
          basic_utils_crush.
        eapply IHlen in H3.
        basic_goal_prep;
          basic_utils_crush.
        left.
        exists (i::x0).
        basic_goal_prep;
          basic_utils_crush.
        { rewrite <- app_assoc; eauto. }
        {
          rewrite H2 in H1.
          rewrite H1.
          eauto.
        }
      }
      {
        rewrite in_flat_map in *.
        revert H3; case_match;
        basic_goal_prep;
          basic_utils_crush.
        revert H3; case_match;
          basic_goal_prep;
          basic_utils_crush.
        left.
        exists (i,n).
        basic_goal_prep;
          basic_utils_crush.
        {
          rewrite H2.
          congruence.
        }
        {
          eapply IHlen.
          basic_goal_prep;
            basic_utils_crush.
          exists H1.
          basic_goal_prep;
            basic_utils_crush.
          rewrite <- app_assoc; eauto.
        }
      }
    }
  Qed.

  Lemma MapTreeN_ntree_fold_keys A (k:list idx) len (t : MapTreeN.ntree idx A len)
    : In k (MapTreeN.ntree_fold A (fun acc k _ => k::acc) len t [])
      <-> Is_Some (MapTreeN.ntree_get t k) /\ List.length k = len.
  Proof.
    rewrite (ntree_fold'_keys _ k len t [] []).
    intuition (basic_goal_prep;
               basic_utils_crush).
  Qed.

  (*TODO: move to lists*)
  Lemma all_true_filter (B : Type) (f : B -> bool) (l : list B)
    : all (fun x => Is_true (f x)) l -> filter f l = l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    destruct (f a);
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma all_true_filter_key (B : Type) (k : list B) l
    : List.length k = List.length l ->
      all (fun x => Is_true x) l -> filter_key k l = k.
  Proof.
    revert k;
      induction l;
      destruct k;
      basic_goal_prep;
      basic_utils_crush.
    destruct a;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma ntree_fold_keys A (k:list idx) t
    : fully_constrained t ->
      In k (ntree_fold A (fun acc k _ => k::acc) t [])
      <-> Is_Some (ntree_get t k) /\ List.length k = List.length t.(constrained_indices).
  Proof.
    unfold ntree_get,  fully_constrained, ntree_fold.
    destruct t; cbn [SpacedMapTreeN.inner_tree SpacedMapTreeN.constrained_indices].
    autorewrite with bool utils.
    intro Hall.
    revert inner_tree.
    rewrite all_true_filter with (f:=id) (l:=constrained_indices); eauto.
    intro.
    rewrite MapTreeN_ntree_fold_keys.
    intuition eauto;
      rewrite all_true_filter_key in *; eauto.
  Qed.

  (*TODO: move to Lists*)
  Lemma fold_right_invariant A (P : A -> Prop) f acc l
    : P acc -> all P l -> (forall a b, P a -> P b -> P (f a b)) -> P (fold_right f acc l).
  Proof.
    intros Hacc Hl Hf; revert Hl;
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma all_map A B P (f : A -> B) l
    : all P (map f l) <-> all (fun x => P (f x)) l.
  Proof.
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma all_implies A (P Q : A -> Prop) l
    : (forall x,  P x -> Q x) -> all P l -> all Q l.
  Proof.
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    

  Lemma fold_intersect_indices t1 tries
    : all (fun t' : ntree unit => ntree_len_eq t1 t') tries ->
      constrained_indices (fold_right (ntree_intersect_unchecked (fun _ _ : unit => tt)) t1 tries)
      = fold_right (List.zip orb) (constrained_indices t1) (map constrained_indices tries).
  Proof.    
    unfold ntree_intersect_unchecked, ntree_len_eq.
    induction tries;
      basic_goal_prep;
      eauto.
    
    unshelve erewrite compute_unchecked_eq.
    {
      autorewrite with bool utils in *.
      break.
      rewrite IHtries; eauto.
      clear IHtries.
      eapply fold_right_invariant; eauto.
      2:{
        unfold zip.
        basic_goal_prep;
          basic_utils_crush.
        rewrite combine_length; Lia.lia.
      }
      rewrite all_map.
      eapply all_implies; eauto.
      basic_goal_prep;
        basic_utils_crush.
      congruence.
    }      
    destruct t1, a;
      basic_goal_prep;
    basic_utils_crush.
  Qed.
  
  Lemma generic_join'_sound t1 tries assignment
    : all (fun t' : ntree unit => ntree_len_eq t1 t') tries ->
      all Is_true (fold_right (zip orb) (constrained_indices t1) (map constrained_indices tries)) ->
      In assignment (generic_join' t1 tries) ->
      all (fun t => Is_Some (ntree_get t assignment)) (t1::tries).
  Proof.
    unfold generic_join'.
    intros Hlen Hconstrained.
    rewrite ntree_fold_keys.
    2:{
      unfold fully_constrained.
      basic_utils_crush.
      rewrite fold_intersect_indices; eauto.
    }
    clear Hconstrained.
    rewrite fold_ntree_intersect; eauto.
    intros; break.
    clear H2.
    generalize dependent tries.
    induction tries;
      basic_goal_prep.
    1:basic_utils_crush.
    revert H1; repeat (case_match; cbn); intuition eauto.
  Qed.

  Lemma build_trie_length nodes fvs a t
    : Some t = build_trie nodes fvs a ->
      List.length t.(constrained_indices) = List.length fvs.
  Proof.
    unfold build_trie.
    cbn.
    repeat (case_match; cbn);
      basic_goal_prep;
      basic_utils_crush.
    cbn.
    unfold c_is_of_vars, var_indices.
    basic_utils_crush.
  Qed.

  
  Lemma list_Mmap_invariant A B (f : A -> option B) (P : B -> Prop) l l'
    : (forall x y, Some y = f x -> P y) -> Some l' = list_Mmap f l -> all P l'.
  Proof.
    intro Hf.
    revert l';
      induction l;
      repeat (case_match; cbn);
      basic_goal_prep;
      basic_utils_crush.
    revert H1;
      repeat (case_match; cbn);
      basic_goal_prep;
      basic_utils_crush.
    cbn; intuition eauto.
  Qed.

  Lemma build_tries_length nodes q l t1
    : Some (t1::l) = build_tries nodes q ->
      all (fun t' : ntree unit => ntree_len_eq t1 t') l.
  Proof.
    unfold build_tries; destruct q;
      cbn.
    intro HM.
    eapply list_Mmap_invariant in HM.
    { cbn in *; intuition eauto. }
    {
      unfold ntree_len_eq.
      basic_goal_prep;
        basic_utils_crush.
      destruct clauses0; cbn in HM; try congruence.
      revert HM; repeat case_match;
      basic_goal_prep;
        basic_utils_crush.
      cbn.
      unfold c_is_of_vars, var_indices.
      basic_utils_crush.
      erewrite build_trie_length; eauto.
    }
  Qed.

  Definition in_node_map (n : node_map) a :=
    match map.get n a.(atom_fn) with
    | Some t => In (a.(atom_args),a.(atom_ret)) t
    | None => False
    end.

  
  Context `{WithDefault idx}.

  (* Note: defaults don't protect against out-of-scope idxs *)
  Definition atom_subst (sub : named_list idx idx) (a : atom) : atom :=
    let (f, args, r) := a in
    Build_atom f
      (map (named_list_lookup default sub) args)
      (named_list_lookup default sub r).

  Definition matches_pat mp (x:idx) :=
    match mp with Some x' => x = x' | None => True end.

  Definition table_compatible (t : table) (sub : named_list idx idx) args rv :=
    let args_pat := map (named_list_lookup_err sub) args in
    let r_pat := named_list_lookup_err sub rv in
    all (fun '(k,r) => all2 matches_pat args_pat k /\ matches_pat r_pat r) t.

  (* TODO: move to Lists.v*)
  Lemma named_list_lookup_from_err (i0 : idx) (sub' : named_list idx idx) r
    : Some i0 = named_list_lookup_err sub' r ->
      named_list_lookup default sub' r = i0.
  Proof using Eqb_idx_ok.
    induction sub';
      basic_goal_prep; try congruence.
    eqb_case r i; try congruence; eauto.
  Qed.
  
  Lemma table_compatible_lookup (t : ne_table) sub' args r
    :  table_compatible t sub' args r ->
       In r (map fst sub') ->
       incl args (map fst sub') ->
       In (map (named_list_lookup default sub') args, named_list_lookup default sub' r) t.
  Proof.
    clear idx_leb.
    unfold table_compatible, matches_pat.
    destruct t as [[x i] t].
    induction t;
      basic_goal_prep;
      basic_utils_crush.
    2:{
      revert H7;
      case_match;
      basic_goal_prep;
      subst;
      basic_utils_crush.
      { erewrite named_list_lookup_from_err; eauto. }
      { exfalso.
        eapply pair_fst_in_exists in H3; break.
        eapply named_list_lookup_none in HeqH5; eauto.
      }
    }
    {
      revert x H2 H4.
      clear H7 H6 H3 r.
      induction args;
        destruct x;
        repeat case_match;
        basic_goal_prep;
        subst;
        basic_utils_crush.
      revert H3;
      case_match;
      basic_goal_prep;
      subst;
      basic_utils_crush.
      { erewrite named_list_lookup_from_err; eauto. }
      { exfalso.
        eapply pair_fst_in_exists in H2; break.
        eapply named_list_lookup_none in HeqH3; eauto.
      }
    }
  Qed.


  (* TODO: move to namedlist *)
  Lemma lookup_app_notin {A} (x:idx) (l1 l2 : named_list idx A) 
    : fresh x l2 ->
      named_list_lookup_err (l1++l2) x
      = named_list_lookup_err l1 x.
  Proof.
    clear idx_leb.
    induction l1;
      basic_goal_prep;
      basic_utils_crush.
    {
      symmetry.
      rewrite named_list_lookup_none_iff.
      eauto.
    }
    {
      eqb_case x i; eauto.
    }
  Qed.
  
  Local Lemma map_lookup_app_notin {A} l (l1 l2 : named_list idx A) 
    : all (fun x => fresh x l2) l ->
      map (named_list_lookup_err (l1++l2)) l
      = map (named_list_lookup_err l1) l.
  Proof.
    clear idx_leb.
    induction l;
      cbn; eauto.
    intuition (f_equal; eauto using lookup_app_notin).
  Qed.

  Lemma table_compatible_snoc_unconstrained t sub' a args r i
    : ~ In a args ->
      a <> r ->
      table_compatible t sub' args r ->
      table_compatible t (sub' ++ [(a, i)]) args r.
  Proof.
    unfold table_compatible.
    intros Hargs Hr.
    eapply all_implies.
    basic_goal_prep;
      subst;
      basic_utils_crush.
    2:{
      clear H2.
      unfold matches_pat in *.
      rewrite lookup_app_notin; eauto.
      cbv; intuition eauto.
    }
    {
      clear H3.
      unfold matches_pat in *.
      rewrite map_lookup_app_notin; eauto.
      {
        unfold fresh.
        cbn.
        revert Hargs; clear;
          induction args;
          basic_goal_prep;
          basic_utils_crush.
      }
    }
  Qed.

  
  Lemma empty_indices_of a l
    : [] = indices_of (var_arg a) (map var_arg l) ->
      ~ In a l.
  Proof.
    unfold indices_of.
    generalize 0.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    cbn in *.
    eqb_case a a0;
      try congruence.
    eapply IHl; eauto.
  Qed.
  
  Lemma build_trie'_sound (ne_tab : ne_table) assignment args r fvs sub'
    : List.length fvs = List.length assignment ->
      table_compatible ne_tab sub' args r ->
      let v_is := var_indices fvs (map var_arg (args ++ [r])) in
      Is_Some (MapTreeN.ntree_get (build_trie' ne_tab v_is)
                 (filter_key assignment (c_is_of_vars v_is))) ->
      In r (map fst sub' ++ fvs) ->
      incl args (map fst sub' ++ fvs) ->
      let sub := named_list_lookup default (sub' ++ combine fvs assignment) in
      In (map sub args, sub r) ne_tab.
  Proof.
    revert assignment sub'.
    induction fvs;
      destruct assignment;
      try (basic_goal_prep; congruence).
    {
      intros.
      eapply table_compatible_lookup; 
        basic_goal_prep;
        basic_utils_crush.
    }
    {
      intros.
      subst v_is sub.
      cbn [combine] in *.

      
      revert H4; cbn.
      case_match.
      {
        (*unconstrained case *)
        replace (map fst sub' ++ a :: fvs)
          with (map fst (sub' ++ [(a,i)]) ++ fvs) in *.
        2:{
          clear.
          rewrite map_app.
          basic_goal_prep;
            basic_utils_crush.
          rewrite <- app_assoc.
          eauto.
        }
        replace (sub' ++ (a,i) :: combine fvs assignment)
          with ((sub' ++ [(a,i)]) ++ combine fvs assignment) in *.
        2:{
          rewrite <- app_assoc.
          eauto.
        }
        intro Hsome.
        eapply IHfvs; eauto.
        {
          eapply empty_indices_of in HeqH4.
          eapply table_compatible_snoc_unconstrained; eauto;
            basic_utils_crush.
        }
      }
      {
        (*
        Design questions:
          1. can I assume some sort on the table?
             - needs to be per-query, but does it have to be per recursive branch?
          2. what data structure does the table need to have?                                  - is there something that is more amenable to quick lookup&insertion?
             - related: when/what lookups,insertions do I perform?
               for equalities: no lookups, but batched insertions
                               w/ potentially mergable results
               for type inference: lookups for every metametavariable/hole,
               alternately a recursive whole-term lookup
         *)
        (*
        TODO: properties of split_by;
        fold_left invariant;
        put sound
         *)
  Admitted.

  
  Definition atom_ws fvs (a:atom) :=
    In a.(atom_ret) fvs /\ incl a.(atom_args) fvs.

  (*TODO: move to Lists*)
  Lemma all2_map_l A B C (f : A -> B) (P : B -> C -> Prop) l1 l2
    : all2 P (map f l1) l2 <-> all2 (fun x y => P (f x) y) l1 l2.
  Proof.
    clear.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
    all:apply IHl1; eauto.
  Qed.

  Lemma all2_implies B C (P Q : B -> C -> Prop) l1 l2
    : (forall x y, P x y -> Q x y) -> all2 P l1 l2 -> all2 Q l1 l2.
  Proof.
    clear.
    intro Hpq.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma table_compatible_nil (t : table) args r
    : all (fun row => List.length args = List.length (fst row)) t ->
      table_compatible t [] args r.
  Proof.
    unfold table_compatible, matches_pat.
    cbn.
    eapply all_implies.
    {
      basic_goal_prep.
      intuition eauto.
      rewrite all2_map_l.
      revert args H2;
        induction l;
        destruct args;
        basic_goal_prep;
        basic_utils_crush.
    }
  Qed.    
  
  Lemma build_trie_sound t fvs c nodes assignment
    : atom_ws fvs c ->
      Some t = build_trie nodes fvs c ->
      Is_Some (ntree_get t assignment) ->
      in_node_map nodes (atom_subst (combine fvs assignment) c).
  Proof.
    unfold build_trie, atom_ws.
    destruct c.
    unfold in_node_map, ntree_get.
    cbn in *.    
    repeat case_match;
      try (cbv [default option_default]; congruence).
    intros; basic_utils_crush.
    eapply build_trie'_sound
      with (ne_tab:= (l, i, H2))
           (sub':=[]);
      eauto.
    { admit (*ntree get len lemma*). }
    {
      eapply table_compatible_nil.
      admit (*table arity wfness*). }
  Abort.    
    
  Lemma build_tries_sound l q nodes assignment
    : Some l = build_tries nodes q ->
      all2 (fun t c => Is_Some (ntree_get t assignment) ->
                       in_node_map nodes (atom_subst (combine (free_vars q) assignment) c))
        l q.(clauses).
  Proof.
    unfold build_tries.
    destruct q.
    cbn.

  Abort.
  
  (* Note: We don't need completeness for our purposes, but it should hold. *)
  Theorem generic_join_sound nodes q assignment
    : (*wf_query q -> (probably necessary) *)
    In assignment (generic_join nodes q) ->
      let sub := combine q.(free_vars) assignment in
      forall c, In c q.(clauses) ->
                in_node_map nodes (atom_subst sub c).
  Proof.
    unfold generic_join.
    repeat case_match.
    all: basic_utils_crush.
    eapply generic_join'_sound in H3.
    2:{ eapply build_tries_length; eauto. }
    2:{ admit (*TODO: add wf query assumption *). }
    revert HeqH2 H3.
    generalize (n::H2).
    clear n H2.
    intros.
    repeat case_match.
    (*TODO: use build_tries_sound*)
  Abort.
   *)
  
  (*
  TODO: disjunctive-normal-form queries.
  TODO: differential query generation to use the frontier.

  TODO: add DNF optimization to QueryOpt (best place?)
  expected pipeline will look something like:
  - accept a set of rules as term-term pairs
  - generate queries from LHSs
  - optimize each query individually to deduplicate clauses
  - generate delta-rules
  - consider (delta)-query set as a (tagged) disjunction
  - disjunction-optimize query set
    + choose variable orders such that there is maximal trie-sharing
      * note: deciding variable order might be faster before delta-rules,
              since maximality should be invariant under that transformation
      * any 2 deltas of the same rule will share exactly all but 2 of their clauses
      * note: some wiggle room; only need relative order to be sahred, not exact var position.
              e.g. if Q1(a,b,c,d) :- ... C1(a,c) and Q2(e,f,g,h) :- ... C1(f,g) they can share
    + build some sort of sharing/index structure for the clause trie graph;
      each clause will have its filter-list and then a view into the shared trie bank
  - build shared trie bank
  - build trie-referencing query set
  - compute the intersection for each query
  - apply matching RHS to each output, update egraph
  - bump frontier pointer
   *)

  (*
    DNF optimization requires solving a (slight generalization of) this problem:

    Consider a (finite) set X of identifiers and a (finite) set S of (finite) sequences from X.
    Find an ordering x1 < x2 on X that minimizes |S/~|
    where s1 ~ s2 iff there exists a bijection f : {e in s1} -> {e in s2}
    such that f(s1) = s2 and f is monotonic wrt <.

    Note: output is critical. optimization is run once per rule-set,
    so effectively offline
    Saturation has complexity >= O(I*D*|S/~|) where I is iterations until saturation
    and D is the size of the full database.


    simple, greedy heuristic:
    - rename rules to be disjointly named
    - choose a var order for each rule
    - choose a rule order, append var lists

    Given an order, can compute sharing polynomially:
    for each clause, unify w/ first other compatible clause
   *)
(*
  Definition build_queryset' (qs : list query) :=
    fst (fold (fun q '(qset,hc) =>
                 foreach cl in q.(clauses) in
                   let (s,cl') := norm_clause q in
                   let x <- hc_put cl' in
                   let _ <- qs_put x cl' in
                   ret (q.(free_vars),s)
                   
           )
           ((empty, []) : queryset * hashcons atom idx) qs).
  *)

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

End WithMap.

Arguments atom_fn {idx symbol}%type_scope a.
Arguments atom_args {idx symbol}%type_scope a.
Arguments atom_ret {idx symbol}%type_scope a.

Arguments db {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope i.
Arguments equiv {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope i.
Arguments parents {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope i.
Arguments epoch {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope i.
Arguments worklist {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope i.

Existing Class analysis.

#[export] Instance unit_analysis {idx symbol} : analysis idx symbol unit:=
  {
    analyze _ _ := tt;
    analysis_meet _ _ := tt;
  }.

Arguments union {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope {H} v v1 _.
Arguments hash_node {idx}%type_scope {Eqb_idx} idx_succ%function_scope {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope {H} f args%list_scope _.
Arguments Build_atom {idx symbol}%type_scope atom_fn 
  atom_args%list_scope atom_ret.


  
Arguments Build_rule_set {idx symbol}%type_scope {symbol_map idx_map}%function_scope 
  query_clauses compiled_rules%list_scope.


Arguments rebuild {idx}%type_scope {Eqb_idx} {symbol}%type_scope 
  {Eqb_symbol} {symbol_map idx_map idx_trie}%function_scope 
  {analysis_result}%type_scope {H}
  fuel%nat_scope _.


Arguments saturate_until' {idx}%type_scope {Eqb_idx} idx_succ%function_scope 
  idx_zero {symbol}%type_scope {Eqb_symbol} {symbol_map}%function_scope {symbol_map_plus}
  {idx_map}%function_scope {idx_map_plus} {idx_trie}%function_scope
  {analysis_result}%type_scope {H}
  spaced_list_intersect%function_scope 
  rs P fuel%nat_scope _.

Arguments saturate_until {idx}%type_scope {Eqb_idx} idx_succ%function_scope 
  idx_zero {symbol}%type_scope {Eqb_symbol} {symbol_map}%function_scope {symbol_map_plus}
  {idx_map}%function_scope {idx_map_plus} {idx_trie}%function_scope
  {analysis_result}%type_scope {H}
  spaced_list_intersect%function_scope 
  rs P fuel%nat_scope _.

Arguments are_unified {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope x1 x2 _.


Arguments empty_egraph {idx}%type_scope idx_zero {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope.


Arguments canonicalize {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope a _.
Arguments find {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
   {analysis_result}%type_scope a _.

Module PositiveIdx.

  (*TODO: move to Eqb or sim. locaion *)
  #[export] Instance positive_Eqb : Eqb positive := Pos.eqb.

  (* TODO: update test example
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
        Build_atom _ _ 10 [4;5] 6;
        Build_atom _ _ 20 [2] 3;
        Build_atom _ _ 10 [1;1;2] 3
      ].
  Time Compute (generic_join_pos db1 query1).
  
  Example query2 : query :=
    Build_query _ _ [1;2;3]
      [
        Build_atom _ _ 10 [1;2;2] 3
      ].

  Compute (generic_join_pos db1 query2).
   *)
End PositiveIdx.

(*
Eval cbv [UnionFind.union Mbind Mret] in UnionFind.union.

UnionFind.union =
fun (idx : Type) (Eqb_idx : Eqb idx) (idx_map : map.map idx idx) (rank_map : map.map idx nat)
  (h : union_find idx idx_map rank_map) (x y : idx) =>
@!
let (h0, cx) <- UnionFind.find idx Eqb_idx idx_map rank_map h x
in (Mbind
      (fun '(h1, cy) =>
       @!
       if eqb cx cy then ret (h1, cx)
       else (Mbind
               (fun rx : nat =>
                @!
                let ry <- map.get (rank idx idx_map rank_map h1) cy
                in match ry ?= rx with
                   | Eq =>
                       @!
                       ret ({|
                              rank := map.put (rank idx idx_map rank_map h1) cx (Init.Nat.succ rx);
                              parent := map.put (parent idx idx_map rank_map h1) cy cx;
                              max_rank :=
                                Init.Nat.max (max_rank idx idx_map rank_map h1) (Init.Nat.succ rx);
                              next := next idx idx_map rank_map h1
                            |}, cx)
                   | Lt =>
                       @!
                       ret ({|
                              rank := rank idx idx_map rank_map h1;
                              parent := map.put (parent idx idx_map rank_map h1) cy cx;
                              max_rank := max_rank idx idx_map rank_map h1;
                              next := next idx idx_map rank_map h1
                            |}, cx)
                   | Gt =>
                       @!
                       ret ({|
                              rank := rank idx idx_map rank_map h1;
                              parent := map.put (parent idx idx_map rank_map h1) cx cy;
                              max_rank := max_rank idx idx_map rank_map h1;
                              next := next idx idx_map rank_map h1
                            |}, cy)
                   end) (map.get (rank idx idx_map rank_map h1) cx)))
      (UnionFind.find idx Eqb_idx idx_map rank_map h0 y))
*)
