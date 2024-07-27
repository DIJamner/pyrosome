Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind FunctionalDB Monad.
Import Monad.StateMonad.

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
      (idx_succ : idx -> idx).

  Notation log_upd := (log_upd idx symbol).
  Notation atom := (atom idx symbol).
  
  Record normalized_upd : Type :=
    Build_norm {
      lets : list (atom * idx (*ordered binders *));
      eqns : list (idx * idx) (* variables *);
      puts : list (atom * idx (*variables*));
    }.

  (*Note: could improve performance by reversing at the end,
    but the performance is negligible compared to running the query anyway.
   *)
  Definition push_let a x '(Build_norm l e p) : normalized_upd :=
    Build_norm (l++[(a,x)]) e p.
  
  Definition push_put a x '(Build_norm l e p) : normalized_upd :=
    (*order is irrelevant *)
    Build_norm l e ((a,x)::p).
  
  Definition push_eqn x y '(Build_norm l e p) : normalized_upd :=
    (*order is irrelevant *)
    Build_norm l ((x,y)::e) p.
  
  Definition push_eqns e' '(Build_norm l e p) : normalized_upd :=
    (*order is irrelevant *)
    Build_norm l (e++e') p.

  (*TODO: move to FunctionalDB*)
  Arguments unify {idx symbol}%type_scope _ _.
  Arguments put_row {idx symbol}%type_scope _ _.
  Arguments let_row {idx symbol}%type_scope _ _.

  (* Assumes no shadowing *)
  Definition normalize_upd l : normalized_upd -> normalized_upd :=
    match l with
    | unify i1 i2 => (push_eqn i1 i2)
    | put_row a i => (push_put a i)
    | let_row a x => (push_let a x)
    end.
  
  Definition normalize_upds l :=
    List.fold_left (fun f l => Basics.compose (normalize_upd l) f) l id
      (Build_norm [] [] []).

  Definition unnormalize_upds '(Build_norm l e p) : list log_upd :=
    let lk : list log_upd := List.map (fun '(a,x) => let_row a x) l in
    let ek : list log_upd := List.map (fun '(x,y) => unify x y) e in
    let pk : list log_upd := List.map (fun '(a,x) => put_row a x) p in
    lk ++ ek ++ pk.

  Fixpoint find_in_eqns' (x : idx) e acc :=
    match e with
    | [] => None
    | (y,z)::e' =>
        if eqb x y then Some (z,acc++e')
        else 
        if eqb x z then Some (y,acc++e')
        else find_in_eqns' x e' ((y,z)::acc)
    end.

  (*may reorder eqns*)
  Definition find_in_eqns x e := find_in_eqns' x e [].
  
  (*Note: could improve performance but the performance is negligible compared to running the query anyway.
   *)
  Fixpoint elim_new_unified_vars' l e : normalized_upd -> normalized_upd :=
    match l with
    | [] => push_eqns e
    | (a,x)::l' =>
        match find_in_eqns x e with
        | Some (y,e') =>
            Basics.compose (elim_new_unified_vars' l' e')
              (push_put a y)
        | None =>
            Basics.compose (elim_new_unified_vars' l' e)
              (push_let a x)
        end
    end.

  Definition elim_new_unified_vars '(Build_norm l e p) :=
    elim_new_unified_vars' l e (Build_norm [] [] p).

  (*TODO: move to FunctionalDB.v*)
  Arguments Build_atom {idx symbol}%type_scope atom_fn atom_args%list_scope.
  Instance Eqb_atom : Eqb atom :=
    fun '(Build_atom f1 a1 r1) '(Build_atom f2 a2 r2) =>
      andb (eqb f1 f2 ) (andb (eqb a1 a2 ) (eqb r1 r2)).

  Definition sub_var (sub : list (idx*idx)) x : idx := named_list_lookup x sub x.
  
  Definition eqn_sub (sub : list (idx*idx)) :=
    map (fun '(x,y) => (sub_var sub x, sub_var sub y)).

  Definition atom_sub sub '(Build_atom f args r) : atom :=
    Build_atom f (map (sub_var sub) args) (sub_var sub r).
  
  Definition put_sub (sub : list (idx*idx)) : list (atom * idx) -> _ :=
    map (fun '(a, x) => (atom_sub sub a, sub_var sub x)).
  
  Definition let_sub (sub : list (idx*idx)) : list (atom * idx) -> _ :=
    map (fun '(a, x) => (atom_sub sub a, x)).
  
  (* delays the substitution to apply it to l as we recurse. *)
  Fixpoint dedup_lets' l sub acc :=
    match l with
    | [] => (acc, sub)
    | (a,x)::l' =>
        let a_sub := atom_sub sub a in
        (*note: bad asymptotics, but it doesn't matter *)
        match named_list_lookup_err (let_sub sub l') a_sub with
        | Some y =>
            let sub' := (x,y)::sub in
            dedup_lets' l' sub' acc
        | None =>
            dedup_lets' l' sub ((a,x)::acc)
        end
    end.

  (* Need to reverse l on input so that when we find a duplicate, we remove the later one.
     Removing the earlier one might incorrectly free a variable.
   *)
  Definition dedup_lets l := dedup_lets' (rev l) [] [].
  
  Definition dedup '(Build_norm l e p) :=
    let (l',sub) := dedup_lets l in
    Build_norm l' (List.dedup (eqb (A:=_)) (eqn_sub sub e))
      (List.dedup (eqb (A:=_)) (put_sub sub p)).

  
  Definition optimize_upd l :=
    unnormalize_upds (dedup (elim_new_unified_vars (normalize_upds l))).

  Notation query := (query idx symbol).
  Context (symbol_map : forall A, map.map symbol A).
  Context 
      (idx_map : forall A, map.map idx A)
      (idx_map_ok : forall A, map.ok (idx_map A)).
  Section Queries.

    (* necessary to identify when a clause mentions the output.
       TODO: should clauses always bind output? Might be some performance concerns.
     *)
    Context (arities : symbol_map nat).

    (* TODO: move to FunctionalDB.v *)
    Arguments atom_fn {idx symbol}%type_scope a.
    Arguments atom_args {idx symbol}%type_scope a.
    Arguments clauses {idx symbol}%type_scope q.
    Arguments free_vars {idx symbol}%type_scope q.
    Arguments Build_query {idx symbol}%type_scope (free_vars clauses)%list_scope.

    Definition dead_var_elim q : query :=
      let in_clauses x := existsb (fun a => inb x a.(atom_args)) q.(clauses) in
      let fvs' := filter in_clauses q.(free_vars) in
      Build_query fvs' q.(clauses).

    (*TODO: move to utils*)
    Instance nat_default : WithDefault nat := 0.
    
    (* returns a junk value in the none case for convenience *)
    Definition arity f :=
      unwrap_with_default (map.get arities f).

    (*TODO: move to better place (list.v?) *)
    Fixpoint split_last {A} `{WithDefault A} (l : list A) :=
      match l with
      | [] => ([], default)
      | [a] => ([], a)
      | a :: (_ :: _) as l0 =>
          let (l',x) := split_last l0 in
          (a::l',x)
      end.

    Definition gensym : state idx idx :=
      fun s => (idx_succ s, s).

    Context {idx_default : WithDefault idx}.

    Notation instance := (instance idx symbol symbol_map idx_map).
    Arguments db_put {idx}%type_scope {Eqb_idx} {symbol}%type_scope
      {symbol_map idx_map}%function_scope s ks%list_scope v i.

    Definition uf_empty : union_find idx (idx_map _) (idx_map _) :=
      (empty idx (idx_map idx) (idx_map nat) default).

    Definition clauses_to_db (clauses : list atom) : instance :=
      fold_left (fun acc a =>
                   let '(Build_atom f args out) := a in
                   (*TODO: should db_put really return the idx? *)
                   (snd (db_put f args out acc)))
        clauses (Build_instance _ _ _ _ map.empty uf_empty).

    Context (idx_max : idx -> idx -> idx).

    Definition query_to_db q : instance := clauses_to_db q.(clauses).

    Notation db_map := (db_map idx symbol symbol_map idx_map).
    Definition db_to_clauses : db_map -> list atom :=
      let args_map_to_args _ args_map :=
        MapTreeN.ntree_fold
          _
          (fun acc keys val => (keys, val)::acc)
          _ args_map []
      in
      map.fold (fun clauses f args_map =>
                  (map (fun '(args,r) => Build_atom f args r) (args_map_to_args _ (projT2 args_map)))
                    ++ clauses) [].

    (* Note: does not need to produce a mapping from old vars to new ones.
       just grab the union-find from the instance *)
    Fail Definition db_to_query (i : instance) : query :=
      let clauses := db_to_clauses i.(db) in      
      _.

    End Queries.

      (*Optimization pipeline:
        - query -> db
        - rebuild
        - db -> query
        - prune unused output vars
        - optimize update
        - rename vars to be dense near 0

        TODO: check that there's no point in optimizing the update first
       *)

    (*
      general idea for variable order:
      1. RHS vars in order of row arity
         + question: this puts sorts (via sort_of) early. Is that a good thing?
           Seems like it might be?
     *)

    
End WithMap.
