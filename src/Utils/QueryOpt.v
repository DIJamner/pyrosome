Require Import String Lists.List.
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
  Arguments unify {idx symbol}%type_scope _ _ _.
  Arguments put_row {idx symbol}%type_scope _ _ _.
  Arguments let_row {idx symbol}%type_scope _ _ _.
  Arguments done {idx symbol}%type_scope.

  (* Assumes no shadowing *)
  Fixpoint normalize' l : normalized_upd -> normalized_upd :=
    match l with
    | unify i1 i2 k =>
        Basics.compose (normalize' k) (push_eqn i1 i2)
    | put_row a i k =>
        Basics.compose (normalize' k) (push_put a i)
    | let_row a x k =>
        Basics.compose (normalize' k) (push_let a x)
    | done => id
    end.

  Definition normalize l := normalize' l (Build_norm [] [] []).

  Definition unnormalize '(Build_norm l e p) : log_upd :=
    let pk : log_upd := List.fold_left (fun k '(a,x) => put_row a x k) p done in
    let ek : log_upd := List.fold_left (fun k '(x,y) => unify x y k) e pk in
    List.fold_right (fun '(a,x) k => let_row a x k) ek l.

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
    fun '(Build_atom f1 a1) '(Build_atom f2 a2) =>
      andb (eqb f1 f2) (eqb a1 a2).

  Definition sub_var (sub : list (idx*idx)) x : idx := named_list_lookup x sub x.
  
  Definition eqn_sub (sub : list (idx*idx)) :=
    map (fun '(x,y) => (sub_var sub x, sub_var sub y)).

  Definition atom_sub sub '(Build_atom f args) : atom :=
    Build_atom f (map (sub_var sub) args).
  
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
    unnormalize (dedup (elim_new_unified_vars (normalize l))).

End WithMap.
