(* An implementation of the core of egglog

   TODO: benchmark, then use plist everywhere feasible and retest
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind FunctionalDB QueryOpt.
From Utils Require TrieMap.
Import Sets.
Import StateMonad.

(*TODO: move somewhere *)
Inductive transitive_closure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| trans_base a b : R a b -> transitive_closure R a b
| trans_step a b c : R a b -> transitive_closure R b c -> transitive_closure R a c.

(*TODO: move to FUnctionalDB*)


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

  Notation atom := (atom idx symbol).

  (*TODO: implement*)
  Axiom atom_subst : named_list idx idx -> atom -> atom.

  
  Definition lift_idx_eq (ieq:idx -> idx -> Prop) (a b : atom) : Prop :=
    a.(atom_fn) = b.(atom_fn)
    /\ Forall2 ieq a.(atom_args) b.(atom_args)
    /\ ieq a.(atom_ret) b.(atom_ret).

  Definition reflexively {A} (R : relation A) : A -> Prop :=
    fun a => R a a.


  Definition idx_closure (R_idx : relation idx) : relation atom -> relation atom :=
    union_closure (lift_idx_eq R_idx).

  Record eqlog_data : Type :=
    {
      R_idx : relation idx;
      P_atom : atom -> Prop;
    }.

  Definition R_atom d a b := lift_idx_eq d.(R_idx) a b /\ d.(P_atom) a.                  

  Record eqlog_data_wf (d : eqlog_data) : Prop :=
    {
      (* TODO Equivalence or PER? an equiv prob. wouldn't hurt, R_atom is still a PER*)
      R_idx_PER : Equivalence d.(R_idx);
      P_atom_respects_R_idx : forall a b, R_atom d a b -> d.(P_atom) b;
    }.

  
  
  Definition functional_dependence (P : atom -> Prop) : relation idx :=
    fun x y => exists f args, P (Build_atom f args x) /\ P (Build_atom f args y).
  
  Local Definition ifc R (P : atom -> Prop) :=
    transitive_closure (fun x y => R x y \/ functional_dependence P x y).
  
  Section __.
    Context (P : atom -> Prop)
      (R : relation idx).
    
    Inductive atom_functional_closure : atom -> Prop :=
    | atom_base a : P a -> atom_functional_closure a
    | atom_idx_closure a b
      : atom_functional_closure a ->
        lift_idx_eq (ifc R atom_functional_closure) a b ->
        atom_functional_closure b.

    (* TODO: prove it's an equivalence relation *)
    Definition idx_functional_closure : relation idx :=
      ifc R atom_functional_closure.

  End __.

  (* Assumes rule wf, d wf, & fresh assignment wf wrt rule *)
  Definition interp_rule_step
    (r : uncompiled_rw_rule idx symbol) (d : eqlog_data)
    (fresh_assignment : named_list idx idx)
    : eqlog_data :=
    let new_atoms query_assignment :=
      map (atom_subst (fresh_assignment ++ query_assignment)) r.(uc_write_clauses _ _)
    in
    let new_unions query_assignment :=
      let sub := fresh_assignment ++ query_assignment in
      map (fun '(x,y) => (named_list_lookup x sub x, named_list_lookup y sub y))
        r.(uc_write_unifications _ _)
    in
    let assignment_valid a :=
      map fst a = r.(uc_query_vars _ _)
      /\ all d.(P_atom) (map (atom_subst a) r.(uc_query_clauses _ _)) in
    let P' x := d.(P_atom) x \/ exists qa, assignment_valid qa /\ In x (new_atoms qa) in
    let R' x y := d.(R_idx) x y
                  \/ exists qa, assignment_valid qa
                                /\ (In (x,y) (new_unions qa)
                                    \/ In (y,x) (new_unions qa))
    in
    {|
      R_idx := idx_functional_closure P' R';
      P_atom := atom_functional_closure P' R';
    |}.

  (*TODO: implement*)
  Axiom fresh_assignment_valid : named_list idx idx -> uncompiled_rw_rule idx symbol -> Prop.
  
  (* Note: this applies the rules in order, whereas the egraph applies them in parallel.
     There is no difference in the limit though.
   *)
  Inductive interp_eqlog (l : list (uncompiled_rw_rule idx symbol)) (S0 : eqlog_data) : eqlog_data -> Prop :=
  | interp_eqlog_base : interp_eqlog l S0 S0
  | interp_eqlog_step S1 r fa
    : interp_eqlog l S0 S1 ->
      In r l ->
      fresh_assignment_valid fa r ->
      interp_eqlog l S0 (interp_rule_step r S1 fa).

End WithMap.
