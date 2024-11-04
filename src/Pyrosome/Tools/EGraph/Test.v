(* Some basic tests of the egraph machinery *)
Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
From Utils.EGraph Require Import Defs QueryOpt.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
Import StringInstantiation.

Notation log_rule := (log_rule string string).

(* TODO: make this available in other places than the tests *)
Declare Custom Entry logrule.
Declare Custom Entry atom.
Declare Custom Entry unification.
Declare Scope log_scope.
Bind Scope log_scope with log_rule.
Delimit Scope log_scope with log.

(*TODO: move to defining file*)
Arguments Build_log_rule {idx symbol}%type_scope
  (query_vars query_clauses write_clauses write_unifications)%list_scope.

Notation "!! x" := x (at level 60, x custom logrule) : log_scope.

(*TODO: compute query vars for convenience*)
Notation "wc , .. , wc' | wu , .. , wu' :- qc , .. , qc' [ var .. var' ]" :=
  (Build_log_rule
     (cons var' .. (cons var nil) ..)
     (cons qc' .. (cons qc nil) ..)
     (cons wc' .. (cons wc nil) ..)
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        wu custom unification at level 50,
        qc custom atom at level 50,
        var constr at level 0).

Notation "wc , .. , wc' :- qc , .. , qc' [ var .. var' ]" :=
  (Build_log_rule
     (cons var' .. (cons var nil) ..)
     (cons qc' .. (cons qc nil) ..)
     (cons wc' .. (cons wc nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50,
        qc custom atom at level 50,
        var constr at level 0).

Notation "wc , .. , wc' | wu , .. , wu' :- [ var .. var' ]" :=
  (Build_log_rule
     (cons var' .. (cons var nil) ..)
     nil
     (cons wc' .. (cons wc nil) ..)
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        wu custom unification at level 50,
        var constr at level 0).

Notation "wc , .. , wc' :- [ var .. var' ]" :=
  (Build_log_rule
     (cons var' .. (cons var nil) ..)
     nil
     (cons wc' .. (cons wc nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50,
        var constr at level 0).


(*TODO: compute query vars for convenience*)
Notation "wc , .. , wc' | wu , .. , wu' :- qc , .. , qc'" :=
  (Build_log_rule
     nil
     (cons qc' .. (cons qc nil) ..)
     (cons wc' .. (cons wc nil) ..)
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        wu custom unification at level 50,
        qc custom atom at level 50).

Notation "wc , .. , wc' :- qc , .. , qc'" :=
  (Build_log_rule
     nil
     (cons qc' .. (cons qc nil) ..)
     (cons wc' .. (cons wc nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50,
        qc custom atom at level 50).

Notation "wc , .. , wc' | wu , .. , wu' :-" :=
  (Build_log_rule
     nil
     nil
     (cons wc' .. (cons wc nil) ..)
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        wu custom unification at level 50).

Notation "wc , .. , wc' :-" :=
  (Build_log_rule
     nil
     nil
     (cons wc' .. (cons wc nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50).

Notation "f a .. a' -> r" :=
  (Build_atom f (cons a' .. (cons a nil) ..) r)
    (in custom atom at level 50,
        f constr at level 0,
        a constr at level 0,
        r constr at level 0).

Notation "f -> r" :=
  (Build_atom f nil r)
    (in custom atom at level 50,
        f constr at level 0,
        r constr at level 0).

Notation "a = b" :=
  (a,b)
    (in custom unification at level 50, a constr at level 0,
    b constr at level 0).
           
Definition example1 : list log_rule :=
  [!! "dog" -> "d" :-;
   !! "cat" -> "c" :-;
   !! "catdog" -> "d" | "d" = "c" :- "dog" -> "d", "cat" -> "c" [ "c" "d" ];
   !! "canine" "y" -> "y" :- "dog" -> "y" [ "y" ];
   !! "animal" "a" -> "t" :- "canine" "a" -> "t" [ "a" "t" ];
   !! "animal" "x" -> "x" :- "cat" -> "x" [ "x" ]
  ]%log.


Definition ex1_set :=
  Eval vm_compute in
    QueryOpt.build_rule_set _ _ string_succ "v0" _ string_trie_map
      _ string_trie_map example1.

Definition ex1_graph :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.pt_spaced_intersect) ex1_set (Mret false) 4
       (empty_egraph default))).

(*TODO: strange epoch behavior. Should only take 3 cycles? but 9 appears?
  - catdog in cycle 0
  - animal[cat], canine [dog] in cycle 1

  Without catdog, nothing in cycle 0, canine + animal in cycle 1

  Issue: something to do w/ epoch of first elts? but then why does catdog work?

  TODO: not rebuilding correctly. "0" should disappear from tuples.

  TODO: animal[0] instead of animal[]; using the wrong side of the union?
        - does get unioned though
        - alternative explanation: catdog happens before animal
  TODO: should parents update output var? Doesn't quite seem right.
  TODO!!!!!!!! critical fix: need to update the out-var.

  TODO: fix epoch merging.
  Currently, looks like an identical overwrite updates the epoch.
  It can't, or epochs aren't as useful.
  TODO: hash_node should already handle this; why doesn't it?
  Canine gets re-entered every round
  Idea: maybe related to non-canonical out ptrs? yes.
  Now animal, canine both do it.
  Maybe something adding non-canonical node still?


 *)
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex1_graph.(db _ _ _ _ _))).
Compute (fst (canonicalize _ _ _ _ _ _ (Build_atom "animal" ["0"] "0") ex1_graph)).
Compute (map.tuples ex1_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex1_graph.(parents _ _ _ _ _)).

Import PositiveInstantiation.
Local Existing Instance pos_trie_map.
(* expect ["foo"; "foo"]*)
Compute
  (map (map pts) (map.keys (pt_spaced_intersect (fun 'tt 'tt => tt)
           ((map.put map.empty ["foo"] tt : pos_trie_map, [true; false]),
             [(map.put map.empty ["foo"] tt : pos_trie_map, [false;true])]) : pos_trie_map))).

(*
(*TODO: implement & test queries*)
Definition query_egraph 

  Definition process_erule'
    (* each trie pair is (total, frontier) *)
    (db_tries : symbol_map (idx_map (idx_trie unit * idx_trie unit)))
    (r : erule) (frontier_n : idx) : ST unit :=
    let tries : ne_list _ := ne_map (trie_of_clause r.(query_vars) db_tries frontier_n)
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

  

  (*TODO: update/implement rebuilding*)
  Definition run1iter (rs : rule_set) : ST unit :=
    @! let tries <- build_tries rs in
      (* increment the epoch so that all added nodes are in the next frontier.
           TODO: check for off-by-one errors
       *)
      let _ <- increment_epoch in
      let _ <- list_Miter (process_erule tries) rs.(compiled_rules) in
      (* TODO: compute an adequate upper bound for fuel *)
      (rebuild 1000).
*)
