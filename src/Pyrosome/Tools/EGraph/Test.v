(* Some basic tests of the egraph machinery *)
Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
From Utils.EGraph Require Import Defs Semantics QueryOpt.
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
   !! "canine" "x" -> "t" :- "dog" -> "x" [ "x" ];
   !! "animal" "x" -> "t" :- "dog" -> "x" [ "x" ];
   !! "animal" "x" -> "t" :- "cat" -> "x" [ "x" ]
  ]%log.


Definition ex1_set :=
  Eval vm_compute in
    QueryOpt.build_rule_set _ _ string_succ "v0" _ string_trie_map
      _ string_trie_map example1.

Definition ex1_graph :=
  Eval vm_compute in
    (saturate_until string_succ "v0"
       (@PositiveInstantiation.pt_spaced_intersect) ex1_set (Mret false) 10
       (empty_egraph default)).

(*TODO: test queries*)
