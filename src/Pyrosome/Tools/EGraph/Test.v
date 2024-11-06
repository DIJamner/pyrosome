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
     (cons wc .. (cons wc' nil) ..)
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
     (cons wc .. (cons wc' nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50,
        qc custom atom at level 50,
        var constr at level 0).

Notation "wc , .. , wc' | wu , .. , wu' :- [ var .. var' ]" :=
  (Build_log_rule
     (cons var' .. (cons var nil) ..)
     nil
     (cons wc .. (cons wc' nil) ..)
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        wu custom unification at level 50,
        var constr at level 0).

Notation "wc , .. , wc' :- [ var .. var' ]" :=
  (Build_log_rule
     (cons var' .. (cons var nil) ..)
     nil
     (cons wc .. (cons wc' nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50,
        var constr at level 0).


(*TODO: compute query vars for convenience*)
Notation "wc , .. , wc' | wu , .. , wu' :- qc , .. , qc'" :=
  (Build_log_rule
     nil
     (cons qc' .. (cons qc nil) ..)
     (cons wc .. (cons wc' nil) ..)
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        wu custom unification at level 50,
        qc custom atom at level 50).

Notation "wc , .. , wc' :- qc , .. , qc'" :=
  (Build_log_rule
     nil
     (cons qc' .. (cons qc nil) ..)
     (cons wc .. (cons wc' nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50,
        qc custom atom at level 50).

Notation "wc , .. , wc' | wu , .. , wu' :-" :=
  (Build_log_rule
     nil
     nil
     (cons wc .. (cons wc' nil) ..)
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        wu custom unification at level 50).

Notation "wc , .. , wc' :-" :=
  (Build_log_rule
     nil
     nil
     (cons wc .. (cons wc' nil) ..)
     [])
    (in custom logrule at level 60,
        wc custom atom at level 50).

(*TODO: compute query vars for convenience*)
Notation "| wu , .. , wu' :- qc , .. , qc' [ var .. var' ]" :=
  (Build_log_rule
     (cons var' .. (cons var nil) ..)
     (cons qc' .. (cons qc nil) ..)
     nil
     (cons wu' .. (cons wu nil) ..))
    (in custom logrule at level 60,
        wu custom unification at level 50,
        qc custom atom at level 50,
        var constr at level 0).


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


Notation process_const_rules := (process_const_rules _ _ string_succ "v0" _ _ _ _).
Notation increment_epoch := (increment_epoch _ string_succ _ _ _ _).
Notation rebuild := (rebuild _ _ _ _ _ _ _).
Notation run1iter :=
  (run1iter _ _ string_succ "v0" _ _ _ _ _ _ _ (@PositiveInstantiation.pt_spaced_intersect)).

Definition ex0 :=
  Eval vm_compute in
    (snd (Mseq (process_const_rules ex1_set)
            (rebuild 1000)
            (empty_egraph default))).
(*
Compute ex0.(epoch).
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex0.(db _ _ _ _ _))).
Compute (map.tuples ex0.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex0.(parents _ _ _ _ _)).
*)



Definition ex1 :=
  Eval vm_compute in
    (snd (run1iter ex1_set 1000 ex0)).
(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex1.(db _ _ _ _ _))).
Compute (map.tuples ex1.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex1.(parents _ _ _ _ _)).
*)

Definition ex1_graph :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.pt_spaced_intersect) ex1_set (Mret false) 5
       (empty_egraph default))).
(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex1_graph.(db _ _ _ _ _))).
Compute (fst (canonicalize _ _ _ _ _ _ (Build_atom "animal" ["0"] "0") ex1_graph)).
Compute (map.tuples ex1_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex1_graph.(parents _ _ _ _ _)).
 *)


Definition example2 :=
  [!! "zero" -> "z", "nat" "z" -> "_"  :-;
   !! "S" "n" -> "+n", "nat" "+n" -> "_" :- "nat" "n" -> "_" ["n" "_"];
   !!  | "n" = "m" :- "S" "n" -> "r", "S" "m" -> "r" [ "m" "n" "r" ];
   (* skip Sn /= 0 because we don't have /= *)
   !! "add" "m" "n" -> "mn", "nat" "mn" -> "_0" | "_0" = "_1" :-
      "nat" "m" -> "_0" , "nat" "n" -> "_1" ["m" "n" "_0" "_1"];
   !! | "n" = "r" :-  "zero" -> "z", "add" "z" "n" -> "r" ["n" "r" "z"];
   !! "S" "n" -> "s'", "add" "m" "n" -> "mn", "S" "mn" -> "r" :-
      "S" "m" -> "s", "add" "s" "n" -> "r" ["n" "r" "s" "m"];
   (* Initializing rules*)
   !! "foo" -> "f", "nat" "f" -> "nf" :-
  ]%log.


Definition ex2_set :=
  Eval vm_compute in
    QueryOpt.build_rule_set _ _ string_succ "v0" _ string_trie_map
      _ string_trie_map example2.


Definition ex2_graph :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.pt_spaced_intersect) ex2_set (Mret false) 2
       (empty_egraph default))).

(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex2_graph.(db _ _ _ _ _))).
Compute (map.tuples ex2_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex2_graph.(parents _ _ _ _ _)).
*)

Import PositiveInstantiation.
Local Existing Instance pos_trie_map.
(* expect ["foo"; "foo"]*)
(*
Compute
  (map (map pts) (map.keys (pt_spaced_intersect (fun 'tt 'tt => tt)
           ((map.put map.empty ["foo"] tt : pos_trie_map, [true; false]),
             [(map.put map.empty ["foo"] tt : pos_trie_map, [false;true])]) : pos_trie_map))).
*)
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
