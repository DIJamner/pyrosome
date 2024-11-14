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
  (run1iter _ _ string_succ "v0" _ _ _ _ _ _ _ (@PositiveInstantiation.compat_intersect)).

Definition ex0 :=
  Eval vm_compute in
    (snd (Mseq (process_const_rules ex1_set)
            (rebuild 1000)
            (empty_egraph default))).

Ltac test H :=
  let H' := fresh in
  assert H  as H' by (vm_compute; reflexivity);
  clear H'.

Goal False.
  test (ex0.(epoch) = "").
  test (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex0.(db _ _ _ _ _))
          = [("dog", [([], ("", ""))]); ("cat", [([], ("", "0"))])]).
  test (map.tuples ex0.(equiv _ _ _ _ _).(UnionFind.parent _ _ _) = [("0", "0"); ("", "")]).
  test (map.tuples ex0.(parents _ _ _ _ _)
       = [("0", [{| atom_fn := "cat"; atom_args := []; atom_ret := "0" |}]);
        ("", [{| atom_fn := "dog"; atom_args := []; atom_ret := "" |}])]).
Abort.



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
       (@PositiveInstantiation.compat_intersect) ex1_set (Mret false) 5
       (empty_egraph default))).

(*TODO: intersection very broken*)
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
       (@PositiveInstantiation.compat_intersect) ex2_set (Mret false) 2
       (empty_egraph default))).

(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex2_graph.(db _ _ _ _ _))).
Compute (map.tuples ex2_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex2_graph.(parents _ _ _ _ _)).
 *)

Definition ex2_query :=
  [ !! "ERR" -> "X" :- "zero" -> "z", "add" "z" "n" -> "n" ["z" "n"]
  ]%log.

Definition ex2_qset :=
  Eval vm_compute in
    QueryOpt.build_rule_set _ _ string_succ "v0" _ string_trie_map
      _ string_trie_map ex2_query.


Arguments run_query {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map}%function_scope {symbol_map_plus} {idx_map}%function_scope {idx_map_plus}
  {idx_trie}%function_scope spaced_list_intersect%function_scope rs n%nat_scope _.
Arguments run_query' {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map}%function_scope {symbol_map_plus} {idx_map}%function_scope {idx_map_plus}
  {idx_trie}%function_scope rs n%nat_scope _.

Notation run_query := (run_query (@PositiveInstantiation.compat_intersect)).
Notation run_query' := (run_query').
Notation build_tries := (build_tries _ _ _ _ _ _ _ _).

Compute (fst (run_query ex2_qset 0 ex2_graph)).

(* Lang tests *)
(*
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches.
From Pyrosome.Lang Require Import SimpleVSubst SimpleUnit SimpleEvalCtx.
Import Core.Notations.

Require Coq.derive.Derive.

Open Scope lang_scope.*)

Import Core.Notations.


Definition monoid : lang string := 
  {[l
  [s|
      -----------------------------------------------
      #"S" srt
  ];
  [:|  "a": #"S", "b" : #"S"
       -----------------------------------------------
       #"*" "a" "b" : #"S"
  ];
  [:=  "a": #"S", "b" : #"S", "c" : #"S"
       ----------------------------------------------- ("assoc")
       #"*" (#"*" "a" "b") "c"
       = #"*" "a" (#"*" "b" "c")
       : #"S"
  ]
  ]}.

Definition monoid_rule_set_full :=
  Eval vm_compute in
    (build_rule_set monoid monoid).

Definition monoid_rule_set :=
  Eval vm_compute in
    (build_rule_set (PositiveInstantiation.filter_eqn_rules monoid) monoid).

Definition monoid_ex1 : lang string := 
  {[l
  [:|  
       -----------------------------------------------
       #"foo" : #"S"
  ];
  [:|  
       -----------------------------------------------
       #"bar" : #"S"
  ](*;
  [:=  
       ----------------------------------------------- ("foobar")
       #"*" "foo" "bar"
       = #"foo"
       : #"S"
  ]*)
  ]}.


Definition monoid_ex1_rule_set :=
  Eval vm_compute in
    (build_rule_set monoid_ex1 monoid_ex1).

Definition monoid_ex1_base :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.compat_intersect) monoid_ex1_rule_set (Mret false) 0
       (empty_egraph default))).
      
Definition monoid_ex1_graph :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.compat_intersect) monoid_rule_set_full (Mret false) 2
       monoid_ex1_base)).

Compute (map (uncurry (rule_to_log_rule string_succ sort_of
                         (fold_right string_max "x0") monoid_ex1))
           monoid_ex1).
Compute (map (uncurry (rule_to_log_rule string_succ sort_of
                         (fold_right string_max "x0") monoid))
           monoid).
(*
  !! "S" -> "x3", "*" "a" "b" -> "x4", "@sort_of" "x4" -> "x3" :- "@sort_of" "a" -> "x2",
  "S" -> "x2", "@sort_of" "b" -> "x1", "S" -> "x1" ["a" "x2" "b" "x1"];
 *)
(*look ok *)
(*TODO: optimization will make the above more readable*)

Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples monoid_ex1_base.(db _ _ _ _ _))).
(* TODO only see odd allocations. What is happening w/ the even ones
   and can I get rid of them? They appear in the uf.
 *)
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples monoid_ex1_graph.(db _ _ _ _ _))).
(*TODO: assoc never matching. Question: are there any * ( * _ _) _s? yes. Should match
  Example expected match:
  S -> ""
               sort_of 0 -> ""
  * 0 0 -> 5   sort_of 5 -> ""
  * 5 0 -> Z0  sort_of Z0 -> ""

!! "S" -> "x<", "*" "b" "c" -> "x8", "S" -> "x9", "@sort_of" "x8" -> "x9",
   "*" "a" "x8" -> "x:", "S" -> "x;", "@sort_of" "x:" -> "x;", "@sort_of" "x:" -> "x<"
           | "x6" = "x:" :-

   "@sort_of" "a" -> "x3",
   "S" -> "x3",
   "@sort_of" "b" -> "x2", 
   "S" -> "x2",
   "@sort_of" "c" -> "x1",
   "S" -> "x1",
   "@sort_of" "x6" -> "x7",
   "S" -> "x7",
   "*" "x4" "c" -> "x6",
   "@sort_of" "x4" -> "x5",
   "S" -> "x5",
   "*" "a" "b" -> "x4"
   ["a" "x3" "b" "x2" "c" "x1" "x6" "x7" "x4" "x5"];

   Satisfying match:
   x3 = x2 = x1 = x7 = x5 := "".
   a = b = c := 0.
   x4 := 5.
   x6 := Z0

 *)

Compute (filter (fun p => negb (eqb (fst p) (snd p)))
           (map.tuples monoid_ex1_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _))).
Compute (map.tuples monoid_ex1_graph.(parents _ _ _ _ _)).
(*TODO: are the vars not bound properly in the write clause? yes, see zero-var match below*)
(*
 [("@sort_of",
         [(["0"], ("", "")); (["2"], ("", "")); (["5"], ("0", ""));
          (["?"], ("1", ""))]); ("bar", [([], ("", "0"))]);
        ("*", [(["v0"; "v0"], ("0", "5")); (["5"; "v0"], ("1", "?"))]);
        ("foo", [([], ("", "2"))]); ("S", [([], ("", ""))])]
 *)

(*TODO: doesn't match but should *)
Compute (fst (run_query monoid_rule_set_full 0 monoid_ex1_graph)).

Let tries :=
      Eval vm_compute in
      (unwrap_with_default (fst (run_query' monoid_rule_set_full 0 monoid_ex1_graph))).

Definition ne_firstn {A} n (l : ne_list A) : ne_list A :=
  (fst l, firstn n (snd l)).
(*TODO: why is this empty?*)

Compute (intersection_keys string _ (@PositiveInstantiation.compat_intersect)
           (ne_firstn 0 tries)).
(*even the first 2 cancel*)
Compute (intersection_keys string _ (@PositiveInstantiation.compat_intersect)
           (ne_firstn 1 tries)).

Compute (map.tuples (PositiveInstantiation.proj_node_map
           (PositiveInstantiation.compat_intersect (fun _ _ : unit => tt)
           (ne_firstn 0 tries)) : string_trie_map _)).
(*
  TODO: all tries contain elts, must be that there's an empty intersection.

  TODO: triple order?!!
  tree ["x4"; "x6"; "c"] contains  ["5"; "Z0"; "0"]!
  4th tree from the front
 *)
Compute (ne_map (fun '(m,l) => (map.tuples m,
                                 map fst (filter snd (combine ["x5"; "x4"; "x7"; "x6"; "x1"; "c"; "x2"; "b"; "x3"; "a"] l)))) tries).
(*
   query_clause_ptrs :=
         ("*", "", ["x4"; "b"; "a"],
          [("S", "", ["x5"]); ("@sort_of", "", ["x5"; "x4"]); ("*", "0", ["x4"; "x6"; "c"]);
           ("S", "", ["x7"]); ("@sort_of", "", ["x7"; "x6"]); ("S", "", ["x1"]);
           ("@sort_of", "", ["x1"; "c"]); ("S", "", ["x2"]); ("@sort_of", "", ["x2"; "b"]);
           ("S", "", ["x3"]); ("@sort_of", "", ["x3"; "a"])]);

Question: is this an intersection bug? by-hand intersection seems to work?

*)


Compute (named_map map.tuples (map.tuples monoid_rule_set_full.(Defs.query_clauses _ _ _ _))).
(*[("@sort_of", [("", ([1], 0))]); ("*", [("0", ([2; 0], 1)); ("", ([1; 2], 0))]);
        ("S", [("", ([], 0))])]*)

(*Some
    S -> x1   (PositiveInstantiation.pos_trie_leaf tt, [true; false; false; false],
    @sort_of b->x1     [(PositiveInstantiation.pos_trie_leaf tt, [true; true; false; false]);
    S -> x2     (PositiveInstantiation.pos_trie_leaf tt, [false; false; true; false]);
    @sort_of  a->x2     (PositiveInstantiation.pos_trie_leaf tt, [false; false; true; true])])


     {|
       Defs.query_vars := ["x1"; "b"; "x2"; "a"];
       query_clause_ptrs :=
         ("S", "", ["x1"],
          [("@sort_of", "", ["x1"; "b"]); ("S", "", ["x2"]); ("@sort_of", "", ["x2"; "a"])]);
       Defs.write_clauses :=
         [{| atom_fn := "S"; atom_args := []; atom_ret := "x3" |};
          {| atom_fn := "*"; atom_args := ["b"; "a"]; atom_ret := "x4" |};
          {| atom_fn := "@sort_of"; atom_args := ["x4"]; atom_ret := "x3" |}];
       Defs.write_unifications := []
     |}
 *)

Compute (map.tuples (map_map map.tuples monoid_rule_set_full.(Defs.query_clauses _ _ _ _))).
(*[("@sort_of", [("", (["0"], ""))]); ("*", [("0", (["1"; ""], "0")); ("", (["0"; "1"], ""))]);
        ("S", [("", ([], ""))])]*)
Compute (map.tuples (map_map map.tuples (fst (build_tries monoid_rule_set_full monoid_ex1_base)))).
(*Results: [("@sort_of", [("", (PositiveInstantiation.pos_trie_leaf tt, PositiveInstantiation.pos_trie_leaf tt))]);
        ("S", [("", (PositiveInstantiation.pos_trie_leaf tt, PositiveInstantiation.pos_trie_leaf tt))])]
        Leaves are not defaults (empty is default).
        Only make sense if flags are [false..]

TODO: why are the * tries not here? answer: no * nodes.
Observation: issue appears with a rule that has some matches, but not all fn symbols exist!
probably assuming that * is in the egraph

TODO: check intersection keys/flag lists?
*)

Definition compute_tries rs := build_tries rs.
(*
Compute (map.tuples ex2_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex2_graph.(parents _ _ _ _ _)).
 *)


Import PositiveInstantiation.
Local Existing Instance pos_trie_map.
(* expect ["foo"; "foo"]*)
Compute
  (map (map pts) (map.keys (compat_intersect (fun 'tt 'tt => tt)
           ((map.put map.empty ["foo"] tt : pos_trie_map, [true; false]),
             [(map.put map.empty ["foo"] tt : pos_trie_map, [false;true])]) : pos_trie_map))).
Fail.
(**)
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
