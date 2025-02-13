(* Some basic tests of the egraph machinery *)
Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
From Utils.EGraph Require Import Defs QueryOpt Semantics.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
Import StringInstantiation.

(* TODO: make this available in other places than the tests *)
Declare Custom Entry logrule.
Declare Custom Entry atom.
Declare Scope log_scope.
Bind Scope log_scope with sequent.
Delimit Scope log_scope with log.

Notation "!! x" := x (at level 60, x custom logrule) : log_scope.

(*TODO: compute query vars for convenience*)
Notation "wc , .. , wc' :- qc , .. , qc'" :=
  (Build_sequent _ _
     (cons qc' .. (cons qc nil) ..)  
     (cons wc .. (cons wc' nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50,
        qc custom atom at level 50).

Notation "wc , .. , wc' :-" :=
  (Build_sequent _ _
     nil
     (cons wc .. (cons wc' nil) ..))
    (in custom logrule at level 60,
        wc custom atom at level 50).

Notation "f a .. a' -> r" :=
  (atom_clause (Build_atom f (cons a' .. (cons a nil) ..) r))
    (in custom atom at level 50,
        f constr at level 0,
        a constr at level 0,
        r constr at level 0).

Notation "f -> r" :=
  (atom_clause (Build_atom f nil r))
    (in custom atom at level 50,
        f constr at level 0,
        r constr at level 0).

Notation "a = b" :=
  (eq_clause a b)
    (in custom atom at level 50, a constr at level 0,
    b constr at level 0).
           
Definition example1 : list (sequent _ _) :=
  [!! "dog" -> "d" :-;
   !! "cat" -> "c" :-;
   !! "catdog" -> "d" , "d" = "c" :- "dog" -> "d", "cat" -> "c";
   !! "canine" "y" -> "y" :- "dog" -> "y";
   !! "animal" "a" -> "t" :- "canine" "a" -> "t";
   !! "animal" "x" -> "x" :- "cat" -> "x"
  ]%log.


Definition ex1_set :=
  Eval vm_compute in
    QueryOpt.build_rule_set string_succ "v0" (idx_map:=string_trie_map) example1.


Notation process_const_rules := (process_const_rules _ _ string_succ "v0" _ _ _ _).
Notation increment_epoch := (increment_epoch _ string_succ _ _ _ _).
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
          = [("dog", [([], ("", ""))]); ("cat", [([], ("", "#"))])]).
  test (map.tuples ex0.(equiv _ _ _ _ _).(UnionFind.parent _ _ _) = [("#", "#"); ("", "")]).
  test (map.tuples ex0.(parents _ _ _ _ _)
       = [("#", [{| atom_fn := "cat"; atom_args := []; atom_ret := "#" |}]);
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

(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex1_graph.(db _ _ _ _ _))).
Compute (fst (canonicalize _ _ _ _ _ _ (Build_atom "animal" ["0"] "0") ex1_graph)).
Compute (map.tuples ex1_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex1_graph.(parents _ _ _ _ _)).
 *)


Definition example2 :=
  [!! "zero" -> "z", "nat" "z" -> "_"  :-;
   !! "S" "n" -> "+n", "nat" "+n" -> "_" :- "nat" "n" -> "_";
   !!  "n" = "m" :- "S" "n" -> "r", "S" "m" -> "r";
   (* skip Sn /= 0 because we don't have /= *)
   !! "add" "m" "n" -> "mn", "nat" "mn" -> "_0", "_0" = "_1" :-
      "nat" "m" -> "_0" , "nat" "n" -> "_1";
   !! "n" = "r" :-  "zero" -> "z", "add" "z" "n" -> "r";
   !! "S" "n" -> "s'", "add" "m" "n" -> "mn", "S" "mn" -> "r" :-
      "S" "m" -> "s", "add" "s" "n" -> "r";
   (* Initializing rules*)
   !! "foo" -> "f", "nat" "f" -> "nf" :-
  ]%log.


Definition ex2_set :=
  Eval vm_compute in
    QueryOpt.build_rule_set string_succ "v0" (idx_map:=string_trie_map) example2.


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
  [ !! "ERR" -> "X" :- "zero" -> "z", "add" "z" "n" -> "n"
  ]%log.

Definition ex2_qset :=
  Eval vm_compute in
    QueryOpt.build_rule_set string_succ "v0" (idx_map:=string_trie_map) ex2_query.


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
       (@PositiveInstantiation.compat_intersect) monoid_rule_set_full (Mret false) 3
       monoid_ex1_base)).
(*TODO: seems to work!
Definition monoid_ex1_graph' :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.compat_intersect) monoid_rule_set (Mret false) 2
       monoid_ex1_graph)).
*)
(*
Compute (map (uncurry (rule_to_log_rule string_succ sort_of
                         (fold_right string_max "x0") monoid_ex1))
           monoid_ex1).
Compute (map (uncurry (rule_to_log_rule string_succ sort_of
                         (fold_right string_max "x0") monoid))
           monoid).
*)
(*
  !! "S" -> "x3", "*" "a" "b" -> "x4", "@sort_of" "x4" -> "x3" :- "@sort_of" "a" -> "x2",
  "S" -> "x2", "@sort_of" "b" -> "x1", "S" -> "x1" ["a" "x2" "b" "x1"];
 *)
(*look ok *)
(*TODO: optimization will make the above more readable*)

(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples monoid_ex1_base.(db _ _ _ _ _))).
*)
(* TODO: why are a bunch of things equal to foo, bar? I don't have a 0,
   so the only things that are equal should be *s
 *)
(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples monoid_ex1_graph.(db _ _ _ _ _))).

Compute (filter (fun p => negb (eqb (fst p) (snd p)))
           (map.tuples monoid_ex1_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _))).
Compute (map.tuples monoid_ex1_graph.(parents _ _ _ _ _)).
 *)

(*
Compute (fst (run_query monoid_rule_set_full 0 monoid_ex1_graph)).
*)

Let tries :=
      Eval vm_compute in
      (unwrap_with_default (fst (run_query' monoid_rule_set_full 0 monoid_ex1_graph))).

Definition ne_firstn {A} n (l : ne_list A) : ne_list A :=
  (fst l, firstn n (snd l)).

(*
Compute (intersection_keys string _ (@PositiveInstantiation.compat_intersect)
           (ne_firstn 0 tries)).
Compute (intersection_keys string _ (@PositiveInstantiation.compat_intersect)
           (ne_firstn 1 tries)).

Compute (map.tuples (PositiveInstantiation.proj_node_map
           (PositiveInstantiation.compat_intersect (fun _ _ : unit => tt)
           (ne_firstn 0 tries)) : string_trie_map _)).
*)
(*
Compute (ne_map (fun '(m,l) => (map.tuples m,
                                 map fst (filter snd (combine ["x5"; "x4"; "x7"; "x6"; "x1"; "c"; "x2"; "b"; "x3"; "a"] l)))) tries).
*)
(*
Compute (named_map map.tuples (map.tuples monoid_rule_set_full.(Defs.query_clauses _ _ _ _))).
(*[("@sort_of", [("", ([1], 0))]); ("*", [("0", ([2; 0], 1)); ("", ([1; 2], 0))]);
        ("S", [("", ([], 0))])]*)
*)
(*
Compute (map.tuples (map_map map.tuples monoid_rule_set_full.(Defs.query_clauses _ _ _ _))).
(*[("@sort_of", [("", (["0"], ""))]); ("*", [("0", (["1"; ""], "0")); ("", (["0"; "1"], ""))]);
        ("S", [("", ([], ""))])]*)
Compute (map.tuples (map_map map.tuples (fst (build_tries monoid_rule_set_full monoid_ex1_base)))).
*)

Definition compute_tries rs := build_tries rs.
(*
Compute (map.tuples ex2_graph.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex2_graph.(parents _ _ _ _ _)).
 *)



(*
Import PositiveInstantiation.
Local Existing Instance pos_trie_map.
(* expect ["foo"; "foo"]*)
Goal
  let '(ptl, cil) :=
    split [(map.put map.empty ["foo"] tt : pos_trie_map, [true; false]);
           (map.put map.empty ["foo"] tt : pos_trie_map, [false;true])] in
  let fuel := S (Datatypes.length (hd [] cil)) in  
  (map (map pts) (map.keys (@! let ptl' <- list_Mmap (M:=option) id ptl in
    (pt_spaced_intersect' (fun 'tt 'tt => tt) fuel cil ptl' [] [])        
                                : pos_trie_map))) = [ ["foo"; "foo"] ].
reflexivity.
Abort.
*)


Definition logic : lang string := 
  {[l
  [s|
      -----------------------------------------------
      #"S" srt
  ];
  [:|  
       -----------------------------------------------
       #"T" : #"S"
  ];
  [:|  
       -----------------------------------------------
       #"F" : #"S"
  ];
  [:|  "a": #"S", "b" : #"S"
       -----------------------------------------------
       #"\/" "a" "b" : #"S"
  ];
  [:|  "a": #"S", "b" : #"S"
       -----------------------------------------------
       #"/\" "a" "b" : #"S"
  ];
  [:|  "a": #"S"
       -----------------------------------------------
       #"-" "a" : #"S"
  ];
  [:=  
       ----------------------------------------------- ("-T")
       #"-" #"T" = #"F" : #"S"
  ];
  [:=  
       ----------------------------------------------- ("-F")
       #"-" #"F" = #"T" : #"S"
  ];
  [:=  "a": #"S", "b" : #"S"
       ----------------------------------------------- ("de Morgan-/\")
       #"-" (#"/\" "a" "b")
       = #"\/" (#"-" "a") (#"-" "b")
       : #"S"
  ];
  [:=  "b" : #"S"
       ----------------------------------------------- ("/\-T")
       #"/\" #"T" "b" = "b" : #"S"
  ];
  [:=  "b" : #"S"
       ----------------------------------------------- ("/\-F")
       #"/\" #"F" "b" = #"F" : #"S"
  ];
  [:=  "b" : #"S"
       ----------------------------------------------- ("/\-=")
       #"/\" "b" "b" = "b" : #"S"
  ];
    (* initial terms *)
  [:|  
       -----------------------------------------------
       #"foo" : #"S"
  ];
  [:|  
       -----------------------------------------------
       #"bar" : #"S"
  ]
    
  ]}.



Definition logic_rule_set_full :=
  Eval vm_compute in
    (build_rule_set logic logic).

Definition logic_rule_set :=
  Eval vm_compute in
    (build_rule_set (PositiveInstantiation.filter_eqn_rules logic) logic).
(*TODO: is the optimization not working? multiple S write clauses.
  answer: no, since optimization doesn't handle existential vars.
  
 *)

(*
Compute (map (optimize_log_rule string _ string_succ "v0" string _ string_trie_map string_trie_map _ id 100 (*TODO: magic number*))
           (map (uncurry (rule_to_log_rule string_succ sort_of (fold_right string_max "") logic))
              logic)).
*)

Definition logic_ex1_base :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.compat_intersect) logic_rule_set_full (Mret false) 1
       (empty_egraph default))).
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples logic_ex1_base.(db _ _ _ _ _))).
Compute (filter (fun p => negb (eqb (fst p) (snd p)))
           (map.tuples monoid_ex1_base.(equiv _ _ _ _ _).(UnionFind.parent _ _ _))).
      
Definition logic_ex1_graph :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PositiveInstantiation.compat_intersect) logic_rule_set (Mret false) 5
       logic_ex1_base)).
(*TODO: why no unifications?*)
Compute (filter (fun p => negb (eqb (fst p) (snd p)))
           (map.tuples monoid_ex1_base.(equiv _ _ _ _ _).(UnionFind.parent _ _ _))).
