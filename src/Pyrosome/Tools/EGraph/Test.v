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

Definition inject : list (sequent _ _) :=
  [!! "G" = "G1", "A" = "A1" :- "exp" "G" "A" -> "x", "exp" "G1" "A1" -> "x"]%log.


Definition ex1_set :=
  Eval vm_compute in
    QueryOpt.build_rule_set string_succ "v0" (idx_map:=string_trie_map) 1000 example1.


Notation process_const_rules := (process_const_rules _ _ string_succ "v0" _ _ _ _ unit).
Notation increment_epoch := (increment_epoch _ string_succ _ _ _ _).
Notation run1iter :=
  (run1iter _ _ string_succ "v0" _ _ _ _ _ _ _ (@PosListMap.compat_intersect)).

Definition ex0 :=
  Eval vm_compute in
    (snd (Mseq (process_const_rules ex1_set)
            (rebuild 1000)
            (empty_egraph _ _))).

Ltac test H :=
  let H' := fresh in
  assert H  as H' by (vm_compute; reflexivity);
  clear H'.

Goal False.
  test (ex0.(epoch) = "").
  test (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex0.(db))
        = [("dog", [([], (Build_db_entry _ _ "" "" tt))]);
           ("cat", [([], (Build_db_entry _ _ "" "#" tt))])]).
  test (map.tuples ex0.(equiv).(UnionFind.parent _ _ _) = [("#", "#"); ("", "")]).
  test (map.tuples ex0.(parents)
       = [("#", [{| atom_fn := "cat"; atom_args := []; atom_ret := "#" |}]);
        ("", [{| atom_fn := "dog"; atom_args := []; atom_ret := "" |}])]).
Abort.



Definition ex1 :=
  Eval vm_compute in
    (snd (run1iter 1000 ex1_set ex0)).

(*
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples ex1.(db _ _ _ _ _))).
Compute (map.tuples ex1.(equiv _ _ _ _ _).(UnionFind.parent _ _ _)).
Compute (map.tuples ex1.(parents _ _ _ _ _)).
*)

Definition ex1_graph :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PosListMap.compat_intersect) 1000 ex1_set (Mret false) 5
       (empty_egraph _ _))).

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
    QueryOpt.build_rule_set string_succ "v0" (idx_map:=string_trie_map) 1000 example2.


(*Set NativeCompute Profiling.*)
(*TODO: spending the vast majority of its time on string things*)
Definition ex2_graph :=
  Eval native_compute in
    (snd (saturate_until string_succ "v0"
       (@PosListMap.compat_intersect) 1000 ex2_set (Mret false) 0
       (empty_egraph _ _))).

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
    QueryOpt.build_rule_set string_succ "v0" (idx_map:=string_trie_map) 1000 ex2_query.


Arguments run_query {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map}%function_scope {symbol_map_plus} {idx_map}%function_scope {idx_map_plus}
  {idx_trie}%function_scope {analysis_result}%type_scope
  spaced_list_intersect%function_scope rs n%nat_scope _.
Arguments run_query' {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map}%function_scope {symbol_map_plus} {idx_map}%function_scope {idx_map_plus}
  {idx_trie}%function_scope  {analysis_result}%type_scope rs n%nat_scope _.

Notation run_query := (run_query (@PosListMap.compat_intersect)).
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
    (build_rule_set 1000 monoid monoid).

Definition monoid_rule_set :=
  Eval vm_compute in
    (build_rule_set 1000 (PositiveInstantiation.filter_eqn_rules monoid) monoid).

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
    (build_rule_set 1000 monoid_ex1 monoid_ex1).

Definition monoid_ex1_base :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PosListMap.compat_intersect) 1000 monoid_ex1_rule_set (Mret false) 0
       (empty_egraph _ _))).
      
Definition monoid_ex1_graph :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PosListMap.compat_intersect) 1000 monoid_rule_set_full (Mret false) 2
       monoid_ex1_base)).
(*TODO: seems to work!
Definition monoid_ex1_graph' :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PosListMap.compat_intersect) monoid_rule_set (Mret false) 2
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

#[local] Definition tries :=
      Eval vm_compute in
      (unwrap_with_default (fst (run_query' monoid_rule_set_full 0 monoid_ex1_graph))).

Definition ne_firstn {A} n (l : ne_list A) : ne_list A :=
  (fst l, firstn n (snd l)).

(*
Compute (intersection_keys string _ (@PosListMap.compat_intersect)
           (ne_firstn 0 tries)).
Compute (intersection_keys string _ (@PosListMap.compat_intersect)
           (ne_firstn 1 tries)).

Compute (map.tuples (PosListMap.proj_node_map
           (PosListMap.compat_intersect (fun _ _ : unit => tt)
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
Import PosListMap.
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


Eval vm_compute in
    (map (uncurry (rule_to_log_rule (string_trie_map)
                     (@StringListMap.string_list_trie_map)
                     StringListMap.string_succ "sort_of"
                     logic (analysis_result:=unit) 1000)) logic).

(*TODO: foo, bar rules not simplified.

  !! "#0" = "#",
"#4" = "#1",
"#6" = "#",
 "#3" = "#", 
 "T" -> "#1" :-
 "sort_of" "" -> "#",
 "sort_of" "#1" -> "#", 
           "S" -> "#",
 "-" "" -> "#1",
 "F" -> "";


 *)

Definition logic_rule_set_full :=
  Eval vm_compute in
    (build_rule_set 1000 logic logic).

Definition logic_rule_set :=
  Eval vm_compute in
    (build_rule_set 1000 (PositiveInstantiation.filter_eqn_rules logic) logic).
(*TODO: is the optimization not working? multiple S write clauses.
  answer: no, since optimization doesn't handle existential vars.
  
 *)

Definition logic_ex1_base :=
  Eval vm_compute in
    (snd (saturate_until string_succ "v0"
       (@PosListMap.compat_intersect) 1000 logic_rule_set_full (Mret false) 1
       (empty_egraph _ _))).
Compute (map (fun '(x,y) => (x, map.tuples y)) (map.tuples logic_ex1_base.(db))).
Compute (filter (fun p => negb (eqb (fst p) (snd p)))
           (map.tuples monoid_ex1_base.(equiv).(UnionFind.parent _ _ _))).

Definition logic_ex1_graph :=
  Eval native_compute in
    (snd (saturate_until string_succ "v0"
       (@PosListMap.compat_intersect) 1000 logic_rule_set (Mret false) 5
       logic_ex1_base)).
(*TODO: why no unifications?*)
Compute (filter (fun p => negb (eqb (fst p) (snd p)))
           (map.tuples monoid_ex1_base.(equiv).(UnionFind.parent _ _ _))).

Require Import BinNums Defs.
Import PosListMap.
Instance my_analysis {V} : analysis V V _ := weighted_depth_analysis (fun _ => Some xH).
Require Tools.UnElab.


  Arguments Defs.run1iter {idx}%type_scope {Eqb_idx} idx_succ%function_scope 
  idx_zero {symbol}%type_scope {symbol_map}%function_scope symbol_map_plus
  {idx_map}%function_scope idx_map_plus {idx_trie}%function_scope {analysis_result}%type_scope 
  {H} spaced_list_intersect%function_scope rebuild_fuel%nat_scope rs _.

Ltac egraph rn n :=
      lazymatch goal with
        |- eq_term ?l ?c ?t ?e1 ?e2 =>
          let l' := constr:(ctx_to_rules c ++ l) in
          let rs := constr:(StringInstantiation.build_rule_set rn
                              (PositiveInstantiation.filter_eqn_rules l') l') in
          
        let result := (eval vm_compute in
                        (StringInstantiation.egraph_equal (X:= option positive) (*V:=string*) l' rs rn n c e1 e2 t)) in
          let result' := eval vm_compute in
          (Defs.run1iter string_succ "v0" string_ptree_map_plus string_ptree_map_plus
             (@compat_intersect) 0 rs (snd result)
          ) in
        lazymatch result with
        | (?b, ?g (*, ?r *)) =>
            (*
            (*TODO: how to extract and then rename?*)
            let lp_and_r' := constr:((rename_lang (ctx_to_rules c ++ l) r)) in
            let e1p := constr:(rename_term (var_to_con e1) (snd lp_and_r')) in
             *)
            (*
            let p :=
              (eval native_compute in (
                  let (x1,g0) := add_open_term Pos.succ sort_of (fst lp_and_r')
                                   [] (fst e1p) g in
                  (x1,extract_weighted subst_weight 1000 g0 x1)
              ))
            in
            match p with
            | (?x1,?e1') =>*)
       (* let assign := eval vm_compute in (fst (run_query (@PosListMap.compat_intersect) rw1 7 g)) in*)
            pose (GoalDisplay.lie_to_user (real:=g) tt) as graph;
            let rs' := eval vm_compute in
            (named_map map.tuples (map.tuples rs.(query_clauses _ _ _ _)),
              rs.(compiled_rules _ _ _ _)
            ) in
            pose (GoalDisplay.lie_to_user (real:=rs) tt) as rws;
           
                 (*pose (lie_to_user (real:=rw1) tt) as rules;*)
                 idtac b (*"! Also," e1 "became" e1' "with id" x1
        end*)
         
        | _ => fail "ill-formed!"
        end
      end.

Definition print_egraph {X} (g : instance string string string_trie_map string_trie_map string_list_trie_map X) :=
  (named_map (named_map (entry_value _ X)) (named_map map.tuples (map.tuples g.(db))),
    map.tuples g.(equiv).(parent _ _ _)).

    (*TODO: debug rules?*)
(* TODO: think about variable order for query performance

   TODO: extract now takes all of my ram.
 *)
(*
Goal eq_term logic {{c  "a": #"S", "b" : #"S" }}
  {{s #"S" }}
  {{e #"/\" (#"/\" (#"-" #"F") "b") "a" }}
  {{e #"/\" "b" (#"/\" "a" "a") }}.
 *)

Ltac print_rules :=
 
lazymatch goal with
  |- eq_term ?l ?c ?t ?e1 ?e2 =>
    let l' := constr:(ctx_to_rules c ++ l) in
    let r :=  eval vm_compute in
    (map (uncurry (rule_to_log_rule (string_trie_map)
                     (@StringListMap.string_list_trie_map)
                     StringListMap.string_succ "@sort_of"
                     l' (analysis_result:=unit) 1000)) (PositiveInstantiation.filter_eqn_rules l')) in
        idtac r
end.


Goal eq_term logic {{c  "a": #"S", "b" : #"S" }}
  {{s #"S" }}
  {{e #"/\" (#"/\" (#"-" #"F") "b") "a" }}
  {{e #"/\" "b" (#"/\" "a" "a") }}.


  egraph 1000 10.
  Compute (map.get graph.(analyses _ _ _ _ _ _) "#9").
  (*TODO: 9 can be xO xH here, why is it xI xH?*)
  (* issue: 9 different after 2nd iter, not updated in db,
     but 5 does get updated correctly
   *)
  
  Compute (print_egraph graph).
  Compute (map.tuples graph.(parents)).
  Compute  (named_map map.tuples (map.tuples (graph.(db)))).
  Compute (analyze _ _ _ (analysis:= my_analysis)
             (Build_atom "/\" ["#10"; "#5"] "#9") [Some xH; Some xH]).

  (*(*TODO: extraction is broken*)
  TODO: is the analysis not updated in order to not update the epoch?.
  Need an analysis rebuilding.
  Probably best to keep separate since it's strictly simpler tha ngeneral rebuilding.
  idea: after an analysis update, make sure to update parents.

  Is this the problem?.
  wouldn't this mean that the top-level analyses aren't updated?.
  but the problem is that they are out of sync*)
  Import coqutil.Datatypes.Result.
  lazymatch goal with
  |- eq_term ?l ?c ?t ?e1 ?e2 =>
    let l' := constr:(ctx_to_rules c ++ l) in
    
  let e' := eval vm_compute in
  (let (x1,g0) := add_open_term StringListMap.string_succ
                    StringListMap.sort_of l' true
                    [] (var_to_con e1) graph in
   let (x2,g1) := add_open_term StringListMap.string_succ
                    StringListMap.sort_of l' true
                    [] (var_to_con e2) graph in
   let ex1 := extract_weighted g0 1000 x1 in
   let ex2 := (extract_weighted g1 1000 x2) in
   existT id _ ((of_Success ex1), x1, (of_Success ex2), x2)) in
    idtac e'
  end.
  (*
  Compute (print_egraph graph).
  Compute (map.tuples graph.(parents)).
*)
  (*TODO: did something get unioned the wrong way? 7 still has its parents, as does 10.
  the 7,9 union should have merged them*)
  Compute (print_egraph graph).
  Compute (map.tuples graph.(parents)).
  Compute graph.(worklist).
  Compute (map.tuples graph.(parents)).

  Compute (print_egraph (snd (rebuild 100 graph))).
  (*
  TODO: rebuild doesn't do anything when it should; 7 non-canonical.
  Note: wrong, but might be harmless?
  TODO: not fully rebuilt!!!
          TODO: sort of 7 is 10. what is 10?.
  Note: above will be resolved on full rebuilding
              *)
print_rules.
(*TODO: still have bug on T rule*)
  pose (
   (!! "#1" = "#2", "@sort_of" "#2" -> "" :- "/\" "#1" "#" -> "#2", "S" -> "", 
     "F" -> "#1", "@sort_of" "#" -> "")%log) as seq.
  

  (* TODO: issue not with filter! why is there no #2 in the conclusion eqs?
     where did #2 come from? did something not do a proper subst?
   *)
  Compute (QueryOpt.optimize_sequent string string_Eqb
      StringListMap.string_succ string_default string
      StringListMap.string_trie_map StringListMap.string_trie_map
      StringListMap.string_list_trie_map seq 1000).
  Compute (QueryOpt.opt_verbose string string_Eqb
      StringListMap.string_succ string_default string
      StringListMap.string_trie_map StringListMap.string_trie_map
      StringListMap.string_list_trie_map seq 1000).
  
  
  Compute (QueryOpt.opt_live_eqn string string_Eqb
      StringListMap.string_succ string_default string
      StringListMap.string_trie_map StringListMap.string_trie_map
      StringListMap.string_list_trie_map seq 1000 "#1" "#0").

  Compute (QueryOpt.opt_conclusion_atoms string string_Eqb
      StringListMap.string_succ string_default string
      StringListMap.string_trie_map StringListMap.string_trie_map
      StringListMap.string_list_trie_map seq 1000).
  (*
  [{| atom_fn := "@sort_of"; atom_args := ["#2"]; atom_ret := "" |};
        {| atom_fn := "@sort_of"; atom_args := ["#"]; atom_ret := "" |};
        {| atom_fn := "F"; atom_args := []; atom_ret := "#0" |};
        {| atom_fn := "S"; atom_args := []; atom_ret := "" |};
        {| atom_fn := "/\"; atom_args := ["#"; "#0"]; atom_ret := "#2" |}] *)
  assert (QueryOpt.opt_assumption_atoms string string_Eqb
      StringListMap.string_succ string_default string
      StringListMap.string_trie_map StringListMap.string_trie_map
      StringListMap.string_list_trie_map seq 1000 = []).

  {
    unfold opt_assumption_atoms.
Definition focus {A} (a:A) : Prop := False.
Opaque focus.
(*
  
  TODO: error! reflexivity for #2 not included in assumptions!.
  How is that possible w/ atom /\ 1 # -> 2?
     = [{| atom_fn := "@sort_of"; atom_args := ["#"]; atom_ret := "" |};
        {| atom_fn := "F"; atom_args := []; atom_ret := "#1" |};
        {| atom_fn := "S"; atom_args := []; atom_ret := "" |};
        {| atom_fn := "/\"; atom_args := ["#"; "#1"]; atom_ret := "#2" |}]

    = [{| atom_fn := "@sort_of"; atom_args := ["#"]; atom_ret := "" |};
        {| atom_fn := "F"; atom_args := []; atom_ret := "#1" |};
        {| atom_fn := "S"; atom_args := []; atom_ret := "" |};
        {| atom_fn := "/\"; atom_args := ["#"; "#1"]; atom_ret := "#2" |};
        {| atom_fn := "@sort_of"; atom_args := ["#2"]; atom_ret := "" |};
        {| atom_fn := "@sort_of"; atom_args := ["#"]; atom_ret := "" |};
        {| atom_fn := "F"; atom_args := []; atom_ret := "#0" |};
        {| atom_fn := "S"; atom_args := []; atom_ret := "" |};
        {| atom_fn := "/\"; atom_args := ["#"; "#0"]; atom_ret := "#2" |}]
    : list (atom string string)

               = !! "#1" = "#0", "@sort_of" "#2" -> "" :- "/\" "#1" "#" -> "#2", 
          "S" -> "", "F" -> "#1", "@sort_of" "#" -> ""
  
  Compute (QueryOpt.opt_known_atoms string string_Eqb
      StringListMap.string_succ string_default string string_Eqb
      StringListMap.string_trie_map StringListMap.string_trie_map
      string_ptree_map_plus
      StringListMap.string_list_trie_map seq).
  TODO: issue w/ /\ false rule:
      wrong unification. (1,0) should be (1,2).
   Issue in erule compilation, specifically optimization
  {|
    query_vars := [""; "#2"; "#"; "#1"];
    query_clause_ptrs :=
      ({| query_ptr_symbol := "@sort_of"; query_ptr_ptr := ""; query_ptr_args := [""; "#"] |},
       [{| query_ptr_symbol := "F"; query_ptr_ptr := ""; query_ptr_args := ["#1"] |};
        {| query_ptr_symbol := "S"; query_ptr_ptr := ""; query_ptr_args := [""] |};
        {| query_ptr_symbol := "/\"; query_ptr_ptr := "#"; query_ptr_args := ["#2"; "#"; "#1"] |}]);
    write_vars := ["#0"];
    write_clauses := [{| atom_fn := "@sort_of"; atom_args := ["#2"]; atom_ret := "" |}];
    write_unifications := [("#1", "#0")]
  |};
   !! "#1" = "#2", "@sort_of" "#2" -> "" :- "/\" "#1" "#" -> "#2", "S" -> "", 
    "F" -> "#1", "@sort_of" "#" -> "";
  
Compute (named_map (named_map (entry_value _ _))
           (named_map map.tuples (map.tuples (graph.(db))))).
(*TODO: still broken
  ([("@sort_of", [("", ([1], 0))]); ("T", [("", ([], 0))]); ("F", [("", ([], 0))]);
  ("-", [("", ([1], 0))]); ("S", [("", ([], 0))]); ("/\", [("#", ([1; 2], 0)); ("", ([1; 1], 0))])],*)


lazymatch goal with
  |- eq_term ?l ?c ?t ?e1 ?e2 =>
    let l' := constr:(ctx_to_rules c ++ l) in
    let r :=  eval vm_compute in
    (map (uncurry (rule_to_log_rule (string_ptree_map_plus)
                     (@StringListMap.string_list_trie_map)
                     StringListMap.string_succ "@sort_of"
                     l' (analysis_result:=unit))) (filter_eqn_rules l')) in
        idtac r
end.
  
([("@sort_of", [("", ([1], 0))]); ("T", [("", ([], 0))]); ("F", [("", ([], 0))]);
  ("-", [("", ([1], 0))]); ("S", [("", ([], 0))]); ("/\", [("#", ([1; 2], 0)); ("", ([1; 1], 0))])],

                                  
                                  {|
    query_vars := [""; "#2"; "#"; "#1"];
    query_clause_ptrs :=
      ({| query_ptr_symbol := "@sort_of"; query_ptr_ptr := ""; query_ptr_args := [""; "#"] |},
       [{| query_ptr_symbol := "T"; query_ptr_ptr := ""; query_ptr_args := ["#1"] |};
        {| query_ptr_symbol := "S"; query_ptr_ptr := ""; query_ptr_args := [""] |};
        {| query_ptr_symbol := "/\"; query_ptr_ptr := "#"; query_ptr_args := ["#2"; "#"; "#1"] |}]);
    write_vars := [];
    write_clauses := [];
    write_unifications := [("#1", ""); ("#", "#2")]
                                  |};
#1 = "", # = #2
 :-
 sort_of # -> "".
 T -> #1.
 S -> "".
 /\ #1 # -> #2.
                
*)

 
Compute (*(named_map (named_map (entry_value _ _))*)
           (named_map map.tuples (map.tuples (graph.(db)))).
(*TODO: fires when T in the LHS of /\.
  Could this be a bug w/ dead var eqns on the write side?
 *)

(*
lazymatch goal with
  |- eq_term ?l ?c ?t ?e1 ?e2 =>
    let l' := constr:(ctx_to_rules c ++ l) in
    let r :=  eval vm_compute in
    (map (uncurry (rule_to_log_rule (@StringListMap.string_trie_map)
                     (@StringListMap.string_list_trie_map)
                     StringListMap.string_succ "@sort_of"
                     l' (analysis_result:=unit))) (filter_eqn_rules l')) in
        idtac r
end.
lazymatch goal with
  |- eq_term ?l ?c ?t ?e1 ?e2 =>
    let l' := constr:(ctx_to_rules c ++ l) in
    
  let e' := eval vm_compute in
  (let (x0,g0) := add_open_term StringListMap.string_succ
                    StringListMap.sort_of l' true
                    [] (var_to_con e1) graph in
  let (x1,g1) := add_open_term StringListMap.string_succ
                    StringListMap.sort_of l' true
                    [] (var_to_con e1) graph in
   (unwrap_with_default (extract_weighted g0 1000 x0),
     unwrap_with_default (extract_weighted g1 1000 x1))) in
    idtac e'
end.
*)

(*
 !! "#0" = "", "#1" = "#2", "#3" = "", "@sort_of" "#2" -> "" :- 
    "/\" "#1" "#" -> "#2", "S" -> "", "F" -> "#1", "@sort_of" "#" -> "";
 Check code path  for 0 = ""
 !! "#0" = "", "#" = "#2" :- "/\" "#1" "#" -> "#2", "S" -> "", 
    "T" -> "#1", "@sort_of" "#" -> "";
 *)
Compute (*(named_map (named_map (entry_value _ _))*)
           (named_map map.tuples (map.tuples (graph.(db)))).
                     
Compute (map.tuples graph.(equiv).(parent _ _ _)).

(*TODO: why false?
  
 *)
Compute (fst (egraph_sort_of StringListMap.string_succ "@sort_of" "" "#5" graph)).

(*TODO: issue: unified T and S! why?*)
Compute (eq_proven StringListMap.string_succ "@sort_of" "" ""
           "#5" graph).


Abort.
