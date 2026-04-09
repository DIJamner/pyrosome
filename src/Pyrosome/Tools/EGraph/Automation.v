Set Implicit Arguments.

(*TODO: clean up imports*)
Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Ltac Result.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

From Utils Require Import EGraph.Defs.
Require Import Pyrosome.Tools.EGraph.Defs.
Import PositiveInstantiation.
From coqutil Require Import Map.Interface.
Require Import Utils.Monad PosRenaming NArith.
Import StateMonad.
Require Import Tools.UnElab.
Import StringInstantiation.


From Pyrosome Require Import Tools.Matches.


Definition print_egraph {X} (g : instance string string string_trie_map string_trie_map string_list_trie_map X) :=
  (NamedList.named_map (NamedList.named_map (entry_value _ X)) (NamedList.named_map map.tuples (map.tuples g.(db))),
    map.tuples g.(equiv).(UnionFind.parent _ _ _)).


Definition subst_weight (r : renaming string) (a : atom positive positive) :=
  if inb (map.get (p_to_v r) a.(atom_fn))
       [Some "val_subst"; Some "blk_subst"] then Some 20%nat
  else Some (length a.(atom_args)).

Definition filter_rules :=
(fun pat : string * Rule.rule string =>
   match pat with
   | (_, term_rule _ _ _) => false
   | _ => true
   end).

Fixpoint term_depth (e : term string) :=
  match e with
  | var _ => 1
  | con _ l => 1 + (fold_left Pos.max (map term_depth l) 1)
  end.

Instance depth_analysis : analysis string string (option positive) :=
  weighted_depth_analysis (fun a => Some 1).

(*TODO: generalize what rules to run *)
Theorem egraph_sound
  (rebuild_fuel sat_fuel efuel red_fuel : nat) l filter
  reversible
  inj_rules
  (c : ctx string) t (e1 e2 : term string)
  : wf_lang l ->
    wf_ctx (Model:=core_model l) c ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    Is_Success (fst (egraph_reducing_equal' l filter reversible inj_rules rebuild_fuel sat_fuel efuel red_fuel c e1 e2)) ->
    eq_term l c t e1 e2.
Proof.
  intros ? ? ? ?.
  unfold egraph_reducing_equal'.
  (*TODO: verify renaming.*)
Admitted.

(* TODO: think about variable order for query performance

 *)

(*TODO: call Matches.t' or some other tactic to solve subgoals*)
Ltac by_reduction' reversible inj_rules :=
  (*TODO: check subsumed by egraph reduction
  try reduce;
   *)
    apply (egraph_sound 100 100 100 100 filter_rules reversible inj_rules);
    [prove_from_known_elabs| | | | flagged_exact I].


(* TODO: plug inj_rules into tactics *)
Definition empty_inj_rules : list (string * list string) := [].

Ltac by_reduction :=
  by_reduction' (fun _ : string * Rule.rule string => true) empty_inj_rules.

Ltac auto_elab_compiler' reversible inj_rules :=
  cleanup_elab_after
  setup_elab_compiler;
  repeat
     ([>repeat t; cleanup_elab_after try 
                    (try decompose_sort_eq; by_reduction' reversible inj_rules)
      | .. ]).

Ltac auto_elab_compiler :=
  auto_elab_compiler' (fun _ : string * Rule.rule string => true) empty_inj_rules.

(* for building filters from lists in tactics *)
Definition rule_named_in l :=
  (fun p : string * Rule.rule string => inb (fst p) l).

(*******************************
 Extraction facilities.

Operations on the same egraph should use a single `weight` paremeter.
Weight is a function from atoms (representing a single level of an AST) to values in the range [0,oo],
representing infinity as None, where a value of infinity means that term will never be extracted.

 *******************************)
Import StringInstantiation.

Notation instance := (instance string string string_trie_map string_trie_map string_list_trie_map (option positive)).

Definition empty_egraph := (empty_egraph (idx:=string) (default : string)
                              (symbol:=string) (symbol_map := string_trie_map)
                              (idx_map := string_trie_map) (option positive)).

Definition add_ctx weight l :=
  add_ctx (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition add_open_term weight l :=
  add_open_term (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition add_open_sort weight l :=
  add_open_sort (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition rebuild weight fuel : state instance _ := (rebuild (idx:=string) fuel (symbol:=string) (H:=weighted_depth_analysis weight)).

Notation extract_weighted := (extract_weighted (V:=string) (V_map:=string_trie_map) (V_trie:=string_list_trie_map)).
