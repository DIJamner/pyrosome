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

(*
Instance my_analysis : analysis string string (option positive) :=
  weighted_depth_analysis (fun a => if inb a.(atom_fn) ["val_subst"; "blk_subst"]
                                    then Some 20
                                    else Some 1 (*(length a.(atom_args))) *) ).

Instance full_term_analysis : analysis string string (option (term string)) :=
  {
    analyze a r :=
      (@! let args <- option_all r in
        ret con a.(atom_fn) args);
    analysis_meet r1 r2 :=
    match r1, r2 with
    | None, _ => r2
    | _, None => r1
    | Some e, Some e' =>
        if Pos.ltb (term_depth e) (term_depth e')
        then Some e else Some e'
    end;
  }.
*)

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
Admitted.

Ltac egraph rule_transform n :=
      lazymatch goal with
        |- eq_term ?l ?c ?t ?e1 ?e2 =>
          let l' := constr:(ctx_to_rules c ++ l) in
          let rs := constr:(StringInstantiation.build_rule_set
                              1000 (rule_transform l') l') in
        let result := (eval vm_compute in
                        (StringInstantiation.egraph_equal (*V:=string*) l' rs n c e1 e2 t)) in
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
       (* let assign := eval vm_compute in (fst (run_query (@PositiveInstantiation.compat_intersect) rw1 7 g)) in*)
            pose (lie_to_user (real:=g) tt) as graph;
           
              pose (lie_to_user (real:=rs) tt) as rules;
                 idtac b (*"! Also," e1 "became" e1' "with id" x1
        end*)
         
        | _ => fail "ill-formed!"
        end
    end.
    (*TODO: debug rules?*)
(* TODO: think about variable order for query performance

 *)


(*
Lemma egraph_simpl2_sound
  : forall (rebuild_fuel cap fuel efuel : nat) (l : lang string)
           (c : named_list string (sort string)) t e1 e2 e1' e2' debug
           weights,
       wf_lang l ->
       wf_ctx (Model:= core_model l) c ->
       wf_term l c e1 t ->
       wf_term l c e2 t ->
       Defs.PositiveInstantiation.egraph_simpl2'_progressive
         (H1:= weighted_depth_analysis weights)
         l rebuild_fuel cap fuel efuel c e1 e2 = (e1',e2', debug) ->
       eq_term l c t e1' e2'->
       eq_term l c t e1 e2.
Admitted. *)

(*TODO: remove the need for cap? *)
(* TODO: make injective-aware version
   TODO: currently broken
 *)
(*
Ltac egraph_simpl2 cap :=
    compute_eq_compilation;
    eapply (egraph_simpl2_sound 100 cap 100 100);
    [prove_from_known_elabs| shelve | shelve | shelve | vm_compute; reflexivity | ].*)

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
