Set Implicit Arguments.

(*TODO: clean up imports*)
Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
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


Definition print_egraph {X} (g : instance string string string_trie_map string_trie_map string_list_trie_map X) :=
  (NamedList.named_map (NamedList.named_map (entry_value _ X)) (NamedList.named_map map.tuples (map.tuples g.(db))),
    map.tuples g.(equiv).(UnionFind.parent _ _ _)).


Definition subst_weight (r : renaming string) (a : atom positive positive) :=
  if inb (map.get (p_to_v r) a.(atom_fn))
       [Some "val_subst"; Some "blk_subst"] then Some 20%nat
  else Some (length a.(atom_args)).

Definition filter_rules := fun V : Type =>
filter
  (fun pat : V * Rule.rule V =>
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
 *)
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

Ltac egraph rule_transform n :=
      lazymatch goal with
        |- eq_term ?l ?c ?t ?e1 ?e2 =>
          let l' := constr:(ctx_to_rules c ++ l) in
          let rs := constr:(StringInstantiation.build_rule_set
                              (rule_transform l') l') in
        let result := (eval vm_compute in
                        (StringInstantiation.egraph_equal (X:= option (term string)) (*V:=string*) l' rs n c e1 e2 t)) in
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



(*******************************
 Extraction facilities.

Operations on the same egraph should use a single `weight` paremeter.
Weight is a function from atoms (representing a single level of an AST) to values in the range [0,oo],
representing infinity as None, where a value of infinity means that term will never be extracted.

 *******************************)
Import StringInstantiation.

Notation instance := (instance string string string_trie_map string_trie_map string_list_trie_map (option positive)).

Notation empty_egraph := (empty_egraph (idx:=string) default (symbol:=string)).

Definition add_ctx weight l :=
  add_ctx (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition add_open_term weight l :=
  add_open_term (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition rebuild weight fuel : state instance _ := (rebuild (idx:=string) fuel (symbol:=string) (H:=weighted_depth_analysis weight)).

Notation extract_weighted := (extract_weighted (V:=string) (V_map:=string_trie_map) (V_trie:=string_list_trie_map)).

