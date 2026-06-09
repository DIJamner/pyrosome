(* The positive-index engine for type inference.

   Tools/EGraph/TypeInference builds elaboration problems over strings (so it
   can gensym readable hole names), but running the actual e-graph saturation
   over strings uses the slow string tries.  This file provides the e-graph
   computation specialized to [positive] indices (mirroring
   Defs.PositiveInstantiation), so that TypeInference can rename a built
   problem into positives, saturate here, and unrename the result. *)
Set Implicit Arguments.

From Stdlib Require Import Lists.List NArith.BinNat Strings.String.
Import ListNotations.
Open Scope list.

From coqutil Require Import Map.Interface Datatypes.Result.
From Utils Require Import Utils Monad.
From Utils Require Import TrieMap PosListMap FullPosTrie FullPosTrieConv.
From Utils.EGraph Require Import Semantics Defs QueryOpt.
From Utils Require Import UnionFind.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Tools.EGraph Require Import Defs.
Import StateMonad.
Import PArith.
Open Scope positive.

Notation atom := (atom positive positive).
Notation instance := (instance positive positive trie_map trie_map
                        (@FullPosTrie.full_pos_trie_map) (option positive)).
Notation sequent := (sequent positive positive).

Local Notation term := (@Term.term positive).
Local Notation sort := (@Term.sort positive).
Local Notation ctx := (@Term.ctx positive).
Local Notation rule := (@Rule.rule positive).
Local Notation lang := (@Rule.lang positive).
Local Notation named_list := (@named_list positive).

(* The special [sort_of] symbol: [xH], exactly as in Defs.PositiveInstantiation
   (which egraph_sound / egraph_reducing_equal' use).  We deliberately share
   their positive instantiation so type inference and the soundness path run
   the *same* compiled rules. *)
Local Notation sort_of := PosListMap.sort_of.

(* Build the extraction weight from a "is this symbol a hole" predicate.
   Holes (and the [sort_of] symbol) get infinite weight (None) so that
   extraction never picks them; everything else gets weight 1.  This mirrors
   TypeInference's string [weight], where holes are the "?"-prefixed names. *)
Definition mk_weight (is_hole : positive -> bool) : atom -> option positive :=
  fun a =>
    if Pos.eqb a.(atom_fn) sort_of then None
    else match a.(atom_args) with
         | [] => if is_hole a.(atom_fn) then None else Some 1
         | _ => Some 1
         end.

Section WithWeight.

  (* The extraction weight.  Supplied by the caller (TypeInference) since it
     depends on which renamed positives are holes. *)
  Context (weight : atom -> option positive).

  Definition empty_egraph : instance :=
    Defs.empty_egraph (idx:=positive) (default:positive) (symbol:=positive)
      (symbol_map:=trie_map) (idx_map:=trie_map)
      (idx_trie:=(@FullPosTrie.full_pos_trie_map)) (option positive).

  Definition add_open_term (l : lang) :=
    Defs.add_open_term (V:=positive) (V_map:=trie_map) Pos.succ sort_of l
      (H:=weighted_depth_analysis weight) true.

  Definition add_open_sort (l : lang) :=
    Defs.add_open_sort (V:=positive) (V_map:=trie_map) Pos.succ sort_of l
      (H:=weighted_depth_analysis weight) true.

  Definition update_entry (a : atom) : state instance unit :=
    Defs.update_entry (idx:=positive) (symbol:=positive)
      (H:=weighted_depth_analysis weight) a.

  (* Add a term with holes, and assert that its sort is [sort_id]. *)
  Definition add_elab_term (l : lang) (e : term) (sort_id : positive)
    : state instance positive :=
    @! let t_id <- add_open_term l true [] e in
      let _ <- update_entry (Build_atom sort_of [t_id] sort_id) in
      ret t_id.

  Notation extract_weighted :=
    (extract_weighted (V:=positive) (V_map:=trie_map)
       (V_trie:=(@FullPosTrie.full_pos_trie_map))).

  (* The constant rules of [l] (those with empty context), compiled to
     sequents.  Mirrors TypeInference.const_rules but over positives. *)
  Definition const_rules (l : lang) : list sequent :=
    flat_map (fun '(n,r) =>
                match rule_to_log_rule trie_map _ Pos.succ sort_of l
                        (analysis_result:=unit) 1000%nat n r with
                | Result.Success s => [s]
                | Result.Failure _ => []
                end)
      (filter (fun '(n,r) => inclb (get_ctx r) []) l).

  (* Run the saturation, given the language [l] and the precompiled injection
     sequents [inj_seqs].  Mirrors TypeInference.state_operation. *)
  Definition state_operation (l : lang) (inj_seqs : list sequent)
    : state instance bool :=
    (* epoch leb [Pos.leb]: proper semi-naive evaluation, which is complete and
       more efficient.  (The string engine runs naive only because string_succ's
       little-endian suffix has no cheap <=; positive has a real order.) *)
    @saturate_until positive Pos.eqb Pos.succ (default (A:=positive))
      Pos.leb
      positive trie_map ptree_map_plus trie_map ptree_map_plus
      (@FullPosTrie.full_pos_trie_map) (option positive)
      (weighted_depth_analysis weight) (@fpt_spaced_intersect)
      1000%nat
      0%nat (* window *)
      (@QueryOpt.build_rule_set positive Pos.eqb Pos.succ (default (A:=positive))
         positive trie_map ptree_map_plus trie_map
         (@FullPosTrie.full_pos_trie_map) 1000%nat
         (inj_seqs ++ const_rules l))
      (Mret false) 1000%nat.

  (* ---- decoding ---- *)

  Fixpoint con_to_var (context : ctx) (t : term) : term :=
    match t with
    | con name [] =>
        if (inb name (map fst context)) then (var name) else t
    | con name subterms => con name (map (con_to_var context) subterms)
    | _ => t
    end.

  Definition result_to_term (r : Result.result term) : term :=
    match r with
    | Result.Success t => t
    | _ => default
    end.

  Definition term_to_sort (t : term) : sort :=
    match t with
    | var x => scon x []
    | con n s => scon n s
    end.

  Definition decode_term (context : ctx) (graph : instance) (t_id : positive) : term :=
    con_to_var context (result_to_term (extract_weighted graph 1000%nat t_id)).

  Definition decode_sort (context : ctx) (graph : instance) (t_id : positive) : sort :=
    term_to_sort (decode_term context graph t_id).

  Fixpoint decode_ctx (graph : instance) (ids : named_list positive) : ctx :=
    match ids with
    | [] => []
    | (x,x_id)::ids =>
        let context := decode_ctx graph ids in
        (x, decode_sort context graph x_id)::context
    end.

  (* What the caller wants to add/decode for a rule. *)
  Variant payload :=
    | pp_sort
    | pp_term (t : sort)
    | pp_sort_eq (t1 t2 : sort)
    | pp_term_eq (e1 e2 : term) (t : sort).

  Variant decoded :=
    | pd_sort (c : ctx)
    | pd_term (c : ctx) (t : sort)
    | pd_sort_eq (c : ctx) (t1 t2 : sort)
    | pd_term_eq (c : ctx) (e1 e2 : term) (t : sort).

  Variant rule_ids :=
    | id_sort (c_ids : named_list positive)
    | id_term (c_ids : named_list positive) (t_id : positive)
    | id_sort_eq (c_ids : named_list positive) (t1_id t2_id : positive)
    | id_term_eq (c_ids : named_list positive) (e1_id e2_id t_id : positive).

  (* Add the context sorts and the rule payload to the egraph. *)
  Definition build_to_egraph (l : lang) (ctx_holes : named_list sort)
    (p : payload) : state instance rule_ids :=
    @! let c_ids <- list_Mmap (fun '(n,s) =>
                                 @! let x <- add_open_sort l true [] s in
                                   ret (n, x)) ctx_holes in
      match p with
      | pp_sort => @! ret (id_sort c_ids)
      | pp_term t =>
          @! let t_id <- add_open_sort l true [] t in
            ret (id_term c_ids t_id)
      | pp_sort_eq t1 t2 =>
          @! let t1_id <- add_open_sort l true [] t1 in
            let t2_id <- add_open_sort l true [] t2 in
            ret (id_sort_eq c_ids t1_id t2_id)
      | pp_term_eq e1 e2 t =>
          @! let t_id <- add_open_sort l true [] t in
            let e1_id <- add_elab_term l e1 t_id in
            let e2_id <- add_elab_term l e2 t_id in
            ret (id_term_eq c_ids e1_id e2_id t_id)
      end.

  Definition decode_rule (graph : instance) (ids : rule_ids) : decoded :=
    match ids with
    | id_sort c_ids => pd_sort (decode_ctx graph c_ids)
    | id_term c_ids t_id =>
        let c := decode_ctx graph c_ids in
        pd_term c (decode_sort c graph t_id)
    | id_sort_eq c_ids t1_id t2_id =>
        let c := decode_ctx graph c_ids in
        pd_sort_eq c (decode_sort c graph t1_id) (decode_sort c graph t2_id)
    | id_term_eq c_ids e1_id e2_id t_id =>
        let c := decode_ctx graph c_ids in
        let t := decode_sort c graph t_id in
        pd_term_eq c (decode_term c graph e1_id) (decode_term c graph e2_id) t
    end.

  (* The whole pipeline: build, saturate, decode. *)
  Definition run_infer (l : lang) (inj_seqs : list sequent)
    (ctx_holes : named_list sort) (p : payload) : decoded :=
    let comp : state instance rule_ids :=
      @! let ids <- build_to_egraph l ctx_holes p in
        let _ <- state_operation l inj_seqs in
        ret ids
    in
    let (ids, g) := comp empty_egraph in
    decode_rule g ids.

  (* Compiler-case entry points: the decoding context [c'] is given (the
     already-compiled target context), rather than inferred.  Mirrors
     TypeInference.infer_compiler_case_simple's egraph step. *)
  Definition run_compile_sort (l : lang) (inj_seqs : list sequent)
    (c' : ctx) (t : sort) : sort :=
    let comp : state instance positive :=
      @! let x <- add_open_sort l true [] t in
        let _ <- state_operation l inj_seqs in
        ret x
    in
    let (x, g) := comp empty_egraph in
    decode_sort c' g x.

  Definition run_compile_term (l : lang) (inj_seqs : list sequent)
    (c' : ctx) (t_sort : sort) (e : term) : term :=
    let comp : state instance positive :=
      @! let t_id <- add_open_sort l true [] t_sort in
        let x <- add_elab_term l e t_id in
        let _ <- state_operation l inj_seqs in
        ret x
    in
    let (x, g) := comp empty_egraph in
    decode_term c' g x.

End WithWeight.
