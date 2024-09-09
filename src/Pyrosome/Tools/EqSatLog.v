(*
   Based on this paper, with some deviation:
   Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker,
   Eli Rosenthal, Zachary Tatlock, and Max Willsey. 2023.
   Better Together: Unifying Datalog and Equality Saturation.
   Proc. ACM Program. Lang. 7, PLDI, Article 125 (June 2023), 25 pages.
   URL: https://doi.org/10.1145/3591239
 *)
Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind FunctionalDB QueryOpt Monad.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ClosedTerm.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  
  Context 
      (V_map : forall A, map.map V A)
      (V_map_ok : forall A, map.ok (V_map A))
      (V_trie : forall A, map.map (list V) A).

  Notation instance := (instance V V V_map V_map V_trie).

  Notation atom := (atom V V).
  
  Record eqsat : Type := {
      inst : instance;
      (* TODO: maintain a separate sort map?
      sort_map : V_map V;*)
    }.

  Context (succ : V -> V).
  
  (* Include sort_of as special symbol/fn in db. *)
  Context (sort_of : V).


  (*
    TODO: compile rules to rw sets
    - IR: each term compiles to a set of clauses
    - IR clause-set-pairs compile to rw rules + lists of clauses (writer monad?)
    - rules plus deduped clause lists become rw sets
      + question: does dedup have to happen here? seems more like a query opt.
      + question: does query opt run on the IR or the target? IR makes more sense.
                  *TODO: move IR->target to functionaldb or query opt(this one)
   *)

  (*
Record
rw_set (idx symbol : Type) (symbol_map : forall A : Type, map.map symbol A)
  : Type := Build_rw_set
  { query_clauses : map.rep;  compiled_rules : list (compiled_rw_rule idx symbol) }.

    Record compiled_rw_rule (idx symbol : Type) : Type := Build_compiled_rw_rule
  { query_vars : list idx;
    query_clause_ptrs : ne_list (symbol * nat * list idx);
    write_clauses : list (FunctionalDB.atom idx symbol) }.
   *)


  
  Definition gensym {M} `{Monad M} : stateT V M V :=
    fun s => Mret (succ s, s).

  Definition writer S A : Type := list S * A.

  Instance writer_monad S : Monad (writer S) :=
    {
      Mret _ a := ([],a);
      Mbind _ _ f ma :=
        let '(l1,a) := ma in
        let '(l2,b) := f a in
        (l2++l1,b)
    }.

  Definition write {A} a : writer A unit :=
    ([a],tt).

  (* TODO: rework.
     1. no vars in eqsatlog; convert to closed terms via variable-> constant transformation.
     2. no type pointers in egraph? I think types can be inferred/checked w/out any explicit pointers,
        and eqns should not have to check types.
   *)
  
  Variant extended_clause :=
    | rel_clause : atom -> extended_clause
    (* useful? in the case that the rhs of e = e' is a variable*)
    | unif_clause : V -> V -> extended_clause.

  (*
    Translation of rewrite into query:
    G |- e1 ~> e2 : A
    xi : Bi |- e1 ~> e2 : scon nA aj

    becomes
    to_clauses(e2, kA) |-> k1 :- to_clauses(G)
                              /\ to_clauses(A) |-> kA
                              /\ to_clauses(e1, kA) |-> k1

   to_clauses(var x, kA) := lookup(x) |-> x /\ sort_of(x,kA) [keep var map around w/ gensym, alt. multiple passes]
   to_clauses(con n ei, kA) := node n ki |-> k /\ to_clauses(ei,rulectx) |-> ki /\ sort_of(k,kA)


   Important: should dedup the queries; performance critical
   To dedup: use hashcons w/ logic vars as ptrs (in other words: maintain a set of existing nodes)
   One thing to be careful of: bound vars on rhs of |->

   Semantics of cj(x1...xn)... :- ai(x1...xn)...:
   roughly: forall x1...xn such that ai ... , add cj ...
   Note: for xk where xk in fv(c) - fv(a), choose a default (fresh) value

   For a sound (but not complete) characterization,
   forall e1, e2. DB  + c1 ... cm |= e1 = e2 -> DB + c1...cm+1 |= e1 = e2;
   and, forall x1...xn, (forall i, DB + c1 ... cm |= ai) -> |- cm+1
   TODO: address delayed rebuilding; this characterization rebuilds on every +

   *)

  (*TODO: move to db*)
  Arguments Build_atom {idx symbol}%type_scope atom_fn atom_args%list_scope atom_ret.

  

  Definition rel_clause' x s r := rel_clause (Build_atom x s r).

  (*TODO: should work exclusively on closed terms for performance.
    Can use the bijection between clsoed and open terms.
   *)
  Fixpoint term_to_clauses (e : term) : stateT V (writer extended_clause) V :=
    match e with
    | con n s =>
        @! let s' <- list_Mmap term_to_clauses s in
          let ax <- gensym in
          let tt <- lift (write (rel_clause' n s' ax)) in
          ret ax
    end.

  (* Open terms are for patterns only.
     TODO: is this necessary? probably.
     Consider best archtecture to take advantage of query rebuilding.
   *)
  Fixpoint term_pat_to_clauses (e : Term.term V)
    : stateT V (writer extended_clause) V :=
    match e with
    | var x => Mret x (*assumes gensym doesn't hit vars*)
    | Term.con n s =>
        @! let s' <- list_Mmap term_pat_to_clauses s in
          let ax <- gensym in
          let tt <- lift (write (rel_clause' n s' ax)) in
          ret ax
    end.

  Definition sort_pat_to_clauses (t : sort)
    : stateT V (writer extended_clause) V :=
    match t with
    | scon n s =>
        @! let s' <- list_Mmap term_pat_to_clauses s in
          let ax <- gensym in
          let tt <- lift (write (rel_clause' n s' ax)) in
          ret ax
    end.

  Definition term_pat_to_clauses_known_ret (e : Term.term V) (retV : V)
    : stateT V (writer _) unit :=
    @! let e' <- term_pat_to_clauses e in
      (lift (write (unif_clause e' retV))).
  
  (*TODO: use writer that appends to the end or reverse *)
  Fail Fixpoint term_pat_to_upd (varmap : named_list V) (e : term)
    : stateT V (writer log_upd) V (* ret var *) :=
    match e with
    | var x => Mret (named_list_lookup default varmap x)
    | con n s =>
        @!let args <- list_Mmap (term_pat_to_upd varmap) s in
          let i <- gensym in
          let _ <- lift (write (let_row (Build_atom n args) i)) in
          let t := sort_of n s in
          let _ <- lift (write (put_row sort_of i t)) in
          ret i
    end.

  Definition clauses_of_extended_list : list extended_clause -> list atom :=
    flat_map (fun c => match c with rel_clause a => [a] | _ => [] end).
  
  Definition unifications_of_extended_list : list extended_clause -> list (V * V) :=
    flat_map (fun c => match c with unif_clause x y => [(x,y)] | _ => [] end).

  (*TODO: put in FunctionalDB.v*)
  
  Arguments atom_args {idx symbol}%type_scope a.
  Arguments atom_ret {idx symbol}%type_scope a.
  (*
  Arguments db {idx symbol}%type_scope {symbol_map idx_map}%function_scope i.
  Arguments unify {idx symbol}%type_scope _ _.
Arguments fold_updates {idx}%type_scope {Eqb_idx}
    {symbol}%type_scope {symbol_map idx_map}%function_scope
    (idx_succ)%function_scope {H3} has_changed%bool_scope (upd subs)%list_scope.
Arguments equiv {idx symbol}%type_scope {symbol_map idx_map}%function_scope i.
Arguments db {idx symbol}%type_scope {symbol_map idx_map}%function_scope i.
Arguments Build_instance {idx symbol}%type_scope {symbol_map idx_map}%function_scope db equiv.
Arguments union {idx}%type_scope {Eqb_idx idx_map rank_map} h x y.

Arguments rebuild {idx}%type_scope {Eqb_idx} {symbol}%type_scope {symbol_map idx_map}%function_scope i.

  (*TODO: put in QueryOpt*)
  (*TODO: should the fvs be included in a query or computed via these functions?*)
  Definition fvs_of_atom (a : atom) :=
    a.(atom_ret)::a.(atom_args).

  Definition fvs_of_clauses l :=
    List.dedup (eqb (A:=_)) (flat_map fvs_of_atom l).
  
  Arguments db_to_clauses {idx symbol}%type_scope {symbol_map idx_map}%function_scope _.
  Arguments clauses_to_db {idx}%type_scope {Eqb_idx}
    {symbol}%type_scope {symbol_map idx_map}%function_scope
    {idx_default} clauses%list_scope.

  (*TODO: order vars better*)
  Definition db_to_query (i : instance) : query _ _ :=
      let clauses := db_to_clauses i.(db) in      
      Build_query _ _ (fvs_of_clauses clauses) clauses.

  (*TODO: what to do if union returns none?
   *)
  Definition inst_unify (i:instance) '(x,y) :=
    match union i.(equiv) x y with
    | Some (equiv',_) => Build_instance i.(db) equiv'
    | None => i
    end.
  
  Definition extended_list_to_query l : query _ _ :=
    let i := clauses_to_db (clauses_of_extended_list l) in
    let i1 := fold_left inst_unify (unifications_of_extended_list l) i in
    let i2 := rebuild i1 in
    db_to_query i2.

  *)

  (*******************************************)
  
  (*Extraction sketches*)
  (*
    Extraction is about finding a (least-weight) tree in a graph,
    starting from a given root.
    Specifically, a tree such that each leaf is a valid leaf node.
    (in the egraph case, a 0-argument node, i.e. a node with no out edges)

    restatement: lowest-weight 'full' tree, where a full tree is not a prefix of any other tree.
    Dyn prog?
    compute lowest-weight 'full' tree for all nodes.
    go by node arity?
    for each node, compute the lwft from its children's lwfts if all exist, save weight.
    If not all children have lwfts, move to reserve worklist.
    once worklist is empty, switch to reserve if it is shorter than the starting worklist.
    Repeat.

    Define weight as the sum of node weights

    Idea:
    - maintain extraction incrementally w/ egraph
    - as table in db? (requires finer-grain control over what columns are up to equivalence)
    - requires proper node indexing (can't forget original node ids)

    Supporting syntactic analyses:
    for each table/symbol, maintain a legend of which inputs/outputs are semantic,
    i.e. congruent wrt equivalence
    Issue: how to merge outputs that are syntacitc?
    answer: need merge defined; e.g. for extraction, use weight ordering
    in other words: can weaken requirements to lattice instead of UF (mentioned in egg papers)

    On efficiency: if extraction is "fast enough" post hoc,
    then it seems wrong to put it in the egraph,
    since it would slow down the inner loop
   *)
  (*
  Section EExtract.
    (* look for node with least weight, interpreting None as oo *)
    Context (node_weight : node -> option nat).
  Fixpoint extract' fuel eclasses : idx_map (term * nat) :=
    let process n :=
      let (f, args) := n in
      @! let w <- node_weight n in
        
    in
    @! let eclasses := build_classes i in
      let nodes <- lookup eclasses x in
      minimum node_weight (ap_map process nodes).

  End EExtract.
  *)


  (******************************************)

  (*interprets an equation as a left-to-right rewrite*)
  (*
  Definition eqn_to_rewrite e1 e2 :=
    (*TODO: handle side conditions *)
    let gs_state := succ (list.fold_left max (fvs e1) in
    let q1 := extended_list_to_query (term_pat_to_clauses e1 gs_state) in
    let q2 := TODO: what is different on the put side?
    *)
(*
  Definition rewrite_to_log_op c t e1 e2 :=
    let (next, clauses, c', e1', t') :=
      (@!let {stateT V (writer _)}
               c' <- ctx_pat_to_clauses c in
         let t' <- sort_pat_to_clauses c' t in
         let e1' <- term_pat_to_clauses c' e1 in
         let _ <- lift (write (Build_atom _ _ sort_of [e1'] ,t')) in
         ret (c',e1',t') 0 in
    let (next', clauses', e2') :=
      (@!let {stateT V (writer (atom V V * V))}
               e2' <- term_pat_to_clauses c' e2 in
         let _ <- lift (write (var_clause e2' e1'))in
         TODO: need to subst in both sets of clauses in case e2' not new
         Question: is this a design issue?.
       In the case that both LHS and RHS are variables, can't unify them in the conclusion.
       Solution: just add a unify x,y command
                                                                               
       (*TODO: want to add the clause e1' = e2'; how best to write that?
           could have term_pat_to_clauses take a default arg?
           - likely best: take a fn of type stateT V _ V; use gensym normally,
             const arg for a default

          ex.:  x, y : A
                P : eq x y
                ----------
                x = y : A
          *)
         let _ <- lift (write (Build_atom _ _ sort_of [e2'] ,t')) in
         ret e2') next in
    (*TODO: for optimizing queries: is equivalence (or even inclusion) of queries decidable? (might be)
      idea: query-db correspondence: run one query on the other?
      - note: consider whether this requires a completeness theorem about queries (probably doesn't)
     *)

 (*TODO: sketch full translation on paper*)
 
  
  (*TODO: does the wrong thing w/ vars
  Definition ctx_to_clauses

  Definition lang_rule_to_log_rule n (r : rule) : log_rule :=
    match r with
    (* TODO: what to do with the sorts?
       Include sort_of as special symbol/fn in db? might be easiest
     *)
    | term_rule c _ t =>
        (*TODO: want multiple conclusions?
          Can be immitated by chained single-conclusion rules, but at > n times cost where n is #conclusions
          e.g.:
          (n args) |-> ?x, (sort_of ?x) |-> xt :- ... t |-> xt

          alternately: want a different `default` for `sort_of`?
          Question: can I ignore/never materialize the sort? No: side conditions are defined by their sorts

          Note about Multi-conclusion rules:
          - need to have separate variables for outputs that aren't matched in the assumptions.
          General idea: assumptions generate a subst,
          future rules treat vars in the subst diff from vars out of the subst
          Can I remove the awk. in-list vs option distinction by making the clause always have the var this way?
         *)
        term_to_clauses : state V 
        Note: need fresh variable state across assumptions, conclusion?
                                                                      
      Build_log_op (concl_cons (term_to_conclusion (con n (map fst c)))... (fun x y => sort_of x y)  ]  ((ctx_to_assumptions c))

  TODO: rules to eqsat program
  TODO: sort map rebuilding
 *)
 *)


End WithVar.
