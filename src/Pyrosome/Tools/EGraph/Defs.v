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

From Utils Require Import Utils UnionFind EGraph.Defs EGraph.QueryOpt Monad ExtraMaps.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Theory Require ClosedTerm.
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

  
  (*TODO: a bit of an abuse of the code*)
  Definition var_to_con (t : term) :=
    ClosedTerm.open_term []
      (ClosedTerm.close_term t).

  Definition sort_var_to_con (t : sort) :=
    ClosedTerm.open_sort []
      (ClosedTerm.close_sort t).

  (* TODO: move to closedterm?
   *)
  Definition ctx_to_rules : ctx -> lang :=
    named_map (term_rule [] []).  
  
  Context 
      (V_map : forall A, map.map V A)
      (V_map_plus : ExtraMaps.map_plus V_map)
      (V_map_ok : forall A, map.ok (V_map A))
      (V_trie : forall A, map.map (list V) A).

  Notation instance := (instance V V V_map V_map V_trie).

  Notation atom := (atom V V).

  Context (succ : V -> V).
  
  (* Include sort_of as special symbol/fn in db. *)
  Context (sort_of : V).

  (*TODO: move*)
  Definition gensym {M} `{Monad M} : stateT V M V :=
    fun s => Mret (s, succ s).

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

  
  Context (supremum : list V -> V).
  
  (* Open terms are for patterns only.
     To run an egraph on terms with variables,
     first map variables to constructors.
   *)
  Section WithLang.
    
    Context (l : lang).
    
    Section __.
      Context (sort_pat_to_clauses : Term.sort V -> stateT V (writer atom) V).
      
      Fixpoint term_pat_to_clauses' (e : Term.term V)
        : stateT V (writer atom) V :=
        match e with
        | var x => Mret x (*assumes gensym doesn't hit pattern vars*)
        | Term.con n s =>
          match named_list_lookup_err l n with
          | Some (term_rule c args t) =>
              @! let s' <- list_Mmap term_pat_to_clauses' s in
                let ax <- gensym in
                let tt <- lift (write (Build_atom n s' ax)) in
                (*TODO: this produces a lot of duplication.
                  Optimization is important.
                 *)
                let tx <- sort_pat_to_clauses t[/with_names_from c s/] in
                let tt <- lift (write (Build_atom sort_of [ax] tx)) in
                (* TODO: sort_of atoms *)
                ret ax
          | _ => Mret default (*shouldn't happen*)
          end
        end.
    End __.

    Fixpoint sort_pat_to_clauses' fuel (e : Term.sort V)
      : stateT V (writer atom) V :=
      match fuel, e with
      | 0, _ => Mret default (*shouldn't happen *)
      | S fuel, scon n s =>
          @! let s' <- list_Mmap (term_pat_to_clauses' (sort_pat_to_clauses' fuel)) s in
            let ax <- gensym in
            let tt <- lift (write (Build_atom n s' ax)) in
            (* TODO: sort_of atoms *)
            ret ax
      end.

    Definition sort_pat_to_clauses := sort_pat_to_clauses' (length l).
    Definition term_pat_to_clauses := term_pat_to_clauses' sort_pat_to_clauses.

  Definition ctx_to_clauses : Term.ctx V -> stateT V (writer atom) unit :=
    list_Miter
      (fun '(x,t) =>
         @! let t_v <- sort_pat_to_clauses t in
           (lift (write (Build_atom sort_of [x] t_v)))).
 

  (*TODO: move to queryopt*)
  Arguments Build_log_rule {idx symbol}%type_scope
    (query_vars query_clauses write_clauses write_unifications)%list_scope.

  Definition query_fvs (l : list atom) : list V :=
    dedup (eqb (A:=_)) (flat_map (fun '(Build_atom _ l o) => o::l) l).
  
  (*
    On variable ordering

    Good constraints to satisfy:
    - ctx vars should be in ctx order I think
    - if a variable appears twice in the same clause,
      it should be ordered early
    - given a clause (sort_of x -> y),
      should we have x ordered before y? or the opposite?
    - More generally, should output variables be ordered after input ones?

    sort of considerations:
    If the value of x is fixed, then trie(sort_of x->y) has size 1.
    On the other hand, there may be intersection benefits to restricting y first.
    If there are 10 sorts with 100 elements evenly distributed,
    then order x,y yields a trie with maximal comparisons 200 (100 * (1 + 1*1))
    and order y,x yields a trie with maximal comparisons 110 (10 * (1 + 10*1))

    Goal: to speed up intersection, partition db space as equally as possible
    into small numbers of branches.
    This means that the best variable order is the one where each next var
    has the fewest matches of available vars.
    What remains is that the order should be determined
    by the size of available matches.

    Question about independent components, e.g. sorts of unrelated subterms:
    - is it better to fully determine one component, or constrain each?
    - seems better to fully constrain one thing, so that constraining the next
      happens in as few subtries as possible?
    - if truly independent, then intersection skips, so there is no cost.
    

    Good match set size heuristics:
    - sorts have smaller match sets
      + implies (sort_of x -> y) orders y before x
    - outputs have multiplicity bounded by the min multiplicity of their inputs,         so outputs should usually be ordered before their inputs


    One potential sort order:
    order vars from greatest to least
      
   *)
  
  (*TODO: should drop the 'rw' in the name/change the name.
    Rules can do more than rewrite, essentially a full datalog.

    TODO: should I add back the union output clause?
    My current strategy doesn't work for rules with LHS as a lone var.
    Could also do the same, but for RHS.

    How to handle this?
    x : val unit, y : val unit
    -----------------------
    x = y : val unit

    Need unification clause...

    Idea: add (exactly one?) unification clause to uncompiled rules,
          compile to either current compiled rule, or a rule with only exactly on eunification

   TODO: (IMPORTANT) pick a var order. Currently uses an unoptimized order
   *)
  Definition rule_to_log_rule n (r : rule) : log_rule V V :=
    match r with
    | sort_rule c args =>
        let '(query_clauses,(tt,next_var)) :=
          ctx_to_clauses c (succ (supremum (map fst c))) in
        (*TODO: check for off-by-one*)
        let write_clauses := [Build_atom n (map fst c) next_var] in
        (*TODO: need list of all query vars, not just ctx vars.
          Additionally, the order is important.
         *)
        Build_log_rule (query_fvs query_clauses) query_clauses write_clauses []
    | term_rule c args t => 
        let '(query_clauses,(tt,next_var)) :=
          ctx_to_clauses c (succ (supremum (map fst c))) in
        let '(t_clauses,(v,next_var0)) :=
          sort_pat_to_clauses t next_var in
        (*TODO: check for off-by-one*)
        let write_clauses := (Build_atom sort_of [next_var0] v)::
                             (Build_atom n (map fst c) next_var0):: t_clauses  in
        (*TODO: need list of all query vars, not just ctx vars.
          Additionally, the order is important.
         *)
        Build_log_rule (query_fvs query_clauses) query_clauses write_clauses []
    | sort_eq_rule c t1 t2 => 
        let '(ctx_clauses,(tt,next_var)) :=
          ctx_to_clauses c (succ (supremum (map fst c))) in
        let '(t1_clauses,(v1,next_var0)) :=
          sort_pat_to_clauses t1 next_var in
        let '(t2_clauses,(v2,next_var1)) :=
          sort_pat_to_clauses t2 next_var0 in
        (*TODO: need list of all query vars, not just ctx vars.
          Additionally, the order is important.
         *)
        Build_log_rule (query_fvs (t1_clauses++ctx_clauses))
          (t1_clauses++ctx_clauses) t2_clauses [(v1,v2)]
    | term_eq_rule c e1 e2 t => 
        let '(ctx_clauses,(tt,next_var)) :=
          ctx_to_clauses c (succ (supremum (map fst c))) in
        let '(e1_clauses,(v1,next_var0)) :=
          term_pat_to_clauses e1 next_var in
        let '(e2_clauses,(v2,next_var1)) :=
          term_pat_to_clauses e2 next_var0 in
        let '(t_clauses,(vt,next_var2)) :=
          sort_pat_to_clauses t next_var1 in
        (*
          TODO: do I need to match the LHS sort? no, right?
          
         *)
        (*TODO: need list of all query vars, not just ctx vars.
          Additionally, the order is important.
         *)
        Build_log_rule (query_fvs (e1_clauses++ctx_clauses)) (e1_clauses++ctx_clauses)
          ((Build_atom sort_of [v2] vt)::e2_clauses++t_clauses) [(v1,v2)]
    end.

  End WithLang.
  
  Notation rw_set := (rw_set V V V_map V_map).
  
  Arguments build_rw_set {idx}%type_scope {Eqb_idx} idx_succ%function_scope idx_zero 
    {symbol}%type_scope default_symbol {symbol_map}%function_scope {symbol_map_plus} 
    {idx_map}%function_scope rules%list_scope.
  
  (* Note: only pass in the subset of the language you want to run.
     Often, that will be exactly the equational rules.

     Assumes incl l l'
   *)
  Definition rw_set_from_lang (l l': lang) : rw_set :=
    build_rw_set succ _ _ (map (uncurry (rule_to_log_rule l')) l).

  Local Notation hash_node := (hash_node succ).

  Section AddTerm.
    (*
    (* TODO: this definitely exists somewhere *)
    Definition sort_of_term n s :=
      match named_list_lookup_err l n with
      | Some (term_rule c args t) =>
          t[/combine (map fst c) s/]
      | _ => default
      end.
     *)

    Context (l : lang).
    Section __.
      Context (add_open_sort : named_list V -> Term.sort V -> state instance V).
      Fixpoint add_open_term' (sub : named_list V) (e : Term.term V)
      : state instance V :=
      match e with
      | Term.var x => Mret (named_list_lookup default sub x)
      | Term.con n s =>          
          match named_list_lookup_err l n with
          | Some (term_rule c args t) =>
              @! let s' <- list_Mmap (add_open_term' sub) s in
                let x <- hash_node n s' in
                let tsub := combine (map fst c) s' in
                let tx <- add_open_sort tsub t in
                (* TODO: allocates extra id when the node is fresh *)
                let tx' <- hash_node sort_of [x] in
                let _ <- union tx tx' in
                ret x
          | _ => Mret default
          end
      end.
    End __.

    Fixpoint add_open_sort' fuel (sub : named_list V) (t : Term.sort V)
      : state instance V :=
      match fuel with
      | 0 => Mret default (*should never happen*)
      | S fuel =>
        let (n,s) := t in
        @! let s' <- list_Mmap (add_open_term' (add_open_sort' fuel) sub) s in
          (hash_node n s')
      end.

    (*
      The recursion is bounded by the number of rules since every term in a sort
      must be of a previously defined sort.
     *)
    Definition add_open_sort := add_open_sort' (length l).
    Definition add_open_term := add_open_term' add_open_sort.

    End AddTerm.

    (* TODO: any reason to use the non-open ones? can just use the open one w/ empty sub
    Fixpoint add_term (t : term)
      : state instance V :=
      match t with
      | con n s =>
          @! let s' <- list_Mmap add_term s in
            let sub := combine (map fst c
            (hash_node succ default n s')
      end.
    
    Definition add_sort (t : term)
      : state instance V :=
      match t with
      | con n s =>
          @! let s' <- list_Mmap add_term s in
            (hash_node succ default n s')
      end.
     *)

    (*TODO: inherited from functionaldb. fill in.*)
    Context (spaced_list_intersect
              (*TODO: nary merge?*)
              : forall {B} (merge : B -> B -> B),
                ne_list (V_trie B * list bool) ->
                (* Doesn't return a flag list because we assume it will always be all true*)
                V_trie B).

    Definition egraph_sort_of (x t : V) : state instance bool :=
      @! let t0 <- hash_node sort_of [x] in
        let t1 <- find V _ V _ _ _ t in
        ret eqb t0 t1.

    Definition eq_proven x1 x2 t : state instance bool :=
      @!let b1 <- egraph_sort_of x1 t in
        let b2 <- are_unified x1 x2 in
        ret (andb b1 b2).

    Definition egraph_equal l (rws : rw_set) fuel (e1 e2 : Term.term V) (t : Term.sort V) :=
      let comp : state instance bool :=
        @!let {(state instance)} x1 <- add_open_term l [] e1 in
          let {(state instance)} x2 <- add_open_term l [] e2 in
          let {(state instance)} xt <- add_open_sort l [] t in
          (saturate_until succ default spaced_list_intersect rws (eq_proven x1 x2 xt) fuel)
      in (comp (empty_egraph default)).

(*
    Worked example:
    
  [:="G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"exp" "G" "A",
      "v2" : #"exp" "G" "B"
      ----------------------------------------------- ("project 1")
      #".1" (#"pair" "v1" "v2") = "v1" : #"exp" "G" "A"
  ];

    Query clauses from context (partially deduped):
    (#"env") ~> 0
    (#"sort_of" "G") ~> 0
    (#"ty") ~> 1
    (#"sort_of" "A") ~> 1
    (#"sort_of" "B") ~> 1
    {#"exp" "G" "A") ~> 2
    (#"sort_of" "v1") ~> 2
    {#"exp" "G" "B") ~> 3
    (#"sort_of" "v2") ~> 3

    Query clauses from LHS (partial dedup, extends above):
    (#"pair" "G" "A" "B" "v1" "v2") ~> 4
    (#".1" "G" "A" "B" 4) ~> 5
    (#"sort_of" 5) ~> 2         //TODO: prove this one unnecessary? (possible, but necessary?)

    Write clauses (from RHS):
    (#".1" "G" "A" "B" 4) ~> "v1"


    general case: write clauses are clauses of RHS + LHS_top -> RHS_top_id.
    If RHS is not a variable, can optimize to clauses of RHS
    where the var for RHS_top is LHS_top_id
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
  
    Section EExtract.
      (*TODO: generalize from nat to any metric (e.g. list nat),
        or max instead of sum
      
      Check list_sum.
      Check Nat.ltb.
       *)
      
      (* look for node with least weight, interpreting None as oo *)
      Context (symbol_weight : atom -> option nat).
      
      (* TODO generalize to be monadic *)
      Fixpoint minimum' {A} (ltb : A -> A -> bool) (l : list A) (min : A) : A :=
        match l with
        | [] => min
        | x::l =>
            if ltb x min then minimum' ltb l x else minimum' ltb l min
        end.

      Definition minimum {A} ltb (l : list A) :=
        match l with
        | [] => None
        | x::l => Some (minimum' ltb l x)
        end.

      Definition enter {A} `{Eqb A} x : stateT (list A) option unit :=
        fun l => if inb x l then None else Some (tt,(x::l)).
      
      Definition exit {A} `{Eqb A} : stateT (list A) option unit :=
        fun l => Some (tt, tl l).

      (*TODO: doesn't have to return an option/always returns Some*)
      Fixpoint Mfiltermap {A B} (f : A -> stateT (list V) option B) (l : list A)
        : stateT (list V) option (list B) :=
        match l with
        | [] => Mret []
        | x::l =>
            fun s =>
              match f x s with
              | None => Mfiltermap f l s
              | Some (x',s') =>
                  @!let (l', s') <- Mfiltermap f l s' in
                    ret (x'::l',s')
              end
        end.
      
    (* returns the weight of the extracted term.
       TODO: memoize
       Maintains a 'visited' stack to avoid cycles
     *)
      Fixpoint extract' fuel eclasses (uf : union_find V (V_map V) (V_map nat)) (x : V)
        : stateT (list V) option (term * nat) :=
        match fuel with
        | 0 => fun _ => None
        | S fuel =>
            let process (x : V) p : stateT (list V) option (term*nat) :=
              let '(f, args):= p in 
              @!let _ <- enter x in
                let weight <- lift (symbol_weight (Build_atom (f:V) args x)) in
                let args' <- list_Mmap (extract' fuel eclasses uf) args in
                let _ <- exit in
                ret (con f (map fst args'),
                    (list_sum (weight::(map snd args'))))
            in
            (* TODO: is find necessary? might always be a no-op *)
            @!let (_,x') <- lift (UnionFind.find _ _ _ _ uf x) in
              let cls <- lift (map.get eclasses x) in
              let candidates <- Mfiltermap (process x) cls in
              (lift (minimum (fun x y => Nat.ltb (snd x) (snd y)) candidates))
        end.

      Definition build_eclasses : db_map V V _ _ -> V_map (list (V * list V)) :=
        let process_row f acc args '(_,out) :=
          match map.get acc out with
          | Some l => map.put acc out ((f,args)::l)
          | None => map.put acc out [(f,args)]
          end
        in
        let process_table acc f :=
          map.fold (process_row f) acc
        in
        map.fold process_table map.empty.
        
      Definition extract fuel (i : instance) x :=
        let cls := (build_eclasses i.(db _ _ _ _ _)) in
        option_map fst
          (option_map fst (extract' fuel cls i.(equiv _ _ _ _ _) x [])).
    
    (*TODO: differential extraction;
    extract 2 terms together with a shared weight metric (distance)
     *)

  End EExtract.


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


Require Import NArith Tries.Canonical.
From Utils Require Import TrieMap SpacedMapTreeN.
From Pyrosome.Tools Require Import PosRenaming.
Module PositiveInstantiation.
  

  (*TODO: duplicated; move to Eqb or sim. locaion *)
  #[export] Instance positive_Eqb : Eqb positive := Pos.eqb.

  #[export] Instance positive_default : WithDefault positive := xH.

  Section __.
    Context {A : Type}.
    Inductive pos_trie :=
    | pos_trie_empty
    | pos_trie_leaf (a:A)
    | pos_trie_node (m : PTree.tree' pos_trie).

    (*TODO: check for pre-computation optimizations *)
    (* Note: assumes the key is the right length. *)
    Fixpoint pt_get pt k {struct k} : option A :=
      match pt, k with
      | pos_trie_empty, _ => None
      | pos_trie_leaf a, [] => Some a
      | pos_trie_node m, p::k' =>
          match PTree.get' p m with
          | Some pt' => pt_get pt' k'
          | None => None
          end
      | _, _ => None        
      end.

    Fixpoint pt_put pt k v {struct k} :=
      match pt, k with
      | pos_trie_empty, []
      | pos_trie_leaf _, _ => pos_trie_leaf v
      (*this case shouldn't happen:
        | pos_trie_leaf a, p::k' => _
       *)
      (* Note: could be optimized slightly*)
      | pos_trie_empty, p::k' =>
          pos_trie_node (PTree.set0 p (pt_put pos_trie_empty k' v))
      (*this case shouldn't happen *)
      | pos_trie_node m, [] => pos_trie_node m
      | pos_trie_node m, p::k' =>
          (* TODO: can do 1 traversal instead of 2*)
          match PTree.get' p m with
          | Some pt' => pos_trie_node (PTree.set' p (pt_put pt' k' v) m)
          | None => pos_trie_node (PTree.set' p (pt_put pos_trie_empty k' v) m)
          end
      end.
    
    Fixpoint pt_remove pt k {struct k} :=
      match pt, k with
      | pos_trie_empty, _
      | pos_trie_leaf _, _ => pos_trie_empty
      (*this case shouldn't happen:
        | pos_trie_leaf a, p::k' => _
       *)
      (*this case shouldn't happen *)
      | pos_trie_node m, [] => pos_trie_empty
      | pos_trie_node m, p::k' =>
          (* TODO: can do 1 traversal instead of 2*)
          match PTree.get' p m with
          | Some pt' => pos_trie_node (PTree.set' p (pt_remove pt' k') m)
          | None => pos_trie_node m
          end
      end.

    (*TODO: check; probably wrong
      TODO: can probably be made faster, if it's the bottleneck
     *)
    Fixpoint pt_fold' {R} (f : R -> _ -> _ -> R) (acc : R) pt stack : R :=
      match pt with
      | pos_trie_empty => acc
      | pos_trie_leaf a => f acc (rev stack) a
      | pos_trie_node m =>
          let f' acc p pt :=
            pt_fold' f acc pt (p::stack)
          in
          trie_fold' f' acc m 1
      end.
    
  (*TODO: temporary? *)
  #[export] Instance pos_trie_map : map.map (list positive) A :=
    {
      rep := pos_trie;
      get := pt_get;
      empty := pos_trie_empty;
      put := pt_put;
      remove := pt_remove;
      fold _ f acc pt := pt_fold' f acc pt [];
    }.

  Section __.
    Context (merge : A -> A -> A).
    Fixpoint pt_spaced_intersect' (ci1 ci2 : list bool) pt1 pt2
      : pos_trie :=
      match ci1, pt1, ci2, pt2 with
      | _, pos_trie_empty, _, _ 
      | _, _, _, pos_trie_empty => pos_trie_empty
      | [], pos_trie_leaf a, [], pos_trie_leaf a' => pos_trie_leaf (merge a a')
      | b1::ci1', pos_trie_node m, b2::ci2', pos_trie_node m' =>
          (*TODO: could optimize*)
          let map' :=
            if b1 then
              if b2 then map_intersect (pt_spaced_intersect' ci1' ci2')
                           (PTree.Nodes m)
                           (PTree.Nodes m')
              else map_map (fun t => pt_spaced_intersect' ci1' ci2' t pt2) (PTree.Nodes m)
            else map_map (fun t => pt_spaced_intersect' ci1' ci2' pt1 t) (PTree.Nodes m)
          in
          match map' with
          | PTree.Empty => pos_trie_empty
          | PTree.Nodes m => pos_trie_node m
          end
      | _,_,_,_ => pos_trie_empty (*TODO: check that this doesn't happen*)
      end.

    (* TODO: port the efficient one from spaced ntree*)
    Definition pt_spaced_intersect (tries : ne_list (pos_trie * list bool)) :=
      let '(trie0,tries) := tries in
      let f '(t,flags) '(t',flags') :=
        (pt_spaced_intersect' flags flags' t t', List.zip orb flags flags') in
      fst (List.fold_left f tries trie0).
    
  End __.

  End __.

  Definition sort_of := xH.
  
  Definition egraph_equal
    : lang positive -> rw_set positive positive trie_map trie_map ->
      nat -> Term.term positive -> Term.term positive -> Term.sort positive ->
      _ :=
    (egraph_equal ptree_map_plus (@pos_trie_map) Pos.succ sort_of (@pt_spaced_intersect)).

  (*TODO: move somewhere?*)
  Definition filter_eqn_rules {V} : lang V -> lang V :=
    filter (fun '(n,r) => match r with term_rule _ _ _ | sort_rule _ _ => false | _ => true end).

  Definition build_rw_set : lang positive -> lang positive -> rw_set positive positive trie_map trie_map :=
    rw_set_from_lang ptree_map_plus Pos.succ sort_of (fold_right Pos.max xH).
  
  (* all-in-one when it's not worth separating out the rule-building.
     Handles renaming.
     
   (*TODO: handle term closing, sort matching*)
   *)
  Definition egraph_equal' {V} `{Eqb V} (l : lang V) n c (e1 e2 : Term.term V) (t : Term.sort V) : _ :=
    let rename_and_run : state (renaming V) _ :=
      @! let l' <- rename_lang (ctx_to_rules c ++ l) in
        let e1' <- rename_term (var_to_con e1) in
        let e2' <- rename_term (var_to_con e2) in
        let t' <- rename_sort (sort_var_to_con t) in
        ret (egraph_equal l' (build_rw_set (filter_eqn_rules l') l') n e1' e2' t')
    in
    (*2 so that sort_of is distict*)
    (rename_and_run ( {| p_to_v := map.empty; v_to_p := {{c }}; next_id := 2 |})).
  
End PositiveInstantiation.

Require Ascii.
Module StringInstantiation.

  Import Ascii.
  Import Strings.String.

  Fixpoint blist_succ (l : list bool) : list bool :=
    match l with
    | [] => [true]
    | x::l' =>
        if x then false::(blist_succ l')
        else true::l'
    end.

  Definition ascii_of_bit_list l :=
    match l with
    | [x; x0; x1; x2; x3; x4; x5; x6] =>
        Ascii.Ascii x x0 x1 x2 x3 x4 x5 x6
    | _ => Ascii.zero
    end.
  
  (* None denotes a carry *)
  Definition ascii_succ a : Ascii.ascii :=
    Eval vm_compute in
      match a with
      | Ascii.Ascii x x0 x1 x2 x3 x4 x5 x6 =>
          (*Note: will roll over at 255*)
          ascii_of_bit_list (blist_succ [x; x0; x1; x2; x3; x4; x5; x6])
      end.

  Require Import Ascii.
  
  Goal ascii_succ "0"%char = "1"%char.
  Proof. compute. reflexivity. Qed.
  
  (*TODO: could consider writing one that retains better legibility.
    Sepcifically: only use printable characters
   *)
  Fixpoint string_succ s : string :=
    match s with
    | "" => "0"
    | String a EmptyString =>
        if andb (Ascii.ltb a "Z"%char) (Ascii.ltb "/"%char a)
        then String (ascii_succ a) EmptyString
        else  String a "0"
    | String a s => String a (string_succ s)
    end.

  Goal string_succ "v8" = "v9".
  Proof. compute. reflexivity. Qed.

  
  Goal string_succ "vZ" = "vZ0".
  Proof. compute. reflexivity. Qed.
  
  Goal string_succ "v/" = "v/0".
  Proof. compute. reflexivity. Qed.

  
  Definition sort_of := "@sort_of".

  Fixpoint stp s : positive :=
    match s with
    | "" => xH
    | String a s' =>
        let p' := Zpower.shift_nat 8 (stp s') in
        match Ascii.N_of_ascii a with
        | N0 => p'
        | Npos p => p + p'
        end
    end.

  Fixpoint positive_to_bit_list p :=
    match p with
    | xH => []
    | xO p' => false::(positive_to_bit_list p')
    | xI p' => true::(positive_to_bit_list p')
    end.

  Fixpoint bit_list_to_string bl : string :=
    match bl with
    | [] => ""
    | x:: x0:: x1:: x2:: x3:: x4:: x5:: x6:: bl' =>
        String (Ascii.Ascii x x0 x1 x2 x3 x4 x5 x6) (bit_list_to_string bl')
    (*TODO: wrong, but won't come up *)
    | _ => "VERY_WRONG"
    end.
  
  Definition pts p : string :=
    bit_list_to_string (positive_to_bit_list p).

  Goal pts (stp "Foo123#") = "Foo123#".
  Proof. reflexivity. Abort.
  
  (*could be able to be much faster, this is just the quick version*)
  Definition string_trie_map value :=
    {|
      map.rep := PTree.t value;
      map.get m k := PTree.get (stp k) m;
      map.empty := PTree.empty value;
      map.put m k v := PTree.set (stp k) v m;
      map.remove m k := PTree.remove (stp k) m;
      map.fold A f a m :=
        let f' a p v := f a (pts p) v in
        @trie_fold value A f' a m;
    |}.

  
  (*TODO: temporary? *)
  #[export] Instance string_list_trie_map A : map.map (list string) A :=
    {
      rep := PositiveInstantiation.pos_trie;
      get m k := PositiveInstantiation.pt_get m (map stp k);
      empty := PositiveInstantiation.pos_trie_empty;
      put m k v:= PositiveInstantiation.pt_put m (map stp k) v;
      remove m k := PositiveInstantiation.pt_remove m (map stp k);
      fold _ f acc pt :=
        let f' a p v := f a (map pts p) v in
        PositiveInstantiation.pt_fold' f' acc pt [];
    }.

  #[export] Instance string_ptree_map_plus : map_plus string_trie_map :=
    {|
      map_intersect A B C f (m1 : string_trie_map A) m2 :=
        @TrieMap.intersect A B C f m1 m2;
      ExtraMaps.map_fold_values := @map_fold_values;
      map_map :=
        fun (A B : Type) (f : A -> B) =>
          PTree.map_filter (fun x : A => Some (f x))
    |}.
  
  Definition egraph_equal
    : lang string -> rw_set string string string_trie_map string_trie_map ->
      nat -> _ -> Term.term string -> Term.term string -> Term.sort string ->
      _ :=
    fun l rw n c e1 e2 t =>
    let l' := ctx_to_rules c ++ l in
    egraph_equal string_ptree_map_plus (@string_list_trie_map) string_succ sort_of
      (@PositiveInstantiation.pt_spaced_intersect) l' rw n
  (var_to_con e1) (var_to_con e2) (sort_var_to_con t).

  Definition string_max (s1 s2 : string) :=
    match String.compare s1 s2 with
    | Gt => s1
    | _ => s2
    end.
  
  Definition build_rw_set : lang string ->
                            lang string ->
                            rw_set string string string_trie_map string_trie_map :=
    rw_set_from_lang string_ptree_map_plus string_succ sort_of
      (fold_right string_max "x0").

End StringInstantiation.
