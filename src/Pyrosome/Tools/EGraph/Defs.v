(*
   Based on this paper, with some deviation:
   Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker,
   Eli Rosenthal, Zachary Tatlock, and Max Willsey. 2023.
   Better Together: Unifying Datalog and Equality Saturation.
   Proc. ACM Program. Lang. 7, PLDI, Article 125 (June 2023), 25 pages.
   URL: https://doi.org/10.1145/3591239
 *)
Set Implicit Arguments.

Require Import Datatypes.String Lists.List Sorting.Permutation.
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
        (l1++l2,b)
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
  
  (*
    
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
        let write_clauses :=  t_clauses ++
                                [Build_atom n (map fst c) next_var0;
                                   Build_atom sort_of [next_var0] v] in
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
          (t_clauses++e2_clauses++[Build_atom sort_of [v2] vt]) [(v1,v2)]
    end.

  End WithLang.
  
  Notation rule_set := (rule_set V V V_map V_map).
  
  
  
  (* Note: only pass in the subset of the language you want to run.
     Often, that will be exactly the equational rules.

     Assumes incl l l'
   *)
  Definition rule_set_from_lang (l l': lang) : rule_set :=
    build_rule_set succ _ id (map (uncurry (rule_to_log_rule l')) l).

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
              : forall {B} `{WithDefault B} (merge : B -> B -> B),
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

    Definition egraph_equal l (rws : rule_set) fuel (e1 e2 : Term.term V) (t : Term.sort V) :=
      let comp : state instance bool :=
        @!let {(state instance)} x1 <- add_open_term l [] e1 in
          let {(state instance)} x2 <- add_open_term l [] e2 in
          let {(state instance)} xt <- add_open_sort l [] t in
          (saturate_until succ default spaced_list_intersect rws (eq_proven x1 x2 xt) fuel)
      in (comp (empty_egraph default)).


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

    
(* Egraph-based elaboration:
   Idea: have an add_unelab_term fn that allocates fresh idxs for elab holes,
   without terms that point to them.
   Also: adds 2 sort_of constraints at each level:
   1. canonical sort
   2. expected sort

   Last piece: generate & add eqlog rules for injectivity:
   - not expressible pyrosome rules (would break monotonicity)
   - e.g. | a = d, b = e :- "->" a b -> c, "->" d e -> c

   Then saturate, then extract
 *)
      


End WithVar.

(*TODO: move most of this to Utils*)
Require Import NArith Tries.Canonical.
From Utils Require Import TrieMap (*SpacedMapTreeN *).
From Pyrosome.Tools Require Import PosRenaming.
Module PositiveInstantiation.
  

  (*TODO: duplicated; move to Eqb or sim. locaion *)
  #[export] Instance positive_Eqb : Eqb positive := Pos.eqb.

  #[export] Instance positive_default : WithDefault positive := xH.

  Section __.
    Context {A : Type}.
    Inductive pos_trie' :=
    | pos_trie_leaf (a:A)
    | pos_trie_node (m : PTree.tree' pos_trie').

    (*None is empty *)
    Definition pos_trie := option pos_trie'.

    Definition of_ptree (t : PTree.tree pos_trie') : pos_trie :=
      match t with
      | PTree.Empty => None
      | PTree.Nodes m => Some (pos_trie_node m)
      end.

    (*TODO: check for pre-computation optimizations *)
    (* Note: assumes the key is the right length. *)
    Fixpoint pt_get' pt k {struct k} : option A :=
      match pt, k with
      | pos_trie_leaf a, [] => Some a
      | pos_trie_node m, p::k' =>
          match PTree.get' p m with
          | Some pt' => pt_get' pt' k'
          | None => None
          end
      | _, _ => None        
      end.

    Definition pt_get pt k : option A :=
      match pt with    
      | None => None
      | Some pt => pt_get' pt k
      end.

    Fixpoint pt_singleton k v :=
      match k with
      | [] => pos_trie_leaf v
      | p::k' =>
          pos_trie_node (PTree.set0 p (pt_singleton k' v))
      end.
    
    Fixpoint pt_put' pt k v {struct k} :=
      match pt, k with
      | pos_trie_leaf _, _ => pos_trie_leaf v
      (*this case shouldn't happen:
        | pos_trie_leaf a, p::k' => _
       *)
      (*this case shouldn't happen *)
      | pos_trie_node m, [] => pos_trie_node m
      | pos_trie_node m, p::k' =>
          (* TODO: can do 1 traversal instead of 2*)
          match PTree.get' p m with
          | Some pt' => pos_trie_node (PTree.set' p (pt_put' pt' k' v) m)
          | None => pos_trie_node (PTree.set' p (pt_singleton k' v) m)
          end
      end.
    
    Definition pt_put pt k v :=
      match pt with
      | None => Some (pt_singleton k v)
      | Some pt => Some (pt_put' pt k v)
      end.
    
    Fixpoint pt_remove' pt k {struct k} :=
      match pt, k with
      | pos_trie_leaf _, _ => None
      (*this case shouldn't happen:
        | pos_trie_leaf a, p::k' => _
       *)
      (*this case shouldn't happen *)
      | pos_trie_node m, [] => None
      | pos_trie_node m, p::k' =>
          (* TODO: can do 1 traversal instead of 2*)
          match PTree.get' p m with
          | Some pt' =>
              match pt_remove' pt' k' with
              | None => of_ptree (PTree.remove' p m)
              | Some ptr => Some (pos_trie_node (PTree.set' p ptr m))
              end
          | None => Some (pos_trie_node m)
          end
      end.
    
    Fixpoint pt_remove pt k {struct k} :=
      match pt with
      | None => None
      | Some ptr => pt_remove' ptr k
      end.

    (*TODO: check; probably wrong
      TODO: can probably be made faster, if it's the bottleneck
     *)
    Fixpoint pt_fold' {R} (f : R -> _ -> _ -> R) (acc : R) pt stack : R :=
      match pt with
      | pos_trie_leaf a => f acc (rev stack) a
      | pos_trie_node m =>
          let f' acc p pt :=
            pt_fold' f acc pt (p::stack)
          in
          trie_fold' f' acc m 1
      end.

    Definition pt_fold {R} (f : R -> _ -> _ -> R) (acc : R) pt : R :=
      match pt with
      | None => acc
      | Some pt => pt_fold' f acc pt []
      end.
    
  (*TODO: temporary? *)
  #[export] Instance pos_trie_map : map.map (list positive) A :=
    {
      rep := pos_trie;
      get := pt_get;
      empty := None;
      put := pt_put;
      remove := pt_remove;
      fold _ := pt_fold;
    }.

  (* Helper function for projecting the inner map when we assume the node case.
     Should not be called on other cases.
   *)
  Definition proj_node_map' p : PTree.tree pos_trie' :=
    match p with
    | pos_trie_leaf a => PTree.Empty
    | pos_trie_node m => PTree.Nodes m
    end.
  
  Definition proj_node_map p : PTree.tree pos_trie' :=
    match p with
    | None => PTree.Empty
    | Some m => proj_node_map' m
    end.

  
  Definition proj_node_map_unchecked `{WithDefault A} p : PTree.tree' pos_trie' :=
    match p with
    | pos_trie_leaf a => PTree.Node010 (pos_trie_leaf default)
    | pos_trie_node m => m
    end.
  
  Section __.
    Context `{WithDefault A}.
    (*TODO: make this an option or no?*)
    Context (merge : A -> A -> A).

    (* assumes all elements of ptl are leaves *)
    Fixpoint leaf_intersect' (a:A) ptl : A :=
      match ptl with
      | [] => a
      | (pos_trie_leaf a')::ptl' => leaf_intersect' (merge a a') ptl'
      | (pos_trie_node _)::_ => a (*should never happen*)
      end.
    Definition leaf_intersect ptl : option A :=
      match ptl with
      | (pos_trie_leaf a)::ptl => Some (leaf_intersect' a ptl)
      | _ => None (*should never happen*)
      end.
    
    (*
      Challenge: what if the first trie has a false for the next var?
                         not so easy to invoke intersection.
                       More generally, how to intersect n spaced things?.
                       
      Algorithm: (assume all var lists have the same depth and match their tries)
      Project trie's from tries. If any empty, return empty.
      With n spaced trie's with empty var lists, invoke leaf_intersect.
      Else, partition tries into those with true next vars and false next vars.
      list_intersect the true next vars.
      TODO: does that make sense? not really, since there is no good way to deal with the children.


      Algorithm v2: "
      "
      Else, partition tries into those with true next vars and false/no next vars.
      If no trues, assume all tries are leaves, use leaf_intersect (sound if the tries cover the var set)
      else, call list_intersect' on the trues, with recursive call appending the false tries to its argument

      Question: is it enough to generlize list_intersect to work w/ elts_intersect : A -> list A -> option A?
      Seems like it might not be b/c of children list.

      Also, the performance is wrong if we eagerly intersect the subtries?
      No, that seems ok; we don't eagerly intersect them
     *)

    Fixpoint partition_tries (cil : list (list bool)) (ptl : list pos_trie')
      (acc : quad _ _ _ _) :=
      (* assume both lists have the same length *)
      match cil, ptl with
      | [], [] => acc
      | ([] as l1)::cil, pt::ptl
      | (false::l1)::cil, pt::ptl =>
          let (true_cil, true_tries, other_cil, other_tries) := acc in
          partition_tries cil ptl (mk4 true_cil true_tries (l1::other_cil) (pt::other_tries))
      | (true::l1)::cil, pt::ptl =>
          let (true_cil, true_tries, other_cil, other_tries) := acc in
          partition_tries cil ptl (mk4 (l1::true_cil) (pt::true_tries) other_cil other_tries)
      | _, _ => acc (*mk4 default default default default*) (*should never happen *)
      end.

    Definition partition_tries_spec (cil : list (list bool)) (ptl : list pos_trie')
      (acc : quad _ _ _ _) :=
      let l := combine cil ptl in
      let true_filter := rev (map (fun p => (tl (fst p), snd p))
                                (filter (fun p => hd false (fst p)) l)) in
      let false_filter := rev (map (fun p => (tl (fst p), snd p))
                                 (filter (fun p => negb (hd false (fst p))) l)) in
      let (true_cil, true_tries) := split true_filter in
      let (false_cil, false_tries) := split false_filter in
      mk4 (true_cil++acc.(p41))
        (true_tries++acc.(p42))
        (false_cil++acc.(p43))
        (false_tries++acc.(p44)).

    (*TODO: move to utils*)
    Hint Rewrite map_rev : utils.
                                
    (*TODO: move to utils?*)
    Hint Rewrite map_app : utils.
    Hint Rewrite split_map : utils.
    
    Lemma partition_tries_correct cil ptl acc
      : partition_tries cil ptl acc = partition_tries_spec cil ptl acc.
    Proof.
      unfold partition_tries_spec.
      revert acc ptl;
        induction cil;
        destruct ptl, acc;
        basic_goal_prep; eauto.
      { repeat case_match; eauto. }
      {
        do 2 case_match; 
        basic_goal_prep;
        basic_utils_crush.
        all: rewrite IHcil;
        basic_goal_prep;
          basic_utils_crush.
        all: f_equal.
        all: rewrite <- app_assoc.
        all: reflexivity.
      }
    Qed.
    
    Lemma filter_complement_permutation C (l : list C) f
      : Permutation (filter f l ++ filter (fun x => negb (f x)) l) l.
    Proof using.
      clear merge.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      case_match; cbn; eauto.
      change (a:: ?l) with ([a] ++ l).
      rewrite Permutation_app_comm.
      rewrite <- !app_assoc.
      apply Permutation_app_head.
      rewrite Permutation_app_comm.
      eauto.
    Qed.

    Lemma partition_tries_ptl_perm cil ptl acc out
      : Datatypes.length cil = Datatypes.length ptl ->
        partition_tries cil ptl acc = out ->
        Permutation (ptl ++ acc.(p42) ++ acc.(p44))
          (out.(p42) ++ out.(p44)).
    Proof.
      rewrite partition_tries_correct.
      unfold partition_tries_spec.
      repeat (basic_goal_prep;
              basic_utils_crush).
      rewrite !app_assoc.
      apply Permutation_app_tail.
      apply Permutation_sym.
      rewrite Permutation_app_comm.
      rewrite !app_assoc.
      apply Permutation_app_tail.
      rewrite <- rev_app_distr.
      rewrite <- !map_app.
      rewrite <- Permutation_rev.
      rewrite List.map_map; cbn.
      change (fun x => ?f x) with f.
      rewrite filter_complement_permutation.
      rewrite map_combine_snd; eauto.
    Qed.
    
    (* Fuel makes sense here since it is likely to be small (5-20)
       and makes the recursion much more convenient.
       Fuel must be more than the length of the lists in cil.

       takes in two cil lists and two ptl lists to avoid appending them
       in the recursive call.
       It's exactly two because we separate the trues and the falses.
       Assumes cil++cil', and ptl++ptl' are nonempty.

       TODO: debug, clean up. Review datatypes.
     *)
    Fixpoint pt_spaced_intersect' fuel cil ptl cil' ptl'
      : option pos_trie' :=
      match fuel with
      | O => None (* should never happen*)
      | S fuel =>
          let (true_cil, true_tries, other_cil, other_tries) :=
            partition_tries cil' ptl'
              (partition_tries cil ptl (mk4 [] [] [] [])) in
          match true_tries with
          (* assume true_cil is empty *)
          | [] =>
              (* if other_cil is also empty (shouldn't happen)
                 or its first element is the empty list
                 
                 Assume: all cil elements have the same length.
               *)
              if hd [] other_cil then Datatypes.option_map pos_trie_leaf (leaf_intersect other_tries)
              else pt_spaced_intersect' fuel other_cil other_tries [] []
          | pt1::true_tries =>
              (*
                TODO: this feels like a bug in-waiting.
                what is the length of the ptl' that gets passed to the recursive call?
                Might be fine, but be careful.
               *)
              match list_intersect'
                      (pt_spaced_intersect' fuel other_cil other_tries true_cil)
                      (*TODO: avoid map? it's hard to avoid given the possibility of
                  leaf_intersect.
                       *)
                      (proj_node_map_unchecked pt1)
                      (map proj_node_map_unchecked true_tries)
              with
              | None => None
              | Some pt => Some (pos_trie_node pt)
              end
          end
      end.
    
    Definition pt_spaced_intersect (tries : list (pos_trie * list bool)) : pos_trie :=
      (*This split has to happen at some point, so here is fine*)
      let '(ptl, cil) := split tries in
      let fuel := S (length (hd [] cil)) in
      @! let ptl' <- list_Mmap id ptl in
        (pt_spaced_intersect' fuel cil ptl' [] []).
    
    Definition spaced_get x (p : list bool * pos_trie) : option A :=
      let key := map fst (filter snd (combine x (fst p))) in
      pt_get (snd p) key.

    Inductive depth' : pos_trie' -> nat -> Prop :=
    | leaf_depth a : depth' (pos_trie_leaf a) 0
    | node_depth m n
      : (forall k v, PTree.get' k m = Some v ->
                     depth' v n) ->
        depth' (pos_trie_node m) (S n).

    Definition depth t n :=
      match t with
      | Some t' => depth' t' n
      | None => True
      end.

    Fixpoint has_depth' (n : nat) (t : pos_trie') :=
      match n, t with
      | O, pos_trie_leaf _ => true
      | S n, pos_trie_node m =>
          map.forallb (fun k => has_depth' n) (PTree.Nodes m : TrieMap.trie_map _)
      | _, _ => false
      end.
    
    Definition has_depth n (t : pos_trie) :=
      match t with
      | None => true
      | Some x => has_depth' n x
      end.

    (*
    (* TODO: provably false (by example). figure out the bug *)
    Example pt_spaced_intersect'1_false
      : exists l p,
        depth' p (Datatypes.length (filter id l))
        /\ pt_spaced_intersect' (S (Datatypes.length l)) [l] [p] [] [] = Some p.
    Proof.
      exists [false; true].
      eexists.
      split.
      2: cbn.
      instantiate (1:=[false])

    (* TODO: provably false (by example). figure out the bug *)
    Example pt_spaced_intersect1 t l
      : depth t (length (filter id l)) -> pt_spaced_intersect [(t,l)] = t.
    Proof.
      unfold pt_spaced_intersect.
      basic_utils_crush.
      cbn -[pt_spaced_intersect'] in *.
      destruct t; eauto.
      cbn in H0.
      cbn.
      cbn [Mbind].
      cbn [map fst snd hd list_Mmap id].
      cbv[id].
      cbn -[pt_spaced_intersect'].
      destruct t; auto.
      revert p.
      induction l.
      {
        basic_goal_prep.
        destruct p; cbn; eauto.
        safe_invert H0.
      }
      cbn [pt_spaced_intersect'] in *.
      intros.
      rewrite !partition_tries_correct in *.
      unfold partition_tries_spec.
      cbn.
      (* TODO: why is the 2nd partition_tries becoming visible?*)
      basic_utils_crush.
      destruct a; cbn.
      2:{
        specialize (IHl p).
        apply IHl in H0.
        clear IHl.
        rewrite !partition_tries_correct in *.
        unfold partition_tries_spec in *.
        repeat (basic_goal_prep;
                basic_utils_crush).
        destruct l; cbn in *; eauto.
        destruct b; cbn in *; eauto.
        (*
        list_intersect'_correct
        destruct p; cbn in *; eauto.
        safe_invert H0.
        assert (exists k v, PTree.get' k m = Some v) by admit.
        break.
        pose proof H0.
        eapply H3 in H0.
        specialize (IHl x0).
        destruct l.*)
    Admitted.
     *)

    
    Lemma all_const C P (x:C) l
      : all P l ->
        (forall y, P y -> y = x) ->
        l = repeat x (length l).
    Admitted.

    Lemma filter_false_In:
      forall (B : Type) (f : B -> bool) (l : list B),
        (forall x : B, In x l -> f x = false) -> filter f l = [].
    Admitted.

    Lemma map_combine_fst' C D
      : forall (lA : list C) (lB : list D),
        map fst (combine lA lB) = (firstn (length lB) lA).
    Admitted.
    Hint Rewrite  map_combine_fst' : utils.
    
    Lemma map_combine_snd' C D
      : forall (lA : list C) (lB : list D),
        map snd (combine lA lB) = (firstn (length lA) lB).
    Admitted.
    Hint Rewrite  map_combine_snd' : utils.

    
    Lemma firstn_repeat m n C (x:C)
      : firstn m (repeat x n) = repeat x (min m n).
    Proof.
    Admitted.
    Hint Rewrite firstn_repeat : utils.

    Hint Rewrite PeanoNat.Nat.min_id : utils.
    Hint Rewrite map_repeat : utils.

    
    Hint Rewrite rev_repeat : utils.

    
    Lemma repeat_default_hd C (x:C) n
      : hd x (repeat x n) = x.
    Proof.
      destruct n; reflexivity.
    Qed.
    Hint Rewrite repeat_default_hd : utils.

    
    Hint Rewrite firstn_all : utils.
    Hint Rewrite repeat_length : utils.

    Lemma tl_repeat C (x:C) n
      : tl (repeat x n) = repeat x (pred n).
    Proof.
      destruct n; reflexivity.
    Qed.
    Hint Rewrite tl_repeat : utils.

    
    Lemma fold_left_fix_In C D (f : C -> D -> C) l acc
      : (forall x, In x l -> f acc x = acc) -> fold_left f l acc = acc.
    Admitted.

    
    Lemma option_all_empty C (l : list (option C))
      : Some [] = option_all l <-> l = [].
    Admitted.
    Hint Rewrite option_all_empty : utils.

    
    Lemma combine_eq_nil C D (l1 : list C) (l2 : list D)
      : combine l1 l2 = [] <-> l1 = [] \/ l2 = [].
    Proof.
      destruct l1; cbn; try now intuition eauto.
      destruct l2; cbn; try now intuition eauto.
    Qed.
    Hint Rewrite combine_eq_nil : utils.

    Lemma app_eq_nil' : forall [A : Type] (l l' : list A), l ++ l' = [] <-> l = [] /\ l' = [].
    Proof.
      split; eauto using app_eq_nil.
      intuition subst.
      reflexivity.
    Qed.
    Hint Rewrite app_eq_nil' : utils.

    Lemma map_eq_nil' : forall [A B : Type] (f : A -> B) (l : list A), map f l = [] <-> l = [].
    Proof.
      split; eauto using map_eq_nil.
      intuition subst.
      reflexivity.
    Qed.
    Hint Rewrite map_eq_nil' : utils.

    Hint Rewrite length_zero_iff_nil : utils.

    

    Lemma filter_eq_nil : forall [A : Type] (f : A -> bool) (l : list A), filter f l = [] <-> l = [].
    Proof. Admitted.
    Hint Rewrite filter_eq_nil : utils.

    
    Lemma rev_eq_nil C (l : list C)
      : rev l = [] <-> l = [].
    Proof. Admitted.
    Hint Rewrite  rev_eq_nil : utils.

    Hint Rewrite combine_nil : utils.

    
    Lemma map_id C (l : list C)
      : map id l = l.
    Admitted.

    
    Lemma Mbind_option_map A1 A2 A3 (f : A2 -> option A3) (g : A1 -> A2) ma
      : Mbind f (option_map g ma)
        = Mbind (fun a => f (g a)) ma.
    Admitted.
    Hint Rewrite Mbind_option_map : utils.
  
    
    Lemma all2_empty_r A1 A2 (R : A1 -> A2 -> Prop) l1
      : all2 R l1 [] <-> l1 = [].
    Admitted.
    Hint Rewrite all2_empty_r : utils.
    
    Lemma all2_empty_l A1 A2 (R : A1 -> A2 -> Prop) l2
      : all2 R [] l2 <-> l2 = [].
    Admitted.
    Hint Rewrite all2_empty_l : utils.

     (* A simpler version to serve as an intermediate step, removing the double lists *)
    Fixpoint pt_spaced_intersect'_simple fuel l
      : option pos_trie' :=
      match fuel with
      | O => None (* should never happen*)
      | S fuel =>
          let (true_cil, true_tries, other_cil, other_tries) :=
            partition_tries_spec (map fst l) (map snd l) (mk4 [] [] [] []) in
          match true_tries with
          | [] =>
              if hd [] other_cil then Datatypes.option_map pos_trie_leaf (leaf_intersect other_tries)
              else pt_spaced_intersect' fuel other_cil other_tries [] []
          | pt1::true_tries =>
              match list_intersect'
                      (fun true_tries => pt_spaced_intersect'_simple fuel
                                           (combine (other_cil++true_cil) (other_tries++true_tries)))
                (proj_node_map_unchecked pt1)
                (map proj_node_map_unchecked true_tries)
              with
              | None => None
              | Some pt => Some (pos_trie_node pt)
              end
          end
      end.

    Hint Rewrite filter_app : utils.

    
    Lemma partition_tries_app cil1 cil2 ptl1 ptl2 acc
      : length cil1 = length ptl1 ->
        partition_tries cil2 ptl2 (partition_tries cil1 ptl1 acc)
        = partition_tries (cil1++cil2) (ptl1++ptl2) acc.
    Proof.
      rewrite !partition_tries_correct.
      unfold partition_tries_spec.
      destruct acc.
      cbn.
      basic_utils_crush.
      cbn.
      rewrite !combine_app; eauto.
      basic_utils_crush.
      rewrite !rev_app_distr.
      rewrite !app_assoc.
      reflexivity.
    Qed.

    (*TODO: move? *)
    Lemma list_intersect'_ext A1 A2 (f g : list A1 -> option A2) t ts
      : (forall l, f l = g l) ->
        list_intersect' f t ts = list_intersect' g t ts.
    Admitted.

    
    Hint Rewrite rev_length : utils.
    
    Lemma pt_spaced_intersect'_simple_spec fuel cil1 cil2 ptl1 ptl2
      : Datatypes.length cil1 = Datatypes.length ptl1->
        pt_spaced_intersect' fuel cil1 ptl1 cil2 ptl2
        = pt_spaced_intersect'_simple fuel (combine (cil1 ++ cil2) (ptl1 ++ ptl2)).
    Proof.
      revert cil1 cil2 ptl1 ptl2.
      induction fuel;
        basic_goal_prep; eauto.
      rewrite partition_tries_app; auto.
      rewrite !partition_tries_correct.
      unfold partition_tries_spec; cbn [p41 p42 p43 p44].
      autorewrite with utils bool in *.
      repeat lazymatch goal with
               |- match ?c with _ => _ end
                  = match ?c with _ => _ end =>
                 case_match; auto
             end.
      (*erewrite list_intersect'_ext; eauto.
      intros.
      rewrite HeqH1.
      rewrite IHfuel; eauto.
      basic_utils_crush.
    Qed.*)
    Admitted.
    
    Lemma with_names_from_map_snd A1 A2 (l : list (A1 * A2))
      : with_names_from l (map snd l) = l.
    Admitted.
    Hint Rewrite with_names_from_map_snd : utils.

    
    Definition merge_list l :=
      match l with
      | [] => None
      | e::es => Some (List.fold_left merge es e)
      end.
    
    Lemma pt_spaced_intersect'_simple_correct fuel x l
      : (fuel > length x)%nat ->
          all (fun p => length (fst p) = length x) l ->
          all (fun p => Is_true (has_depth' (length (filter id (fst p))) (snd p))) l ->
          let bools := List.fold_left
                         (fun acc l => map2 orb (combine l acc))
                         (tl (map fst l))
                         (hd [] (map fst l))
          in
          spaced_get x (bools, pt_spaced_intersect'_simple fuel l)
          = Mbind merge_list (list_Mmap (spaced_get x) (map (pair_map id Some) l)).
    Proof.
      revert x l.
      induction fuel; intros; try Lia.lia.
      unfold spaced_get.
      subst bools.
      cbn [pt_spaced_intersect'_simple].
      unfold partition_tries_spec.
      cbn [p41 p42 p43 p44 fst snd].
      autorewrite with utils bool.
      cbn [p41 p42 p43 p44 fst snd].
      case_match.
      {
        symmetry in HeqH3.
        autorewrite with utils bool in *.
        intuition subst;
          autorewrite with utils bool in *;
          subst;
          eauto.
      }
      (*
      (*TODO: H3, H4*)
      rewrite HeqH3.
      unfold pt_get.
      change (match ?c with
              | Some pt => Some (?f pt)
              | None => None
              end)
        with (option_map f c).
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      autorewrite with utils bool.
      rewrite !List.map_map; cbn [fst snd].
      TODO: what's the diff between H3, H4/ l0,p?
                                                Why does l0 show up, but not p?
        TODO: simplify further: have 1 combined list!
        TODO: list_intersect'_correct
       *)
    Abort.

    (*TODO: update
      Lemma pt_spaced_intersect'_correct fuel x cil1 cil2 ptl1 ptl2
        : (fuel > length x)%nat ->
          all (fun l => length l = length x) cil1 ->
          all (fun l => length l = length x) cil2 ->
          all2 (fun l t => Is_true (has_depth' (length (filter id l)) t)) cil1 ptl1 ->
          all2 (fun l t => Is_true (has_depth' (length (filter id l)) t)) cil2 ptl2 ->
          
          let bools := List.fold_left
                         (fun acc l => map2 orb (combine l acc))
                         (tl (cil1++cil2))
                         (hd [] (cil1++cil2))
          in
          spaced_get x (pt_spaced_intersect' fuel cil1 ptl1 cil2 ptl2, bools)
          = Mbind merge_list (list_Mmap (spaced_get x) (combine (map Some (ptl1++ptl2)) (cil1 ++ cil2))).
      Proof.
        revert x cil1 cil2 ptl1 ptl2.
        induction fuel; intros; try Lia.lia.
        unfold spaced_get.
        subst bools.
        cbn [pt_spaced_intersect'].
        rewrite ! partition_tries_correct.
        unfold partition_tries_spec.
        cbn [p41 p42 p43 p44 fst snd].
        autorewrite with utils bool.
        cbn [p41 p42 p43 p44 fst snd].
        case_match.
        {
          symmetry in HeqH5.
          autorewrite with utils bool in *.
          intuition subst;
            autorewrite with utils bool in *;
            subst;
            eauto.
        }
        case_match.
        {
          symmetry in HeqH5, HeqH6.
          autorewrite with utils bool in *.
          intuition subst;
            autorewrite with utils bool in *;
            subst;
            eauto.
        }
        assert (combine (l::H5) (p::H6)
                = rev (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                         (filter (fun p : list bool * pos_trie' => hd false (fst p)) (combine cil2 ptl2)))
                    ++
                    rev
                    (map (fun p : list bool * pos_trie' => (tl (fst p), snd p))
                       (filter (fun p : list bool * pos_trie' => hd false (fst p)) (combine cil1 ptl1))))
          by admit.
        clear H7 (*TODO: we might need this*).

        
        unfold pt_get.
        change (match ?c with
                | Some pt => Some (?f pt)
                | None => None
                end)
          with (option_map f c).
        change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
          with (Mbind f c).
        autorewrite with utils bool.

        TODO: simplify things: get rid of cil1,2
        list_intersect'_correct
                    
        cbn.

        
        destruct x; cbn in *.








        
        case_match.
        1:case_match.
        all:unfold spaced_get.
        all: subst.
        all: cbn [fst snd].
        {
          revert HeqH6.
          rewrite Mmap_option_all.
          autorewrite with utils bool.
          intuition subst; cbn in *; eauto.
          all:autorewrite with utils bool in *; eauto.
          symmetry in H5.
          autorewrite with utils bool in *; eauto.
        }
        all: cbn [pt_spaced_intersect'].
        all:rewrite ! partition_tries_correct.
        all:unfold partition_tries_spec.
        all: autorewrite with utils bool.
        all: cbn.
        all:rewrite !List.map_map.
        all: cbn.
        all: case_match.
        all: try symmetry in HeqH7.
        all: autorewrite with utils bool in *.
        all:break.
        {
          intuition subst; cbn in *.
          all:autorewrite with utils bool in *.
          all: subst.
          all:autorewrite with utils bool in *.
          all: cbn in *.
          all: try congruence.
          symmetry in H5.
          all:autorewrite with utils bool in *.
          subst.
          cbn in *.
          congruence.
        }
        2:{
          symmetry in HeqH0.
          autorewrite with utils bool in *.
          intuition subst; cbn in *.
          all:autorewrite with utils bool in *.
          all: subst.
          all:autorewrite with utils bool in *.
          all: cbn in *.
          all: try congruence.
        }
        all: case_match.
        1,3:exfalso.
        1,2:[>symmetry in HeqH8 | symmetry in HeqH7];
        autorewrite with utils bool in *;
        intuition subst; cbn; eauto;
        autorewrite with utils bool in *;
        cbn in *; congruence.
        all: unfold pt_get.
        all:change (match ?c with
                | Some pt => Some (?f pt)
                | None => None
                end)
          with (option_map f c).
        all:change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
          with (Mbind f c).
        all:autorewrite with utils bool in *.
        TODO: issue: want goal to have 1 true at the front of bools
        rewrite list_intersect'_correct.
        ....
        
        2:{
          
          }
            
        }
        {
          rewrite Mmap_option_all in HeqH6.
          rewrite <- map_app in HeqH6.
          rewrite <- map_id with (l:= (cil1 ++ cil2)) in HeqH6.
          rewrite <- map_combine_separated in HeqH6.
          cbv [id] in HeqH6.
          rewrite List.map_map in HeqH6.
          cbn in *.
        }
        
        3:{
        TODO: relate a H6, l h7?


        }
        {
          rewrite <- rev_app_distr in HeqH7.
          rewrite <- rev_involutive with (l:=l::H7) in HeqH7.
          apply rev_inj in HeqH7.
          
        basic_utils_crush.
        {
        }
        all: autorewrite with utils bool.
        2:{
        cbn [fst snd].
        set (key:=(map fst (filter snd (combine x bools)))).
        subst bools.
        
        revert x len cil1 cil2 ptl1 ptl2.
        induction fuel; intros; try Lia.lia.
        cbn [pt_spaced_intersect'].
        rewrite ! partition_tries_correct.
        unfold partition_tries_spec.
        basic_utils_crush.
        rewrite !List.map_map.
        cbn.
        unfold spaced_get.
        cbn.
        destruct len.
        {
          eapply all_const with (x:=[]) in H1, H2.
          2,3: destruct y; cbn; intros; congruence.
          generalize dependent (Datatypes.length cil1).
          generalize dependent (Datatypes.length cil2).
          intros; subst.
          autorewrite with utils bool.
          rewrite !filter_false_In with (f:=(fun p : list bool * pos_trie' => hd false (fst p))).
          2,3:destruct x0; intro Hcom;
            apply in_combine_l in Hcom;
            apply repeat_spec in Hcom;
            subst;
            reflexivity.
          rewrite !Permutation.filter_true_In
            with (f:=(fun p : list bool * pos_trie' => negb (hd false (fst p)))).
          2,3:destruct x0; intro Hcom;
            apply in_combine_l in Hcom;
            apply repeat_spec in Hcom;
          subst; reflexivity.
          repeat change (fun x => ?f x) with f.
          autorewrite with utils bool.
          rewrite <- !List.map_map with (f :=fst).
          autorewrite with utils bool.
          autorewrite with utils bool.
          subst bools.
          cbn.
          rewrite <- !repeat_app.
          autorewrite with utils bool.
          rewrite fold_left_fix_In.
          2:{
            intros l Hin.
            apply repeat_spec in Hin; subst.
            reflexivity.
          }
          unfold spaced_get.
          cbn.
          Hint Rewrite combine_nil : utils.
          autorewrite with utils bool.
          cbn.
          TODO: did I case too early on the len?
     *)

    (*
    Lemma leaf_intersect_correct l
      : 
      spaced_get x
        (option_map pos_trie_leaf (leaf_intersect l), [])
        = Mbind (fun es => match es with
                           | [] => None
                           | e :: es0 => Some (fold_left merge es0 e)
                           end)
            (list_Mmap (spaced_get x) (combine l (repeat [] (length l)))).
      
          
          TODO: leaf intersect lemma
          
          Lemma repeat_default_hd
            : hd x (repeat x n) = x.


            rev_app_distr
          rewrite !map_combine_fst'.
          rewrite !firstn_repeat.
          Lemma 
          rewrite !H1, !H2.
        cbn beta.
     *)

    (*TODO update
    (*TODO: how to do this other than by matching on p?*)
      Lemma pt_spaced_intersect_correct x p
        : let bools := List.fold_left
                         (fun acc p => map2 orb (combine (snd p) acc))
                         (tl p)
                         (hd [] (map snd p))
          in
        match list_Mmap (spaced_get x) p with
        | Some es => spaced_get x (pt_spaced_intersect p, bools)
                     = match es with
                       | [] => None
                       | e::es => Some (List.fold_left merge es e)
                       end
        | _ => spaced_get x (pt_spaced_intersect p, bools) = None
        end.
      Proof.
     *)
        

        (*
      Lemma pt_spaced_intersect'_correct x p
        : all (fun l => len = length l) cil ->
          all (fun l => len = length l) ptl ->
        let bools := List.fold_left
                         (fun acc l => map2 orb (combine l  acc))
                         cil
                         (repeat true len)
          in
        match list_Mmap (spaced_get x) p with
        | Some es => spaced_get x (pt_spaced_intersect p, bools)
                     = match es with
                       | [] => None
                       | e::es => Some (List.fold_left merge es e)
                       end
        | _ => spaced_get x (pt_spaced_intersect p, bools) = None
        end.
      Proof.
        todo: lemma about intersect'
              *)
        
    (*TODO: ditch this compat layer? *)
    Definition compat_intersect (p : ne_list (pos_trie * list bool)) : pos_trie :=
      pt_spaced_intersect (fst p::snd p).

    (*TODO: update
      Lemma compat_intersect_correct x p
        : let bools := List.fold_left
                         (fun acc p => map2 orb (combine (snd p) acc))
                         (snd p)
                         (snd (fst p))
          in
        match spaced_get x (fst p), list_Mmap (spaced_get x) (snd p) with
        | Some e, Some es => spaced_get x (compat_intersect p, bools)
                             = Some (List.fold_left merge es e)
        | _,_ => spaced_get x (compat_intersect p, bools) = None
        end.
      Proof.
        (*
        TODO: to avoid unrolling, write one for pt_spaced_intersect
        
        revert p.
        (*TODO: should work, but might need to do induction on cil*)
        induction x.
        {
          unfold spaced_get, compat_intersect, pt_spaced_intersect.
          basic_goal_prep.
          destruct (split  l) as [ptl cil] eqn:Hsplit.
          cbn.
          cbv [id].
          destruct p; cbn;
            repeat (case_match; subst; cbn in 
                    2:{
          
        unfold compat_intersect.
        unfold pt_spaced_intersect.
        destruct p.
        cbn [fst snd].
        destruct (split (p :: l)) as [ptl cil] eqn:Hsplit.
        generalize dependent ptl.
        revert x p l.
        
        TODO: induction on distinguished elt cil?
              *)
      Abort.
     *)
    
  End __.

  End __.

  Definition sort_of := xH.

  (*TODO: the default is biting me*)
  Definition egraph_equal
    : lang positive -> rule_set positive positive trie_map trie_map ->
      nat -> Term.term positive -> Term.term positive -> Term.sort positive ->
      _ :=
    (egraph_equal ptree_map_plus (@pos_trie_map) Pos.succ sort_of (@compat_intersect)).

  (*TODO: move somewhere?*)
  Definition filter_eqn_rules {V} : lang V -> lang V :=
    filter (fun '(n,r) => match r with term_rule _ _ _ | sort_rule _ _ => false | _ => true end).

  Definition build_rule_set : lang positive -> lang positive -> rule_set positive positive trie_map trie_map :=
    rule_set_from_lang ptree_map_plus _ Pos.succ sort_of (fold_right Pos.max xH).
  
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
        ret (egraph_equal l' (build_rule_set (filter_eqn_rules l') l') n e1' e2' t')
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
  Proof. compute. reflexivity. Abort.
  
  Fixpoint string_num_succ s : string :=
    match s with
    | "" => "0"
    | String a s' =>
        if andb (Ascii.ltb a "9"%char) (Ascii.ltb "/"%char a)
        then String (ascii_succ a) s'
        else String "0"%char (string_num_succ s')
    end.
  
  Definition string_succ s : string :=
    match index 0 "#" s with
    | None => s ++"#"
    | Some n =>
        let pre := substring 0 n s in
        let post := substring (S n) (length s) s in
        pre++"#" ++(string_num_succ post)
    end.

  Goal string_num_succ "8" = "9".
  Proof. compute. reflexivity. Abort.

  
  Goal string_succ "v#8" = "v#9".
  Proof. compute. reflexivity. Abort.

  
  Goal string_succ "vZ#" = "vZ#0".
  Proof. compute. reflexivity. Abort.
  
  Goal string_succ "v/" = "v/#".
  Proof. compute. reflexivity. Abort.
  
  Goal string_succ "v#9" = "v#00".
  Proof. compute. reflexivity. Abort.
  
  Goal string_succ "v#90" = "v#01".
  Proof. compute. reflexivity. Abort.

  
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
      empty := None;
      put m k v:= PositiveInstantiation.pt_put m (map stp k) v;
      remove m k := PositiveInstantiation.pt_remove m (map stp k);
      fold _ f acc pt :=
        let f' a p v := f a (map pts p) v in
        PositiveInstantiation.pt_fold f' acc pt;
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
    : lang string -> rule_set string string string_trie_map string_trie_map ->
      nat -> _ -> Term.term string -> Term.term string -> Term.sort string ->
      _ :=
    fun l rw n c e1 e2 t =>
    let l' := ctx_to_rules c ++ l in
    egraph_equal string_ptree_map_plus (@string_list_trie_map)
      string_succ sort_of
      (@PositiveInstantiation.compat_intersect) l' rw n
  (var_to_con e1) (var_to_con e2) (sort_var_to_con t).

  Definition string_max (s1 s2 : string) :=
    match String.compare s1 s2 with
    | Gt => s1
    | _ => s2
    end.
  
  Definition build_rule_set : lang string ->
                            lang string ->
                            rule_set string string string_trie_map string_trie_map :=
    rule_set_from_lang string_ptree_map_plus _ string_succ sort_of
      (fold_right string_max "x0").

End StringInstantiation.
