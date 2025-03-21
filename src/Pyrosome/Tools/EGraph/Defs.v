(*
   Based on this paper, with some deviation:
   Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker,
   Eli Rosenthal, Zachary Tatlock, and Max Willsey. 2023.
   Better Together: Unifying Datalog and Equality Saturation.
   Proc. ACM Program. Lang. 7, PLDI, Article 125 (June 2023), 25 pages.
   URL: https://doi.org/10.1145/3591239
 *)
Set Implicit Arguments.

Require Import BinNat Datatypes.String Lists.List Sorting.Permutation.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
From Utils.EGraph Require Import Semantics Defs QueryOpt.
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
  Fixpoint var_to_con (t : term) :=
    match t with
    | var x => con x []
    | con n s => con n (map var_to_con s)
    end.

  Definition sort_var_to_con (t : sort) :=
    match t with
    | scon n s => scon n (map var_to_con s)
    end.

  (* TODO: move to closedterm?
   *)
  Definition ctx_to_rules : ctx -> lang :=
    named_map (fun t => term_rule [] [] (sort_var_to_con t)).
  
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

    Context (analysis_result : Type)
      `{analysis V V analysis_result}.

    Local Notation instance := (instance analysis_result).
    Local Notation hash_entry := (hash_entry succ).


    Section SortFlag.
    (* A flag for determining whether to emit sort annotations.
       Default to true for writes and false for queries.
     *)
    Context (with_sorts : bool).

    Section __.
      Context (add_open_sort : named_list V -> Term.sort V -> state instance V).
      Fixpoint add_open_term' (sub : named_list V) (e : Term.term V)
        : state instance V :=
        match e with
        (* We could make x the default here so that the empty sub behaves as identity.
           This would be convenient, but would make it to easy to use unallocated names
           by accident.
         *)
        | Term.var x => Mret (named_list_lookup default sub x)
        | Term.con n s =>          
            match named_list_lookup_err l n with
            | Some (term_rule c args t) =>
                @! let s' <- list_Mmap (add_open_term' sub) s in
                  let x <- hash_entry n s' in
                  if with_sorts then
                    let tsub := combine (map fst c) s' in
                    let tx <- add_open_sort tsub t in
                    let tx' <- hash_entry sort_of [x] in
                    let _ <- union tx tx' in
                    ret x
                  else ret x
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
          (hash_entry n s')
      end.

    (*
      The recursion is bounded by the number of rules since every term in a sort
      must be of a previously defined sort.
     *)
    Definition add_open_sort := add_open_sort' (length l).
    Definition add_open_term := add_open_term' add_open_sort.
    

  Notation alloc :=
    (alloc V succ V V_map V_map V_trie _).


  Definition add_ctx (c : ctx) : state instance _ :=
    list_Mfoldr (fun '(x,t) sub =>
                   (*use the empty substitution to indicate the identity.
                      Assumes that the input egraph starts with an allocator
                    *)
                   @! let t_v <- add_open_sort sub t in
                     (* using the variables from ctx isn't sound,
                          so we make sure to allocate a fresh one
                      *)
                     let {(state instance)} x' <- alloc in
                     let tx' <- hash_entry sort_of [x'] in
                     let _ <- union t_v tx' in
                     ret (x,x')::sub) c [].

  End SortFlag.
  
    (*TODO: deprecate & use (version of?) instance version below only
      For best results, properly (& generically?) lay out queries as an alternate
      presentation of a DB.
      Then we can use term_to_db . db_as_query

      current impedence: variable symbols & canonical reps.
      we need to maintain the variable names so that the query results are accessible.
      Current code inserts variable symbols to check for unificaitons.
      Can maintain names exactly (plus some unknown generated names)
      by adding all union-find edges as unification clauses.
      ISSUE: queries do not have unification clauses, since it's always better to write
      them as using a shared variable.
      Option: have a separate pass from a generalized query to a query that doesn't have unif. vars.
      generalized query is essentially the output, so it makes sense.
      A subst-left-with-right heuristic is sufficient if applied correctly,
      since it can line up with the union-find conversion to always produce the canonical rep.

      Updated pipeline overview:
      Pyrosome rule -> db -> LRule -> erule

      LRule := all x..., Q => exists y... P, where Q,P are eq sequents
      eq sequent := list lclause * list unif_clause

      all X, (And P) -> exists Y, (And Q)
      all X, exists Y, -(And P) or (And Q)
      all X, exists Y, Or -P (And Q)

      Some math notes:

      DB is a category w/ databases as objects and value substitutions as arrows
      A query is a database, the results of a query Q on database D are Hom(Q,D)

      EG is a category w/ egraphs as objects and (eq-preserving) value substitutions as arrows
      A query (optionally w/ unification rules) is an egraph, the results of a query are still Hom(Q,D).
      Up to equivalence, we can pick a canonical form and quotient the homset by the equivalence of D.
      Also, Hom(Q,D)/D_= is a subset of Hom(Q,D).

      What is a rule in this context?
      Given a rule G |- G' and db D, we compute Hom(G,D).
      Then we construct from that a D'. Is this a natural transformation of some kind?

      Note: the above arrows are odd; they compose substitution with subset.
      Is this a double category?

      Attempt (without the language of double categories, because I haven't learned it yet)

      DB is 2 categories w/ dbs as objects.
      DB1: vertical morphisms: subset relation
      DB2: horizontal morphisms: substitutions

      morphism1: --->
      morphism2: ====>

          s
      Q  ===> Qs  --->  D
          |             |
          |    =====!>  |
          \/            |
          s'            \/
      Q' ===> Q's ---> D'


      Running Q as a query on D produces { s | s in Hom(Q,Qs) for Qs subset D}
      
      Running Q',s additively on D produces D'
      - compute s' as s + id where id fills Q's domain
        + Note: this is a interesting property that definitely has a name, we'll call it P1
      - compute Q's from Q' and s'
      - compute D' as the union/join of D and Q's


      P1: for any morphism s : Q => Qs and object Q' such that dom(Q) subset dom(Q'),
          s + id is an arrow Q' -> Q's for some Q's


     Another way of describing things:
     D' = D U { Q'[s] | s in Hom(Q,Qs) for Qs subset D}

     Issue: above not quite right b/c of existentials.
     Need disjoint vars for all the Q'[s]s.
     How to capture that?
     idea: no id(it's not right), pull in another morphism


     next description attempt :

     Given rule Q |- R and database D:

     D' is the union of D and
     coproduct { R'_fs | f+s : R -> R'_fs, s in Hom(Q,Qs) for Qs subset D,
               f is bijective, and dom(f) + dom(s) = ...
     }

     TODO: coproduct is too disjoint; only want fi to be disjoint

     next attempt:

     
     D' is the union of D and
     { R'_fs | f+s : R -> R'_fs, s in Hom(Q,Qs) for Qs subset D,
               f is bijective, and dom(f) + dom(s) = dom(R)
     }
     where the ranges of fi are mutually disjoint

     *)

  
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
  Definition rule_to_log_rule n (r : rule) : sequent V V :=
    match r with
    | sort_rule c args =>        
        sequent_of_states
          (add_ctx false c)
          (fun sub => add_open_sort true sub (scon n (id_args c)))
    | term_rule c args t => 
        sequent_of_states
          (add_ctx false c)
          (* add_open_term sees the language, so it handles t *)
          (fun sub => add_open_term true sub (con n (id_args c)))
    (* TODO: this currently only goes one direction.
       As a design question, is that what I want?
     *)
    | sort_eq_rule c t1 t2 =>
        sequent_of_states
          (@!let sub <- add_ctx false c in
             let x1 <- add_open_sort false sub t1 in
             ret (sub,x1))
          (fun '(sub,x1) =>
             @! let x2 <- add_open_sort true sub t2 in
               (union x1 x2))
    | term_eq_rule c e1 e2 t => 
        sequent_of_states
          (@!let sub <- add_ctx false c in
             let x1 <- add_open_term false sub e1 in
             ret (sub,x1))
          (* TODO: should I add that t is its sort?*)
          (fun '(sub,x1) =>
             @! let x2 <- add_open_term true sub e2 in
               (union x1 x2))
    end.

  End WithLang.
  
  Notation rule_set := (rule_set V V V_map V_map).
  
  
  
  (* Note: only pass in the subset of the language you want to run.
     Often, that will be exactly the equational rules.

     Assumes incl l l'
   *)
  Definition rule_set_from_lang (l l': lang) : rule_set :=
    build_rule_set succ _ (map (uncurry (rule_to_log_rule l'
                                           (analysis_result:=unit))) l).

 

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
    

    Section __.
      Context {X : Type}
        `{analysis V V X}.

      
    Local Notation hash_entry := (hash_entry (symbol:=V) succ (analysis_result:=X)).
      
    Definition egraph_sort_of (x t : V) : state (instance X) bool :=
      @! let t0 <- hash_entry sort_of [x] in
        let t1 <- find t in
        ret eqb t0 t1.

    Definition eq_proven x1 x2 t : state (instance X) bool :=
      @!let b1 <- egraph_sort_of x1 t in
        let b2 <- are_unified x1 x2 in
        ret (andb b1 b2).

    (*TODO: move to Utils *)
    Instance WithDefault_squared {V} `{WithDefault V}
      : WithDefault (WithDefault V) := ltac:(assumption).

    (*Note: l has to contain the ctx_to_rules of the context *)
    Definition egraph_equal l (rws : rule_set) fuel (e1 e2 : Term.term V) (t : Term.sort V) :=
      let comp : state (instance X) bool :=
        @!let {(state (instance X))} x1 <- add_open_term l true [] e1 in
          let {(state (instance X))} x2 <- add_open_term l true [] e2 in
          let {(state (instance X))} xt <- add_open_sort l true [] t in
          let {(state (instance X))} _ <- rebuild 1000 (*TODO: magic number *) in
          (saturate_until succ V_default
             spaced_list_intersect rws (eq_proven x1 x2 xt) fuel)
      in (comp (empty_egraph default X)).

    End __.

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
      Context (symbol_weight : atom -> option N).
      
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

      Definition enter {A S} `{Eqb A} x : stateT S (stateT (list A) option) unit :=
        fun S l => if inb x l then None else Some (tt, S,(x::l)).
      
      Definition exit {A S} `{Eqb A} :  stateT S (stateT (list A) option) unit :=
        fun S l => Some (tt, S, tl l).

      (*TODO: doesn't have to return an option/always returns Some*)
      Fixpoint Mfiltermap {S A B}
        (f : A -> stateT S (stateT (list V) option) B) (l : list A)
        : stateT S (stateT (list V) option) (list B) :=
        match l with
        | [] => Mret []
        | x::l =>
            fun S s =>
              match f x S s with
              | None => Mfiltermap f l S s
              | Some (x', S', s') =>
                  @!let {option} (l', S', s') <- Mfiltermap f l S' s' in
                    ret {option} (x'::l', S', s')
              end
        end.

      Definition memoize {A M} `{Monad M} (f : V -> stateT (V_map A) M A) (x:V)
        : stateT (V_map A) M A :=
        fun S =>
          match map.get S x with
          | Some v => Mret (v,S)
          | None => f x S
          end.

      Definition list_sum := fun l : list N => fold_right N.add 0%N l.

      Notation ST := (stateT (V_map (term * N)) (stateT (list V) option)).
      
    (* returns the weight of the extracted term.
       TODO: memoize
       Maintains a 'visited' stack to avoid cycles
     *)
      Fixpoint extract' fuel eclasses (uf : union_find V (V_map V) (V_map _)) (x : V)
        : stateT (V_map (term * N)) (stateT (list V) option) (term * N) :=
        match fuel with
        | 0 => fun _ _ => None
        | S fuel =>
            let process (x : V) p
              : stateT (V_map (term * N)) (stateT (list V) option) (term * N) :=
              let '(f, args):= p in 
              @!let {ST} _ <- enter x in
                let {ST} weight <-
                      lift (T:= stateT (V_map _))
                        (lift (symbol_weight (Build_atom (f:V) args x))) in
                let {ST} args' <- list_Mmap (memoize (extract' fuel eclasses uf)) args in
                let {ST} _ <- exit in
                ret {ST} (con f (map fst args'),
                    (list_sum (weight::(map snd args'))))
            in
            (* TODO: is find necessary? might always be a no-op *)
            @!let {ST} (_,x') <- lift (T:= stateT (V_map _))
                                   (lift (T:= stateT (list V))
                                      (UnionFind.find _ _ _ _ uf x)) in
              let {ST} cls <- lift (T:= stateT (V_map _))
                                (lift (T:= stateT (list V))
                                   (map.get eclasses x)) in
              let {ST} candidates <- Mfiltermap (process x) cls in
              (lift (T:= stateT (V_map _))
                 (lift (T:= stateT (list V))
                    (minimum (fun x y => N.ltb (snd x) (snd y)) candidates)))
        end.

      Definition build_eclasses {X} : db_map V V _ _ X -> V_map (list (V * list V)) :=
        let process_row f acc args row :=
          let out := row.(entry_value _ _) in
          match map.get acc out with
          | Some l => map.put acc out ((f,args)::l)
          | None => map.put acc out [(f,args)]
          end
        in
        let process_table acc f :=
          map.fold (process_row f) acc
        in
        map.fold process_table map.empty.
        
      Definition extract fuel {X} (i : instance X) x :=
        let cls := (build_eclasses i.(db)) in
        option_map fst
          (option_map fst (extract' fuel cls i.(equiv) x map.empty [])).
      
    (*TODO: differential extraction;
    extract 2 terms together with a shared weight metric (distance)
     *)

    End EExtract.

    Section AnalysisExtract.      
      (* look for node with least weight, interpreting None as oo.
         Note: positive because termination depends on nonzero weight.N
       *)
      Context (symbol_weight : atom -> option positive).

      Definition oP_le (a b : option positive) :=
        match b, a with
        | None, _ => true
        | _, None => false
        | Some b', Some a' => BinPos.Pos.leb a' b'
        end.
      
      Definition oP_lt (a b : option positive) :=
        match a, b with
        | None, _ => false
        | _, None => true
        | Some a', Some b' => BinPos.Pos.ltb a' b'
        end.

      Definition oP_minimum (a b : option positive) :=
        match a, b with
        | None, _ => b
        | _, None => a
        | Some a', Some b' => Some (BinPos.Pos.min a' b')
        end.
      
      Definition oP_maximum (a b : option positive) :=
        match a, b with
        | None, _
        | _, None => None
        | Some a', Some b' => Some (BinPos.Pos.max a' b')
        end.

      Definition oP_add (a b : option positive) :=
        match a, b with
        | None, _
        | _, None => None
        | Some a', Some b' => Some (BinPos.Pos.add a' b')
        end.

      (*TODO: move this somewhere better*)
      Existing Instance PositiveIdx.positive_Eqb.

      Instance weighted_depth_analysis : analysis V V (option positive) :=
        {
          analyze a arg_as :=
            match arg_as with
            | [] => (symbol_weight a)
            | arg0::arg_as' =>
                oP_add (symbol_weight a) (List.fold_left oP_maximum arg_as' arg0)
            end;
          analysis_meet := oP_minimum;
        }.

      (*TODO: deprecate the old one*)
      Definition build_eclasses' {X}
        : db_map V V _ _ X -> V_map (list (V * list V * X)) :=
        let process_row f acc args row :=
          let out := row.(entry_value _ _) in
          let ra := row.(entry_analysis _ _) in
          match map.get acc out with
          | Some l => map.put acc out ((f,args,ra)::l)
          | None => map.put acc out [(f,args,ra)]
          end
        in
        let process_table acc f :=
          map.fold (process_row f) acc
        in
        map.fold process_table map.empty.

      Definition node_lt (x_a : option positive) (p : ne_list V * option positive) :=
        oP_le (snd p) x_a.

      Context (i : instance (option positive)).
      
      Let e_classes := build_eclasses' i.(db).

      Definition decr fuel {A} `{WithDefault A} (f : _ -> A) :=
        match fuel with
        | O => default
        | S fuel' => f fuel'
        end.

      (*TODO: move to Utils*)
      Instance fun_default {A B} `{WithDefault B} : WithDefault (A -> B) :=
        fun _ => default.

      Fixpoint extract_weighted fuel x : option term :=
        @! let x_a <- map.get i.(analyses _ _ _ _ _ _) x in
          let x_class <- map.get e_classes x in
          let (x_f, x_args, _) <- List.find (node_lt x_a) x_class in
          let children <- list_Mmap (decr fuel extract_weighted) x_args in
          ret (con x_f children).
          
    End AnalysisExtract.
    
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
    
    Definition pt_remove pt k :=
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
    Proof using .
    Admitted.
    

    Lemma filter_true_In:
      forall (B : Type) (f : B -> bool) (l : list B),
        (forall x : B, In x l -> f x = true) -> filter f l = l.
    Proof using .
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

    
(*
    Lemma filter_eq_nil : forall [A : Type] (f : A -> bool) (l : list A), filter f l = [] <-> l = [].
    Proof. Abort. (*FALSE!*)
    Hint Rewrite filter_eq_nil : utils.
 *)

    
    Lemma rev_eq_nil C (l : list C)
      : rev l = [] <-> l = [].
    Proof. Admitted.
    Hint Rewrite  rev_eq_nil : utils.

    Hint Rewrite combine_nil : utils.

    
    Lemma map_id C (l : list C)
      : map id l = l.
    Proof using.
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
              if hd [] other_cil then option_map pos_trie_leaf (leaf_intersect other_tries)
              else pt_spaced_intersect'_simple fuel (combine other_cil other_tries)
          | pt1::true_tries =>
              option_map pos_trie_node
                (list_intersect'
                   (fun true_tries => pt_spaced_intersect'_simple fuel
                                        (combine (other_cil++true_cil) (other_tries++true_tries)))
                   (proj_node_map_unchecked pt1)
                   (map proj_node_map_unchecked true_tries))
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


    
    Lemma all_rev T (P : T -> Prop) l
      : all P (rev l) <-> all P l.
    Admitted.
    Hint Rewrite all_rev : utils.
    
    Lemma all_map T T' (f : T -> T') (P : T' -> Prop) l
      : all P (map f l) <-> all (fun x => P (f x)) l.
    Admitted.
    Hint Rewrite all_map : utils.
    
    Lemma all_filter T (P : T -> Prop) l f
      : all P (filter f l) <-> all (fun x => Is_true (f x) -> P x) l.
    Admitted.
    Hint Rewrite all_filter : utils.

    
    Lemma all_impl T (P Q : T -> Prop) l
      : (forall x, In x l -> P x -> Q x) -> all P l -> all Q l.
    Admitted.

    
    Definition not_leaf (p : pos_trie') := if p then False else True.
    Lemma not_leaves_map_proj l
      : all not_leaf l ->
        exists l', l = map pos_trie_node l'.
    Admitted.
    
    Definition merge_list l :=
      match l with
      | [] => None
      | e::es => Some (List.fold_left merge es e)
      end.

    
    Lemma Mbind_option_ext T1 T2 (f g : T1 -> option T2) ma
      : (forall a, ma = Some a -> f a = g a) ->
        Mbind f ma = Mbind g ma.
    Proof. destruct ma; cbn in *; firstorder congruence. Qed.

    
    (* should be a part of Monad_ok at some point*)
    Lemma option_Mbind_assoc T1 T2 T3 (f : T1 -> option T2) (g : T2 -> option T3) ma
      : Mbind (fun a => Mbind g (f a)) ma = Mbind g (Mbind f ma).
    Proof.
      destruct ma; cbn; eauto.
    Qed.
    
    Lemma otree_get_Mbind T k (ma : option (PTree.tree' T))
      : Mbind (PTree.get' k) ma = PTree.get k (otree ma).
    Proof. destruct ma; reflexivity. Qed.

    (*TODO: move to Utils*)
    Definition nonempty {A} (l:list A) :=
      if l then False else True.    
    Definition empty {A} (l:list A) :=
      if l then True else False.
    
    Lemma partition_tries_spec_properties_nonempty cil ptl
      true_cil true_tries other_cil other_tries
        : mk4 true_cil true_tries other_cil other_tries
          = partition_tries_spec cil ptl (mk4 [] [] [] []) ->
          all nonempty cil ->
          let trues := combine (map (cons true) true_cil) true_tries in
          let others := combine (map (cons false) other_cil) other_tries in
          Permutation (combine cil ptl) (trues ++ others)
          /\ length true_cil = length true_tries
          /\ length other_cil = length other_tries.
    Proof.
    Admitted.

    (*TODO: move to TrieMap.v*)    
    Lemma invert_eq_mk4 W X Y Z (w w':W) (x x':X) (y y' : Y) (z z' : Z)
      : mk4 w x y z = mk4 w' x' y' z' <-> w = w' /\ x = x' /\ y = y' /\ z = z'.
    Proof. prove_inversion_lemma. Qed.
    #[local] Hint Rewrite invert_eq_mk4 : utils.

    Hint Rewrite rev_unit : utils.

    
    Lemma rev_combine T1 T2 (l1: list T1) (l2 : list T2)
      : length l1 = length l2 ->
        rev (combine l1 l2) = combine (rev l1) (rev l2).
    Proof using.
      Admitted.

    Lemma map_combine T1 T2 T3 T4 (f : T1 -> T2) (g : T3 -> T4) l1 l2
      : map (pair_map f g) (combine l1 l2) = (combine (map f l1) (map g l2)).
    Proof using.
      clear merge.
      revert l2;
        induction l1;
        destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    Lemma partition_tries_spec_properties_empty cil ptl
      true_cil true_tries other_cil other_tries
      : Datatypes.length cil = Datatypes.length ptl ->
        mk4 true_cil true_tries other_cil other_tries
          = partition_tries_spec cil ptl (mk4 [] [] [] []) ->
          all empty cil ->
          let others := combine other_cil other_tries in
          true_cil = []
          /\ true_tries = []
          /\ Permutation (combine cil ptl) others
          /\ length other_cil = length other_tries.
    Proof.
      unfold partition_tries_spec.
      autorewrite with bool utils.
      intros H0 H'; break; subst.
      autorewrite with bool utils.
      rewrite !List.map_map.
      cbn.
      revert ptl H0;
        induction cil;
        destruct ptl;
        basic_goal_prep;
        try now basic_utils_crush.
      destruct a;
        basic_goal_prep;
        basic_utils_crush.
      1,2:rewrite !filter_false_In; eauto;
      basic_goal_prep;
      apply in_combine_l in H3;
      eapply in_all in H3; eauto.
      1,2: destruct l; cbn in *; tauto.
      rewrite combine_app.
      2:{
        autorewrite with bool utils.
        auto.
      }
      cbn [combine].
      rewrite Permutation_app_comm.
      cbn.
      constructor.
      rewrite <- rev_combine.
      2:{
        autorewrite with bool utils.
        auto.
      }
      rewrite <- Permutation_rev.
      rewrite !filter_true_In.
      2:{
        basic_goal_prep;
        apply in_combine_l in H3;
        eapply in_all in H3; eauto.
        destruct l; cbn in *; tauto.
      }
      rewrite <- List.map_map.
      rewrite map_combine_fst, map_combine_snd by eauto.
      rewrite map_ext_in with (g:=id).
      2:{
        basic_goal_prep.
        eapply in_all in H2; eauto.
        destruct a; cbn in *; tauto.
      }
      rewrite map_id.
      reflexivity.
    Qed.
    
    Lemma combine_map_fst_snd T1 T2 (l : list (T1*T2))
      :  (combine (map fst l) (map snd l)) = l.
    Admitted.

    
    Definition spaced_get1 x (b : bool) m : option _ :=
      if b then PTree.get' x m else Some (pos_trie_node m).

    Definition get_leaf t :=
      match t with
      | pos_trie_leaf a => Some a
      | pos_trie_node m => None
      end.      

    Definition get_map t :=
      match t with
      | pos_trie_leaf a => None
      | pos_trie_node m => Some m
      end.      


    Fixpoint spaced_get' x : list bool * pos_trie' -> option A :=
      match x with
      (* assumes list is also empty*)
      | [] => fun p => get_leaf (snd p)
      (*TODO: get the mbind outside the fun somehow?*)
      | n::x => fun p =>
                  @!let t' <- spaced_get1 n (hd false (fst p)) (proj_node_map_unchecked (snd p)) in
                    (spaced_get' x (tl (fst p), t'))       
      end.

    (*TODO: replace spaced_get w/ this?*)
    Definition spaced_get_ x (p : list bool * pos_trie) : option A :=
      Mbind (spaced_get' x) (option_map (fun t => (fst p, t)) (snd p)).

    Definition zip_bools (l : list _) :=
      List.fold_left
        (fun acc l => map2 orb (combine l acc))
        (tl l)
        (hd [] l).

    (*TODO: add to monad laws*)
    Lemma option_Mbind_Mret T (ma : option T)
      : Mbind Mret ma = ma.
    Proof. destruct ma; reflexivity. Qed.
    Hint Rewrite option_Mbind_Mret : utils.
    
    Lemma option_Mbind_Mret' T1 T2 (f : T1 -> option T2) a
      : Mbind f (Mret a) = f a.
    Proof. reflexivity. Qed.
    Hint Rewrite option_Mbind_Mret' : utils.

    
    Lemma all_app T (P : T -> Prop) l1 l2
      : all P (l1++l2) <-> all P l1 /\ all P l2.
    Admitted.
    Hint Rewrite all_app : utils.

    
    Lemma list_Mmap_None T1 T2 (f : T1 -> option T2) l
      : None = list_Mmap f l ->
        exists x, In x l /\ f x = None.
    Proof.
      induction l;
        repeat (cbn; try case_match);       
        basic_goal_prep;
        basic_utils_crush.
    Qed.      
    
    Lemma leaf_intersect_correct l
      : all (fun t => Is_true (has_depth' 0 t)) l ->
        (leaf_intersect l) = Mbind merge_list (list_Mmap get_leaf l).
    Proof.
      unfold leaf_intersect.
      destruct l; try reflexivity.
      destruct p; try reflexivity.
      repeat basic_goal_prep.
        enough
          (Some (leaf_intersect' a l) =
              match list_Mmap get_leaf l with
              | Some a0 => merge_list (a :: a0)
              | None => None
              end)
          by (case_match; eauto).
        revert a H1; clear H0.
        induction l;
          basic_goal_prep;
          basic_utils_crush.
        case_match; 
          basic_goal_prep;
          basic_utils_crush.
        case_match; 
          basic_goal_prep;
          basic_utils_crush.
        {
          eapply IHl in H2.
          safe_invert H2.
          apply H3.
        }
        {
          symmetry in  case_match_eqn.
          apply list_Mmap_None in case_match_eqn.
          break.
          eapply in_all in H1; eauto.
          basic_goal_prep.
          destruct x;
            basic_goal_prep;
            congruence.
        }
    Qed.

    
    Lemma all2_len T1 T2 (R : T1 -> T2 -> Prop) l1 l2
      : all2 R l1 l2 -> length l1 = length l2.
    Proof.
      revert l2; induction l1; destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Hint Rewrite app_length : utils.

    
    Lemma Permutation_combine_l T1 T2 (l1 l1' : list T1) (l2 l2' : list T2)
      : length l1 = length l2 ->
        Permutation (combine l1 l2) (combine l1' l2') ->
        Permutation l1 l1'.
    Proof.
    Admitted.
    
    Lemma Permutation_combine_r T1 T2 (l1 l1' : list T1) (l2 l2' : list T2)
      : length l1 = length l2 ->
        Permutation (combine l1 l2) (combine l1' l2') ->
        Permutation l2 l2'.
    Proof.
    Admitted.

    Require Import Coq.Classes.Morphisms.
    Instance all_Permutation_Proper {T P} : Proper (@Permutation T ==> iff) (all P).
    Proof.
      intros l1 l2.
      induction 1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Lemma all2_impl T1 T2 (R R' : T1 -> T2 -> Prop) l1 l2
      : (forall x y, In (x,y) (combine l1 l2) -> R x y -> R' x y) ->
        all2 R l1 l2 -> all2 R' l1 l2.
    Proof.
      revert l2; induction l1; destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma all_all2_r T1 T2 (P : T2 -> Prop) l1 l2
      : all2 (fun _ : T1 => P) l1 l2 -> all P l2.
    Proof.
      revert l2; induction l1; destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    (*TODO: this is probably already defined somewhere. Move to utils and dedup.*)
    Definition option_rel {X Y} (R : X -> Y -> Prop) mx my :=
      match mx, my with
      | Some x, Some y => R x y
      | None, None => True
      | _, _ => False
      end.
    
    Instance Mbind_Proper {T1 T2} {R : T1 -> _} {R' : option T2 -> _} `{Reflexive _ R'}
      : Proper ((R ==> R') ==> option_rel R ==> R') Mbind.
    Proof.
      intros f1 f2 Hf x1 x2 Hx.
      unfold option_rel in *.
      destruct x1, x2; cbn in *; try reflexivity; try tauto.
      apply Hf; auto.
    Qed.

    Context (merge_comm : forall a b, merge a b = merge b a).
    Context (merge_assoc : forall a b c, merge a (merge b c) = merge (merge a b) c).
    
    Lemma merge_n_opt_Permutation x y
      : Permutation x y ->
        let m' a b := match a with None => Some b | Some a => Some (merge a b) end in
        fold_left m' x None
        = fold_left m' y None.
    Proof.
      intro Hp.
      generalize dependent (@None A).
      induction Hp;
        basic_goal_prep;
        basic_utils_crush.
      all:subst m'.
      all:basic_goal_prep.
      all: try case_match;
        basic_goal_prep;
        basic_utils_crush.
      all: congruence.
    Qed.

    Lemma merge_list_fold_left l
      : let m' a b := match a with None => Some b | Some a => Some (merge a b) end in
        merge_list l = fold_left m' l None.
    Proof.
      unfold merge_list.
      destruct l; cbn; auto.
      revert a.
      induction l;
        try case_match;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
      
    Instance merge_list_Proper
      : Proper (@Permutation _ ==> eq) merge_list.
    Proof.
      intros x y Hp.
      rewrite !merge_list_fold_left.
      apply merge_n_opt_Permutation; auto.
    Qed.
    
    Instance option_all_Permutation_Proper {T}
      : Proper (@Permutation _ ==> option_rel (@Permutation T)) option_all.
    Proof.
      intros x y Hp.
      unfold option_rel.
      induction Hp.
      { cbn; reflexivity. }
      {
        revert IHHp; cbn.
        repeat (case_match;cbn);
          basic_goal_prep;
          basic_utils_crush.
      }
      {
        repeat (case_match;subst; cbn in *);
                basic_goal_prep;
          basic_utils_crush.
        1: constructor.
      }
      {
        revert IHHp1 IHHp2; cbn.
        repeat (case_match;cbn);
          basic_goal_prep;
          basic_utils_crush.
        rewrite IHHp1.
        auto.
      }
    Qed.
    
    
    Lemma pt_spaced_intersect'_simple_correct fuel x cil1 cil2 ptl1 ptl2
      : (fuel > length x)%nat ->
          all (fun p => length p = length x) cil1 ->
          all (fun p => length p = length x) cil2 ->
          all2 (fun c t => Is_true (has_depth' (length (filter id c)) t)) cil1 ptl1 ->
          all2 (fun c t => Is_true (has_depth' (length (filter id c)) t)) cil2 ptl2 ->
          spaced_get_ x (zip_bools (cil1++cil2), pt_spaced_intersect' fuel cil1 ptl1 cil2 ptl2)
          = Mbind merge_list (list_Mmap (spaced_get_ x) (combine (cil1++cil2)
                                                                 (map Some (ptl1 ++ ptl2)))).
    Proof.
      unfold spaced_get_.
      rewrite Mbind_option_map.
      cbn [fst snd].
      revert x cil1 cil2 ptl1 ptl2.
      induction fuel; intros; try Lia.lia.
      cbn [pt_spaced_intersect'].
      rewrite partition_tries_app.
      2:{ eapply all2_len; eauto. }
      rewrite partition_tries_correct.
      set (p := partition_tries_spec _ _ _).
      remember p as p'.
      subst p.
      destruct p' as [? ? ? ?].
      destruct x.
      {
        apply partition_tries_spec_properties_empty in Heqp'.
        2:{
          autorewrite with utils.
          apply all2_len in H4, H3.
          rewrite H4, H3.
          reflexivity.
        }
        2:{
          basic_utils_crush.
          all:eapply all_impl; try eassumption.
          all:unfold empty.
          all:basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        basic_goal_prep; subst.
        eapply all_const in H1, H2.
        2,3: intro y; destruct y; cbn in *; try Lia.lia; reflexivity.
        assert (p43 = repeat [] (Datatypes.length p44)) by admit. (*provable*)
        subst p43.
        rewrite repeat_default_hd.
        change (match ?c with
                | Some pt => @?f pt
                | None => None
                end)
          with (Mbind f c).
        rewrite Mbind_option_map.
        cbn -[Mbind].
        change (@Some ?A) with (@Mret option _ A).
        rewrite option_Mbind_Mret.
        rewrite leaf_intersect_correct.
        2:{
          symmetry in H7.
          apply Permutation_combine_r in H7.
          2: basic_utils_crush.
          rewrite H7.
          autorewrite with utils.
          split.
          all: eapply all_all2_r.
          all: eapply all2_impl; eauto.
          all: basic_goal_prep.
          {
            apply in_combine_l in H5.
            rewrite H1 in H5.
            apply repeat_spec in H5.
            subst.
            cbn in *; eauto.
          }
          {
            apply in_combine_l in H5.
            rewrite H2 in H5.
            apply repeat_spec in H5.
            subst.
            cbn in *; eauto.
          }
        }
        {
          eapply Mbind_Proper.
          1:eapply merge_list_Proper.
          rewrite !Mmap_option_all.
          apply option_all_Permutation_Proper.
          basic_utils_crush.
          apply Permutation_combine_r in H7.
          2:admit(*length*).
          rewrite <- H7.
          erewrite map_ext_in
            with (f:=(fun p : list bool * pos_trie =>
                        match option_map (fun t : pos_trie' => (fst p, t)) (snd p) with
                        | Some a => get_leaf (snd a)
                        | None => None
                        end)).
          2:{
            intros.
            replace (fst a) with (@nil bool) by admit.
            instantiate (1:= fun a => _ (snd a));
              cbn.
            instantiate (1:= Mbind get_leaf).
            destruct (snd a); reflexivity.
          }
          (*
          rewrite <- map_Mmap
          TODO: map 
        }
          replace p44 with (ptl1 ++ ptl2) by admit.
         Definitely true, just needs lemmas
                            Lemma all_Permutation_Proper P : Proper (Permutation ==> iff) (all P).
        Lemma merge_list_Permutation_Proper
        cil1,2 = repeat [].
        (map cons false p43) incl cil1,2, so p43 = []

                            
        replace 
        TODO: need to assert that p43 nonempty?
        rewrite leaf_intersect_correct.
        admit (*TODO leaf_intersect lemma*).
      }
      {
        apply partition_tries_spec_properties_nonempty in Heqp'.
        2:{
          basic_utils_crush.
          all:eapply all_impl; try eassumption.
          all:unfold nonempty.
          all:basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        break.
        replace (combine (cil1 ++ cil2) (map Some (ptl1 ++ ptl2)))
          with (map (pair_map id Some) (combine (cil1 ++ cil2) (ptl1 ++ ptl2)))
          by admit.
        replace (combine (cil1 ++ cil2) (ptl1 ++ ptl2))
        with (combine (map (cons true) p41) p42 ++ combine (map (cons false) p43) p44)
          by admit.
        replace (zip_bools (cil1 ++ cil2))
          with (zip_bools ((map (cons true) p41) ++ (map (cons false) p43)))
          by admit.
        destruct p42, p41; try (basic_goal_prep;congruence).
        {
          destruct (hd [] p43); [admit (*contradiction*)|].
          (*TODO: bools permutation
          rewrite IHfuel. *)
          cbn [map app].
          replace (zip_bools (map (cons false) p43)) with (cons false (zip_bools p43))
            by admit.
          cbn [spaced_get' fst snd hd tl spaced_get1].
          rewrite !option_Mbind_assoc.
          change (fun x => ?f x) with f in *.
          cbn [combine app].
          rewrite <- !option_Mbind_assoc.
          unfold Mbind at 3.
          cbn - [Mbind].
          unfold Mbind at 2.
          cbn - [Mbind].
          rewrite Mbind_option_ext
            with (g:= fun a => spaced_get' x (zip_bools p43, a)).
          2: admit (*TODO: depth reasoning*).
          change (match ?c with
                  | Some pt => @?f pt
                  | None => None
                  end)
            with (Mbind f c).
          replace (zip_bools p43) with (zip_bools (p43 ++[])) by basic_utils_crush.
          rewrite IHfuel by admit.
          f_equal.
          basic_utils_crush.
          replace (map (pair_map id Some) (combine (map (cons false) p43) p44))
            with (map (pair_map (cons false) Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          replace (combine p43 (map Some p44))
            with (map (pair_map id Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          rewrite !Mmap_option_all.
          rewrite !List.map_map.
          f_equal.
          eapply map_ext.
          basic_goal_prep.
          (*TODO: remember that p0 has positive depth, i.e. is a map*)
          replace (pos_trie_node (proj_node_map_unchecked p0)) with p0 by admit.
          reflexivity.
        }
        {
          change (match ?c with
                  | Some pt => @?f pt
                  | None => None
                  end)
            with (Mbind f c).
          replace (zip_bools (map (cons true) (l :: p41) ++ map (cons false) p43))
            with (true::(zip_bools (l :: p41 ++ p43))) by admit.
          cbn [spaced_get' fst snd hd tl spaced_get1].
          rewrite !option_Mbind_assoc.
          change (fun x => ?f x) with f in *.
          rewrite <- !option_Mbind_assoc.
          change (@Some ?A)
            with (@Mret option _ A).
          change (Mbind ?f (Mret ?a)) with (f a).
          cbn beta.
          rewrite !option_Mbind_assoc.
          rewrite otree_get_Mbind.
          rewrite list_intersect'_correct.
          2:admit.
          change (@PTree.option_map) with (@Mbind option _).
          rewrite !Mmap_option_all.
          rewrite <- !option_Mbind_assoc.
          (*TODO: flip order to make this a change?*)
          replace (zip_bools (l :: p41 ++ p43))
            with (zip_bools (p43 ++ l :: p41)) by admit.
          erewrite Mbind_option_ext.
          2:{
            intros.
            apply IHfuel; admit.
          }
          rewrite !option_Mbind_assoc.
          f_equal.
          rewrite <- !Mmap_option_all.
          TODO: pile of permute/ get goop.
          Mbind f (option_all l)
          = 
          

          Fail.
          rewrite !List.map_map.
          unfold id.
          remember (l::p41) as p41'.
          remember (p0::p42) as p42'.
          cbn -[Mbind option_all].
          change (Mbind ?f (Some ?a)) with (f a).
          cbn -[Mbind option_all].
          cbn beta.
          rewrite <- !option_Mbind_assoc.
          
          rewrite <- surjective_pairing.
          TODO: manage get' on both sides
          rewrite !option_Mbind_assoc.
          









          
          change (match ?c with
                  | Some pt => @?f pt
                  | None => None
                  end)
            with (Mbind f c).
          replace (zip_bools p43) with (zip_bools (p43 ++[])) by basic_utils_crush.
          rewrite IHfuel by admit.
          f_equal.
          basic_utils_crush.
          replace (map (pair_map id Some) (combine (map (cons false) p43) p44))
            with (map (pair_map (cons false) Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          replace (combine p43 (map Some p44))
            with (map (pair_map id Some) (combine p43 p44)).
          2:{
            unfold pair_map.
            rewrite !map_combine_separated.
            rewrite ! map_id.
            reflexivity.
          }
          rewrite !Mmap_option_all.
          rewrite !List.map_map.
          f_equal.
          eapply map_ext.
          basic_goal_prep.
          (*TODO: remember that p0 has positive depth, i.e. is a map*)
          replace (pos_trie_node (proj_node_map_unchecked p0)) with p0 by admit.
          reflexivity.
        }

      
    Lemma pt_spaced_intersect'_simple_correct fuel x l
      : (fuel > length x)%nat ->
          all (fun p => length (fst p) = length x) l ->
          all (fun p => Is_true (has_depth' (length (filter id (fst p))) (snd p))) l ->
          spaced_get_ x (zip_bools l, pt_spaced_intersect'_simple fuel l)
          = Mbind merge_list (list_Mmap (spaced_get_ x) (map (pair_map id Some) l)).
    Proof.
      unfold spaced_get_.
      rewrite Mbind_option_map.
      cbn [fst snd].
      revert x l.
      induction fuel; intros; try Lia.lia.
      cbn [pt_spaced_intersect'_simple].
      set (p := partition_tries_spec _ _ _).
      remember p as p'.
      subst p.
      destruct p' as [? ? ? ?].
      destruct x.
      {
        apply partition_tries_spec_properties_empty in Heqp'.
        2:{
          rewrite all_map.
          eapply all_impl; try apply H1.
          unfold empty.
          basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        basic_goal_prep; subst.
        admit (*TODO leaf_intersect lemma*).
      }
      {
        apply partition_tries_spec_properties_nonempty in Heqp'.
        2:{
          rewrite all_map.
          eapply all_impl; try apply H1.
          unfold nonempty.
          basic_goal_prep; case_match; subst; cbn in *; eauto;
            congruence.
        }
        break.
        rewrite combine_map_fst_snd in *.
        destruct p42, p41; try (basic_goal_prep;congruence).
        {
          destruct (hd [] p43); [admit (*contradiction*)|].
          (*TODO: bools permutation
          rewrite IHfuel. *)
          admit.
        }
        {
          rewrite !Mbind_option_map.
          cbn [spaced_get'].
          cbn [fst snd].
          rewrite !option_Mbind_assoc.
          cbn [get_map].
          change (fun x => ?f x) with f in *.
          change (Mbind (A:=(PTree.tree' pos_trie')) Some)
            with (Mbind (M:=option) (A:=(PTree.tree' pos_trie')) Mret).
          rewrite option_Mbind_Mret.
          (*TODO: because the true list is nonempty*)
          replace (hd false (zip_bools l)) with true by admit.
          cbv [spaced_get1].
          change (fun x => ?f x) with f in *.
          rewrite otree_get_Mbind.
          rewrite list_intersect'_correct.
          2:admit.
          change (@PTree.option_map) with (@Mbind option _).
          rewrite Mmap_option_all with (l:=(map (pair_map id Some) l)).
          erewrite map_ext with (l:=(map (pair_map id Some) l)).
          2:{
            intros.
            rewrite Mbind_option_map.
            cbn [fst snd].
            rewrite option_Mbind_assoc.
            instantiate (1:= fun a => Mbind _ (snd a)).
            cbn beta.
            destruct a; cbn.
            destruct o; cbn; [|reflexivity].
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            rewrite option_Mbind_assoc.
            instantiate (1:= fun a2 => Mbind _ (get_map a2)).
            instantiate (1:= fun a2m => if hd false (fst a) then _ else _).
            cbn.
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            destruct (hd false l1).
            {
              rewrite <- option_Mbind_assoc.
              destruct (get_map p1); cbn; auto.
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            instantiate (1:= Mbind (fun a' : pos_trie' => spaced_get' x (tl (fst a), a')) (PTree.get' p a2m)).
            reflexivity.
            }
            {
              rewrite <- option_Mbind_assoc.
              destruct (get_map p1); cbn; auto.
            change (match ?c with
                    | Some pt => @?f pt
                    | None => None
                    end)
              with (Mbind f c).
            instantiate (1:= spaced_get' x (tl (fst a), pos_trie_node a2m)).
            reflexivity.
            }
          }
          rewrite <- Mmap_option_all with (l:=(map (pair_map id Some) l)).
          
          unfold spaced_get.
          cbn [pt_get].
          TODO: destruct 
                  (list_Mmap (PTree.get' p) (cons (proj_node_map_unchecked p0) (map proj_node_map_unchecked p42)))
                  and the map spaced_gets
          replace (tl (zip_bools l))
            with (combine (app p43 (cons l0 p41)) (app p44 true_tries)).
          rewrite <- !option_Mbind_assoc.
          Unset Printing Notations.
          rewrite !Mbind_option_map.
          
          Fail.
      change (match ?c with
              | Some pt => Some (?f pt)
              | None => None
              end)
        with (option_map f c) in *.
      cbn [fst snd].
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c) in *.
      rewrite !Mbind_option_map.
      cbn [fst snd].
      rewrite !option_Mbind_assoc.
      replace (hd false (zip_bools l)) with true by admit.
      cbv [spaced_get1].
      rewrite <- !option_Mbind_assoc.
      cbn.
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      cbn [Datatypes.length] in *.
      subst mout.
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      rewrite !option_Mbind_assoc.
      rewrite otree_get_Mbind.
      rewrite list_intersect'_correct.
      2: admit.
      change (@PTree.option_map) with (@Mbind option _).
      rewrite <- !option_Mbind_assoc.
      cbn.
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      rewrite <- !option_Mbind_assoc.
      
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      
      answer: this is the false case?
      TODO: spaced get of list_intersect'?
                   why is x not a cons?
      list_intersect'_correct
      specialize (IHfuel x (tl l) ltac:(Lia.lia)).
      cbn [fst snd] in IHfuel.
      rewrite Mbind_option_map in IHfuel.
      subst mout.
      TODO: list intersect
      (combine (p43 ++ p41) (p44 ++ true_tries))
      TODO: IH doesn't have the append
      rewrite IHfuel.
      
          destruct mout; cbn -[Mbind].
          {
            unfold Mbind at 1.
            cbn -[Mbind].
            rewrite !option_Mbind_assoc.
z            TODO: fold mbind
            replace (hd false
                     (fold_left (fun acc l0 : list bool => map2 orb (combine l0 acc)) (tl (map fst l)) (hd [] (map fst l))))
              with true by admit.
            cbn.
            TODO:
          rewrite <- !option_Mbind_assoc.
          rewrite option_eta_equiv with
            (k:=fun mout => spaced_get (p :: x)
                               (bools, match mout with
                                       | Some pt => Some (pos_trie_node pt)
                                       | None => None
                                       end)) (o:=mout).
          subst mout.
          unfold option_eta; cbn.
          unfold 
          spaced_get (p::k) := Mbind (spaced_get k) (get p (project m)).
          TODO: spaced_get should eval on cons key?.
          alt unfold everywhere
          end.
          option_eta
          list_intersect'_correct
        }

      Fail.



      
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
        shelve.
      }
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
      assert (all not_leaf (p::H3)).
      {
        rewrite HeqH3.
        autorewrite with utils bool.
        eapply all_impl; eauto.
        basic_goal_prep.
        destruct l0 as [| [] ?];
          basic_goal_prep;
          try tauto.
        destruct p0;
          tauto.
      }
      apply not_leaves_map_proj in H4.
      break.
      destruct x0; cbn in H4; try congruence.
      safe_invert H4.
      rewrite List.map_map with (f:=pos_trie_node).
      cbn [proj_node_map_unchecked].
      rewrite map_id.
      rewrite List.map_map in HeqH3.
      cbn in HeqH3.
      change (fun x => ?f x) with f in *.
      destruct x.
      {
        basic_goal_prep.
        assert (l = combine (repeat [] (length l)) (map snd l)).
        {
          revert H1; clear.
          induction l;
            basic_goal_prep;
            basic_utils_crush.
        }
        rewrite H3 in HeqH3.
        basic_utils_crush.
        rewrite filter_false_In in HeqH3.
        2:{
          basic_goal_prep.
          apply in_combine_l in H4.
          apply repeat_spec in H4.
          subst.
          reflexivity.
        }
        basic_goal_prep.
        congruence.
      }
      remember ((fold_left (fun acc l0 : list bool => map2 orb (combine l0 acc)) (tl (map fst l))
                   (hd [] (map fst l)))) as bools.
      destruct bools.
      1: admit (*TODO: contradiction *).
      cbn [combine filter map fst snd].
      destruct b.
      {
        cbn [map fst pt_get'].
      change (match ?c with
              | Some pt => @?f pt
              | None => None
              end)
        with (Mbind f c).
      rewrite option_Mbind_assoc.
      rewrite otree_get_Mbind.
      erewrite list_intersect'_correct.
      2:admit (*TODO*).
      change (@PTree.option_map) with (@Mbind option _).
      rewrite <- option_Mbind_assoc.
      cbn.
      TODO: top-level thought:
          would it be better to prove a list-of-lists induction principle?.
      would it be sufficient to have a destructor since we induct on fuel?.
      note: could replace l im bools w/ output of partition via perm
      TODO: IH
      basic_utils_crush.

      Proof sketch:
        input splits into 


      
      TODO: Mbind_assoc
      TODO: may be n falses, need the first true!
      TODO: have to pull the first bool out of map2 orb.
      Question: can I transpose the listoflists?. probably not
      have it be a list of tuples, rather than a tuple of lists?.
      might be easier to work with.
        contradiction.
        cbn.
        rewrite H3 in HeqH3.
        
      TODO: evaluation blocked on x. if empty, behaves diff.x
      erewrite Mbind_option_ext.
      2:{
        intros.
        TODO: x empty?
        cbn.
      cbv [pt_get'].

      Lemma pt_get'_PTree_get'
        :   pt_get

      TODO: need the PTree.get'
        
      TODO: what do I know here?
      TODO: need to know that there's a 'true' in the bools list?.
      QUestion: should bools be constrained propositinally rather than defined?.
      TODO: apply H1,h2 in p::H3?
      
      TODO: pt_get' to PTree.get x0 (otree 
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
  Definition egraph_equal {X} `{analysis _ _ X}
    : lang positive -> rule_set positive positive trie_map trie_map ->
      nat -> Term.term positive -> Term.term positive -> Term.sort positive ->
      _ * instance _ _ _ _ _ X :=
    (egraph_equal ptree_map_plus (@pos_trie_map) Pos.succ sort_of (@compat_intersect)).

  (*TODO: move somewhere?*)
  Definition filter_eqn_rules {V} : lang V -> lang V :=
    filter (fun '(n,r) => match r with term_rule _ _ _ | sort_rule _ _ => false | _ => true end).

  Definition build_rule_set : lang positive -> lang positive -> rule_set positive positive trie_map trie_map :=
    rule_set_from_lang ptree_map_plus _ Pos.succ sort_of (*fold_right Pos.max xH *).
  
  (* all-in-one when it's not worth separating out the rule-building.
     Handles renaming.
     
   (*TODO: handle term closing, sort matching*)
   *)
  Definition egraph_equal' {V} `{Eqb V} {X} `{analysis V V X} (l : lang V) n c (e1 e2 : Term.term V) (t : Term.sort V) : _ :=
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

  Definition egraph_equal {X} `{analysis _ _ X}
    : lang string -> rule_set string string string_trie_map string_trie_map ->
      nat -> _ -> Term.term string -> Term.term string -> Term.sort string ->
      _ * instance _ _ _ _ _ X :=
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
      (* fold_right string_max "x0" *).

End StringInstantiation.
