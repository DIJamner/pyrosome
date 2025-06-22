(*
   Based on this paper, with some deviation:
   Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker,
   Eli Rosenthal, Zachary Tatlock, and Max Willsey. 2023.
   Better Together: Unifying Datalog and Equality Saturation.
   Proc. ACM Program. Lang. 7, PLDI, Article 125 (June 2023), 25 pages.
   URL: https://doi.org/10.1145/3591239
 *)
Set Implicit Arguments.

Require Import BinNat Datatypes.String Datatypes.Result Lists.List Sorting.Permutation.
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

(*TODO: move to Monad.v *)
Definition resultT (M : Type -> Type) A := M (result A).

#[export] Instance resultT_trans : MonadTrans resultT :=
  {|
    transformer_monad M _ :=
      {|
        Mret _ a := (Mret (Success a));
        Mbind _ _ f :=
          Mbind (M:=M) (fun ma => match ma with
                                      | Success a => f a
                                      | Failure err => Mret (Failure err)
                                      end)
      |};
  lift M _ A ma := @! let a <- ma in ret Success a
  |}.


Definition result_monad : Monad result :=
  Eval cbv in (resultT_trans.(transformer_monad) : Monad (resultT id)).
#[export] Existing Instance result_monad.


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
            @!let (_,x') := UnionFind.find uf x in
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

      Definition result_of_option_else {A} (o : option A) (e : result A) :=
          match o with
          | Some a => Success a
          | None => e
          end.

      (*TODO: move to utils *)
      Instance result_default {A} : WithDefault (result A) :=
        error:("Default value!").

      Fixpoint extract_weighted fuel x : result term :=
        @! let x_a <- result_of_option_else
                        (map.get i.(analyses _ _ _ _ _ _) x)
                        error:("No analysis for" x)
          in
          let x_class <- result_of_option_else
                            (map.get e_classes x)
                            error:("No eclass for" x) in
          let (x_f, x_args, _) <- result_of_option_else
                                    (List.find (node_lt x_a) x_class)
                                    error:(x "has no term of size at most" x_a) in
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
From Utils Require PosListMap StringListMap.
Module PositiveInstantiation.
  Export PosListMap.
  
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
  Export StringListMap.

  Definition egraph_equal {X} `{analysis _ _ X}
    : lang string -> rule_set string string string_trie_map string_trie_map ->
      nat -> _ -> Term.term string -> Term.term string -> Term.sort string ->
      _ * instance _ _ _ _ _ X :=
    fun l rw n c e1 e2 t =>
    let l' := ctx_to_rules c ++ l in
    egraph_equal string_ptree_map_plus (@string_list_trie_map)
      string_succ sort_of
      (@PosListMap.compat_intersect) l' rw n
      (var_to_con e1) (var_to_con e2) (sort_var_to_con t).
  
  Definition build_rule_set : lang string ->
                            lang string ->
                            rule_set string string string_trie_map string_trie_map :=
    rule_set_from_lang string_ptree_map_plus _ string_succ sort_of
      (* fold_right string_max "x0" *).

End StringInstantiation.
