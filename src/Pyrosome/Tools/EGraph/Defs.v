(*
   Based on this paper, with some deviation:
   Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker,
   Eli Rosenthal, Zachary Tatlock, and Max Willsey. 2023.
   Better Together: Unifying Datalog and Equality Saturation.
   Proc. ACM Program. Lang. 7, PLDI, Article 125 (June 2023), 25 pages.
   URL: https://doi.org/10.1145/3591239
 *)
Set Implicit Arguments.

From coqutil Require Import Datatypes.String Datatypes.Result.
From Stdlib Require Import
  NArith.BinNat Lists.List Sorting.Permutation.
Import ListNotations.

From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad Result ExtraMaps.
From Utils.EGraph Require Import Semantics Defs QueryOpt.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Theory Require ClosedTerm.
Import Core.Notations.

Open Scope string.
Open Scope list.


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

  Fixpoint con_to_var vars (t : term) :=
    match t with
    | var x => var x (*should never happen *)
    | con n s =>
        if inb n vars then var n else con n (map (con_to_var vars) s)
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
      (* A flag for determining whether to emit secondary sort annotations
         for arguments to allow for sort unification.
         Default to false.
       *)
      Context (with_ctx_sorts : bool).

    Section __.
      Context (add_open_sort : named_list V -> Term.sort V -> state instance V).

       Definition add_ctx_sorts s' (c:ctx) :=
        let tsub := combine (map fst c) s' in
        list_Miter (fun '(x,t) => 
                      @!let tx <- add_open_sort tsub t in
                        (update_entry (Build_atom sort_of [x] tx)))
          (combine s' (map snd c)).
      
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
                  let _ <- if with_ctx_sorts then add_ctx_sorts s' c
                           else Mret tt in
                  if with_sorts then
                    let tsub := combine (map fst c) s' in
                    let tx <- add_open_sort tsub t in
                    let _ <- update_entry (Build_atom sort_of [x] tx) in
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
            match named_list_lookup_err l n with
            | Some (sort_rule c args) =>
                @! let s' <- list_Mmap (add_open_term' (add_open_sort' fuel) sub) s in
                  let _ <- if with_ctx_sorts then add_ctx_sorts (add_open_sort' fuel) s' c
                           else Mret tt in
                  (hash_entry n s')
            | _ => Mret default (*should never happen*)
            end
      end.

    (*
      The recursion is bounded by the number of rules since every term in a sort
      must be of a previously defined sort.
     *)
    Definition add_open_sort := add_open_sort' (S (length l)).
    Definition add_open_term := add_open_term' add_open_sort.
    

  Notation alloc_opaque :=
    (alloc_opaque V succ V V_map V_map V_trie _).


  Definition add_ctx (c : ctx) : state instance _ :=
    list_Mfoldr (fun '(x,t) sub =>
                   (*use the empty substitution to indicate the identity.
                      Assumes that the input egraph starts with an allocator
                    *)
                   @! let t_v <- add_open_sort sub t in
                     (* using the variables from ctx isn't sound,
                          so we make sure to allocate a fresh one.
                          We also write a default analysis value
                          so that things are analyzable and rebuilding doesn't loop
                      *)
                     let {(state instance)} x' <- alloc_opaque in
                     (*Note: do not replace with update_entry.
                       It does not work correctly, likely with
                       the unmapped variables in rule compilation.
                      *)
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
    Context (rf : nat).
    Notation sequent_of_states a c := (sequent_of_states a c rf).
  (*
    
   TODO: (IMPORTANT) pick a var order. Currently uses an unoptimized order

   *)
  Definition rule_to_log_rule n (r : rule) : sequent V V :=
    match r with
    | sort_rule c args =>        
        sequent_of_states
          (add_ctx false false c)
          (fun sub => add_open_sort true false sub (scon n (id_args c)))
    | term_rule c args t => 
        sequent_of_states
          (add_ctx false false c)
          (* add_open_term sees the language, so it handles t *)
          (fun sub => add_open_term true false sub (con n (id_args c)))
    (* TODO: this currently only goes one direction.
       As a design question, is that what I want?
     *)
    | sort_eq_rule c t1 t2 =>
        sequent_of_states
          (@!let sub <- add_ctx false false c in
             let x1 <- add_open_sort false false sub t1 in
             ret (sub,x1))
          (fun '(sub,x1) =>
             @! let x2 <- add_open_sort true false sub t2 in
               (union x1 x2))
    | term_eq_rule c e1 e2 t => 
        sequent_of_states
          (@!let sub <- add_ctx false false c in
             let x1 <- add_open_term false false sub e1 in
             ret (sub,x1))
          (* TODO: should I add that t is its sort?*)
          (fun '(sub,x1) =>
             @! let x2 <- add_open_term true false sub e2 in
               (union x1 x2))
    end.

  End WithLang.
  
  Notation rule_set := (rule_set V V V_map V_map).
  
  
  
  (* Note: only pass in the subset of the language you want to run.
     Often, that will be exactly the equational rules.

     Assumes incl l l'
   *)
  Definition rule_set_from_lang rf (l l': lang) : rule_set :=
    build_rule_set succ _ rf (map (uncurry (rule_to_log_rule l'
                                           (analysis_result:=unit) rf)) l).

 
  Section AnalysisExtract.
      (* look for node with least weight, interpreting None as oo.
         Note: positive because termination depends on nonzero weight.
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

      (* For each eclass, select a node that is optimal for it *)
      Definition select_optimal_nodes {X}
        (le : X -> X -> bool)
        (analyses : V_map X)
        : db_map V V _ _ X -> V_map (V * list V) :=
        let process_row f acc args row :=
          let out := row.(entry_value _ _) in
          let ra := row.(entry_analysis _ _) in
          match map.get analyses out with
          | None => acc (* shouldn't happen? *)
          | Some a => if le ra a then map.put acc out (f,args) else acc
          end
        in
        let process_table acc f :=
          map.fold (process_row f) acc
        in
        map.fold process_table map.empty.

      (*
      Definition atom_le (x_a : option positive) (p : ne_list V * option positive) :=
        oP_le (snd p) x_a.*)
      
      (* properly generalize this to X*)
      Context (i : instance (option positive)).
      
      Let optimal_nodes := select_optimal_nodes oP_le i.(analyses) i.(db).

      (*for testing*)
      Definition return_optimal_nodes := optimal_nodes.

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

      (*TODO: move to StateMonad*)
      Definition stateT_get {S M} `{Monad M} : stateT S M S :=
        fun s => Mret (s,s).
      (*returns the put element for convenience*)
      Definition stateT_put {S M} `{Monad M} x : stateT S M unit :=
        fun _ => Mret (tt,x).

      
      Section Memoize.
        Context {A B} {mp : map.map A B} {M} `{Monad M}
          (f : forall {MT} `{MonadTrans MT}, (A -> MT M B) -> A -> MT M B).
        Arguments f [MT]%function_scope {H0} _%function_scope _.

        Definition memoizeF (rec : A -> stateT mp M B) (a: A) : stateT mp M B :=
          @! let s <- stateT_get in
            match map.get s a with
            | Some x => Mret (M:=stateT mp M) x
            | None => @! let {(stateT mp M)} x <- f rec a in
                        let _ <- stateT_put (map.put s a x) in
                        ret {(stateT mp M)} x
            end.
      End Memoize.
      
      Section __.
        Context MT `{MonadTrans MT} (rec : V -> MT result term).
        
        Definition extract_weightedF x : MT result term :=
          @! (*let x_a <- lift (result_of_option_else
                                (map.get i.(analyses) x)
                                error:("No analysis for" x))
            in*)
            let (x_f, x_args) <- lift (result_of_option_else
                                   (map.get optimal_nodes x)
                                   error:("No optimal node for for" x)) in
            let children <- list_Mmap rec x_args in
            ret (con x_f children).
      End __.

      Fixpoint extract_weighted' fuel : V -> stateT (V_map term) result term  :=
        memoizeF extract_weightedF (decr fuel (extract_weighted')).

      (* Memoized so that the same e_class is never accessed twice.
         This makes the procedure at worst linear in the size of the egraph,
         no matter the size of the output term.

         Note: assumes that the egraph has been fully rebuilt,
         but accepts a non-normal input.
       *)
      Definition extract_weighted fuel x :=
        @!let x' := snd (UnionFind.find i.(equiv) x) in
          let p <- extract_weighted' fuel x' map.empty in
          ret fst p.

      (*So that the optimal nodes can be reused*)
      Definition extract_weighted_list fuel :=
        map (extract_weighted fuel).
      
      
    (* Notes on verifying extraction:
       - cheap option: re-add the term and check id
       - more intensive: extract to an arbitrary model
     *)
          
    End AnalysisExtract.
    

    (*TODO: inherited from functionaldb. fill in.*)
    Context (spaced_list_intersect
              (*TODO: nary merge?*)
              : forall {B} `{WithDefault B} (merge : B -> B -> B),
                ne_list (V_trie B * list bool) ->
                (* Doesn't return a flag list because we assume it will always be all true*)
                V_trie B).
    

    Section __.
      (* TODO: generalize later
      Context {X : Type}
        `{analysis V V X}.
       *)

      
      Local Notation hash_entry := (hash_entry (symbol:=V) succ (analysis_result:=option positive)).
      Local Notation instance := (instance (option positive)).

      Instance depth : analysis V V (option positive) :=
        weighted_depth_analysis (fun _ => Some xH).
      
    Definition egraph_sort_of (x t : V) : state instance bool :=
      @! let t0 <- hash_entry sort_of [x] in
        let t1 <- find t in
        ret eqb t0 t1.

    Definition eq_proven x1 x2 t : state instance bool :=
      @!let b1 <- egraph_sort_of x1 t in
        let b2 <- are_unified x1 x2 in
        ret (andb b1 b2).

    (*TODO: move to Utils *)
    Instance WithDefault_squared {V} `{WithDefault V}
      : WithDefault (WithDefault V) := ltac:(assumption).

    

    (*TODO: move to Monad.v*)
    Fixpoint list_Miter_breakable {A M} `{Monad M}
      (f : A -> M bool) (l : list A) : M bool :=
      match l with
      | [] => @! ret false
      | a :: al' => @! let break <- (f a) in
                      if (break : bool) then ret true
                      else (list_Miter_breakable f al')
      end.
    
    (*TODO: move to Utils.EGraph.Defs *)
    Fixpoint scheduled_saturate_until rfuel
      {X} `{analysis V V X} 
       schedule p fuel
      : state (Defs.instance V V _ _ _ X) bool :=
      match fuel with
      | 0 => Mret false
      | S fuel =>
          let process e : state (Defs.instance V V _ _ _ X) bool :=
            saturate_until succ V_default (analysis_result:= X)
              spaced_list_intersect rfuel (snd e) p (fst e) in
          @! let (done : bool) <- list_Miter_breakable process schedule in
            if done then ret true
            else (scheduled_saturate_until rfuel schedule p fuel)
      end.

    (*Note: l has to contain the ctx_to_rules of the context *)
    Definition egraph_equal l schedule
      rfuel fuel (e1 e2 : Term.term V) (t : Term.sort V) :=
      let comp : state instance (bool * _ * _) :=
        @!let {(state instance)} x1 <- add_open_term l true false [] e1 in
          let {(state instance)} x2 <- add_open_term l true false [] e2 in
          let {(state instance)} xt <- add_open_sort l true false [] t in
          let {(state instance)} _ <- rebuild rfuel in
          let {state instance}res <-
                scheduled_saturate_until rfuel schedule (eq_proven x1 x2 xt) fuel in
          ret (res, x1, x2)
      in (comp (empty_egraph default _)).

    (*TODO: move to Utils Defs.v*)
    Arguments get_analysis {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope {analysis_result}%type_scope
  {H} x _.

    Definition weight_less_than x w : state instance bool :=
      @!let {state instance} w' <- get_analysis x in
        ret {state instance} (oP_lt w' w).
    
    (* TODO: this should terminate quickly when it finds reductions,
       but is there a way to have a simplifier that terminates quickly
       in the last (failing) iteration as well?
       Inherently no in general.
       What should be doable: terminate quickly if you discover
       an injectivity opportunity.
       
     *)
    Definition egraph_simpl l (rws : rule_set) rfuel fuel efuel
      (e : Term.term V) :=
      let comp : state instance V :=
        @!let {state instance} x <- add_open_term l true false [] e in
          let w <- get_analysis x in
          let {state instance} _ <- rebuild rfuel in
          let {state instance} _ <- saturate_until succ V_default
                                      (*TODO: short-circuit as soon as the subject weight decreases*)
        spaced_list_intersect rfuel rws (weight_less_than x w) fuel in
          ret {state instance} x
      in
      let (x,g) := comp (empty_egraph default _) in
      extract_weighted g efuel x.

    (* tries to simplify the two input programs.
       Short circuits as soon as either simplifies according to its weight.
     *)
    Definition egraph_simpl2 l schedule rfuel fuel efuel
      (e1 e2 : Term.term V) :=
      let comp : state instance _ :=
        @!let {state instance} x <- add_open_term l true false [] e1 in
          let {state instance} y <- add_open_term l true false [] e2 in
          let w1 <- get_analysis x in
          let w2 <- get_analysis y in
          let {state instance} _ <- rebuild rfuel in
          let pred :=
            (@!let b1 <- weight_less_than x w1 in
              let b2 <- weight_less_than y w2 in
              ret (orb b1 b2))
          in
          let {state instance} _ <-
        (*TODO: short-circuit as soon as the subject weight decreases*)
        scheduled_saturate_until rfuel schedule pred fuel in
          ret {state instance} (x,y)
      in
      let '(x,y,g) := comp (empty_egraph default _) in
      (extract_weighted g efuel x,extract_weighted g efuel y).


    (* Note: l has to contain the ctx_to_rules of the context. *)
    Definition egraph_reducing_equal_step l schedule
      rfuel fuel (e1 e2 : Term.term V) (*t : Term.sort V*) :=
      let comp : state instance (bool * _ * _) :=
        @!let {(state instance)} x1 <- add_open_term l true false [] e1 in
          let {(state instance)} x2 <- add_open_term l true false [] e2 in
          (*let {(state instance)} xt <- add_open_sort l true false [] t in*)
          let w1 <- get_analysis x1 in
          let w2 <- get_analysis x2 in
          let {state instance} _ <- rebuild rfuel in
          (*TODO: factor out monadic orb? *)
          let pred :=
            (@!let b1 <- weight_less_than x1 w1 in
               if (b1:bool) then ret true else
               let b2 <- weight_less_than x2 w2 in
               if (b2:bool) then ret true else
               (are_unified x1 x2))
          in
          let {state instance}res <-
                scheduled_saturate_until rfuel schedule pred fuel in
          ret (res, x1, x2)
      in (comp (empty_egraph default _)).

    Fixpoint select_inj_args (c : ctx) inj_args (s1 s2 : list term) : option _ :=
      match inj_args, c, s1, s2 with
      | [], [], _, _ => Some []
      | [], (_::_), _, _ => if eqb s1 s2 then Some [] else None
      | x::inj_args', (x',_)::c', e1::s1', e2::s2' =>
          if eqb x x' then
            @!let rest <- select_inj_args c' inj_args' s1' s2' in
              ret (e1,e2)::rest
          else if eqb e1 e2 then select_inj_args c' inj_args s1' s2'
               else None
      | _, _, _, _ => None (* should be unreachable *)
      end.

    (*TODO: include the type?
      going to be a bit of trickiness either way
      TODO: do the same for sorts.
      Right now I think the calling code assumes all sorts are injective.
     *)
    Definition cong_subgoals l inj_list '(e1,e2) :=
      match e1, e2 with
      | con n1 s1, con n2 s2 =>
          match eqb n1 n2, named_list_lookup_err inj_list n1, named_list_lookup_err l n1 with
          | true, Some inj_args, Some (term_rule c _ t) =>
              match select_inj_args c inj_args s1 s2 with
              | Some l => l
              | None => [(e1,e2)]
              end
          | _, _, _ => [(e1,e2)]
          end
      | _,_ => (*shouldn't happen, but this makes the proof easiest*) [(e1,e2)]
      end.
    
    (* Computes egraph equality, but attempts to mitigate e-graph
       explosion by restarting computation when things get simpler.
       When it does, it furthermore tries to use knowledge of injective
       constructors to break down the goal.
       TODO: deduplicate goals
      Note: l has to contain the ctx_to_rules of the context *)
    Fixpoint egraph_reducing_cong l schedule
      rfuel sat_fuel efuel red_fuel inj_list
      (goals : list (Term.term V * Term.term V))
      : result unit :=
      match red_fuel with
        (*TODO: import the notation*)
      | 0 => Failure (dlist.dcons "out of fuel for reduction" dlist.dnil)
      | S red_fuel =>
          (*TODO: iterate congruence*)
          let goals' := flat_map (cong_subgoals l inj_list) goals in
          let process '(e1,e2) :=
            let '(res,x,y,g) := egraph_reducing_equal_step l schedule
                                  rfuel sat_fuel e1 e2 in
            if res then Success tt
            else
              @!let e1' <- extract_weighted g efuel x in
                let e2' <- extract_weighted g efuel y in
                (* TODO: is there a reason to do this? *)
                (*let t' <- extract_weighted g efuel y in*)
                (*TODO: take injectivity into account*)
                (egraph_reducing_cong l schedule
                   rfuel sat_fuel efuel red_fuel inj_list [(e1',e2')])
          in
          list_Miter process goals'
      end.
    
    (* Computes egraph equality, but attempts to mitigate e-graph
       explosion by restarting computation when things get simpler.
       When it does, it furthermore tries to use knowledge of injective
       constructors to break down the goal.
      Note: l has to contain the ctx_to_rules of the context
      TODO: currently drops t! decide whether t is useful.
     *)
    Fixpoint egraph_reducing_equal l schedule inj_list
      rfuel sat_fuel efuel red_fuel (e1 e2 : Term.term V) (*t : Term.sort V*)
      : result unit :=
      egraph_reducing_cong l schedule
        rfuel sat_fuel efuel red_fuel inj_list [(e1,e2)].

    (*TODO: move to defining file*)
    Arguments run1iter {idx}%type_scope {Eqb_idx} idx_succ%function_scope 
      idx_zero {symbol}%type_scope {symbol_map}%function_scope {symbol_map_plus}
      {idx_map}%function_scope {idx_map_plus} {idx_trie}%function_scope 
      {analysis_result}%type_scope {H} spaced_list_intersect%function_scope
      rebuild_fuel%nat_scope rs _.

    (*
    Fixpoint egraph_simpl_capped'
      rws rn en (cap : nat) (e : Term.term V) x g
      : result _ :=
      match cap with
      | O => error:("Term not reduced within" cap "iterations")
      | S cap =>
          let (_,g') := run1iter succ _ spaced_list_intersect rn rws g in
          @! let e' <- extract_weighted g' en x in
            if eqb e e' then (egraph_simpl_capped' rws rn en cap e' x g')            
            else ret e'            
      end.
     *)

    Definition get_extract en x : resultT (state instance) _ :=
      fun g => (extract_weighted g en x, g).
    
    Fixpoint egraph_simpl2_capped'
      rws rn en (cap : nat) (e1 e2 : Term.term V) x1 x2
      : resultT (state instance) (term * term) :=
      match cap with
      | O => Mret error:("Terms not reduced within" cap "iterations")
      | S cap =>
          @! let _ <- lift (run1iter succ _ spaced_list_intersect rn rws) in
            let e1' <- get_extract en x1 in
            let _ <- lift (log_event cap) in
            let _ <- lift (log_event "extracted e1 and e2. cap is") in
             let e2' <- get_extract en x2 in
             if andb (eqb e1 e1') (eqb e2 e2')
             then (egraph_simpl2_capped' rws rn en cap e1' e2' x1 x2)            
             else ret (e1',e2')
      end.
    
    Definition print_egraph
      (g : instance) :=
      (NamedList.named_map (NamedList.named_map (entry_value _ _))
         (NamedList.named_map map.tuples (map.tuples g.(db))),
        map.tuples g.(equiv).(UnionFind.parent _ _ _)).

    End __.
    
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
  Definition egraph_equal
    : lang positive -> _ -> nat ->
      nat -> Term.term positive -> Term.term positive -> Term.sort positive -> _ :=
    (egraph_equal ptree_map_plus (@pos_trie_map) Pos.succ sort_of (@compat_intersect)).

  Definition egraph_reducing_equal
    : lang positive -> _ -> _ -> nat ->
      nat -> nat -> nat -> Term.term positive -> Term.term positive -> _ :=
    (egraph_reducing_equal ptree_map_plus (@pos_trie_map) Pos.succ sort_of (@compat_intersect)).

  (*TODO: move somewhere?*)
  Definition filter_eqn_rules {V} : lang V -> lang V :=
    filter (fun '(n,r) => match r with term_rule _ _ _ | sort_rule _ _ => false | _ => true end).

  Definition build_rule_set : nat -> lang positive -> lang positive -> rule_set positive positive trie_map trie_map :=
    rule_set_from_lang ptree_map_plus _ Pos.succ sort_of (*fold_right Pos.max xH *).

  (*TODO: move *)
  Definition rev_rule {V} (r : rule V) :=
    match r with
    | sort_eq_rule x x0 x1 => sort_eq_rule x x1 x0
    | term_eq_rule x x0 x1 t => term_eq_rule x x1 x0 t
    | _ => r
    end.      

  
  (* all-in-one when it's not worth separating out the rule-building.
     Handles renaming.
     
   (*TODO: handle sort matching*)

   (* TODO: extract magic numbers?*)
   *)
  Definition egraph_equal' {V} `{Eqb V} {X} `{analysis V V X}
    (l : lang V)
    (lang_filter : V * rule V -> bool)
    (reversible : V * rule V -> bool)
    rn n c (e1 e2 : Term.term V) (t : Term.sort V) : _ :=
    let rename_and_run : state (renaming V) _ :=
      @! let l' <- rename_lang (ctx_to_rules c ++ l) in
        let e1' <- rename_term (var_to_con e1) in
        let e2' <- rename_term (var_to_con e2) in
        let t' <- rename_sort (sort_var_to_con t) in
        (* Never filter context rules since they are always constant rules. *)
        let pos_rules <- rename_lang (ctx_to_rules c ++ filter lang_filter l) in        
        (* build in backwards steps *)
        let rev_rules := named_map rev_rule
                           (filter (fun p => reversible p
                                             && lang_filter p)
                              l) in
        let pos_rev_rules <- rename_lang (ctx_to_rules c ++ rev_rules) in       
        ret (egraph_equal l'
               [(10%nat,build_rule_set rn pos_rules l');
                (1%nat,build_rule_set rn pos_rev_rules l')]
               rn n e1' e2' t')
    in
    (*2 so that sort_of is distict*)
    (rename_and_run ( {| p_to_v := map.empty; v_to_p := {{c }}; next_id := 2 |})).
  (*
   (fun g : instance =>
                  (@!let {result} e1' <- extract_weighted g extract_fuel x1 in
                     let {result} e2' <- extract_weighted g extract_fuel x2 in
                     
                     error:(x1 "not identified with" x2
                              "Extracted term 1:" e1'
                              "Extracted term 2:" e2'), g)) *)
  
  Fixpoint unrename_term {V} `{WithDefault V} (r : renaming V)
    (e : Term.term positive) : Term.term V :=
    match e with
    | var x => var (unwrap_with_default (Interface.map.get r.(p_to_v) x))
    | con n s =>
        con (unwrap_with_default (Interface.map.get r.(p_to_v) n))
          (map (unrename_term r) s)
    end.
  
  Definition egraph_simpl
    : lang positive -> rule_set positive positive trie_map trie_map -> nat ->
      nat -> nat -> Term.term positive -> _ :=
    (egraph_simpl ptree_map_plus (@pos_trie_map) Pos.succ sort_of (@compat_intersect)).

  Definition rename_inj {V} `{Eqb V} '(n,args) : state (renaming V) (positive * list positive) :=
    @! let n' <- to_p n in
      let args' <- list_Mmap (to_p (V:=V)) args in
      ret (n',args').
  
  Definition egraph_reducing_equal' {V} `{Eqb V} {X} `{analysis V V X}
    (l : lang V)
    (lang_filter : V * rule V -> bool)
    (reversible : V * rule V -> bool)
    inj_rules
    rn n efuel red_fuel c (e1 e2 : Term.term V) (*t : Term.sort V*) : _ :=
    let rename_and_run : state (renaming V) (result unit) :=
      @! let l' <- rename_lang (ctx_to_rules c ++ l) in
        let e1' <- rename_term (var_to_con e1) in
        let e2' <- rename_term (var_to_con e2) in
        (*let t' <- rename_sort (sort_var_to_con t) in*)
        (* Never filter context rules since they are always constant rules. *)
        let {state (renaming V)} pos_rules <- rename_lang (ctx_to_rules c ++ filter lang_filter l) in        
        (* build in backwards steps *)
        let rev_rules := named_map rev_rule
                           (filter (fun p => reversible p
                                             && lang_filter p)
                              l) in
        let {state (renaming V)} pos_rev_rules <- rename_lang (ctx_to_rules c ++ rev_rules) in
        let renamed_inj_rules <- list_Mmap rename_inj inj_rules in
        ret {state (renaming V)} (egraph_reducing_equal l'
               [(10%nat,build_rule_set rn pos_rules l');
                (1%nat,build_rule_set rn pos_rev_rules l')]
               renamed_inj_rules
               rn n efuel red_fuel e1' e2')
    in
    (*2 so that sort_of is distict*)
    (rename_and_run ( {| p_to_v := map.empty; v_to_p := {{c }}; next_id := 2 |})).

  
End PositiveInstantiation.


Require Ascii.
Module StringInstantiation.
  Export StringListMap.

  Definition egraph_equal
    : lang string -> rule_set string string string_trie_map string_trie_map -> nat ->
      nat -> nat -> _ -> Term.term string -> Term.term string -> Term.sort string ->
      _ * instance _ _ _ _ _ _ :=
    fun l rw rn n en c e1 e2 t =>
    let l' := ctx_to_rules c ++ l in
    egraph_equal string_ptree_map_plus (@string_list_trie_map)
      string_succ sort_of
      (@PosListMap.compat_intersect) l' [(n,rw)] rn 1
      (var_to_con e1) (var_to_con e2) (sort_var_to_con t).
  
  Definition build_rule_set : nat ->
                              lang string ->
                            lang string ->
                            rule_set string string string_trie_map string_trie_map :=
    rule_set_from_lang string_ptree_map_plus _ string_succ sort_of
      (* fold_right string_max "x0" *).

End StringInstantiation.

