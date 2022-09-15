(*
  Implementation based on Egg: https://dl.acm.org/doi/pdf/10.1145/3434304
 *)
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

(*TODO: clean up imports*)
Require Import Bool String List ZArith.
Import ListNotations.
Open Scope string.
Open Scope list.
From coqutil Require Import Map.Interface.
Require Import List Int63 ZArith.
Import ListNotations.
Open Scope int63.
From Utils Require Import Utils Natlike ArrayList PersistentArrayList.
Import PArrayList (array, length).
From Utils Require Import Utils Natlike ExtraMaps Monad RelationalDB.
Import Sets.
Import Int63QueryTrie.      
      
From Utils Require ArrayList DenseInt63Map TrieMapInt63.
From Named Require Import Term Rule Core.
From Named.egraph Require UnionFindExplained.
Import UnionFindExplained (union_find).
(*Import Core.Notations.*)


Notation named_list := (@named_list int).
Notation named_map := (@named_map int).
Notation term := (@term int).
Notation ctx := (@ctx int).
Notation sort := (@sort int).
Notation subst := (@subst int).
Notation rule := (@rule int).
Notation lang := (@lang int).

  (*
   Big TODO:
   Do I need to include the sorts in the terms?
   reasons I currently include them:
   1. so I can answer queries of the form "What is the type of the term with id x"
   2. (intuitively) so that I can track conversions when destructing wf terms

   For 1:
   - Used for typechecking
   - can be re-constituted by adding the sort from the node's term rule
   - should just be a hashcons lookup, O(n). Worse than O(1), but probably fine

   For 2:
   If for each instance of a conversion, we add the lhs and rhs sorts 
   and rewrite until they are equal, then we should be able to produce a wfness proof
   for any term in the egraph if we can prove 2 invariants:

   (for sorts)
   Invariant 1: let id1 <- add(t1); id2 <- add(t2). If id1 = id2 then c |- t1 = t2.

   (for terms)
   Invariant 2: If find(add(e1)) = find (add(e2)), c |- e1 : t1, and c |- e2 : t2, 
   then c |- t1 = t2 and c|- e1 = e2 : t1


   *)
  
  Variant enode :=
    | con_node : int -> list int -> enode
    (*TODO: separate constructor for sorts?  | scon_node : list int -> enode *)
    | var_node : (*(* sort id*) int ->*) (* var *) int -> enode.

  (* TODO: make sets fast*)

  Fixpoint list_eqb {A} `{Eqb A} (l1 l2 : list A) :=
    match l1, l2 with
    | [], [] => true
    | a1::l1, a2::l2 =>
        (eqb a1 a2) && (list_eqb l1 l2)
    | _, _ => false
    end.

  Axiom TODO: forall {A} , A.

  (* TODO: move to Utils.v once implemented *)

  #[refine] Instance list_Eqb {A} `{Eqb A} : Eqb (list A) :=
    {
      eqb := list_eqb
    }.
  all: apply TODO.
  Defined.

  #[refine] Instance enode_eqb : Eqb enode :=
    {
      eqb n1 n2 :=
      match n1, n2 with
      | var_node x, var_node y => eqb x y
      | con_node n1 s1, con_node n2 s2 =>
          (eqb n1 n2) && (eqb s1 s2)
      | _,_=>false
      end;
    }.
  all: apply TODO.
  Defined.

  Fixpoint named_list_put {A B} `{Eqb A} (l : @Utils.named_list A B) k v :=
    match l with
    | [] => [(k,v)]
    | (k',v')::l =>
        if eqb k k' then (k,v)::l else (k',v')::(named_list_put l k v)
    end.

  Fixpoint named_list_remove {A B} `{Eqb A} (l : @Utils.named_list A B) k :=
    match l with
    | [] => []
    | (k',v')::l =>
        if eqb k k' then l else (k',v')::(named_list_remove l k)
    end.
  
  Section __.
    (* Not fast, but will run*)
    Local Instance named_list_map A B `{Eqb A} : map.map A B :=
      {
        rep := @Utils.named_list A B;
        get := named_list_lookup_err;
        empty := [];
        put := named_list_put;
        remove := named_list_remove;
        fold _ f acc l := List.fold_left (fun acc '(k, v) => f acc k v) l acc;
      }.
  End __.

  Definition node_set := set_from_map (@named_list_map enode unit _).
  Definition node_map := (@named_list_map enode int _).


  (* TODO : separate sort eclasses? it would avoid awkwardness around esort dummy value
   *)
  Record eclass : Type :=
    MkEClass {
        nodes : node_set;
        parents : node_map;
        (* value is unused if the class represents a sort
         TODO: is this the best way? could also fix it as 0
        
        esort : int;*)
      }.

  (*TODO: does a dense or sparse map give better performance here?
    Probably dense, since all nodes initially have their own eclasses
   *)
  Definition eclass_map := DenseInt63Map.map eclass.

  (*{int_map : map.map int int}*)

  (* Fix a specific context that the egraph is operating in.
     This means that we can't reuse egraphs between rules
     in a proof of compiler correctness,
     but it is difficult to do so even when tracking multiple contexts.

     On user programs this is generally the empty context.
   *)
  Record egraph :=
    MkEGraph {
        (* TODO: context sorts added to the egraph at initialization *)
        ectx : named_list int;
        id_equiv : union_find;
        eclasses : eclass_map;
        hashcons : node_map;
        worklist : list int
      }.


  (*Definition union '(ns1,ps1) '(ns2,ps2) : t :=
    (NodeSets.union ns1 ns2, (*TODO: need map union?*)map.union ps1 ps2).*)

  Definition eclass_empty : eclass :=
    MkEClass map.empty map.empty.

  (* more common to call than empty *)
  (* Assumes no parents *)
  Definition eclass_singleton n : eclass := 
    MkEClass (map.singleton n tt) map.empty.

  Definition eclass_add_parent '(MkEClass ns ps) '(pn,pi) : eclass :=
    MkEClass ns (map.put ps pn pi).
  
  (*TODO: use coq-record-update? *)
  Definition set_class_parents '(MkEClass ns _) ps :=
    MkEClass ns ps.

  Definition empty_egraph :=
    MkEGraph [] UnionFindExplained.empty map.empty map.empty [].
  
  
  Section EGraphOps.
    Import StateMonad.

    Local Notation "'ST'" := (ST egraph).

    Definition find a : ST int :=
      fun '(MkEGraph ctx U M H W) =>
        let (U, i) := UnionFindExplained.find U a in
        (MkEGraph ctx U M H W,i).

    Definition alloc : ST int :=
      fun '(MkEGraph ctx U M H W) =>
        let (U, i) := UnionFindExplained.alloc U in
        (MkEGraph ctx U M H W,i).

    Definition hashcons_lookup (n : enode) : ST (option int) :=
      fun g =>
        let mi := map.get g.(hashcons) n in
        (g, mi).

    Definition set_hashcons n i : ST unit :=
      fun '(MkEGraph ctx U M H W) =>
        let H := map.put H n i in
        (MkEGraph ctx U M H W,tt).
    
    Definition remove_hashcons n : ST unit :=
      fun '(MkEGraph ctx U M H W) =>
        let H := map.remove H n in
        (MkEGraph ctx U M H W,tt).
    
    Definition set_eclass (i: int) (c : eclass) : ST unit :=
      fun '(MkEGraph ctx U M H W) =>
        let M := map.put M i c in
        (MkEGraph ctx U M H W,tt).

    Definition union_ids a b expl : ST int :=
      fun '(MkEGraph ctx U M H W) =>
        let (U, i) := UnionFindExplained.union U a b expl in
        (MkEGraph ctx U M H W, i).

    (* return a default value rather than none
     for ease-of-use
     *)
    Definition get_eclass (i : int) : ST eclass :=
      (*TODO: using a meaningless default here.
      Decide if an option is better.
      If I want empty as the default,
      I need to decide that ctx and srt don't matter if empty,
      which seems wrong
       *)
      fun g => (g, unwrap_with_default eclass_empty (map.get g.(eclasses) i)).

    Definition add_to_worklist (i : int) : ST unit :=
      fun '(MkEGraph ctx U M H W) =>
        let W := i::W in
        (MkEGraph ctx U M H W, tt).

    (* Returns the worklist for iteration and removes it from the egraph *)
    Definition pull_worklist : ST (list int) :=
      fun '(MkEGraph ctx U M H W) =>
        (MkEGraph ctx U M H [], W).

    
    (* Returns the egraph's context *)
    Definition get_ectx : ST (named_list int) :=
      fun g => (g, g.(ectx)).
    
    Definition ectx_cons x (i: int) : ST unit :=
      fun '(MkEGraph ctx U M H W) =>
        let ctx := (x,i)::ctx in
        (MkEGraph ctx U M H W,tt).
    
    Definition is_worklist_empty : ST bool :=
      fun g => (g, match g.(worklist) with [] => true | _ => false end).    

    (*adds (n,p) as a parent to i*)
    Definition add_parent n p i : ST unit :=
      @! let ci <- get_eclass i in
         (set_eclass i (eclass_add_parent ci (n,p))).
    
    Definition canonicalize n : ST enode :=
      match n with     
      | con_node name args =>
          @! let args <- list_Mmap find args in       
             ret con_node name args
      | var_node x =>
          @! ret var_node x
      end.

    
    Definition eqb_ids a b : ST bool :=
      @! let fa <- (find a) in
         let fb <- (find b) in
         ret eqb fa fb.

    
    Definition lookup n : ST (option int) :=
      @! let n <- canonicalize n in
         (hashcons_lookup n).

    Definition add_parent_to_children n i : ST unit :=
      match n with
      | con_node name args =>
          @! let args <- list_Miter (add_parent n i) args in
             ret tt
      | var_node x => @! ret tt
      end.

    (*
      Adds a node to the egraph without checking whether it is valid in the language
     *)
    Definition add_node_unchecked (n : enode) : ST int :=
      @! let mn <- lookup n in
         match mn with
         | Some i => @! ret i
         | None => 
             @! let i <- alloc in
                let tt <- set_eclass i (eclass_singleton n) in
                let tt <- add_parent_to_children n i in
                let tt <- set_hashcons n i in
                ret i
         end.

    

    Definition merge (a b : int) expl : ST int :=
      @! let ca <- find a in
         let cb <- find b in
         if eqb ca cb
         then ret ca
         else let i <- union_ids a b expl in
              let tt <- add_to_worklist i in
              ret i.

    Definition ERR_EXPL : UnionFindExplained.expl :=
      [inl (B:=int) 0%int63].


    (*TODO: think about parents wrt srt, ctx
    if c |- e : t, then e is a parent of t
    need to set those somewhere

    TODO: provide congruence proof for merge
     *)
    Definition repair (i : int) : ST unit :=
      @! let c <- get_eclass i in
         let tt <- @! for pn pi from c.(parents) in
         let tt <- remove_hashcons pn in
         let pn <- canonicalize pn in
         let ci <- find pi in
         (set_hashcons pn ci) in
           let new_parents <-
                 @! for/fold pn pi
                    from c.(parents)
                             [[new_parents := (map.empty : node_map)]] in
           let pn <- canonicalize pn in
           match map.get new_parents pn : option int return ST map.rep with
             (*TODO: provide congruence proof for merge*)
           | Some np => Mseq (merge pi np ERR_EXPL) (@! ret new_parents)
           | None =>
               @! let ci <- find pi in
                  ret (map.put new_parents pn ci)
           end in
             (set_eclass i (set_class_parents c new_parents)).

    Definition rebuild_aux : N -> ST unit :=
      N.recursion
        (Mret tt)
        (fun _ rec =>
           @! let (is_empty : bool) <- is_worklist_empty in
              if is_empty then ret tt
              else
                let tt <- rec in
                let W <- pull_worklist in
                (*TODO: should worklist and/or cW be a set? Egg has a dedup step.
                For now we are not deduplicating here, but we probably should at some point
                 *)
                let cW <- list_Mmap find W in
                (list_Miter repair cW)).
    
    (* TODO: need to track  I = ~=\=_node to use as fuel
     *)
    Definition rebuild : ST unit :=
      @! let incong_bound := 100 in
         (rebuild_aux 100).

    Definition int_set : set int := trie_set.

    (*TODO: move to Utils once implemented *)
    #[refine] Instance pair_Eqb {A} `{Eqb A} {B} `{Eqb B} : Eqb (A * B) :=
      {
        eqb '(a1,a2) '(b1,b2) := (eqb a1 b1) && (eqb a2 b2);
      }.
    all: apply TODO.
    Defined.

    Definition eqn_set : set (int*int) :=
      set_from_map (@pair_map _ _ _ int_set (TrieMapInt63.map _)).
    
    Section WithLang.

      Context (l : lang).


      (*TODO: profile state monad and writer monad performance *)
      Definition Checker A := ST (option (A * eqn_set)).
      
      (*TODO:
          machinery for monad transformers?
       *)
      Instance state_monad : Monad Checker :=
        {
          Mret _ a := fun s => (s,Some (a,map.empty));
          Mbind _ _ f ma :=
          fun s =>
            let (s,ma) := ma s in
            match ma with
            | Some (a,eqns) =>
                let (s, ma) := f a s in
                (s, option_map (pair_map_snd (union eqns)) ma)
            | None => (s, None) end
        }.

      Definition require_equal p : Checker unit :=
        Mret (M:=ST) (Some (tt, map.singleton p tt)).

      Definition liftST {A} : ST A -> Checker A :=
        Mfmap (fun a => Some (a,map.empty)).
      Definition liftOpt {A} (ma : option A) : Checker A :=
        Mret (M:=ST) (option_map (fun a => (a,map.empty)) ma).

      Instance ST_default {A} `{WithDefault A} : WithDefault (ST A) :=
        fun s => (s,default).
      
      
      Section Inner.
        Context (add_sort' : named_list (int * int) -> sort -> Checker int).

        (* breaks the term down into nodes, computes their sorts,
         and adds them to the egraph.
         Returns the top-level node's id and a set of all sort ids
         that must be equated for the added term to typecheck.
         Using a set takes advantage of subterm duplicaton to reduce
         the number of generated goals.

         Invariants:
         If this returns Some v, then:
         - The added term is well-scoped with respect to the egraph's context
         - The added term's constructors are all term constructors of the language
         - All constructors are used with the appropriate arity

         Thus, if for all (i1, i2) in the eqn_set we have find i1 = find i2,
         then the added term is well-typed.
         *)
        (*
          TODO: make sort to be checked against an input, not an output?
         *)
        Section Inner2.
          Context (add_term' : term -> Checker (int * int)).

          (*TODO: return pair of lists or list of pairs?*)
          Fixpoint add_args' (s : list term) (c : ctx) {struct s}
            : Checker (list (int * int)) :=
            match s, c with
            | [],[] => @! ret []
            | e::s, (_,t)::c =>
                @! let sci <- add_args' s c in
                   let (ei, ti) <- add_term' e in
                   (* sort given by c *)
                   let ti' <- add_sort' (with_names_from c sci) t in
                   let tt <- require_equal (ti, ti') in
                   ret (ei, ti)::sci
            | _,_ => @! ret None
            end.
        End Inner2.

        
        (*  sub is a map from vars to id pairs with the egraph's ctx as its domain.
            We need this argument for processing sorts from the language
            
            The range is pairs of (eid,tid) where eid is a term id and tid
            is a sort id.
         *)
        Context (sub_and_ctx : named_list (int * int)).
        
        Fixpoint add_term' (e : term) {struct e} : Checker (int * int) :=
          match e with
          | var x =>
              @! let x' <- liftST (add_node_unchecked (var_node x)) in
                 (liftOpt (named_list_lookup_err sub_and_ctx x'))
          | con n s =>
              @! let term_rule c _ t <?- liftOpt (named_list_lookup_err l n) in
                 let sci  <- add_args' add_term' s c in
                 (* sort generated from sort of n rule *)
                 let t_id <- add_sort' (with_names_from c sci) t in
                 let i <- liftST (add_node_unchecked
                                    (con_node n (map fst sci))) in
                 ret (i,t_id)
          end.
      End Inner.

      Let add_args'
          (add_sort' : named_list (int * int) -> sort -> Checker int)
          (sub_and_ctx : named_list (int * int))
        : list term -> ctx -> Checker (list (int * int)) :=
            add_args' add_sort' (add_term' add_sort' sub_and_ctx).
      
      (*Use fuel here equal to the length of the language.
        This is sufficient since the fuel is used when a term checks its sort,
        given in either t or c of a rule c|- (n x...) : t
        and all sorts must be defined before they are used.
        
        TODO: check that it's actually sufficient
       *)
      Fixpoint add_sort' (fuel : nat)
               (sub_and_ctx : named_list (int * int))
               (t : sort) : Checker int :=
        match fuel with
        | O => @! ret None (* Hitting this case means the input was malformed *)
        | S fuel' =>
            match t with
            | scon n s =>
                @! let sort_rule c _ <?- liftOpt (named_list_lookup_err l n) in
                   let sci  <- add_args' (add_sort' fuel') sub_and_ctx s c in
                   let i <- liftST (add_node_unchecked
                                      (con_node n (map fst sci))) in
                   ret i
            end            
        end.

      Fixpoint sub_and_ctx_from_ectx (acc : int) (ectx : named_list int)
        : named_list (int * int) :=
        match ectx with
        | [] => []
        | (x,ti)::ectx' =>
            (x,(acc,ti))::(sub_and_ctx_from_ectx (succ acc) ectx')
        end.
      
      Definition add_sort (t : sort) : Checker int :=
        @! let ectx <- liftST get_ectx in
           (add_sort' (List.length l) (sub_and_ctx_from_ectx zero ectx) t).

      Definition add_term (e : term) : Checker (int*int) :=
        @! let ectx <- liftST get_ectx in
           (add_term' (add_sort' (List.length l)) (sub_and_ctx_from_ectx zero ectx) e).

      Fixpoint add_term_unchecked (e : term) {struct e} : ST int :=
        match e with
        | var x => add_node_unchecked (var_node x)
        | con n s =>
            @! let si  <- list_Mmap add_term_unchecked s in
               (add_node_unchecked (con_node n si))
        end.
      
      Definition add_sort_unchecked (t: sort) : ST int :=
        match t with
        | scon n s =>
            @! let si  <- list_Mmap add_term_unchecked s in
               (add_node_unchecked (con_node n si))
        end.

      (*TODO: generalize and break out into Utils*)
      Section ListMap.        
        
        Fixpoint list_compare l1 l2 :=
          match l1, l2 with
          | [],[] => Eq
          | [], _ => Lt
          | _, [] => Gt
          | x1::l1, x2::l2 =>
              match Int63.compare x1 x2 with
              | Eq => list_compare l1 l2
              | c => c
              end
          end.

        Definition list_ltb l1 l2 :=
          match list_compare l1 l2 with
          | Lt => true
          | _ => false
          end.

        (* Make this an instance so we can use single-curly-braces so we don't need to qualify field-names with [SortedList.parameters.] *)
        Local Instance list_strict_order: @SortedList.parameters.strict_order _ list_ltb
          := { ltb_antirefl := TODO
             ; ltb_trans := TODO
             ; ltb_total := TODO }.
      End ListMap.


      Definition relation_map : map.map (list int) unit :=
        SortedList.map (SortedList.parameters.Build_parameters
                          (list int) unit list_ltb)
          list_strict_order.

      
      Definition relation : set (list int) := set_from_map relation_map.

      Definition db : map.map int relation := TrieMapInt63.map _.

      Definition arg_map : map.map int int := TrieMapInt63.map _.
      
      Section UncheckedSub.
        
        Context (sub : arg_map).
        
        Fixpoint add_term_unchecked_sub (e : term) {struct e} : ST int :=
          match e with
          | var x =>
              @! ret unwrap_with_default default (map.get sub x)
          | con n s =>
              @! let si  <- list_Mmap add_term_unchecked_sub s in
                 (add_node_unchecked (con_node n si))
          end.
        
        Definition add_sort_unchecked_sub (t: sort) : ST int :=
          match t with
          | scon n s =>
              @! let si  <- list_Mmap add_term_unchecked_sub s in
                 (add_node_unchecked (con_node n si))
          end.

      End UncheckedSub.

      (*
      Notes about the safety of adding unchecked nodes:
      - If the node is wf, then it can be kept as-added
        + Specifically, it can keep its sort since by proving it wf,
          the egraph will unify its written sort with the other side of any
          conversion in the wfness proof
      - If the node is equated with another node, that means they have the same sort
      Hope: If the node is not wf, then it cannot be equated with a wf node

      If we take this as true, then consider the following algorithm:
      - add all nodes/terms unchecked
      - record (TODO: how) all equations that must be proven
      - iterate to saturation (or step bound)
      - check that all equations satisfy reflexivity
       *)


      Section EqualitySaturation.
        Context {A} (update : A -> ST A) (pred : A -> bool).



        Definition get_eclasses : ST eclass_map :=
          fun g => (g, g.(eclasses)).


        Definition db_append (m : db) x v :=
          match map.get m x with
          | None => map.put m x (map.singleton v tt)
          | Some l => map.put m x (add_elt l v)
          end.
        
        
        Definition generate_db : ST db :=
          @! let classes <- get_eclasses in
             for/fold i cls from classes [[acc:=map.empty]] in
               (* all nodes in a class have identical index up to find *)
               let i' <- find i in
               for/fold node _ from cls.(nodes) [[acc:=acc]] in
                 match node with
                 | con_node n s =>
                     @!let s' : list int <- list_Mmap find s in
                       ret db_append acc n (i'::s')
                 | var_node x =>
                     (*TODO: how to index into DB for vars vs con?
                       for now, require them to use disjoint names
                       works, but feels awkward and causes issues later

                       The best thing would be to index based off of
                       bool * positive rather than positive
                      *)
                     @! ret db_append acc x [i]
                        
                 end.
        
        
        (* returns (max_var, root, list of atoms)*)
        Fixpoint compile_term_aux (max_var : int) p : int * int * list (atom _) :=
          match p with
          | con f s =>
              let '(max_var, s_vars, atoms) :=
                fold_left (fun '(max_var, s_vars, atoms) p =>
                             let '(max_var, x, atoms') :=
                               compile_term_aux max_var p in
                             (max_var,x::s_vars, atoms'++atoms))
                          s
                          (max_var, [], []) in
              let x := succ max_var in
              (x, x, (f,s_vars)::atoms)
          | var x => (max_var, x, [])
          end.

        (* returns (max_var, root, list of atoms)*)
        Definition compile_sort_aux (max_var : int) p :=
          match p with
          | scon f s =>
              let '(max_var, s_vars, atoms) :=
                fold_left (fun '(max_var, s_vars, atoms) p =>
                             let '(max_var, x, atoms') :=
                               compile_term_aux max_var p in
                             (max_var,x::s_vars, atoms'++atoms))
                          s
                          (max_var, [], []) in
              let x := succ max_var in
              (x, x, (f,s_vars)::atoms)
          end.

        (*TODO: move to natlike.v*)
        Definition max {A} `{Natlike A} (a b : A) : A :=
          if ltb b a then a else b.
        
        Definition compile_term_pattern (p : term) : query _ :=
          (*TODO: remove duplicates in fv *)
          let vars := fv p in
          let max_var := fold_left max vars zero in
          let '(_,root, atoms) := compile_term_aux max_var p in
          Build_query _ (root::vars) atoms.
        
        Definition compile_sort_pattern (p : sort) : query _ :=
          (*TODO: remove duplicates in fv *)
          let vars := fv_sort p in
          let max_var := fold_left max vars zero in
          let '(_,root, atoms) := compile_sort_aux max_var p in
          Build_query _ (root::vars) atoms.

        Local Notation generic_join :=
          (generic_join int int
                        int_set query_trie qt_unconstrained _ qt_tree qt_nil
                        values_of_next_var choose_next_val relation db arg_map).
        
        Definition ematch (d : db) (p : term) :=
          let q := compile_term_pattern p in
          generic_join d q.
        
        Definition ematch_sort (d : db) (p : sort) :=
          let q := compile_sort_pattern p in
          generic_join d q.
        

        (*TODO: currently only rewrites left-to-right.
        Evaluate whether this is sufficient.
         *)
        Definition try_rewrite (d : db) (r : rule) : ST unit :=
          match r with
          (* TODO: what to do with C? Needs to be used by ematch.

           Consider heap lookup miss,
           where a, inequality premise is not used in the equation.
           How to handle this?
           - implement pluggable term generators/deciders for specific sorts?
           Hard to deal with; ignore for now?
           How does egg deal with side conditions?

           Vague idea: if using relational e-matching, turn C into part of the query.
           

           *)
          | sort_eq_rule c t1 t2 =>
              list_Miter (fun sub =>
                            @! let cid <- add_sort_unchecked_sub sub t1 in
                               let cid' <- add_sort_unchecked_sub sub t2 in
                               let _ <- merge cid cid' ERR_EXPL in
                               ret tt)
                         (ematch_sort d t1)
          | term_eq_rule c e1 e2 t =>
              (* TODO: add_unchecked seems like it would expect the rhs to include sorts.
               Do we need a lang with all-annotated terms?
               
               TODO: expose add_with_subst to use here
               TODO: is it safe to add unchecked here?
                     - means that there might be conversions in added term
                       that are not represented in the egraph
                     (only applies if sorts are removed from nodes)
               *)
              list_Miter (fun sub =>
                            @! let cid <- add_term_unchecked_sub sub e1 in
                               let cid' <- add_term_unchecked_sub sub e2 in
                               let _ <- merge cid cid' ERR_EXPL in
                               ret tt)
                         (ematch d e1)
          | _ => @!ret tt (* not a rewrite rule *)
          end.
        
        (*
      Iteratively applies rewrite rules to the egraph
      until either:
      - the egraph is saturated (*TODO: implement*)
      - the accumulator satisfies the predicate
      - the fuel runs out

      TODO: encode the termination type in the output?
      TODO: fuel : N
         *)
        Fixpoint equality_saturation (acc: A) (fuel : nat) : ST A :=
          match fuel with
          | O => @! ret acc
          | S fuel' =>
              if pred acc then @! ret acc
              else
                @! let db <- generate_db in
                   (*TODO: filter lang once before this fixpoint starts *)
                   (* Main rewrite loop
                    Since DB is separate, we  don't have to separate reads and writes
                    and still only need one rebuild
                    *)
                   let tt <- list_Miter (try_rewrite db) (map snd l) in
                   let tt <- rebuild in
                   let acc' <- update acc in
                   (equality_saturation acc' fuel')
          end.
        
      End EqualitySaturation.

      (*TODO: move to Monad.v*)
      
      Definition map_Mandmap {K V}
                 {MP : map.map K V}
                 (f : K -> V -> ST bool)
                 (p : @map.rep _ _ MP) : ST bool :=
        map_Mfold (fun k v b => @! let b' <-  (f k v) in ret (andb b' b)) p true.

      

      Definition is_empty {A} := (existsb (A:=A) (fun _ => true)).
      Definition is_empty_map {K V} {m : map.map K V} :=
        (map.forallb (map:=m) (fun _ _ => false)).
      
      (* should be called under a try_with_backtrack?*)
      Definition resolve_checker' {A} (c : Checker A)  (fuel : nat): ST (option A) :=
        @! let meqns : (option (_ * eqn_set)) <- c in
           match meqns with
           | Some (a, eqns) =>
               @! let eqns' : eqn_set <-
                                equality_saturation
                                  (fun eqns : eqn_set =>
                                     map_Mfold (fun '(a,b) _ eqns =>
                                                  (@! let a' <- find a in
                                                      let b' <- find b in
                                                      if eqb a' b' then ret eqns
                                                      else ret add_elt eqns (a',b')))
                                               eqns
                                               map.empty)
                                  (*Note: this is delicate since the map is non-canonical
                            (e.g. when a |-> Empty)
                                   *)
                                  is_empty_map
                                  eqns
                                  fuel in
                  ret if is_empty_map eqns' then Some a else None
           | None => @! ret None
           end.

      Let fuel := 100%nat.
      
      Definition add_and_check_term (e : term) : ST (option (int *int)) :=
        try_with_backtrack (resolve_checker' (add_term e) fuel).

      (*TODO: should this check that x is fresh?*)
      Definition add_and_check_ctx_cons x t : ST bool :=
        @! let mint <- try_with_backtrack (resolve_checker' (add_sort t) fuel) in
           match mint with
           | Some int =>
               @! let x' <- add_node_unchecked (var_node x) in
                  let _ <- ectx_cons x' int in
                  ret true
           | None => @!ret false
           end.

      
      (* assumes saturation *)
      Definition saturated_compare_eq i1 i2 : ST bool :=
        @! let ci1 <- find i1 in
           let ci2 <- find i2 in
           ret (eqb i1 i2).
      

      
      Fixpoint check_ctx' (c : ctx) : option egraph :=
        match c with
        | [] => Some empty_egraph
        | (x,t)::c =>
            @! let ! compute_fresh x c in
               let g <- check_ctx' c in
               let (g',b) := add_and_check_ctx_cons x t g in
               let ! b in
               ret g'
        end.

      Definition check_ctx c := if check_ctx' c then true else false.
      
      
    End WithLang.

    
    
  End EGraphOps.

  From Named Require Import SimpleVSubst SimpleVSTLC.

  (*TODO: move to Renaming.v*)
  Section Renaming.
    Context {A B : Type}
            `{Eqb A}
            `{Natlike B}.
    Import StateMonad.

    Definition fresh_stb : ST B B :=
      fun b => (succ b, b).

    Section WithConstrMap.
      Context (constr_map : @Utils.named_list A B).

      
      Section WithVarMap.
        Context (var_map : @Utils.named_list A B).

        Fixpoint rename_term e :=
          match e with
          | var x => var (named_list_lookup default var_map x)
          | con n s => con (named_list_lookup default constr_map n) (map rename_term s)
          end.

        Definition rename_sort t :=
          match t with
          | scon n s => scon (named_list_lookup default constr_map n) (map rename_term s)
          end.

      End WithVarMap.
      
      Definition fresh_stnlb : ST (@Utils.named_list A B * B) B :=
        fun '(s,b) => (s,succ b, b).
      
      Definition get_var_map : ST (@Utils.named_list A B * B) _ :=
        fun '(s,b) => (s,b, s).
      
      Definition set_var x xb : ST (@Utils.named_list A B * B) _ :=
        fun '(s,b) => ((x,xb)::s,b, tt).
      
      Fixpoint auto_rename_ctx c : ST (@Utils.named_list A B * B) (Term.ctx B) :=
        match c with
        | [] => @!ret []
        | (x,t)::c =>
            @! let c' <- auto_rename_ctx c in
               let var_map <- get_var_map in
               let t' := rename_sort var_map t in
               let xb <- fresh_stnlb in
               let _ <- set_var x xb in
               ret (xb,t')::c'
        end.


      Definition rename_args vs (args : list A) : list B :=
        map (named_list_lookup default vs) args.
      
      Definition auto_rename_rule r fresh_id : _ * Rule.rule _ :=
        match r with
        | sort_rule c args =>
            let '(vs, fresh_id', c') := auto_rename_ctx c ([],fresh_id) in
            let args' := rename_args vs args in
            (fresh_id', sort_rule c' args')
        | term_rule c args t =>
            let '(vs, fresh_id', c') := auto_rename_ctx c ([],fresh_id) in
            let args' := rename_args vs args in
            let t' := rename_sort vs t in
            (fresh_id', term_rule c' args' t')
        | sort_eq_rule c t1 t2 =>
            let '(vs, fresh_id', c') := auto_rename_ctx c ([],fresh_id) in
            let t1' := rename_sort vs t1 in
            let t2' := rename_sort vs t2 in
            (fresh_id', sort_eq_rule c' t1' t2')
        | term_eq_rule c e1 e2 t =>
            let '(vs, fresh_id', c') := auto_rename_ctx c ([],fresh_id) in
            let e1' := rename_term vs e1 in
            let e2' := rename_term vs e2 in
            let t' := rename_sort vs t in
            (fresh_id', term_eq_rule c' e1' e2' t')
        end.

    End WithConstrMap.

    
    Definition get_constr_map : ST (@Utils.named_list A B * B) _ :=
      fun '(s,b) => (s,b, s).
    Definition set_constr x xb : ST (@Utils.named_list A B * B) _ :=
      fun '(s,b) => ((x,xb)::s,b, tt).

    Definition lift_auto_rename_rule r
      : ST (@Utils.named_list A B * B) (Rule.rule _) :=
      fun '(sb,fr) =>
        let '(fr',r') := auto_rename_rule sb r fr in
        (sb,fr',r').
    
    Fixpoint rename_lang_ext l : ST (@Utils.named_list A B * B) (Rule.lang _) :=
      match l with
      | [] => @!ret []
      | (x,r)::l =>
          @! let l' <- rename_lang_ext l in
             let r' <- lift_auto_rename_rule r in
             let x' <- fresh_stnlb in
             let _ <- set_constr x x' in
             ret (x',r')::l'
      end.

    Definition rename_lang (l : Rule.lang A) : Rule.lang _ :=
      snd (rename_lang_ext l ([],zero)).

    Definition rename_constr_subst (l : Rule.lang A) :=
      fst (fst (rename_lang_ext l ([],zero))).

    
    Definition rename_ctx (constr_map : @Utils.named_list A B)
               (ctx : Term.ctx _) fr :=
      snd (auto_rename_ctx constr_map ctx ([],fr)).
    
  End Renaming.


  Import Term.Notations.

  Definition int_value_subst : Rule.lang int :=
    Eval compute in (rename_lang value_subst).
  (*TODO: are vars different?*)
  Definition constr_rename : named_list int :=
    Eval compute in (rename_constr_subst value_subst).

  Definition test_ctx :=
    Eval compute in (rename_ctx constr_rename
                                {{c "G" : #"env",
                                      "A" : #"ty",
                                        "B" : #"ty"}}
                                100).
  Definition initial_egraph :=
    Eval compute in
      (match check_ctx' int_value_subst test_ctx with
       | Some g => g
       | None => empty_egraph
       end).
  
  (*TODO: instant at size = 2, stalls at size =3
  TODO: slow even when fuel is 0
  TODO: why is this slow? Probably a union-find thing? maybe a sets thing?
*)

  Definition test_ctx_var_map :=
    [("B", 102);("A",101);("G",100)].

  Definition test_term :=
    Eval compute in
      (rename_term constr_rename test_ctx_var_map
                   {{e #"ext" "G" "G"}}).

  (*Print test_term.*)
  (*TODO: should return none

 add_term eqns look right,
 but checking still passes. Why?
   *)
  Definition egraph1 :=
    Eval compute in (fst (add_and_check_term
                            int_value_subst
                            test_term
                            initial_egraph)).
  Eval compute in (add_term
                     int_value_subst
                     test_term
                     initial_egraph).


  (*TODO: move to extramaps/Triemap *)
  Definition as_list {A} :=
    TrieMap.trie_fold (B:=A) (fun m k v => (k,v)::m) [].

  (*Compute
    (Utils.named_map as_list (as_list ( Canonical.PTree.Nodes
                                          (Canonical.PTree.Node010
                                             (Canonical.PTree.Nodes
                                                (Canonical.PTree.Node011 tt
                                                                         (Canonical.PTree.Node100 (Canonical.PTree.Node010 tt)))))))).*)


  (*Testing running this on something more complicated*)


  Definition term1 :=
    Eval compute in
      (rename_term constr_rename test_ctx_var_map
                   {{e #"cmp" "G1" "G2" (#"ext" "G3" "A") "f" (#"snoc" "G2" "G3" "A" "g" "v")}}).

  (*Print test_term.*) (*{{e #61 100 100}}*)
  (*TODO: should return none

 add_term eqns look right,
 but checking still passes. Why?
   *)
    Eval compute in (add_term
                            int_value_subst
                            term1
                            initial_egraph).
  Definition egraph2 :=
    Eval compute in (fst (add_and_check_term
                            int_value_subst
                            test_term
                            initial_egraph)).
  (*Print egraph2.*)






