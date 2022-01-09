(*
  Implementation based on Egg: https://dl.acm.org/doi/pdf/10.1145/3434304
*)
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool String List ZArith.
Import ListNotations.
Open Scope string.
Open Scope list.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils Natlike ExtraMaps Monad RelationalDB.
Import Sets.
From Utils Require ArrayList UnionFind TrieMap.
From Named Require Import Term Rule Core.
(*Import Core.Notations.*)


Definition idx := positive.
Definition array := TrieMap.TrieArrayList.trie_array.
  
  Notation named_list := (@named_list idx).
  Notation named_map := (@named_map idx).
  Notation term := (@term idx).
  Notation ctx := (@ctx idx).
  Notation sort := (@sort idx).
  Notation subst := (@subst idx).
  Notation rule := (@rule idx).
  Notation lang := (@lang idx).

  Notation union_find := (@UnionFind.union_find idx array).

  (**************************************************
   Big TODO:
   Do I need to include the sorts in the terms?
   reasons I currently include them:
   1. so I can answer queries of the form "What is the type of the term with id x
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


   **************************************************)

  (*possibly poor naming*)
  Definition principal_sort l c e : option sort :=
    match e with
    | var x => named_list_lookup_err c x
    | con n s =>
        @! let (term_rule c' _ t) <?- named_list_lookup_err l n in
           ret t[/with_names_from c' s/]
    end.

  (* If this is provable, then I can quickly compute the sort as described above.
     This means that terms don't need to store their sorts
     TODO: prove
*)
  Axiom principal_sort_equiv
    : forall  l c e t pt, wf_term l c e t ->
      principal_sort l c e = Some pt ->
      eq_sort l c t pt.

  


  (*******)

  
  Variant enode :=
    | con_node : idx -> list idx -> enode
    (*TODO: separate constructor for sorts?  | scon_node : list idx -> enode *)
    | var_node : (*(* sort id*) idx ->*) (* var *) idx -> enode.

(* TODO: make sets fast*)

Fixpoint list_eqb {A} `{Eqb A} (l1 l2 : list A) :=
  match l1, l2 with
  | [], [] => true
  | a1::l1, a2::l2 =>
      (eqb a1 a2) && (list_eqb l1 l2)
  | _, _ => false
  end.

(*TODO: move to Utils once implemented *)
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
Definition node_map := (@named_list_map enode idx _).


  (* TODO : separate sort eclasses? it would avoid awkwardness around esort dummy value
   *)
  Record eclass : Type :=
    MkEClass {
        nodes : node_set;
        parents : node_map;
        (* value is unused if the class represents a sort
         TODO: is this the best way? could also fix it as 0
        
        esort : idx;*)
      }.

Definition eclass_map := TrieMap.map eclass.

  (*{idx_map : map.map idx idx}*)

  (* Fix a specific context that the egraph is operating in.
     This means that we can't reuse egraphs between rules
     in a proof of compiler correctness,
     but it is difficult to do so even when tracking multiple contexts.

     On user programs this is generally the empty context.
   *)
  Record egraph :=
    MkEGraph {
        (* TODO: context sorts added to the egraph at initialization *)
        ectx : named_list idx;
        id_equiv : union_find;
        eclasses : eclass_map;
        hashcons : node_map;
        worklist : list idx
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
  
  (*TODO: use coq-record-update?*)
  Definition set_class_parents '(MkEClass ns _) ps :=
    MkEClass ns ps.

  
  Section EGraphOps.
    Import StateMonad.

    Local Notation "'ST'" := (ST egraph).

    Definition find a : ST idx :=
      fun '(MkEGraph ctx U M H W) =>
        let (U, i) := UnionFind.find U a in
        (MkEGraph ctx U M H W,i).

    Definition alloc : ST idx :=
      fun '(MkEGraph ctx U M H W) =>
        let (U, i) := UnionFind.alloc U in
        (MkEGraph ctx U M H W,i).

    Definition hashcons_lookup (n : enode) : ST (option idx) :=
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
    
    Definition set_eclass (i: idx) (c : eclass) : ST unit :=
      fun '(MkEGraph ctx U M H W) =>
        let M := map.put M i c in
        (MkEGraph ctx U M H W,tt).

    Definition union_ids a b : ST idx :=
      fun '(MkEGraph ctx U M H W) =>
        let (U, i) := UnionFind.union U a b in
        (MkEGraph ctx U M H W, i).

    (* return a default value rather than none
     for ease-of-use
     *)
    Definition get_eclass (i : idx) : ST eclass :=
      (*TODO: using a meaningless default here.
      Decide if an option is better.
      If I want empty as the default,
      I need to decide that ctx and srt don't matter if empty,
      which seems wrong
       *)
      fun g => (g, unwrap_with_default eclass_empty (map.get g.(eclasses) i)).

    Definition add_to_worklist (i : idx) : ST unit :=
      fun '(MkEGraph ctx U M H W) =>
        let W := i::W in
        (MkEGraph ctx U M H W, tt).

    (* Returns the worklist for iteration and removes it from the egraph *)
    Definition pull_worklist : ST (list idx) :=
      fun '(MkEGraph ctx U M H W) =>
        (MkEGraph ctx U M H [], W).

    
    (* Returns the egraph's context *)
    Definition get_ectx : ST (named_list idx) :=
      fun g => (g, g.(ectx)).
    
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

    
    Definition lookup n : ST (option idx) :=
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
    Definition add_node_unchecked (n : enode) : ST idx :=
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

    

    Definition merge (a b : idx) : ST idx :=
      @! let ca <- find a in
         let cb <- find b in
         if eqb ca cb
         then ret ca
         else let i <- union_ids a b in
              let tt <- add_to_worklist i in
              ret i.


    (*TODO: think about parents wrt srt, ctx
    if c |- e : t, then e is a parent of t
    need to set those somewhere
     *)
    Definition repair (i : idx) : ST unit :=
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
           match map.get new_parents pn : option idx return ST map.rep with
             
           | Some np => Mseq (merge pi np) (@! ret new_parents)
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
                For now we are not deduplicating here, but we probably should at some poidx
                 *)
                let cW <- list_Mmap find W in
                (list_Miter repair cW)).
    
    (* TODO: need to track  I = ~=\=_node to use as fuel
     *)
    Definition rebuild : ST unit :=
      @! let incong_bound := 100 in
         (rebuild_aux 100).


    Definition idx_set := trie_set.

    (*TODO: move to Utils once implemented *)
    #[refine] Instance pair_Eqb {A} `{Eqb A} {B} `{Eqb B} : Eqb (A * B) :=
      {
        eqb '(a1,a2) '(b1,b2) := (eqb a1 b1) && (eqb a2 b2);
      }.
    all: apply TODO.
    Defined.

    (* TODO: make pair sets just like pair maps to avoid set_from_map*)
    Definition eqn_set := set_from_map (@pair_map _ _ _ trie_set (TrieMap.map _)).
    
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
        Context (add_sort' : named_list (idx * idx) -> sort -> Checker idx).

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
          Context (add_term' : term -> Checker (idx * idx)).

          (*TODO: return pair of lists or list of pairs?*)
          Fixpoint add_args' (s : list term) (c : ctx) {struct s}
            : Checker (list (idx * idx)) :=
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
        Context (sub_and_ctx : named_list (idx * idx)).
        
        Fixpoint add_term' (e : term) {struct e} : Checker (idx * idx) :=
          match e with
          | var x => liftOpt (named_list_lookup_err sub_and_ctx x)
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
          (add_sort' : named_list (idx * idx) -> sort -> Checker idx)
          (sub_and_ctx : named_list (idx * idx))
        : list term -> ctx -> Checker (list (idx * idx)) :=
            add_args' add_sort' (add_term' add_sort' sub_and_ctx).
      
      (*Use fuel here equal to the length of the language.
        This is sufficient since the fuel is used when a term checks its sort,
        given in either t or c of a rule c|- (n x...) : t
        and all sorts must be defined before they are used.
        
        TODO: check that it's actually sufficient
       *)
      Fixpoint add_sort' (fuel : nat)
               (sub_and_ctx : named_list (idx * idx))
               (t : sort) : Checker idx :=
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

      Fixpoint sub_and_ctx_from_ectx (acc : idx) (ectx : named_list idx)
        : named_list (idx * idx) :=
        match ectx with
        | [] => []
        | (x,ti)::ectx' =>
            (x,(acc,ti))::(sub_and_ctx_from_ectx (succ acc) ectx')
        end.
      
      Definition add_sort (t : sort) : Checker idx :=
        @! let ectx <- liftST get_ectx in
           (add_sort' (length l) (sub_and_ctx_from_ectx zero ectx) t).

      Definition add_term (e : term) : Checker (idx*idx) :=
        @! let ectx <- liftST get_ectx in
           (add_term' (add_sort' (length l)) (sub_and_ctx_from_ectx zero ectx) e).

      Fixpoint add_term_unchecked (e : term) {struct e} : ST idx :=
          match e with
          | var x => add_node_unchecked (var_node x)
          | con n s =>
              @! let si  <- list_Mmap add_term_unchecked s in
                 (add_node_unchecked (con_node n si))
          end.
      
      Definition add_sort_unchecked (t: sort) : ST idx :=
          match t with
          | scon n s =>
              @! let si  <- list_Mmap add_term_unchecked s in
                 (add_node_unchecked (con_node n si))
          end.

      Section UncheckedSub.
        
        Context (sub : arg_map).
      
        Fixpoint add_term_unchecked_sub (e : term) {struct e} : ST idx :=
          match e with
          | var x =>
              @! ret unwrap_with_default default (map.get sub x)
          | con n s =>
              @! let si  <- list_Mmap add_term_unchecked s in
                 (add_node_unchecked (con_node n si))
          end.
      
      Definition add_sort_unchecked_sub (t: sort) : ST idx :=
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
                     @!let s' : list idx <- list_Mmap find s in
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
        Fixpoint compile_term_aux (max_var : idx) p : idx * idx * list atom :=
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
        Definition compile_sort_aux (max_var : idx) p :=
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
        
        Definition compile_term_pattern (p : term) : query :=
          (*TODO: remove duplicates in fv *)
          let vars := fv p in
          let max_var := fold_left max vars zero in
          let '(_,root, atoms) := compile_term_aux max_var p in
          Build_query (root::vars) atoms.
        
        Definition compile_sort_pattern (p : sort) : query :=
          (*TODO: remove duplicates in fv *)
          let vars := fv_sort p in
          let max_var := fold_left max vars zero in
          let '(_,root, atoms) := compile_sort_aux max_var p in
          Build_query (root::vars) atoms.

        
        (*TODO: output type*)
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
                             let _ <- merge cid cid' in
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
                             let _ <- merge cid cid' in
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

      
    (* assumes saturation *)
    Definition compare_eq i1 i2 : ST bool :=
      @! let ci1 <- find i1 in
         let ci2 <- find i2 in
         ret (eqb i1 i2).

      Definition is_empty {A} := (existsb (A:=A) (fun _ => true)).
      
      (* should be called under a try_with_backtrack?*)
      Definition resolve_checker' (c : Checker unit)  (fuel : nat): ST bool :=
        @! let meqns : (option (unit * eqn_set)) <- c in
           match meqns with
           | Some (_, eqns) =>
               ((@! let eqns' : eqn_set <-
                        equality_saturation
                          (fun eqns : eqn_set =>
                             @! let eqns : eqn_set <-
                                      list_Mmap (fun '((a,b),_) => (find a, find b)) eqns in
                                ret filter(fun '((a,b),_) => negb (eqb a b))  eqns)
                          is_empty
                          eqns
                          fuel in
                  ret (is_empty eqns')) : ST bool)
           | None => (@! ret false) : ST bool
           end.
      
    End WithLang.

    
    
  End EGraphOps.

  
End __.
