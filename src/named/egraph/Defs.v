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
From Utils Require ArrayList UnionFind.
From Named Require Import Term Rule.
(*Import Core.Notations.*)

(*TODO: move to utils*)
Definition unwrap_with_default {A} (default : A) ma :=
  match ma with None => default | Some a => a end.

Section __.
  Context {idx : Type}
          `{Natlike idx}
          {array : Type -> Type}
          `{ArrayList.ArrayList idx array}.
  
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

  
  Variant enode :=
    (* CONVENTION: for terms, first element of args is the sort *)
    (* TODO: determine if this is a good way to do it *)
    | con_node : idx -> list idx -> enode
    (*TODO: separate constructor for sorts?  | scon_node : list idx -> enode *)
    | var_node : (*(* sort id*) idx ->*) (* var *) idx -> enode.

  Context {node_set : set enode}
          {node_map : map.map enode idx}.


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

  Context {eclass_map : map.map idx eclass}.
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


    Context {idx_set : set idx}
            {eqn_set : set (idx*idx)}.
    
    Section WithLang.

      Context (l : lang).

      
      (* TODO: add union to interface *)
      Axiom union : forall {A} {s : set A}, s -> s -> s.

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

      Instance option_default {A} : WithDefault (option A) := None.
      Instance ST_default {A} `{WithDefault A} : WithDefault (ST A) :=
        fun s => (s,default).
      
      (*TODO: move to Monad once tested *)
      Notation "'let' p <?- e 'in' b" :=
        (Mbind (fun x => match x with p => b | _ => default end) e)
          (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).
      
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
                                    (con_node n (t_id::(map fst sci)))) in
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
        | 0 => @! ret None (* Hitting this case means the input was malformed *)
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

      Axiom (db : Type).

      (*TODO: implement*)
      Axiom generate_db : ST db.

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
            list_Miter (fun '(sub,cid) =>
                          @! let cid' <- add_sort_unchecked sub c t2 in
                             (merge cid cid'))
                       (ematch_sort d c t1)
        | term_eq_rule c e1 e2 t =>
            (* TODO: add_unchecked seems like it would expect the rhs to include sorts.
               Do we need a lang with all-annotated terms?
             *)
            list_Miter (fun '(sub,cid) =>
                          @! let cid' <- add_term_unchecked sub c e2 t in
                             (merge cid cid'))
                       (ematch d c e1 t)
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
        | 0 => @! ret acc
        | S fuel' =>
            if pred acc then @! ret acc
            else
              @! let db <- generate_db in
                 (*TODO: filter lang once before this fixpoint starts *)
                 (* Main rewrite loop
                    Since DB is separate, we  don't have to separate reads and writes
                    and still only need one rebuild
                  *)
                 let tt <- list_Miter (try_rewrite db) l in
                 let tt <- rebuild in
                 let acc' <- update acc in
                 (equality_saturation acc' fuel')
        end.
                                    


                                          
    End WithLang.
      
   (* Context {arg_map : map.map idx idx}.*)

  (* TODO: is it worth using a more efficient structure?
     If we assume that the max length is ~10, maybe not
   *)
  Definition esubst := list (idx*idx).
  Definition match_result := list (esubst * eclass).
  


  (* TODO: zero is a questionable default unless I implement null idea*)
  Fixpoidx esubst_lookup (s : esubst) (n : idx) : idx :=
    match s with
    | [] => 0%idx63
    | (s', v)::l' =>
      if eqb n s' then v else esubst_lookup l' n
    end.

  Arguments esubst_lookup !s n/.

  Import Idx63Term.
  (*TODO: take in an actual map for constr_map?*)
  Fixpoint to_eterm (e : term) : eterm :=
    match e with
    | var x => evar x
    | con n s => econ n (map to_eterm s)
    end.

  Arguments to_eterm !e /.

  (* TODO: should I work out how to apply substs to refs?
     necessary if e can be an eterm
   *)
  Fixpoint eterm_subst (s : esubst) (e : term) : eterm :=
    match e with
    | var x => eref (esubst_lookup s x)
    | con n s' =>
      econ n (map (eterm_subst s) s')
    end.

  Arguments eterm_subst s !e /.

  
  Definition lookup_sort (tm : idx) : ST idx :=
    @! let c <- get_eclass tm in
       ret c.(esrt).
       
  Definition lookup_ctx (tm : int) : ST idx :=
    @! let c <- get_eclass tm in
       ret c.(ectx).


  Definition lookup_sort_in_ctx'
            (rec : ctx_idx -> var_idx -> ST (option srt_idx))
            (ctx : ctx_idx)
            (x : var_idx) : ST (option srt_idx) :=
    @! let c <- get_eclass ctx in
       match NodeSets.choose c.(nodes) with
       | Some (ctx_cons_node _ x' srt tl) =>
         if eqb x x' then @! ret Some srt
         else rec tl x
       | _ => @! ret None
       end.

  (*TODO: try to collapse 2 defs*)
  Definition lookup_sort_in_ctx (ctx x : idx) : ST (option srt_idx) :=
    @! let c <- get_eclass ctx in
       match NodeSets.choose c.(nodes) with
       | Some (ctx_cons_node n x' srt tl) =>
         if eqb x x' then @! ret Some srt
         else N.recursion (fun _ _ => @! ret None) (fun _ => lookup_sort_in_ctx') n tl x
       | _ => @! ret None
       end.       

  (*TODO: want this to be fast.
    Build lang into egraph?
    identify c w/ term c[/id/] and do regular lookup?
    how to know the arity of id though?
    middle option: "lang" is already compiled, just another node type?
    what to do with equivalence rules then? drop? need to remember at least the names
   *)
  Definition get_term_ctx_and_sort (l : lang) (c : constr_idx) : option (ctx*sort) :=
    match named_list_lookup_err l c with
    | Some (term_rule c t

  (* assumes that the context and sort have already been added *)
  (* TODO: think about read/write separation & invariants *)
  (* TODO: needs lang as input to generate the sort *)
  Fixpoint add_eterm_no_check lang (ctx (*srt*): idx) (e : eterm) : ST (option idx) :=
    match e with
    | evar x =>
      @! let srt <- lookup_sort_in_ctx ctx x in
         (add_term (var_node x) ctx srt)
    | econ n s =>
      (*TODO: generalize list_Mmap to composition of ST and option.
        Requires monad transformers to be nice
       *)
      @! let margs <- list_Mmap add_eterm s in
         let srt <- 
         match List.option_all margs with
         | Some args =>
           (*TODO: check wfness of top-level constructor here*)
           (*TODO: think about what needs to be canonicalized here *)
           (add_term (con_node n args) ctx srt)
         | None => None
         end
    | eref i => @! ret i
   end.

                                                                             
  (* assumes that the context and sort have already been added *)
  (* TODO: think about read/write separation & invariants;
     have it return a list of sort equations to prove and backtrack if they fail?
     hard to do that though since egraph won't be 'good'.
     Generate equations first? traversing the term is cheap
     ^ TODO: do this
   *)
  (*TODO: does this need to take an eterm? *)
  Fixpoint check_and_add_eterm (ctx (*srt*): idx) (e : eterm) : ST (option int) :=
    match e with
    | evar x =>
      @! let srt <- lookup_sort_in_ctx ctx x in
         (add_term (var_node x) ctx srt)
      (*TODO: need to look up sort
       and check, if srt is provided*)
      add (var_node x ctx srt)
    | econ n s =>
      (*TODO: generalize list_Mmap to composition of ST and option.
        Requires monad transformers to be nice
       *)
      @! let margs <- list_Mmap add_eterm s in
         match List.option_all margs with
         | Some args =>
           (*TODO: check wfness of top-level constructor here*)
           (*TODO: think about what needs to be canonicalized here *)
           (add_term (con_node n args) ctx srt)
           (add (con_node n ctx srt)
         | None => None
         end
    | eref i => (*TODO: check? only if srt provided. write sep. helper?*) do ret i
    end.
                       
  Axiom TODO : forall {A}, A.


  (*TODO: how to treat type info on vars? *)
  (*TODO: use sections earlier to make list_Mmap termination check work *)
  (*TODO: a larget effort to implement, move to sep file*)
  Fixpoint ematch (e : term) : ST match_result :=
    match e with
    | var x => TODO
    | con n s =>
      @! let ematch_s <- list_Mmap ematch s in
         TODO
         end.


                                    
         (*Queries I want in the end:*)

         (* uses egraph saturate_and_compare_eq to determine equivalences,
            checks wfness of each subterm, and adds if wf

            w/ this API, ctx nodes seem reasonable
          *)
         Parameter add_and_check_wf_term : lang -> ctx -> term -> ST (option idx).
         Parameter add_and_check_wf_sort : lang -> ctx -> term -> ST (option idx).
         Parameter get_term : idx -> ST (option term).
         Parameter get_ctx_of_term : idx -> ST (option ctx).
         Parameter get_sort_of_term : idx -> ST (option sort).
         Parameter get_sort : idx -> ST (option sort).

         (* one of these two *)
         Parameter saturate : lang -> ST unit.
         Parameter saturate_until_eq : lang -> idx -> idx -> ST bool.

         (* assumes saturation *)
         Definition compare_eq l i1 i2 : ST bool :=
           do let ci1 <- find i1 in
              let ci2 <- find i2 in
              ret (eqb i1 i2).

              
(*critical properties*)

(*TODO: need to carry a subst*)
(* basic idea: parallel to core? *)
Inductive egraph_matches_term
          (g : egraph) (s : named_list V term)
          (ep e : term) t : Prop :=
| egraph_contains_var : 
  In (i,e) s ->
  (*in_egraph g t = true ->*)
  egraph_sort_of g e t ->
  egraph_contains_term g (var i) e t.

(*Prove for empty egraph, each operation preserves*)
Definition egraph_sound_in_lang g l :=
  (forall c t, in_egraph_sort g c t = true ->
               wf_sort l c t)...
  /\(forall c t, eq_egraph_sort g c t1 t2 = true ->
               eq_sort l c t1 t2)...

Definition ematch_term_sound g : Prop :=
  forall c e t c' s,
    In (c',s) (set_map (materialize g) (ematch g c e t)) ->
    in_egraph g c' e[/s/] t[/s/] = true.
(*corollary: 
  egraph_sound_in_lang g l ->
  wf_subst l c' s c *)

*)
