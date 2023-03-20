(*
  Stripped down egraph for checking proofs
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
Import TrieMap.TrieArrayList.
From Named Require Import Term Rule Core.
(*Import Core.Notations.*)


(*
Section __.
  Context {idx : Type}
          `{Natlike idx}
          {array : Type -> Type}
          `{ArrayList.ArrayList idx array}.
 *)


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
  (*
  
  Notation named_list := (@named_list positive).
  Notation named_map := (@named_map positive).
  Notation term := (@term positive).
  Notation ctx := (@ctx positive).
  Notation sort := (@sort positive).
  Notation subst := (@subst positive).
  Notation rule := (@rule positive).
  Notation lang := (@lang positive).*)

  Notation union_find := (@UnionFind.union_find positive trie_array).
  
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
    | con_node : V -> list positive -> enode
    (*TODO: separate constructor for sorts?  | scon_node : list positive -> enode *)
    | var_node : (*(* sort id*) positive ->*) (* var *) V -> enode.
  
  (* TODO: make sets fast*)

  Fixpoint list_eqb {A} `{Eqb A} (l1 l2 : list A) :=
    match l1, l2 with
    | [], [] => true
    | a1::l1, a2::l2 =>
        (eqb a1 a2) && (list_eqb l1 l2)
    | _, _ => false
    end.

  Lemma list_eqb_refl {A} `{Eqb A} (l : list A) : list_eqb l l = true.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma list_eqb_eq {A} `{Eqb A} (l1 l2 : list A) : list_eqb l1 l2 = true <-> l1 = l2.
  Proof.
    revert l2;
      induction l1; destruct l2; basic_goal_prep; basic_utils_crush.
    {
      apply IHl1; eauto.
    }
    {
      apply IHl1; eauto.
    }
  Qed.
  
  Lemma list_eqb_neq {A} `{Eqb A} (l1 l2 : list A) : list_eqb l1 l2 = false <-> l1 <> l2.
  Proof.
    revert l2;
      induction l1; destruct l2; basic_goal_prep; basic_utils_crush.
    {
      safe_invert H0.
    }
    {
      rewrite andb_true_l in H0.
      rewrite list_eqb_refl in H0.
      safe_invert H0.
    }
    {
      destruct (Eqb_dec a a0); basic_goal_prep; basic_utils_crush.
      {
        simpl.
        apply IHl1; eauto.
      }
      {
        replace (eqb a a0) with false.
        - reflexivity.
        - symmetry.
          rewrite eqb_neq.
          auto.
      }
    }
  Qed.

    
  (* TODO: move to Utils.v once implemented *)

  Instance list_Eqb {A} `{Eqb A} : Eqb (list A) :=
    {
      eqb := list_eqb;
      eqb_refl := list_eqb_refl;
      eqb_eq := list_eqb_eq;
      eqb_neq := list_eqb_neq;
      Eqb_dec := list_eq_dec Eqb_dec;
    }.

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
  all: intros; repeat case_match; simpl; basic_goal_prep; basic_utils_crush.
  all: try safe_invert H; try safe_invert H0; try f_equal.
  all: repeat rewrite ?@eqb_refl, ?@eqb_eq, ?@list_eqb_eq, ?@list_eqb_refl in *; subst; simpl in *; auto.
  all: try congruence.
  {
    destruct (Eqb_dec v v0);basic_goal_prep; basic_utils_crush.
    all: repeat rewrite ?@eqb_refl, ?@eqb_eq, ?@list_eqb_eq, ?@list_eqb_refl in *; subst; simpl in *; auto.
    {
      rewrite @list_eqb_neq.
      intro; subst; auto.
    }
    {
      change (?s1 = ?s2 -> False) with (s1 <> s2) in n.
      rewrite <- @eqb_neq in n.
      rewrite n.
Admitted.
(*    }
    {
  { rewrite list_eqb_eq in H1; auto. }
  { apply eqb_eq; auto. }
  { apply Pos.eqb_eq; auto. }
  {
    destruct (Eqb_dec i i0); basic_goal_prep; basic_utils_crush.
    {
      apply list_eqb_neq in H1.
      apply H1; safe_invert H2; reflexivity.
    }
    {
      apply n; inversion H2; reflexivity.
    }
  }
  {
    destruct (Eqb_dec i i0); basic_goal_prep; basic_utils_crush.
    {
      apply list_eqb_neq; intro; apply H1; congruence.
    }
    {
      apply eqb_neq in n.
      rewrite n.
      reflexivity.
    }
  }
  {
    apply list_eqb_refl.
  }
  {
    change (s1 = s2 -> False) with (s1 <> s2).
    decide equality; apply Eqb_dec.
  }
  Defined.
*)

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
  Definition node_map := (@named_list_map enode positive _).

  (*{positive_map : map.map positive positive}*)

  (* Fix a specific context that the egraph is operating in.
     This means that we can't reuse egraphs between rules
     in a proof of compiler correctness,
     but it is difficult to do so even when tracking multiple contexts.

     On user programs this is generally the empty context.
   *)
  Record egraph :=
    MkEGraph {
        (* TODO: context sorts added to the egraph at initialization *)
        ectx : named_list positive;
        id_equiv : union_find;
        hashcons : node_map
      }.

  Definition empty_egraph :=
    MkEGraph [] UnionFind.empty map.empty.
  
  
  Section EGraphOps.
    Import StateMonad.

    Local Notation "'ST'" := (state egraph).

    Definition find a : ST positive :=
      fun '(MkEGraph ctx U M) =>
        let (U, i) := UnionFind.find U a in
        (i, MkEGraph ctx U M).

    Definition alloc : ST positive :=
      fun '(MkEGraph ctx U M) =>
        let (U, i) := UnionFind.alloc U in
        (i,MkEGraph ctx U M).

    Definition hashcons_lookup (n : enode) : ST (option positive) :=
      fun g =>
        let mi := map.get g.(hashcons) n in
        (mi, g).

    Definition set_hashcons n i : ST unit :=
      fun '(MkEGraph ctx U H) =>
        let H := map.put H n i in
        (tt,MkEGraph ctx U H).
    
    Definition remove_hashcons n : ST unit :=
      fun '(MkEGraph ctx U H) =>
        let H := map.remove H n in
        (tt, MkEGraph ctx U H).

    Definition union_ids a b : ST positive :=
      fun '(MkEGraph ctx U H) =>
        let (U, i) := UnionFind.union U a b in
        (i,MkEGraph ctx U H).

    
    (* Returns the egraph's context *)
    Definition get_ectx : ST (named_list positive) :=
      fun g => (g.(ectx),g).
    
    Definition ectx_cons x (i: positive) : ST unit :=
      fun '(MkEGraph ctx U H) =>
        let ctx := (x,i)::ctx in
        (tt,MkEGraph ctx U H).
    
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

    
    Definition lookup n : ST (option positive) :=
      @! let n <- canonicalize n in
        (hashcons_lookup n).

    Fixpoint lookup_term e : optionT ST positive :=
      match e with
      | var x => lookup (var_node x)
      | con n s =>
          @! let s' <- list_Mmap lookup_term s in
            (lookup (con_node n s') : optionT ST positive)
      end.

    Definition lookup_sort e : optionT ST positive :=
      match e with
      | scon n s =>
          @! let s' <- list_Mmap lookup_term s in
            (lookup (con_node n s') : optionT ST positive)
      end.

    Fixpoint check_ctx' c ec : optionT ST tt :=
      match c, ec with
      | [], [] => @! ret tt 
          

    (*
      Adds a node to the egraph without checking whether it is valid in the language
     *)
    Definition add_node_unchecked (n : enode) : ST positive :=
      @! let mn <- lookup n in
         match mn with
         | Some i => @! ret i
         | None => 
             @! let i <- alloc in
                let tt <- set_hashcons n i in
                ret i
         end.

    Fixpoint add_term_unchecked (e : term) {struct e} : ST positive :=
        match e with
        | var x => add_node_unchecked (var_node x)
        | con n s =>
            @! let si  <- list_Mmap add_term_unchecked s in
               (add_node_unchecked (con_node n si))
        end.
      
      Definition add_sort_unchecked (t: sort) : ST positive :=
        match t with
        | scon n s =>
            @! let si  <- list_Mmap add_term_unchecked s in
               (add_node_unchecked (con_node n si))
        end.


      Section UncheckedSub.
        
        Context (sub : named_list positive).
        
        Fixpoint add_term_unchecked_sub (e : term) {struct e} : ST positive :=
          match e with
          | var x =>
              @! ret unwrap_with_default default (named_list_lookup_err sub x)
          | con n s =>
              @! let si  <- list_Mmap add_term_unchecked_sub s in
                 (add_node_unchecked (con_node n si))
          end.
        
        Definition add_sort_unchecked_sub (t: sort) : ST positive :=
          match t with
          | scon n s =>
              @! let si  <- list_Mmap add_term_unchecked_sub s in
                 (add_node_unchecked (con_node n si))
          end.

      End UncheckedSub.
    

      Definition pf := list enode.

      (* TODO: move to Monad.v*)
        (*TODO: how to generalize?*)
        Instance optionT_default {A} : WithDefault (optionT ST A) := Mret None.

        Class Coerce (A B : Type) : Type := { coerce : A -> B }.

        Instance coerce_id {A} : Coerce A A := {| coerce a := a |}.

       (* Definition coerce {A B} {c : Coerce A B} (a : A) := c a. *)
        
        Class Natural (F H : Type -> Type) : Type :=
          {
            embed :> forall {A}, Coerce (F A) (H A)
          }.

        Instance monad_trans_natural {M} `{Monad M} {T} `{MonadTrans T} : Natural M (T M) :=
          {|
            embed A := {| coerce := @lift T _ M _ _ |}
          |}.

        Instance optionT_inv_natural {M} `{Monad M} : Natural option (optionT M) :=
          {|
            embed A :=
              {| coerce (oa : option A) :=
                  match oa return optionT M _ with
                  | Some a => Mret a
                  | None => Mret None
                  end
              |}
          |}.

        
        Notation "'let' p <-^ e 'in' b" :=
          (Mbind (fun p => b) (coerce e))
            (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).


        Notation "'let' p <?-^ e 'in' b" :=
          (Mbind (fun x => match x with p => b | _ => default end) (coerce e))
            (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).



    Require Import Tries.Canonical.
    Import PTree.

    (*TODO: does this make sense for eqns?*)
    Variant node_result :=
      | term_result : positive -> positive -> node_result
      | sort_result : positive -> node_result.

    

    Record pf_state :=
      {
        pf_egraph : egraph;
        pf_nodes : tree node_result;
        next_idx : positive;
      }.
    
    Section WithLang.

      Context (l : lang).

      Definition egraph_valid g : Prop :=
        (forall x p, In (x,p) g.(ectx) ->
                     forall e g', lookup_term e g = (Some p, g') ->
                                  

      Inductive egraph_proves g : Prop -> Prop :=
      | egraph_var : g.(ectx)
      
      Definition egraph_sound g : Prop :=
        

      Section WithIdxMap.
        Context (result_map : tree node_result).

        (* todo: should I be using stateT option or optionT state?
       should probably flip across most of the below
         *)
        Fixpoint check_args_proof (args : list positive) (c' : ctx) : (optionT ST _) :=
          match args, c' with
          | [], [] => @!ret []
          | p::args, (_,t)::c'=>
              @! let tl <-^ check_args_proof args c' in
                let (term_result e t') <?-^ get p result_map in
                let t_sub <-^ add_sort_unchecked_sub (with_names_from c' (map fst tl)) t in
                let ! Pos.eqb t' t_sub in
                ret (e,t')::tl
          | _,_=> @!ret None
          end.          

        Definition check_node' (n : enode) : optionT ST node_result :=
          match n with
          | var_node x =>
              @! let c <-^ get_ectx in
                let t <-^ named_list_lookup_err c x in
                let e <-^ add_node_unchecked n in
                ret (term_result e t)
          | con_node n s =>
              @! let r <-^ named_list_lookup_err l n in
                match r return optionT ST node_result with
                (* congruence case *)
                | term_rule c' _ t =>
                    @! let s_res <-^ check_args_proof s c' in
                      let s_term_ids := map fst s_res in
                      let sub := with_names_from c' s_term_ids in
                      let t_sub <-^ add_sort_unchecked_sub sub t in
                      let e <-^ add_node_unchecked (con_node n s) in
                      ret (term_result e t_sub)
                | term_eq_rule c' e1 e2 t =>
                    @! let s_res <-^ check_args_proof s c' in
                      let s_term_ids := map fst s_res in
                      let sub := with_names_from c' s_term_ids in
                      let t_sub <-^ add_sort_unchecked_sub sub t in
                      let e1_sub <-^ add_term_unchecked_sub sub e1 in
                      let e2_sub <-^ add_term_unchecked_sub sub e2 in
                      let e <-^ union_ids e1_sub e2_sub in
                      ret (term_result e t_sub)
                | _ => @! ret None
                end
          end.
        
        Lemma check_node'_sound
          : 

      End WithIdxMap.

      Definition check_node (n : enode) : optionT (state pf_state) unit :=
        (fun S =>
           @!match check_node' (pf_nodes S) n (pf_egraph S) with
             | (Some n1,g) =>
                 (Some tt,
                   {| pf_egraph := g;
                     pf_nodes := set (next_idx S) n1 (pf_nodes S);
                     next_idx := next_idx S + 1 |})
             | (None,_) => (None, S)
             end).
      
      (*TODO: use named_list for pf instead of list?*)
      Fixpoint check_proof' (p : pf) : optionT (state pf_state) unit :=
          match p with
          | [] => @!ret tt
          | n::p' =>
              @! let tt <-^ check_proof' p' in
                (check_node n)
          end.
      
      Definition check_proof (p : pf) : option pf_state :=
        let (is_valid, S) :=
          check_proof' p {| pf_egraph := empty_egraph;
                           pf_nodes:= empty _;
                           next_idx := 1 |}
        in
        if is_valid then Some S else None.
      
      Section Inner.
        Context (add_sort' : named_list (positive * positive) -> sort -> Checker positive).

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
          Context (add_term' : term -> Checker (positive * positive)).

          (*TODO: return pair of lists or list of pairs?*)
          Fixpoint add_args' (s : list term) (c : ctx) {struct s}
            : Checker (list (positive * positive)) :=
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
        Context (sub_and_ctx : named_list (positive * positive)).
        
        Fixpoint add_term' (e : term) {struct e} : Checker (positive * positive) :=
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
          (add_sort' : named_list (positive * positive) -> sort -> Checker positive)
          (sub_and_ctx : named_list (positive * positive))
        : list term -> ctx -> Checker (list (positive * positive)) :=
            add_args' add_sort' (add_term' add_sort' sub_and_ctx).
      
      (*Use fuel here equal to the length of the language.
        This is sufficient since the fuel is used when a term checks its sort,
        given in either t or c of a rule c|- (n x...) : t
        and all sorts must be defined before they are used.
        
        TODO: check that it's actually sufficient
       *)
      Fixpoint add_sort' (fuel : nat)
               (sub_and_ctx : named_list (positive * positive))
               (t : sort) : Checker positive :=
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

      Fixpoint sub_and_ctx_from_ectx (acc : positive) (ectx : named_list positive)
        : named_list (positive * positive) :=
        match ectx with
        | [] => []
        | (x,ti)::ectx' =>
            (x,(acc,ti))::(sub_and_ctx_from_ectx (succ acc) ectx')
        end.
      
      Definition add_sort (t : sort) : Checker positive :=
        @! let ectx <- liftST get_ectx in
           (add_sort' (length l) (sub_and_ctx_from_ectx zero ectx) t).

      Definition add_term (e : term) : Checker (positive*positive) :=
        @! let ectx <- liftST get_ectx in
           (add_term' (add_sort' (length l)) (sub_and_ctx_from_ectx zero ectx) e).


      
      (*Parameterize by query trie since the inductive can't be defined generically *)
      Context (query_trie : Type)
              (qt_unconstrained : query_trie -> query_trie)
              (trie_map : map.map positive query_trie)
              (qt_tree : trie_map -> query_trie)
              (qt_nil : query_trie)
              (values_of_next_var : query_trie -> set_with_top positive_set)
              (choose_next_val : positive -> query_trie -> query_trie).
      Context (relation : set (list positive))
              (db : map.map positive relation)
              (arg_map : map.map positive positive).
      
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
                     @!let s' : list positive <- list_Mmap find s in
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
        Fixpoint compile_term_aux (max_var : positive) p : positive * positive * list (atom _) :=
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
        Definition compile_sort_aux (max_var : positive) p :=
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
          (generic_join positive positive
                        positive_set query_trie qt_unconstrained _ qt_tree qt_nil
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
      
      Definition add_and_check_term (e : term) : ST (option (positive *positive)) :=
        try_with_backtrack (resolve_checker' (add_term e) fuel).

      (*TODO: should this check that x is fresh?*)
      Definition add_and_check_ctx_cons x t : ST bool :=
        @! let mpositive <- try_with_backtrack (resolve_checker' (add_sort t) fuel) in
           match mpositive with
           | Some positive =>
               @! let x' <- add_node_unchecked (var_node x) in
                  let _ <- ectx_cons x' positive in
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

End __.

Module PositiveInstantiation.

  Import RelationalDB.PositiveInstantiation.
  
  Definition eclass_map := TrieMap.map (@eclass positive _).

  Definition positive_set := trie_set.

  
  (* TODO: make pair sets just like pair maps to avoid set_from_map*)
  Instance eqn_set : set (positive*positive) :=
    set_from_map (@pair_map _ _ _ trie_set (TrieMap.map _)).


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

  Definition pos_value_subst : Rule.lang positive :=
    Eval compute in (rename_lang value_subst).
  (*TODO: are vars different?*)
  Definition constr_rename : named_list positive :=
    Eval compute in (rename_constr_subst value_subst).

  Definition test_ctx :=
    Eval compute in (rename_ctx constr_rename
                                {{c "G" : #"env",
                                      "A" : #"ty",
                                        "B" : #"ty"}}
                                100).

  Definition check_ctx' l :=
    check_ctx' (positive:=positive) (array := TrieMap.TrieArrayList.trie_array)
               eclass_map eqn_set l
               qt_unconstrained _ qt_tree qt_nil
               values_of_next_var choose_next_val relation db arg_map.
  
  Definition add_and_check_term l :=
    add_and_check_term (positive:=positive) (array := TrieMap.TrieArrayList.trie_array)
                       (eclass_map:=eclass_map) eqn_set l
                       qt_unconstrained _ qt_tree qt_nil
                       values_of_next_var choose_next_val relation db arg_map.
  
  Definition add_term :=
    add_term (positive:=positive) (array := TrieMap.TrieArrayList.trie_array)
             (eclass_map:=eclass_map) eqn_set.
  
  Definition find :=
    find (positive:=positive) (array := TrieMap.TrieArrayList.trie_array)
             (eclass_map:=eclass_map).
  
  Definition initial_egraph :=
    Eval compute in
      (match check_ctx' pos_value_subst test_ctx with
       | Some g => g
       | None => empty_egraph _
       end).

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
                            pos_value_subst
                            test_term
                            initial_egraph)).
  Eval compute in (add_term
                     pos_value_subst
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
                            pos_value_subst
                            test_term
                            initial_egraph).
  Definition egraph2 :=
    Eval compute in (fst (add_and_check_term
                            pos_value_subst
                            test_term
                            initial_egraph)).
  (*Print egraph2.*)

End PositiveInstantiation.





