Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import NArith List.
Import ListNotations.
Open Scope list.

Require Import Tries.Canonical.
Import PTree.

From Utils Require Import Utils Monad.
From Named Require Import Core.
Import Core.Notations.


Require Import Utils.UnionFind.
Require Import Utils.TrieMap.
Import TrieArrayList.
From coqutil Require Import Map.Interface.

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

  Variant node : Type :=
    (* variable name *)
    | nvar : V -> node
    (* Rule label, list of subterms*)
    | ncon : V -> list positive -> node.
                                     (*
    | ncemp : node
    | nccons : positive -> positive -> node.*)

  (* We assume that the head is the root by default.
     Invariant: all indices of the head are < length of the tail
   *)

  Definition pf := list node.

  (*TODO: backport these to core.v. Copied from TreeProofs.v*)
    
    Local Lemma term_con_congruence l c t name s1 s2 c' args t'
      : In (name, term_rule c' args t') l ->
        t = t'[/with_names_from c' s2/] ->
        wf_lang l ->
        eq_args l c c' s1 s2 ->
        eq_term l c t (con name s1) (con name s2).
    Proof.
      intros.
      assert (wf_ctx l c') by with_rule_in_wf_crush.
      rewrite <- (wf_con_id_args_subst c' s1);[| basic_core_crush..].
      rewrite <- (wf_con_id_args_subst c' s2);[|basic_core_crush..].
      subst.
      change (con ?n ?args[/?s/]) with (con n args)[/s/].
      eapply eq_term_subst; eauto.
      {
        apply eq_args_implies_eq_subst; eauto.
      }
      {
        constructor.
        replace t' with t'[/id_subst c'/].
        - eapply wf_term_by; basic_core_crush.
        - basic_core_crush.
      }
    Qed.

    
    Local Lemma sort_con_congruence l c name s1 s2 c' args
      : In (name, sort_rule c' args) l ->
        wf_lang l ->
        eq_args l c c' s1 s2 ->
        eq_sort l c (scon name s1) (scon name s2).
    Proof.
      intros.
      assert (wf_ctx l c') by with_rule_in_wf_crush.
      rewrite <- (wf_con_id_args_subst c' s1);[| basic_core_crush..].
      rewrite <- (wf_con_id_args_subst c' s2);[|basic_core_crush..].
      subst.
      change (scon ?n ?args[/?s/]) with (scon n args)[/s/].
      eapply eq_sort_subst; eauto.
      { apply eq_args_implies_eq_subst; eauto. }
      { constructor.
        eapply wf_sort_by; basic_core_crush.
      }
    Qed.

  
    
  
  Section WithLang.

    Context (l : lang).


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


        
    (*TODO: copied; should be deduplicated if not replaced *)
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

  (*TODO: this isn't very efficient*)

  Axiom eqb_node : Eqb node.
  Existing Instance eqb_node.
  Definition node_map := (@named_list_map node positive _).

  (* Basically an egraph without congruence closure or saturation *)
  Record proof_context :=
    MkPC {
        id_equiv :  union_find;
        hashcons : node_map;
      }.

  Import StateMonad.

  Notation pfM := (stateT proof_context option).

  (*TODO: move to Monad.v*)
  
Notation "'let' p <^- e 'in' b" :=
  (Mbind (fun p => b) (lift e))
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).


  Notation "'ret' { M } e" := (Mret (M:=M) e) (in custom monadic_do at level 90, e constr).

Notation "'let' { M } p <- e 'in' b" :=
  (Mbind (M:=M) (fun p => b) e)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).

Notation "'let' { M } p <?- e 'in' b" :=
  (Mbind (M:=M) (fun x => match x with p => b | _ => default end) e)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).

Instance stateT_default S M A `{WithDefault (M (A*S))%type}
  : WithDefault (stateT S M A) :=
  fun _ => default.

Existing  Instance stateT_trans.
  
  Definition find i : pfM positive :=
    fun pc =>
      @! let (uf', i') <- find pc.(id_equiv) i in
        ret (i',MkPC uf' pc.(hashcons)).

  
  Definition alloc : pfM positive :=
    fun pc => let (uf', i') := alloc pc.(id_equiv) in
              Some (i', MkPC uf' pc.(hashcons)).

  
  Definition set_hashcons n i : pfM unit :=
    fun pc => let hc' := map.put pc.(hashcons) n i in
              Some (tt, MkPC pc.(id_equiv) hc').

  Definition canonicalize n : pfM node :=
    match n with     
    | ncon name args =>
        @! let args <- list_Mmap find args in       
          ret ncon name args
    | nvar x =>
        @! ret nvar x
    end.

    
    Definition eqb_ids a b : pfM unit :=
      @! let fa <- (find a) in
         let fb <- (find b) in
         let ! eqb fa fb in
         ret tt.

    (*TODO: what's the right output type?
      Shouldn't need the 2nd option (but then need a different combinator)
     *)
    Definition lookup n : pfM (option positive) :=
      fun pc =>
        let mi := map.get pc.(hashcons) n in
        Some (mi,pc).
  
      (*
      Adds a node to the egraph without checking whether it is valid in the language
     *)
    Definition add_node_unchecked (n : node) : pfM positive :=
      @! let mn <- lookup n in
         match mn with
         | Some i => @! ret i
         | None => 
             @! let i <- alloc in
                let tt <- set_hashcons n i in
                ret i
         end.

    
    Fixpoint lookup_term (pc : proof_context) (e : term) : option _ :=
      match e with
      | var x => map.get pc.(hashcons) (nvar x)
      | con n s =>
          @! let si <- list_Mmap (lookup_term pc) s in
            (map.get pc.(hashcons) (ncon n si))
      end.

    Definition lookup_sort (pc : proof_context) (t : sort) : option _ :=
      match t with
      | scon n s =>
          @! let si <- list_Mmap (lookup_term pc) s in
            (map.get pc.(hashcons) (ncon n si))
      end.
    

    Section UnderSubst.
      
      Context (sub : named_list positive).

      
      Fixpoint lookup_term' (pc : proof_context) (e : term) : option _ :=
        match e with
        | var x => (named_list_lookup_err sub x)
        | con n s =>
            @! let si <- list_Mmap (lookup_term' pc) s in
              (map.get pc.(hashcons) (ncon n si))
        end.

      Definition lookup_sort' (pc : proof_context) (t : sort) : option _ :=
        match t with
        | scon n s =>
            @! let si <- list_Mmap (lookup_term' pc) s in
              (map.get pc.(hashcons) (ncon n si))
        end.

      Fixpoint add_term_unchecked' (e : term) {struct e} : pfM positive :=
        match e with
        | var x => lift (named_list_lookup_err sub x)
        | con n s =>
            @! let si  <- list_Mmap add_term_unchecked' s in
              (add_node_unchecked (ncon n si))
        end.
      
      Definition add_sort_unchecked' (t: sort) : pfM positive :=
        match t with
        | scon n s =>
            @! let si <- list_Mmap add_term_unchecked' s in
              (add_node_unchecked (ncon n si))
        end.

    End UnderSubst.

    (*

               
     Fixpoint add_term_unchecked (e : term) {struct e} : pfM positive :=
        match e with
        | var x => add_node_unchecked (nvar x)
        | con n s =>
            @! let si  <- list_Mmap add_term_unchecked s in
               (add_node_unchecked (ncon n si))
        end.
      
      Definition add_sort_unchecked (t: sort) : pfM positive :=
        match t with
        | scon n s =>
            @! let si <- list_Mmap add_term_unchecked s in
               (add_node_unchecked (ncon n si))
        end.

    *)
    
    (*
  Section WithCtx.
    (*TODO: ids or sorts on rhs*)
    Context (c : named_list positive).*)
      
      Section Inner.

        (*TODO: return sort or no?*)
        Context (add_term' : term -> (*sort*) positive-> pfM positive).

        (*TODO: return pair of lists or list of pairs?*)
        Fixpoint add_args' (s : list term) (c : ctx) {struct s}
          : pfM (list positive) :=
          match s, c with
          | [],[] => @! ret []
          | e::s, (_,t)::c =>
              @! let sci <- add_args' s c in
                (* sort given by c *)
                let ti <- add_sort_unchecked' (with_names_from c sci) t in
                let ei <- add_term' e ti in
                (*  let tt <- eqb_ids ti' ti in *)
                ret ei::sci
          | _,_ => default
          end.
      End Inner.

      Section UnderSubst.
      
        Context (sub : named_list positive).
        
        Fixpoint add_term' (e : term) (t_in : positive) {struct e} : pfM positive :=
          match e with
          | var x => lift (named_list_lookup_err sub x)
          | con n s =>
              @! let term_rule c _ t <?- lift (named_list_lookup_err l n) in
                let sci <- add_args' add_term' s c in
                (* sort generated from sort of n rule *)
                let t_out <- add_sort_unchecked' (with_names_from c sci) t in
                let tt <- eqb_ids t_in t_out in
                (add_node_unchecked (ncon n sci))
          end.

        Definition add_sort' (t : sort) : pfM positive :=
          let (n,s) := t in
          @! let sort_rule c _ <?- lift (named_list_lookup_err l n) in
            let sci <- add_args' add_term' s c in
            (add_node_unchecked (ncon n sci)).
            
      End UnderSubst.

      Section WithCtx.
      
        Context (ctx : named_list positive).
      
        
        Fixpoint add_term (e : term) (t_in : positive) {struct e} : pfM positive :=
          match e with
          | var x =>
              @! let t_out <^- (named_list_lookup_err ctx x) in
                let tt <- eqb_ids t_in t_out in
                (add_node_unchecked (nvar x))
          | con n s =>
              @! let term_rule c _ t <?- lift (named_list_lookup_err l n) in
                let sci <- add_args' add_term s c in
                (* sort generated from sort of n rule *)
                let t_out <- add_sort_unchecked' (with_names_from c sci) t in
                let tt <- eqb_ids t_in t_out in
                (add_node_unchecked (ncon n sci))
          end.

        Definition add_sort (t : sort) : pfM positive :=
          let (n,s) := t in
          @! let sort_rule c _ <?- lift (named_list_lookup_err l n) in
            let sci <- add_args' add_term s c in
            (add_node_unchecked (ncon n sci)).
            
      End WithCtx.

      Section WithCtx.
        Context (c : ctx).

        
        Definition lookup_sort_of_node (pc : proof_context) (n : node)
          : option _ :=
          match n with
          | nvar x =>
              @!let t <- named_list_lookup_err c x in
              (*TODO: do I want to have this precomputed?*)
                (lookup_sort pc t)
          | ncon n s =>
              @! let (term_rule _ _ t) <?- named_list_lookup_err l n in
                (lookup_sort' (with_names_from c s) pc t)
          end.
  
        
        Definition lookup_term_and_sort (pc : proof_context) (e : term)
          : option _ :=
          match e with
          | var x =>
              @! let i <- map.get pc.(hashcons) (nvar x) in
                let ti <- lookup_sort_of_node pc (nvar x) in
                ret (i,ti)
          | con n s =>
              @! let si <- list_Mmap (lookup_term pc) s in
                let i <- map.get pc.(hashcons) (ncon n si) in
                let ti <- lookup_sort_of_node pc (ncon n si) in
                ret (i,ti)
          end.

        (*TODO: is R really right?*)
      Definition proof_context_valid pc t :=
        uf_ok pc.(id_equiv) t
                  /\ (forall i t, Some i = lookup_sort pc t -> wf_sort l c t)
                  /\ (forall ti i e t,
                         Some ti = lookup_sort pc t ->
                         Some (i,ti) = lookup_term_and_sort pc e ->
                         wf_term l c e t).

      Definition empty := MkPC empty map.empty.

      Lemma empty_ok
        : proof_context_valid empty [].
      Proof.
        unfold proof_context_valid.
        split.
        {
          apply empty_ok.
        }
        split.
        all:intros; simpl in *.
        {
          destruct t0; simpl in *.
          revert H; case_match; congruence.
        }
        {
          destruct e; simpl in *; try congruence.
          revert H0; case_match; congruence.
        }
      Qed.

      
      Lemma lookup_term_forest_equiv f f' pc1 pc2 e
        : forest_equiv f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          lookup_term pc1 e = lookup_term pc2 e.
      Proof.
        intros; induction e;
          intros; simpl in *.
        1: destruct pc1; destruct pc2; simpl in *; subst; now auto.
        enough (list_Mmap (lookup_term pc1) l0
                = list_Mmap (lookup_term pc2) l0) as H'
            by (rewrite H'; case_match; congruence).
        revert dependent l0.
        induction l0;
          intros; simpl in *; auto.
        break.
        rewrite H3.
        case_match; auto.
        rewrite IHl0; eauto.
      Qed.

      (* TODO: generalize*)
      Lemma list_Mmap_ext_option {A B} (f g : A -> option B) ls
        : (forall x, f x = g x) -> list_Mmap f ls = list_Mmap g ls.
      Proof.
        intro; induction ls;
          basic_goal_prep;
          basic_utils_crush.
        rewrite H.
        case_match; auto.
        rewrite IHls.
        case_match; auto.
      Qed.
      
      Lemma map_lookup_term_forest_equiv f f' pc1 pc2 e
        : forest_equiv f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          list_Mmap (lookup_term pc1) e = list_Mmap (lookup_term pc2) e.
      Proof.
        intros; eapply list_Mmap_ext_option.
        intros; eapply lookup_term_forest_equiv; eauto.
      Qed.
        
      Lemma lookup_sort_forest_equiv f f' pc1 pc2 t
        : forest_equiv f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          lookup_sort pc1 t = lookup_sort pc2 t.
      Proof.
        intros; induction t;
          intros; simpl in *.
        enough (list_Mmap (lookup_term pc1) l0
                = list_Mmap (lookup_term pc2) l0) as H'
            by (rewrite H'; case_match; congruence).
        eapply map_lookup_term_forest_equiv; eauto.
      Qed.

      
      Lemma lookup_term'_forest_equiv f f' pc1 pc2 e sub
        : forest_equiv f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          lookup_term' sub pc1 e = lookup_term' sub pc2 e.
      Proof.
        intros; induction e;
          intros; simpl in *.
        1: destruct pc1; destruct pc2; simpl in *; subst; now auto.
        enough (list_Mmap (lookup_term' sub pc1) l0
                = list_Mmap (lookup_term' sub pc2) l0) as H'
            by (rewrite H'; case_match; congruence).
        revert dependent l0.
        induction l0;
          intros; simpl in *; auto.
        break.
        rewrite H3.
        case_match; auto.
        rewrite IHl0; eauto.
      Qed.
      
      Lemma map_lookup_term'_forest_equiv f f' pc1 pc2 e sub
        : forest_equiv f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          list_Mmap (lookup_term' sub pc1) e = list_Mmap (lookup_term' sub pc2) e.
      Proof.
        intros; eapply list_Mmap_ext_option.
        intros; eapply lookup_term'_forest_equiv; eauto.
      Qed.
        

      
      Lemma lookup_sort'_forest_equiv f f' pc1 pc2 t sub
        : forest_equiv f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          lookup_sort' sub pc1 t = lookup_sort' sub pc2 t.
      Proof.
        intros; induction t;
          intros; simpl in *.
        enough (list_Mmap (lookup_term' sub pc1) l0
                = list_Mmap (lookup_term' sub pc2) l0) as H'
            by (rewrite H'; case_match; congruence).
        eapply map_lookup_term'_forest_equiv; eauto.
      Qed.

      
        
      Lemma lookup_term_and_sort_forest_equiv f f' pc1 pc2 e
        : forest_equiv f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          lookup_term_and_sort pc1 e = lookup_term_and_sort pc2 e.
      Proof.
        intros; induction e;
          intros; simpl in *.
        {
          destruct pc1; destruct pc2; simpl in *; subst.
          case_match; eauto.
          my_case Heqnl (named_list_lookup_err c n); eauto.
          erewrite lookup_sort_forest_equiv; eauto.
        }
        {
          erewrite map_lookup_term_forest_equiv; eauto.
          case_match; eauto.
          rewrite H2; case_match; eauto.
          my_case Hnl (named_list_lookup_err l n); auto.
          my_case Hr r; eauto.
          erewrite lookup_sort'_forest_equiv; eauto.
        }
      Qed.

      
      Lemma lookup_term_forest_subrel f f' pc1 pc2 e
        : forest_subrel f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          forall i,
            Some i = lookup_term pc1 e ->
            Some i = lookup_term pc2 e.
      Proof.
        intros Hsub Hokf Hokf';
          induction e;
          intros; simpl in *.
        1: destruct pc1; destruct pc2; simpl in *; subst; now auto.
        revert H1; 
          case_match;[| congruence].
        
        enough (Some l1 = list_Mmap (lookup_term pc2) l0) as H'.
        {
          rewrite<- H'.
          congruence.
        }
        revert dependent l1.
        revert dependent l0.
        induction l0;
          intros; simpl in *; auto.
        break.
        revert HeqH1.
        case_match;[| congruence].
        case_match;[| congruence].
        intro H'; safe_invert H'.
        specialize (H H0 p eq_refl).
        rewrite <- H.
        erewrite <- IHl0; eauto.
      Qed.
      
      Lemma map_lookup_term_forest_subrel f f' pc1 pc2 e
        : forest_subrel f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          forall l,
            Some l = list_Mmap (lookup_term pc1) e ->
            Some l = list_Mmap (lookup_term pc2) e.
      Proof.
        intros ? ? ? ?.
        induction e;
          intros; simpl in *; auto.
        break.
        revert H3.
        case_match;[| congruence].
        case_match;[| congruence].
        intro H'; safe_invert H'.
        erewrite <- lookup_term_forest_subrel; eauto.
        erewrite <- IHe; eauto.
      Qed.

      Lemma lookup_sort_forest_subrel f f' pc1 pc2 t
        : forest_subrel f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          forall i,
            Some i = lookup_sort pc1 t ->
            Some i = lookup_sort pc2 t.
      Proof.
        
        intros Hsub Hokf Hokf';
          induction t;
          intros; simpl in *.
        revert H0; 
          case_match;[| congruence].
        
        enough (Some l1 = list_Mmap (lookup_term pc2) l0) as H'.
        {
          rewrite<- H'.
          congruence.
        }
        revert dependent l1.
        revert dependent l0.
        induction l0;
          intros; simpl in *; auto.
        break.
        revert HeqH0.
        case_match;[| congruence].
        case_match;[| congruence].
        intro H'; safe_invert H'.
        erewrite <- lookup_term_forest_subrel; eauto.
        erewrite <- IHl0; eauto.
      Qed.

      (*TODO: concerning; why is this true?*)
      Lemma lookup_term'_forest_subrel f f' pc1 pc2 e sub
        : forest_subrel f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          lookup_term' sub pc1 e = lookup_term' sub pc2 e.
      Proof.
        intros; induction e;
          intros; simpl in *.
        1: destruct pc1; destruct pc2; simpl in *; subst; now auto.
        enough (list_Mmap (lookup_term' sub pc1) l0
                = list_Mmap (lookup_term' sub pc2) l0) as H'
            by (rewrite H'; case_match; congruence).
        revert dependent l0.
        induction l0;
          intros; simpl in *; auto.
        break.
        rewrite H3.
        case_match; auto.
        rewrite IHl0; eauto.
      Qed.
      
      Lemma map_lookup_term'_forest_subrel f f' pc1 pc2 e sub
        : forest_subrel f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          list_Mmap (lookup_term' sub pc1) e = list_Mmap (lookup_term' sub pc2) e.
      Proof.
        intros; eapply list_Mmap_ext_option.
        intros; eapply lookup_term'_forest_subrel; eauto.
      Qed.
        

      
      Lemma lookup_sort'_forest_subrel f f' pc1 pc2 t sub
        : forest_subrel f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          lookup_sort' sub pc1 t = lookup_sort' sub pc2 t.
      Proof.
        intros; induction t;
          intros; simpl in *.
        enough (list_Mmap (lookup_term' sub pc1) l0
                = list_Mmap (lookup_term' sub pc2) l0) as H'
            by (rewrite H'; case_match; congruence).
        eapply map_lookup_term'_forest_subrel; eauto.
      Qed.

      
        
      Lemma lookup_term_and_sort_forest_subrel f f' pc1 pc2 e
        : forest_subrel f f' ->
          uf_ok pc1.(id_equiv) f ->
          uf_ok pc2.(id_equiv) f' ->
          pc1.(hashcons) = pc2.(hashcons) ->
          forall p,
          Some p = lookup_term_and_sort pc1 e ->
          Some p = lookup_term_and_sort pc2 e.
      Proof.
        intros ? ? ? ?; induction e;
          intros; simpl in *.
        {
          revert H3.
          destruct pc1; destruct pc2; simpl in *; subst.
          case_match; eauto.
          my_case Heqnl (named_list_lookup_err c n); eauto.
          case_match; [|congruence].
          erewrite <- lookup_sort_forest_subrel; cycle 5;
          eauto.
        }
        {
          revert H4.
          case_match; [|congruence].
          erewrite <- map_lookup_term_forest_subrel; cycle 5; eauto.
          rewrite H2; case_match; eauto.
          my_case Hnl (named_list_lookup_err l n); auto.
          my_case Hr r; eauto.
          erewrite lookup_sort'_forest_subrel; eauto.
        }
      Qed.
        

      Lemma find_ok pc f pc' (i i' : positive)
        : proof_context_valid pc f ->
          Some (i', pc') = find i pc ->
          equiv_by_forest f i i'
          /\ (exists f', forest_equiv f f' /\ proof_context_valid pc' f').
      Proof.
        unfold proof_context_valid.
        intros; break.
        revert H0; unfold find.
        destruct pc.
        simpl in *.
        case_match; try congruence.
        break.
        intro H'; safe_invert H'.
        eapply find_spec in HeqH0; eauto; break.
        intuition subst.
        eexists; intuition eauto.
        {
          eapply H1; eauto.
          erewrite lookup_sort_forest_equiv; eauto.
        }
        {
          eapply H2; eauto.
          -erewrite lookup_sort_forest_equiv; eauto.
          -erewrite lookup_term_and_sort_forest_equiv; eauto.
        }
      Qed.

      Definition union i1 i2 : pfM positive :=
        fun pc =>
          @! let (uf', i') <- union pc.(id_equiv) i1 i2 in
            ret (i',MkPC uf' pc.(hashcons)).
      
      Lemma union_ok pc f pc' i' (i1 i2 : positive)
        : proof_context_valid pc f ->
          Some (i', pc') = union i1 i2 pc ->
          exists f', forest_subrel f f'
                     /\ equiv_by_forest f' i1 i'
                     /\ equiv_by_forest f' i2 i'
                     /\ proof_context_valid pc' f'.
      Proof.
        unfold union.
        intro.
        destruct pc; simpl in *.
        case_match; try congruence.
        break.
        intro H'; safe_invert H'.
        revert HeqH0.
        intro.
        destruct H; simpl in *.
        eapply union_spec in HeqH0; eauto.
        break.
        eexists; intuition eauto.
        constructor; intuition eauto.
        {
          eapply H0.
          eapply lookup_sort_forest_subrel; cycle 4.
          1:eauto.
          all:simpl.
          2:eauto.
          2:eauto.
          2:eauto.
          TODO: need better spec for union;
          need to know it's the least rel that satisfies conditions
          TODO: subrel in the wrong direction
          TODO: uf_ok not true
          eapply lookup_term_and_sort_forest_subrel .
          TODO: need rewrite subrel
          erewrite lookup_sort_forest_equiv; eauto.
          admit (*lemma*).
        }
        {
          eapply H1.
          1: erewrite  lookup_sort_forest_equiv; eauto.
          1:admit (*lemma*).
          erewrite lookup_term_and_sort_forest_equiv; eauto.
          admit (*lemma*).
        }
        {
          
        }
        4: constructor; eauto.
        1:
        
        unfold UnionFind.union.
        simpl.
        destruct H.
        case_match; try congruence.
        break.
        eapply find_spec in HeqH1; eauto.
        case_match; try congruence.
        break.
        eapply find_spec in HeqH2; eauto.
        (*TODO: copied*)
        
        Ltac destruct_pos_eqb i j :=
          let Hneq := fresh "Hneq" in
          let Hneq' := fresh "Hneq" in
          destruct (Pos.eq_dec i j) as [? | Hneq];
          [ subst; rewrite Pos.eqb_refl
          | pose proof Hneq as Hneq'; apply Pos.eqb_neq in Hneq'; rewrite Hneq'].
        destruct_pos_eqb p0 p1.
        {
          intro H'; safe_invert H'.
          break.
          eexists; intuition eauto.
          1:admit (*lemma*).
          1:admit (*lemma *).
          constructor; simpl; eauto.
          1:admit (*lemma*).
          split.
          all: intros.
          {
            eapply H0.
            erewrite  lookup_sort_forest_equiv; eauto.
            admit (*lemma*).
          }
          {
            eapply H1.
            1: erewrite  lookup_sort_forest_equiv; eauto.
            1:admit (*lemma*).
            erewrite lookup_term_and_sort_forest_equiv; eauto.
            admit (*lemma*).
          }
        }
        {
          case_match;[| congruence].
          case_match;[| congruence].
          destruct (PeanoNat.Nat.compare_spec n0 n).
          all: intro H'; safe_invert H'.
          all: break.
          case_match;[| congruence].
          
        }
        

  Section WithProofCtx.
    Context (pc : proof_context).

    (*TODO: make i the canonical node*)
    Definition node_at n i :=      
      Some i = map.get pc.(hashcons) n.

     (*
  Inductive eq_sort : ctx -> sort -> sort -> Prop :=
  | eq_sort_by : forall c name t1 t2,
      In (name, sort_eq_rule c t1 t2) l ->
      eq_sort c t1 t2
  | eq_sort_subst : forall c s1 s2 c' t1' t2',
      (* Need to assert wf_ctx c here to satisfy
         assumptions' presuppositions
       *)
      wf_ctx c' ->
      eq_subst (Model:= mut_mod eq_sort eq_term wf_sort wf_term) c c' s1 s2 ->
      eq_sort c' t1' t2' ->
      eq_sort c t1'[/s1/] t2'[/s2/]
  | eq_sort_refl : forall c t,
      wf_sort c t ->
      eq_sort c t t
  | eq_sort_trans : forall c t1 t12 t2,
      eq_sort c t1 t12 ->
      eq_sort c t12 t2 ->
      eq_sort c t1 t2
  | eq_sort_sym : forall c t1 t2, eq_sort c t1 t2 -> eq_sort c t2 t1
  with eq_term : ctx -> sort -> term -> term -> Prop :=
  | eq_term_subst : forall c s1 s2 c' t e1 e2,
      (* Need to assert wf_ctx c' here to satisfy
         assumptions' presuppositions
       *)
      wf_ctx c' ->
      eq_subst (Model:= mut_mod eq_sort eq_term wf_sort wf_term) c c' s1 s2 ->
      eq_term c' t e1 e2 ->
      eq_term c t[/s2/] e1[/s1/] e2[/s2/]
  | eq_term_by : forall c name t e1 e2,
      In (name,term_eq_rule c e1 e2 t) l ->
      eq_term c t e1 e2
  | eq_term_refl : forall c e t,
      wf_term c e t ->
      eq_term c t e e
  | eq_term_trans : forall c t e1 e12 e2,
      eq_term c t e1 e12 ->
      eq_term c t e12 e2 ->
      eq_term c t e1 e2
  | eq_term_sym : forall c t e1 e2, eq_term c t e1 e2 -> eq_term c t e2 e1
  (* Conversion:

c |- e1 = e2 : t 
               ||
c |- e1 = e2 : t'
   *)
  | eq_term_conv : forall c t t',
      eq_sort c t t' ->
      forall e1 e2,
        eq_term c t e1 e2 ->
        eq_term c t' e1 e2
                (*
  (* TODO: do I want to allow implicit elements in substitutions? *)
  (* TODO: do I want to define this in terms of eq_args? *)
  with eq_subst : ctx -> ctx -> subst -> subst -> Prop :=
  | eq_subst_nil : forall c, eq_subst c [] [] []
  | eq_subst_cons : forall c c' s1 s2,
      eq_subst c c' s1 s2 ->
      forall name t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        eq_term c t[/s2/] e1 e2 ->
        eq_subst c ((name, t)::c') ((name,e1)::s1) ((name,e2)::s2)*)*)

    (*TODO:
      1. conversion/node id equivalence
      2. ids for ctxs & types; do I need them?
         - don't need ctxs since always working in 1 ctx
         - don't need sorts since the sort is unambiguous up to union-find
         + should be a relevant lemma in matches
         - do I need to add sorts to egraph for the above to work?
     *)
  Inductive wf_term : ctx -> term -> sort -> positive -> Prop :=
  | wf_term_by : forall c n s args c' t si i,
      In (n, term_rule c' args t) l ->
      wf_args c s c' si ->
      node_at (ncon n si) i ->
      wf_term c (con n s) t[/(with_names_from c' s)/] i
  | wf_term_conv : forall c e t t' i i',
      (* We add this condition so that we satisfy the assumptions of eq_sort
         TODO: necessary? not based on current judgment scheme.
         wf_term c e t should imply wf_sort c t,
         and eq_sort c t t' should imply wf_sort c t


      wf_sort c t -> 
       *)
      wf_term c e t i ->
      wf_sort c t i' ->
      wf_sort c t' i' ->
      (*eq_sort c t t' ->*)
      wf_term c e t' i
  | wf_term_var : forall c n t i,
      In (n, t) c ->
      node_at (nvar n) i ->
      wf_term c (var n) t i
  with wf_sort : ctx -> sort -> positive -> Prop :=
  | wf_sort_by : forall c n s args c' si i,
      In (n, (sort_rule c' args)) l ->
      wf_args c s c' si ->
      node_at (ncon n si) i ->
      wf_sort c (scon n s) i
  with wf_args : ctx -> list term -> ctx -> list positive -> Prop :=
  | wf_args_nil : forall c, wf_args c [] [] []
  | wf_args_cons : forall c s c' name e t i li,
      wf_term c e t[/with_names_from c' s/] i ->
      (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
      wf_args c s c' li ->
      wf_args c (e::s) ((name,t)::c') (i::li).








    
    (*TODO: change section name?*)
    Context (c : ctx).
    Context (wfl : wf_lang l).



    
       
     (*TOOD: replace case_match with this? Copied twice already*)
     Ltac case_match' :=
       try lazymatch goal with
           [ H :  context [ match ?e with
                            | _ => _
                            end] |- _ ] => revert H
         end;
       case_match.
    
  Section Inner.

    Context (proof_result : proof_context).
    
    Fixpoint check_args_proof (args : list positive) (c' : ctx) :=
      match args, c' with
      | [], [] => Some ([],[])
      | p::args, (_,t)::c'=>
          @! let (lhs, rhs) <- check_args_proof args c' in
            let (term_eq_result e1 e2 t') <?- get p proof_result in
            (*TODO: use Eqb instance*)
            let ! sort_eq_dec t[/with_names_from c' rhs/] t' in
            ret (e1::lhs, e2::rhs)
      | _,_=> None
      end.

     Definition check_node (n : node) : option node_result :=
      match n with
      | tn_var n =>
          @! let t <- named_list_lookup_err c n in
             ret (term_eq_result (var n) (var n) t)
      | tn_con n s =>
          @! let r <- named_list_lookup_err l n in
             match r with
             | term_rule c' _ t =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                   ret (term_eq_result (con n lhs) (con n rhs)
                          t[/with_names_from c' rhs/])
             | term_eq_rule c' e1 e2 t =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (term_eq_result e1[/lsub/] e2[/rsub/] t[/rsub/])
             | _ => None
             end
      | tn_trans p0 p1 =>
          @! let (term_eq_result e1 e2 t) <?- get p0 proof_result in
             let (term_eq_result e1' e2' t') <?- get p1 proof_result in
             let ! sort_eq_dec t t' in
             let ! term_eq_dec e2 e1' in
             ret (term_eq_result e1 e2' t)
      | tn_sym p =>
          @! let (term_eq_result e1 e2 t) <?- get p proof_result in
             ret (term_eq_result e2 e1 t)
      | tn_conv p0 p1 =>
          @! let (sort_eq_result t1 t2) <?- get p0 proof_result in
             let (term_eq_result e1 e2 t) <?- get p1 proof_result in
             let ! sort_eq_dec t t1 in
             ret (term_eq_result e1 e2 t2)
                 
      | sn_con n s =>
          @! let r <- named_list_lookup_err l n in
             match r with
             | sort_rule c' _ =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                    ret (sort_eq_result (scon n lhs) (scon n rhs))
             | sort_eq_rule c' t1 t2 =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (sort_eq_result t1[/lsub/] t2[/rsub/])
             | _ => None
             end
      | sn_trans p0 p1 =>
          @! let (sort_eq_result t1 t2) <?- get p0 proof_result in
             let (sort_eq_result t1' t2') <?- get p1 proof_result in
             let ! sort_eq_dec t2 t1' in
             ret (sort_eq_result t1 t2')
      | sn_sym p =>
          @! let (sort_eq_result t1 t2) <?- get p proof_result in
             ret (sort_eq_result t2 t1)
      end.

     
     Definition node_result_sound res :=
       match res with
       | term_eq_result e1 e2 t => eq_term l c t e1 e2
       | sort_eq_result t1 t2 => eq_sort l c t1 t2
       end.

     (* TODO: move somewhere? *)
     Definition tree_all {A} (P : A -> Prop) t :=
       forall n a, get n t = Some a -> P a.

     Context (history_sound : tree_all node_result_sound proof_result).

     
     Lemma check_args_proof_sound args c' a1 a2
       : check_args_proof args c' = Some (a1,a2) ->
         eq_args l c c' a1 a2.
     Proof.
       revert c' a1 a2.
       induction args; destruct c';
         basic_goal_prep;
         try congruence;
         repeat case_match';
         basic_goal_prep;
         try congruence;
         repeat lazymatch goal with
           | [H : (_,_) = ( _,_) |- _ ] => safe_invert H
           | [H : Some _ = Some _ |- _ ] => safe_invert H
          end.
       - constructor.
       - constructor; eauto.
         symmetry in HeqH1.
         eapply history_sound in HeqH1.
         exact HeqH1.
       - safe_invert H.
       - safe_invert H.
     Qed.
     
     Lemma check_node_sound n res
       : check_node n = Some res ->
         node_result_sound res.
     Proof.
       destruct n;
        basic_goal_prep;
        (*weed out trivial goals for efficiency*)
        try congruence;
         repeat case_match';
        basic_goal_prep;
        try congruence;
        repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
          end;
         basic_goal_prep;
           repeat lazymatch goal with
           | [H : Some (term_eq_result _ _ _) = _,
                 hist : tree_all node_result_sound _ |- _] =>
               symmetry in H;
               eapply hist in H
           | [H : Some (sort_eq_result _ _) = _,
                 hist : tree_all node_result_sound _ |- _] =>
               symmetry in H;
               eapply hist in H
           end; simpl in *; eauto with term lang_core.
       - constructor; constructor.
         apply named_list_lookup_err_in; auto.
       - safe_invert HeqH2; subst.
         eapply term_con_congruence; eauto.
         + apply named_list_lookup_err_in; eauto.
         + eapply check_args_proof_sound; eauto.
       - eapply eq_term_subst.
         3: eapply eq_term_by;
         apply named_list_lookup_err_in; eauto.
         + apply named_list_lookup_err_in in HeqH.
           use_rule_in_wf.
           inversion H; subst.
           basic_utils_crush.
         + eapply eq_args_implies_eq_subst.
           eapply check_args_proof_sound; eauto.
       - safe_invert HeqH2; subst.
         eapply sort_con_congruence; eauto.
         + apply named_list_lookup_err_in; eauto.
         + eapply check_args_proof_sound; eauto.
       - eapply eq_sort_subst.
         3: eapply eq_sort_by;
         apply named_list_lookup_err_in; eauto.
         + apply named_list_lookup_err_in in HeqH.
           use_rule_in_wf.
           inversion H; subst.
           basic_utils_crush.
         + eapply eq_args_implies_eq_subst.
           eapply check_args_proof_sound; eauto.
     Qed.
  End Inner.

  (*TODO: use named_list for pf instead of list?*)
  Fixpoint check_proof' (p : pf) : option (tree node_result * positive) :=
    match p with
    | [] => Some (empty _, 1%positive)
    | n::p' =>
        @! let (p_res, next) <- check_proof' p' in
           let n_res <- check_node p_res n in
           ret (set next n_res p_res, next + 1)%positive
    end.

  Definition check_proof (p : pf) : option (term * term * sort) :=
    @! let (m, next) <- check_proof' p in
      let (term_eq_result e1 e2 t) <?- get (next - 1)%positive m in
      ret (e1,e2,t).

      Require Import Lia.
      Open Scope positive.
  
  Lemma check_proof'_fresh' p res next
    : check_proof' p = Some (res, next) ->
      forall n', n' >= next ->
      get n' res = None.
  Proof.
    revert res next; induction p;
      unfold tree_all;
      basic_goal_prep;
      repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
        end;
      basic_goal_prep;
      eauto;
      repeat case_match';
      basic_goal_prep;
      try congruence.
    safe_invert H.
    rewrite gso by lia.
    eapply IHp; eauto; lia.
  Qed.
  
  Lemma check_proof'_fresh p res next
    : check_proof' p = Some (res, next) ->
      get next res = None.
  Proof.
    intros; eapply check_proof'_fresh'; eauto; lia.
  Qed.
    
  Lemma check_proof'_sound p res next
    : check_proof' p = Some (res, next) ->
      tree_all node_result_sound res.
  Proof.
    revert res next; induction p;
      unfold tree_all;
      basic_goal_prep;
        repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
          end;
      basic_goal_prep;
      eauto using check_node_sound;
    repeat case_match';
      basic_goal_prep;
      try congruence.
    safe_invert H; simpl.
    safe_invert HeqH0.
    destruct (Pos.eq_dec n p0).
    {
      subst.
      rewrite gss in H0.
      safe_invert H0.
      eapply check_node_sound; eauto.      
    }
    rewrite gso in H0; eauto.
    eapply IHp; eauto.
  Qed.

  Theorem check_proof_sound p e1 e2 t
    : check_proof p = Some (e1,e2,t) ->
      eq_term l c t e1 e2.
  Proof.
    unfold check_proof.
    remember (check_proof' p) as check.
    destruct check; simpl; try congruence.
    destruct p0; simpl; try congruence.
    repeat case_match;
      basic_goal_prep;
        repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
          end;
      try congruence.
    symmetry in Heqcheck.
    apply check_proof'_sound in Heqcheck.
    simpl in *.
    symmetry in HeqH.
    specialize (Heqcheck _ _ HeqH).
    eauto.
  Qed.
   *)

  End WithLang.

End WithVar.
