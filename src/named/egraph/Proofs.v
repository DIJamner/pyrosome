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
From Named Require Import Term Rule Core.
From Named.egraph Require Import Defs.
Import StateMonad.

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


  (*TODO: gather all contexts from (& in) Defs.v*)
  Context (eclass_map : map.map idx eclass).

  Notation egraph := (egraph (array:=array) eclass_map).
  Notation empty_egraph := (empty_egraph eclass_map).
  Notation find := (find (eclass_map := eclass_map)).
  
  Context (idx_set : set idx).
  Context (eqn_set : set (idx*idx)).

  
  (*Parameterize by query trie since the inductive can't be defined generically *)
  Context (query_trie : Type)
          (qt_unconstrained : query_trie -> query_trie)
          (trie_map : map.map idx query_trie)
          (qt_tree : trie_map -> query_trie)
          (values_of_next_var : query_trie -> set_with_top idx_set)
          (choose_next_val : idx -> query_trie -> query_trie).
  Context (relation : set (list idx))
          (db : map.map idx relation)
          (arg_map : map.map idx idx).

  
  Section WithLang.

    Context (l : lang).
    
    Notation check_ctx' :=
      (check_ctx' (idx:=idx) (array := array)
                  eclass_map eqn_set l
                  qt_unconstrained _ qt_tree
                  values_of_next_var choose_next_val relation db arg_map).
    
    Notation check_ctx :=
      (check_ctx (idx:=idx) (array := array)
                 eclass_map eqn_set l
                 qt_unconstrained _ qt_tree
                 values_of_next_var choose_next_val relation db arg_map).

    
    (*possibly poor naming*)
    Definition principal_sort c e : option sort :=
      match e with
      | var x => named_list_lookup_err c x
      | con n s =>
          @! let (term_rule c' _ t) <?- named_list_lookup_err l n in
             ret t[/with_names_from c' s/]
      end.

    (*TODO: what's the best way to define this?
      In terms of find or in parallel?
      TODO: Move to UnionFind.v
     *)
    Definition union_find_equivalence uf a b :=
      snd (UnionFind.find uf a) = snd (UnionFind.find uf b).

    Inductive term_in_egraph_at_index (g : egraph) i : term -> Prop :=
    | var_in_egraph v
      : map.get g.(hashcons) (var_node v) = Some i ->
        term_in_egraph_at_index g i (var v)
    | con_in_egraph n s s_i
      : Forall2 (term_in_egraph_at_index g) s_i s ->
        (*TODO: handle s_i up to uf_equiv? *)
        map.get g.(hashcons) (con_node n s_i) = Some i ->
        term_in_egraph_at_index g i (con n s).
    
    Variant sort_in_egraph_at_index (g : egraph) i : sort -> Prop :=
    | scon_in_egraph n s s_i
      : Forall2 (term_in_egraph_at_index g) s_i s ->
        (*TODO: handle s_i up to uf_equiv? *)
        map.get g.(hashcons) (con_node n s_i) = Some i ->
        sort_in_egraph_at_index g i (scon n s).

    Parameter is_ctx_of_egraph : egraph -> ctx -> Prop.

    Context (wfl : wf_lang l)
            (c : ctx)
            (wfc : wf_ctx l c).

    Definition wf_egraph g (wf_ids : list idx) :=
      all (fun x => In x wf_ids) (map snd g.(ectx))
      /\ is_ctx_of_egraph g c
      /\ (forall t1 t2 i,
             sort_in_egraph_at_index g i t1 ->
             sort_in_egraph_at_index g i t2 ->
             In i wf_ids ->
             eq_sort l c t1 t2)
      /\ (forall e1 e2 t i,
             term_in_egraph_at_index g i e1 ->
             term_in_egraph_at_index g i e2 ->
             In i wf_ids ->
             (*TODO: does it matter whether the sort is in the egraph?*)
             principal_sort c e1 = Some t ->
             eq_term l c t e1 e2).

    Lemma wf_egraph_sort_wf g wf_ids t i
      : wf_egraph g wf_ids ->
        lookup_sort g t = Some i ->
        In i wf_ids ->
        wf_sort l c t.
    Proof.
      unfold wf_egraph.
      basic_goal_prep.
      eapply eq_sort_wf_l; eauto.
    Qed.

    
    Lemma wf_egraph_term_wf g wf_ids e t i i_t
      : wf_egraph g wf_ids ->
        lookup_term g e = Some (i,i_t) ->
        In i wf_ids ->
        lookup_sort g t = Some i_t ->
        wf_term l c e t.
    Proof.
      unfold wf_egraph.
      basic_goal_prep.
      eapply eq_term_wf_l; eauto.
    Qed.

    (*TODO: do I want a lookup_term function in defs?*)
    
    (*Properties I expect to hold:*)

    Lemma empty_egraph_is_wf : wf_egraph empty_egraph.
    Abort.

             
                      
      
    
    Lemma check_ctx'_sound c g
      : check_ctx' c = Some g -> wf_egraph g.
    Abort.
    
    Theorem check_ctx_sound c
      : check_ctx c = true -> wf_ctx l c.
    Abort.
    
    Lemma find_idempotent
      : find i1 g1 = (g2,i2) ->
        find i2 g2 = (g2,i2).
    Abort.

    
    (*Possibly useful definitions*)

    (*possibly poor naming*)
    Definition principal_sort l c e : option sort :=
      match e with
      | var x => named_list_lookup_err c x
      | con n s =>
          @! let (term_rule c' _ t) <?- named_list_lookup_err l n in
             ret t[/with_names_from c' s/]
      end.
