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

    Notation add_and_check_ctx_cons :=
      (add_and_check_ctx_cons eqn_set l qt_unconstrained trie_map qt_tree values_of_next_var choose_next_val relation db arg_map).

    Notation Checker :=
      (Checker eclass_map eqn_set).

    Notation equality_saturation :=
      (equality_saturation l qt_unconstrained trie_map qt_tree values_of_next_var choose_next_val relation db
       arg_map).
    
    Notation resolve_checker' :=
      (resolve_checker' l qt_unconstrained trie_map qt_tree values_of_next_var choose_next_val relation db arg_map).

    
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
        
    Definition is_ctx_of_egraph (g : egraph) (c : ctx) : Prop :=
      Forall2 (fun '(x1,i) '(x2,t) => x1 = x2 /\ sort_in_egraph_at_index g i t)
              g.(ectx) c.

    Section WithCtx.
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
          sort_in_egraph_at_index g i t ->
          In i wf_ids ->
          wf_sort l c t.
      Proof.
        unfold wf_egraph.
        basic_goal_prep.
        eapply eq_sort_wf_l; eauto.
      Qed.

      
      Lemma wf_egraph_term_wf g wf_ids e t i
        : wf_egraph g wf_ids ->
          term_in_egraph_at_index g i e ->
          In i wf_ids ->
          (*TODO: does it matter whether the sort is in the egraph?*)
          principal_sort c e = Some t ->
          wf_term l c e t.
      Proof.
        unfold wf_egraph.
        basic_goal_prep.
        eapply eq_term_wf_l; eauto.
      Qed.

      (*TODO: allow context extension?*)
      Definition egraph_extends g1 g2 :=
        (forall e i, term_in_egraph_at_index g1 i e ->
                     term_in_egraph_at_index g2 i e)
        /\ (forall t i, sort_in_egraph_at_index g1 i t ->
                        sort_in_egraph_at_index g2 i t)
        /\ (forall i j, union_find_equivalence g1.(id_equiv) i j ->
                        union_find_equivalence g2.(id_equiv) i j).

      Lemma egraph_extends_refl g : egraph_extends g g.
      Proof.
        unfold egraph_extends; intuition.
      Qed.
      
    End WithCtx.

    
    Lemma empty_egraph_is_wf : wf_egraph [] empty_egraph [].
    Proof.
      unfold wf_egraph, is_ctx_of_egraph; basic_goal_prep; basic_utils_crush.
    Qed.

    
    Definition indexed_terms_related c g i1 i2 :=
      (forall t1 t2,
          sort_in_egraph_at_index g i1 t1 ->
          sort_in_egraph_at_index g i2 t2 ->
          eq_sort l c t1 t2)
      /\ (forall e1 e2 t,
             term_in_egraph_at_index g i1 e1 ->
             term_in_egraph_at_index g i2 e2 ->
             (*TODO: does it matter whether the sort is in the egraph?*)
             principal_sort c e1 = Some t ->
             eq_term l c t e1 e2).
    
    Definition up_to_checking {A} P (ch : Checker A) c
      := forall g g' a eqns, ch g = (g', Some (a,eqns)) ->
                            (forall i j, member eqns (i,j) = true ->
                                         indexed_terms_related c g i j) ->
                     P g' a.

    
    Lemma equality_saturation_sound {A} upd pred base fuel g g' (a:A) c good_ids
      : (g', a) = equality_saturation upd pred base fuel g ->
        wf_egraph c g good_ids ->
        egraph_extends g g'
        /\ wf_egraph c g' good_ids.
    Proof.
      revert g g' a base.
      induction fuel; basic_goal_prep.
      {
        basic_utils_crush.
        eapply egraph_extends_refl.
      }
      {
        revert H1; case_match.
        {
          basic_utils_crush.
          eapply egraph_extends_refl.
        }
        {
          TODO: db reasoning
        
    Qed.
      
    
    Lemma resolve_checker'_sound {A} g fuel ch g' (a : A) P c
      : (g', Some a) = resolve_checker' ch fuel g ->
        up_to_checking P ch c ->
        P g' a.
    Proof.
      unfold resolve_checker'.
      simpl.
      case_match.
      case_match; [| cbv; congruence].
      destruct p.
      case_match.
      case_match; [| cbv; congruence].
      intro H'; inversion H'; subst; clear H'.


      
      case_match.
      
    Qed.
    
    Lemma add_and_check_ctx_cons_sound i t c g g' good_ids
      : (g',true) = add_and_check_ctx_cons i t g ->
        wf_egraph c g good_ids ->
        fresh i c ->
        exists good_ids',
          wf_egraph ((i,t)::c) g' (good_ids'++good_ids).
    Proof.
      unfold add_and_check_ctx_cons.
      
      case_match.
      [| cbv; congruence].
      case
    Qed.

    Lemma check_ctx'_sound c g
      : check_ctx' c = Some g -> exists good_ids, wf_egraph c g good_ids.
      revert g.
      induction c; basic_goal_prep; basic_utils_crush.
      { eexists;now eapply empty_egraph_is_wf. }
      {
        revert H1.
        case_match; [| cbv; congruence].
        symmetry in HeqH1; apply use_compute_fresh in HeqH1.
        case_match; [| cbv; congruence].
        specialize (IHc e eq_refl); destruct IHc.
        case_match.
        destruct b; [| cbv; congruence].
        basic_goal_prep; basic_utils_crush.
        eapply add_and_check_ctx_cons_sound in HeqH2; eauto.
        destruct HeqH2; eexists; eauto.
      }
    Qed.

        
        
    Abort.
    
    (*TODO: do I want a lookup_term function in defs?*)
    
    (*Properties I expect to hold:*)

             
                      
      
    
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
