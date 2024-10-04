
Require Import Lists.List.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
From Utils.EGraph Require Import Defs Semantics QueryOpt.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.


Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
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

  Section Properties.
    Context (l : lang) (i : instance).

    Context (sort_of_fresh : fresh sort_of l).

    Definition eq_sum {A B} (eqA : A -> A -> Prop) eqB (x y : A + B) :=
      match x, y with
      | inl x, inl y => eqA x y
      | inr x, inr y => eqB x y
      | _, _ => False
      end.

    (* TODO: find this*)
    Context (sort_of_term : lang -> term -> sort).
    Definition interp_sort_of (args : list (term + sort))
      : option (term + sort) :=
      match args with
      | [inl t] => Some (inr (sort_of_term l t))
      | _ => None
      end.

    Definition left_opt {A B} (x: A + B) :=
      match x with inl x => Some x | _ => None end.

    Definition all_left {A B} (l : list (A+B)) :=
      list_Mmap left_opt l.

    (*TODO: write*)
    Context (is_sort is_term : V -> bool).
      
    Definition lang_model : model V :=
      {|
        domain := term + sort;
        domain_eq := eq_sum (fun x y => exists t, eq_term l [] t x y)
                       (eq_sort l []);
        interpretation f args :=
          if eqb f sort_of then interp_sort_of args
          else if is_sort f then Mbind (fun x => Some (inr (scon f x)))
                                   (all_left args)
               else if is_term f then Mbind (fun x => Some (inl (con f x)))
                                        (all_left args)
                    else None;
      |}.

    Context (supremum : list V -> V).
    
    (* TODO: move to FnDb semantics *)
    Definition rule_sound r m :=
      forall assignment : NamedList.named_list V (domain V m),
        assignment_satisfies m assignment
          (query_clauses V V r) ->
        (forall x y,
            In (x, y) (write_unifications V V r) ->
            named_list_lookup_err assignment x <$>
              (fun x' : domain V m =>
                 named_list_lookup_err assignment y <$> domain_eq V m x'))
        /\ (forall a : Defs.atom V V,
               In a (write_clauses V V r) ->
               list_Mmap (named_list_lookup_err assignment) (atom_args a) <$>
                 (fun args : list (domain V m) =>
                    interpretation V m (atom_fn a) args =
                      named_list_lookup_err assignment (atom_ret a))).

    Context (le_V : V -> V -> Prop)
      (le_V_refl : forall x, le_V x x)
      (le_V_sym : forall x y z, le_V x y -> le_V y z -> le_V x z)
      (* TODO: to work w/ int63, have to weaken this *)
      (succ_le : forall x, le_V x (succ x))
      (succ_neq : forall x, x <> succ x)
      (supremum_le : forall l x, In x l -> le_V x (supremum l)).

    Local Hint Resolve le_V_refl : utils.

    Definition lt_V x y := le_V (succ x) y.

    (*TODO: why isn't this hint working: pair_equal_spec:
    *)
    Lemma term_pat_to_clauses_var next_var e l1 x next_var'
      :  term_pat_to_clauses succ e next_var = (l1, (x, next_var')) ->
         le_V next_var next_var'.
    Proof.
      revert next_var l1 x next_var'.
      induction e.
      {
        basic_goal_prep;
          basic_utils_crush.
        cbv in H.
        rewrite !pair_equal_spec in H.
        basic_goal_prep;
          basic_utils_crush.
      }
      {
        revert H; induction l0;   
        basic_goal_prep;
          unfold Basics.compose in *;
        basic_goal_prep;
          basic_utils_crush.
        {
          cbv in H0;
            rewrite !pair_equal_spec in H0.
          basic_goal_prep; subst; eauto.
        }
        {
          destruct (term_pat_to_clauses succ a next_var) eqn:Hpat.
          unfold uncurry in *.
          basic_goal_prep.
          specialize (H4 v0).
          destruct (list_Mmap (term_pat_to_clauses succ) l0 v0) eqn:Hlist.
          basic_goal_prep.
          cbv [writer] in H0;
            rewrite !pair_equal_spec in H0.
          basic_goal_prep.
          subst.
          epose proof (H4 _ _ _ eq_refl) as Hle.
          eapply H in Hpat.
          eauto.
        }
      }
    Qed.

    (*TODO
    Lemma term_pat_to_clauses_sound next_var
      :  next_var > fvs e ->
         term_pat_to_clauses succ e next_var = (l1, (x, next_var')) ->
         matches assignment l1 ->
         let s := (combine (fvs e) (map (lookup assignment) (fvs e))) in
         lookup assignment x = Some e [/s/].
*)
    
    Lemma rule_model_sound n r
      : In (n,r) l ->
        rule_sound (rule_to_uncompiled_rw succ sort_of supremum n r) lang_model.
    Proof.
      unfold rule_sound, assignment_satisfies.
      destruct r;
        basic_goal_prep.
      all:intuition eauto.
      all: repeat lazymatch goal with
             H : context [let '(_,_) := ?e in _ ] |- _ =>
               let Htuple := fresh "Htuple" in
               destruct e as [? [ [] ? ] ] eqn:Htuple
           end.
      all: repeat (cbn in *; intuition subst).
      {
        (*
        Lemma ctx_to_clauses_var
          : next_var > all map fst c ->
          ctx_to_clauses succ sort_of n0 next_var = (l1, (tt, next_var')) ->
          next_var' > fvs l1.
          
        Lemma ctx_to_clauses_sound
          : next_var > all map fst c ->
          ctx_to_clauses succ sort_of n0 next_var = (l1, (tt, next_var')) ->
          matches assignment l1 ->
          wf_subst l [] (combine (map fst c) (map (lookup assignment) (map fst c))) c.

          (* TODO: does this depend on being conjoined w/ ctx_clauses?
             TODO: what to say about wf type clauses added?

             TODO: need separate lemma for query and for add?
             Probably no?
           *)
        Lemma term_pat_to_clauses_sound
          :  next_var > fvs e ->
             term_pat_to_clauses succ e next_var = (l1, (x, next_var')) ->
             matches assignment l1 ->
             let s := (combine (fvs e) (map (lookup assignment) (fvs e))) in
             lookup assignment x = Some e [/s/].
                
        
        TODO: ctx_to_clauses lemma
        eqb_case n sort_of.
        {
          revert dependent l1.
          TODO: stateT writer tactics?
          Or, as thought, change to reuse more code first?
          TODO: some kind of nested induction?
                     should be a cleaner way?
        lazymatch goal with
        | H : Is_Some_satisfying ?P ?ma |- _ =>
            let Hopt := fresh "Hopt" in
            destruct ma eqn:Hopt
        end.
        unfold Is_Some_satisfying in H0.
        revert H0.
        case_match. [| tauto].
        eqb_case n sort_of.
        {
        TODO: ctx_to_clauses lemma


          destruct (ctx_to_clauses succ sort_of n0 (supremum (map fst n0))) as [? [ [] ?] ] eqn:Hctx.
        TODO: 
        cbn in *.
        basic_goal_prep.
        TODO: why false assumption?
        basic_utils_crush.
    Qed.
         *)
    Abort.

    Theorem lang_model_wf
      : model_of lang_model (map (uncurry (rule_to_uncompiled_rw succ sort_of supremum)) l).
    Proof.

      
    Abort.

    
    
    (*TODO: many of these relations can be functions. what's the best way to define them?*)
    Fixpoint open_term_in_egraph sub e ex :=
      match e with
      | var x => In (x,ex) sub
      | con n s =>
          exists s',
          atom_in_egraph (Build_atom n s' ex) i
          /\ all2 (open_term_in_egraph sub) s s'
      end.

    Definition open_sort_in_egraph sub t tx :=
      match t with
      | scon n s =>
          exists s',
          atom_in_egraph (Build_atom n s' tx) i
          /\ all2 (open_term_in_egraph sub) s s'
      end.

    Local Notation sort_in_egraph := (open_sort_in_egraph []).
    Local Notation term_in_egraph := (open_term_in_egraph []).

    (* Note: not using a sort_of analog disallows presorts. Is that ever a downside?*)
    Definition egraph_wf_sort t :=
      exists tx, sort_in_egraph t tx.

    Definition has_sort_idx ex tx := atom_in_egraph (Build_atom sort_of [ex] tx) i.
    

    Definition has_sort ex sub t :=      
      exists tx,
        open_sort_in_egraph sub t tx
        /\ has_sort_idx ex tx.


    Definition egraph_wf_term e t :=
      exists ex tx,
        term_in_egraph e ex
        /\ sort_in_egraph t tx
        /\ has_sort_idx ex tx.

    Definition egraph_eq_sort t1 t2 :=
      exists tx,
        sort_in_egraph t1 tx
        /\ sort_in_egraph t2 tx.
    
    Definition egraph_eq e1 e2 t :=
      exists ex tx,
        term_in_egraph e1 ex
        /\ term_in_egraph e2 ex
        /\ sort_in_egraph t tx
        /\ atom_in_egraph (Build_atom sort_of [ex] tx) i.

    
    Fixpoint idxs_have_sorts s (c:ctx) :=
      match s, c with
      | [], [] => True
      | i::s, (x,t)::c =>
          has_sort i (combine (map fst c) s) t
          /\ idxs_have_sorts s c
      | _, _ => False
      end.      

    (*
    Definition sort_atom_wf '(Build_atom f s out) (i : V) :=
      match named_list_lookup_err f l with
      | Some (sort_rule c args) => idxs_have_sorts s c
      | _ => False
      end.
    
    Definition term_atom_wf '(Build_atom f s out) i :=
      match named_list_lookup_err f l with
      | Some (term_rule c args t) =>
          exists tx,
          idxs_have_sorts s c
          /\ sort_in_egraph t tx
          /\ has_sort i tx
      | _ => False
      end.
    *)

    (*TODO: Should it derivable from atom_eq? Any reason to keep 2nd def?*)
    Definition atom_wf '(Build_atom f s out) :=
      (* TODO: do I need to add any properties for the sort_of atoms?*)
      match named_list_lookup_err l f with
      | Some (sort_rule c args) => idxs_have_sorts s c
      | Some (term_rule c args t) =>
          idxs_have_sorts s c
          /\ has_sort out (combine (map fst c) s) t
      (*TODO: has_sort here or in sort_of case? shouldn't have both*)
      | None =>
          f = sort_of
         (* /\ match s with
             | [ex] => exists f' args', atom_in_egraph (f',args',ex)
                                        /\ open_sort_in_egraph (sort_of f') out
             | _ => False
             end*)
      | _ => False
      end.

    
    (*
    Definition atom_eq '(Build_atom f s out) f' s' :=
      TODO: need to inspect atoms of s, s'?.
    Answer: this is a union-find property.
    Question: would this be easier to manage if the egraph didn't replace output idxs?.
              No, merging also changes idxs.

    How to define?

     *)
    Arguments equiv {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope i.
    Arguments canonicalize {idx} {Eqb_idx} {symbol}%type_scope
      {symbol_map idx_map idx_trie}%function_scope a.
    Arguments uf_rel {idx}%type_scope {idx_map rank_map} uf1 _ _.

    (*TODO: move to FunctionalDB.v*)
    (* TODO: invariant currently depends on i! Seems undesirable*)
    Class egraph_ok (invariant : atom -> Prop) : Prop :=
      {
        atoms_in_domain
        : forall a,
          atom_in_egraph a i ->
          all (fun x => uf_rel i.(equiv) x x)
            (a.(atom_ret _ _)::a.(atom_args));
        (*
        atoms_satisfy_invariant
        : forall a b,
          atom_in_egraph a ->
          let a' := fst (canonicalize a i) in
          invariant a' b.(atom_fn) b.(atom_args);
        equiv_satisfies_invariant
*)
      }.

    Context (Hwf : egraph_ok atom_wf).

    (*


        : forall a b,
          atom_in_egraph a ->
          atom_in_egraph b ->
          let a' := fst (canonicalize a i) in
          let b' := fst (canonicalize b i) in
          a.(atom_ret) = b.(atom_ret) ->
          invariant a' b.(atom_fn) b.(atom_args);

    Class egraph_wf : Prop :=
      {
        egraph_wf_is_ok :> egraph_ok;
        egraph_sound_eq_sort
        : forall t1 t2, egraph_eq_sort t1 t2 -> eq_sort l [] t1 t2;
        egraph_sound_eq_term
        : forall e1 e2 t, egraph_eq e1 e2 t -> eq_term l [] t e1 e2;
        (*needed for intermetiate steps.
          TODO: can I extract this out?
         *)
        egraph_sound_union_find
        : 
      }.
      
      (forall a, atom_in_egraph a -> atom_wf a)
      (* TODO: union-find;
         Note: exists implies forall
       *)
      /\ (forall x y,
             interp_uf _ _ _ _ i.(equiv _ _ _ _ _) x y ->
             exists e1 e2 t,
               eq_term l [] t e1 e2
               /\ term_in_egraph e1 x
               /\ term_in_egraph e2 y
         ).
    
    Context (Hwf : egraph_wf).
     *)


    Context (wfl : wf_lang l).

    (*equivalent to the longer one below*)
    Theorem egraph_sound_eq
      : (forall t1 t2, egraph_eq_sort t1 t2 -> eq_sort l [] t1 t2)
        /\ (forall e1 e2 t, egraph_eq e1 e2 t -> eq_term l [] t e1 e2).
    Proof.
      split.
      2:{
        unfold egraph_eq.
        intros.
        destruct H as [ex [tx H] ].
        intuition idtac.
        cbn in *.
        assert (interp_uf _ _ _ _ i.(equiv _ _ _ _ _) ex ex) by admit
        (*TODO: need to know ex in uf*).
       (* eapply Hwf in H2.
        break.
        TODO: not sufficient? also need pretty much this properrty in assumption.
        Question: is there anything to prove here?.
        The egraph invariant might be precisely the end theorem.
        Question: how to connect egraph invariant at the FnDb interface?.
        Want a way to prove things on the FnDb side w/out term knowledge.
        Need to prove that rw_set preserves invariant, right?.
        And that it holds for empty (or can that be implied by its structure?).
        Separation of concerns:
          - this file only proves facts about EqLog clauses & terms
          - all proofs about the egraph data structure are in fndb
        revert e2 t ex tx H.
        
        TODO: how to prove this?
        *)
    Admitted.
    
    Lemma egraph_sound_wf_sort t : egraph_wf_sort t -> wf_sort l [] t.
    Proof.
      destruct 1; eapply eq_sort_wf_l; eauto with lang_core.
      eapply egraph_sound_eq; econstructor; eauto.
    Qed.
    
    Lemma egraph_sound_wf e t : egraph_wf_term e t -> wf_term l [] e t.
    Proof.
      destruct 1 as [x H].
      destruct H as [x' ?].
      eapply eq_term_wf_l; eauto with lang_core.
      eapply egraph_sound_eq; repeat econstructor; intuition eauto.
    Qed.

  End Properties.
End WithVar.
