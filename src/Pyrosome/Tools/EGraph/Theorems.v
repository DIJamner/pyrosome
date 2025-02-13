
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


(*TODO: move to Monad.v
      TODO: generalize monad equiv?   
 *)
Lemma list_Mmap_ext A B M `{Monad M} (f g : A -> M B) lst
  : (forall x, In x lst -> f x = g x) ->
    list_Mmap f lst = list_Mmap g lst.
Proof using.
  intro Hfg.
  enough (forall l', incl l' lst ->  list_Mmap f l' = list_Mmap g l')
    by eauto using incl_refl.
  induction l';
    basic_goal_prep;
    basic_utils_crush.
  rewrite Hfg; eauto.
  rewrite H0.
  reflexivity.
Qed.

(*TODO: move to utils*)
Lemma named_list_lookup_prefix {S A} `{Eqb S} (s s' : NamedList.named_list S A) x v
  : named_list_lookup_err s x = Some v ->
    named_list_lookup_err (s++s') x = Some v.
Proof.
  induction s; basic_goal_prep; [congruence|].
  case_match;
    basic_goal_prep;
    basic_utils_crush.
Qed.


Lemma Mmap_lookup_self  {S A} `{Eqb_ok S} (x : NamedList.named_list S A)
  : all_fresh x -> Some (map snd x) = list_Mmap (named_list_lookup_err x) (map fst x).
Proof.
  induction x; basic_goal_prep; basic_utils_crush.
  rewrite list_Mmap_ext with (g:=(named_list_lookup_err x)).
  {
    rewrite <- H1.
    reflexivity.
  }
  {
    basic_goal_prep.
    eqb_case x0 s;
      basic_utils_crush.
  }
Qed.

(*TODO: move to Utils *)
Lemma combine_map_fst_snd S A (s : NamedList.named_list S A)
  : combine (map fst s) (map snd s) = s.
Proof.
  induction s;
    basic_goal_prep;
    basic_utils_crush.
Qed.
#[local] Hint Rewrite combine_map_fst_snd : utils.

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

    (* Note: can prove via lemma (should exist somewhere) that if
       a term is wf under some sort, it has this sort *)
    Definition interp_sort_of args
        : option term :=
        @!let [e] <?- Some args in
          let (con f s) <?- Some e in
          let (term_rule c args t) <?- named_list_lookup_err l f in
          let (scon tf ts) := t in
          ret (con tf ts[/with_names_from c s/]).

    (*TODO: write?
    Context (is_sort is_term : V -> bool).
     *)

    (* since sorts and terms are all jumbled in the domain,
       construct a subsuming judgment.
     *)
    Inductive lang_model_eq : term -> term -> Prop :=
    | lm_eq_terms e1 e2 t : eq_term l [] t e1 e2 -> lang_model_eq e1 e2
    | lm_eq_sorts e1 e2
      : match e1, e2 with
        | con f1 s1, con f2 s2 => eq_sort l [] (scon f1 s1) (scon f2 s2)
        | _,_ => False
        end ->
        lang_model_eq e1 e2.

    (* The reflexive case of _eq *)
    Inductive lang_model_wf : term -> Prop :=
    | lm_wf_term e t : wf_term l [] e t -> lang_model_wf e
    | lm_wf_sort e
      : match e with
        | con f s => wf_sort l [] (scon f s)
        | _ => False
        end ->
        lang_model_wf e.

    Context (wfl : wf_lang l).

    (* TODO: this is sufficient to t/c, but want to relate e and t.
       Worth proving separately or no?
     *)
    Lemma interp_sort_of_wf e t
      : lang_model_wf e ->
        interp_sort_of [e] = Some t -> lang_model_wf t.
    Proof.
      cbn.
      cbv[default option_default].
      repeat (case_match; cbn; try congruence).
      subst.
      apply named_list_lookup_err_in in HeqH0.
      basic_goal_prep;
        basic_utils_crush.
      apply lm_wf_sort;
        basic_goal_prep;
        basic_utils_crush.
      inversion H; subst.
      {
        change (scon v0 l2 [/with_names_from n l0 /])
          with (scon v0 l2) [/with_names_from n l0 /].
        revert HeqH0.
        generalize (scon v0 l2).
        clear v0 l2.
        intros.
        use_rule_in_wf.
        eapply wf_sort_subst_monotonicity; eauto.
        1:basic_core_crush.
        1:basic_core_crush.
        eapply wf_subst_from_wf_args; eauto.
        autorewrite with lang_core utils in *.
        break.
        remember (con v l0) as e.
        revert Heqe.
        revert H0 HeqH0.
        induction 1;
          basic_goal_prep;
          basic_core_crush.
        eapply in_all_fresh_same in H0; eauto;
          basic_core_crush.
      }
      {
        safe_invert H0. 
        eapply in_all_fresh_same in HeqH0; eauto;
          basic_core_crush.
      }
    Qed.

    (*
    (*TODO: clean up*)
    Definition interp_sort_of (x : list {x | lang_model_wf x}) : option {x | lang_model_wf x}.
      refine (match x with [e] => _ | _ => None end).
      pose proof (fun t => interp_sort_of'_wf _ t (proj2_sig e)).
      revert H.
      refine(
      match interp_sort_of' (proj1_sig e) with
      | Some x => fun H => Some (exist _ _ _)
      | None => fun _ => None
      end).
      eapply H.
      reflexivity.
    Defined.
    *)
    
    (* TODO: how to handle the invariant that all contents are wf?
       want sort_of to be meaningful.
       Need a predicate that applies to all elts. Just use refinement type?
     *)
    Definition lang_model : model V :=
      {|
        domain := term;
        (*TODO: necessary? domain_elt : domain -> Prop
          arg. for: want egraph belonging to imply wfness?
          arg against: equation by domain_eq implies this, so unnecessary
         *)
        domain_eq := lang_model_eq;
        interpretation f args :=
          (* TODO: need lemma that sort_of case wf*)
          if eqb f sort_of then interp_sort_of args
          else Some (con f args)
      |}.

    Definition sort_of_term e :=
      match e with
      | con f s => scon f s
      | _ => (*shouldn't happen*) default
      end.
    
    Lemma lang_model_sort_of_sound e t
      : wf_term l [] e t ->
        forall t',
        interp_sort_of [e] = Some t' ->
        wf_term l [] e (sort_of_term t').
    Proof.
      induction 1;
          basic_goal_prep;
          basic_core_crush.
      unfold interp_sort_of in *; cbn in *.
      pose proof H as Hin.
      eapply all_fresh_named_list_lookup_err_in in H; eauto;
        [|basic_core_crush].
      rewrite <- H in H1.
      destruct t.
      basic_utils_crush.
      unfold sort_of_term; cbn.
      change (scon v l0 [/with_names_from c' s /])
        with (scon v l0) [/with_names_from c' s /].
      eapply wf_term_by; eauto.
    Qed.

    Context (supremum : list V -> V).
    Context (V_to_nat : V -> nat)
      (VtN_inj : FinFun.Injective V_to_nat)
    (VtN_succ : forall x, V_to_nat (succ x) = Nat.succ (V_to_nat x)).

    Definition le_V a b := V_to_nat a <= V_to_nat b.
    Definition lt_V a b := V_to_nat a < V_to_nat b.

    Context (supremum_le : forall l x, In x l -> le_V x (supremum l)).
      
    (*
    Context (le_V : V -> V -> Prop)
      (le_V_refl : forall x, le_V x x)
      (le_V_sym : forall x y z, le_V x y -> le_V y z -> le_V x z)
      (* TODO: to work w/ int63, have to weaken this *)
      (succ_le : forall x, le_V x (succ x))
      (succ_neq : forall x, x <> succ x)
      (supremum_le : forall l x, In x l -> le_V x (supremum l)).

    Local Hint Resolve le_V_refl : utils.

    Definition lt_V x y := le_V (succ x) y.
     *)

    (*
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
        basic_goal_prep.
        {
          cbv in H0;
            rewrite !pair_equal_spec in H0.
          basic_goal_prep; subst; eauto.
        }
        {
          destruct (term_pat_to_clauses succ a next_var) eqn:Hpat.
          unfold uncurry in *.
          basic_goal_prep.
          destruct (list_Mmap (term_pat_to_clauses succ) l0 v0) eqn:Hlist.
          basic_goal_prep.
          cbv [writer] in H0;
            rewrite !pair_equal_spec in H0.
          basic_goal_prep.
          subst.
          eapply H in Hpat.
          eapply IHl0 with (next_var:=v0) in H1.
          all: cbn; eauto.
          rewrite Hlist.
          cbn; eauto.
        }
      }
    Qed.
*)

    (*TODO
    Lemma term_pat_to_clauses_sound next_var
      :  next_var > fvs e ->
         term_pat_to_clauses succ e next_var = (l1, (x, next_var')) ->
         matches assignment l1 ->
         let s := (combine (fvs e) (map (lookup assignment) (fvs e))) in
         lookup assignment x = Some e [/s/].
     *)

    
   

    (*TODO: move to core*)
    Lemma wf_subst_fresh c s c'
      : all_fresh c' -> wf_subst l c s c' -> all_fresh s.
    Proof.
      intros H H'; revert H;
        induction H';
        basic_goal_prep;
        basic_utils_crush.
      unfold fresh.
      erewrite wf_subst_dom_eq; eauto.
    Qed.
    Hint Resolve wf_subst_fresh : lang_core.

    (*TODO: move to core *)
    Lemma wf_args_from_wf_subst c s c'
      : wf_subst l c s c' -> wf_args l c (map snd s) c'.
    Proof.
      induction 1;
        basic_goal_prep;
        basic_core_crush.
      rewrite <- combine_map_fst_is_with_names_from.
      erewrite <- wf_subst_dom_eq; eauto.
      unfold fresh.
      basic_utils_crush.
    Qed.
    Hint Resolve wf_args_from_wf_subst : lang_core.

    (*TODO: move to Utils *)
    Lemma named_list_lookup_suffix S A `{Eqb_ok S} (l1 l2 : NamedList.named_list S A) x
      : fresh x l1 ->
        named_list_lookup_err l2 x
        = named_list_lookup_err (l1++l2) x.
    Proof.
      induction l1; basic_goal_prep; try tauto.
      autorewrite with utils in *; break.
      eqb_case x s; auto; try tauto.
    Qed.

    (*
    Lemma sort_pat_to_clauses_next_var_fresh t l1 v v' vt
      : sort_pat_to_clauses succ sort_of l t v = (l1, (vt, v')) ->
        ~In v' (query_fvs l1).
    Proof.
      unfold sort_pat_to_clauses.
      generalize (length l).
      induction n;
        unfold writer in *;
        basic_goal_prep;
        basic_utils_crush.
      destruct t.
      unfold Basics.compose in *.
      revert H; case_match.
      unfold uncurry.
      break.
      unfold gensym.
      cbn.
      basic_goal_prep;
        basic_utils_crush.
    Admitted.
      
    Lemma ctx_to_clauses_next_var_fresh c l1 v
      : ctx_to_clauses succ sort_of l c (succ (supremum (map fst c))) = (l1, (tt, v)) ->
        ~In v (query_fvs l1).
    Proof.
      unfold ctx_to_clauses.
      remember (succ (supremum (map fst c))) as next_var.
      assert (forall x, In x (map fst c) -> lt_V x next_var).
      {
        intros.
        eapply supremum_le in H.
        cbv [le_V lt_V] in *.
        subst.
        rewrite  VtN_succ.
        shelve.
      }
      {
    Abort.

*)

    (*
    Lemma rule_model_sound n r query_assignment
      : all_fresh query_assignment ->
        In (n,r) l ->
        let r' := (rule_to_log_rule succ sort_of supremum l n r) in
        map fst query_assignment = r'.(query_vars _ _) ->
        assignment_satisfies lang_model query_assignment r'.(query_clauses _ _) ->
        exists out_assignment,
          assignment_satisfies lang_model (query_assignment ++ out_assignment)
            r'.(write_clauses _ _)
          /\ assignment_unifies lang_model (query_assignment ++ out_assignment)
               r'.(write_unifications _ _).
    Proof.
      intros.
      subst r'.
      destruct r;
        basic_goal_prep.
      all: repeat lazymatch goal with
             H : context [let '(_,_) := ?e in _ ] |- _ =>
               let Htuple := fresh "Htuple" in
               destruct e as [? [ [] ? ] ] eqn:Htuple
             end.
      all: basic_goal_prep.
      {
        (* TODO: ctx lemma to imply wf args at right types*)
        assert(exists l2, incl l2 query_assignment
                          /\ wf_subst l [] l2 n0)
          by admit.
        break.
        assert (all_fresh x).
        {
          use_rule_in_wf.
          basic_core_crush.
        }
        eexists [(v,con n (map snd x))]; cbn; intuition eauto.
        replace (list_Mmap (named_list_lookup_err (query_assignment
                                                     ++ [(v, con n (map snd x))]))
                   (map fst n0))
          with (Some (map snd x)).
        2:{
          erewrite list_Mmap_ext with (g:= named_list_lookup_err x).
          2:{
            intros.
            erewrite <- wf_subst_dom_eq in H6; eauto.
            eapply pair_fst_in_exists in H6; break.
            erewrite named_list_lookup_prefix with (v:=x1); [|symmetry].
            all: rewrite all_fresh_named_list_lookup_err_in; eauto.
          }
          {            
            erewrite <- wf_subst_dom_eq; eauto.
            eapply Mmap_lookup_self; eauto.
          }
        }
        {
          eqb_case n sort_of.
          {
            exfalso.
            eapply pair_fst_in in H0.
            eapply sort_of_fresh in H0; eauto.
          }
          {
            cbn.
            assert (~In v (query_fvs l1)) by admit (*holds b/c v is fresh after ctx_to_clauses*).        
            lazymatch goal with
              |- named_list_lookup_err (?query_assignment ++ ?out) ?v <$> ?RHS =>
                replace (named_list_lookup_err (query_assignment ++ out) v)
                with (named_list_lookup_err out v)
            end.
            {
            cbn.
            autorewrite with utils bool.
            cbn.
            eapply lm_eq_sorts.
            eapply eq_sort_refl.
            econstructor; eauto with lang_core.
            }
            {
              eapply named_list_lookup_suffix; eauto.
              congruence.
            }
          }
        }
      }
      (*}*)
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

    Theorem lang_model_of
      : model_of lang_model (map (uncurry (rule_to_log_rule succ sort_of supremum l)) l).
    Proof.

      
    Abort.

    *)
    
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
