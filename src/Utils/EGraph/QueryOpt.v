Require Import Datatypes.String Lists.List Coq.Classes.RelationClasses.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps Relations Maps.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)

      (*TODO: just extend to Natlike?*)
      (lt : idx -> idx -> Prop)
      (idx_succ : idx -> idx)
      (idx_zero : WithDefault idx)
      (*TODO: any reason to have separate from idx?*)
    (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
      (default_symbol : WithDefault symbol).

  Existing Instance Eqb_idx.
  Existing Instance idx_zero.
  Existing Instance default_symbol.
  
  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_ok : forall A, @map.ok _ _ (symbol_map A))
    (symbol_map_plus : map_plus symbol_map).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_ok : forall A, map.ok (idx_trie A))
        (idx_trie_plus : map_plus idx_trie).

  Notation atom := (atom idx symbol).
  Notation sequent := (sequent idx symbol).
  
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie).


  (*TODO: moved to semantics and edited
    Semantic interpretation of variables:
    - query_vars is a permutation of (fvs query_clauses)
    - elements of query_vars are universally quantified
    - elements of ((fvs write_clauses) - query_vars) are existentially quantified
    - no new variables in write_unifications
   
  Record log_rule : Type :=
  { query_vars : list idx;
    query_clauses : list atom;
    write_clauses : list atom;
    write_unifications : list (idx * idx);
  }.
*)

  (*
    Normalization through congruence closure

    We can use egraph rebuilding to perform extensive rw rule optimization.
    Just adding all the atoms to the egraph deduplicates them in a simple sense,
    but it still leaves the situation where two identical atoms allocate separate output variables.
    However, rebuilding solves exactly this situation, so we can just call it to handle
    the job for us.

    TODO: what to do about input vs fresh vars in output clauses of query?
    also: split between query and coquery clauses
    - a chance for optimization to eliminate coquery clauses that are in the query
    - how to distinguish query and coquery in the same egraph: special fn table?

    Something that will definitely work:
    - rebuild-optimize just the query, building a map of variable -> egraph index at initialization
                     + Note: this map can be the identity map if the variables are dense and numbered right,
                             but that might be a bit too delicate for something with unimportant performance
    - unify like variables across the rule
    - rebuild-optimize the coquery independently, again w/ a var map to retain the exact names
                     + TODO: what to do about two query variables getting unified?
                             We can safely assume they are output vars.
                             This can be represented by adding a node twice, once for each var.
                             Could also add unification clauses, but that doesn't seem worth it

    Potential improvement:
    Given D  |- G, (f x^ |-> z) where (f x^ |-> y) in D and z not in fv(D), we can remove (f x^ |-> z)
    from the coquery and replace z with y everywhere.
    This could then lead to improvements via congruence, so it would be beneficial to do in the egraph.

    Idea: after optimizing the query, instead of starting from a fresh graph,
    add the coquery to the existing egraph, then rebuild.
    Take the output and subtract all query clauses.
    Question: is this sound & complete?
    - Seems like no: what if two query clauses get unified?
      Could happen when the coquery is supposed to generate a merge.
      Would either result in some query clauses migrating to the coquery,
      or if do really wrong, a rule that restricts the inputs instead of unifying the outputs

    Note: improving the coquery is nice, but not very important, so we'll skip this latter idea for now.


    Core implementation question: add vars as 0-arg constructors
    or 'pun' as ids? Punning makes rebuilding do the right thing automatically, but subtle.
    0-arg constructors requires rws for output.


    TODO: for punning:
    - add vars to union-find such that they are all valid ids
         (note: will benefit from vars being dense starting at 0)
    - add clauses as atoms (put rather than hash since the ids are preallocated)
    - run rebuild
    
    - for coquery, if a var isn't in the query vars, still pre-add it,
      but use hash_node to generate a value, then union them.
      Generates excess free vars the first time a clause is seen, but allows for proper deduplication

    
   *)

  Definition canonicalize_clause c {A} : state (instance A) (clause _ _) :=
    match c with
    | atom_clause a => Mfmap atom_clause (canonicalize a)
    | eq_clause x y =>
        @! let x' <- find x in
          let y' <- find y in
          ret (eq_clause x' y')
    end.
  
  (*TODO: duplicated. move*)
  #[local] Instance map_default {K V} `{m : map.map K V} : WithDefault m := map.empty.

  Definition remove_atom a {A} : state (instance A) unit :=
    fun '(Build_instance _ _ _ _ _ _ db equiv parents epoch wl an) =>
      let tbl_upd tbl := map.remove tbl a.(atom_args) in
      let db' := map_update db a.(atom_fn) tbl_upd in
      (tt,Build_instance _ _ _ _ _ _ db' equiv parents epoch wl an).

  (*TODO: would this be a better signature for UnionFind.find? *)
  Definition uf_find_stateful i : state (union_find idx (idx_map idx) (idx_map nat)) idx :=
    fun uf => let (x,y) := UnionFind.find uf i in (y,x).

  (* Note: could set all ranks to 1, but find might do that in the future anyway,
     and it's not necessary.
   *)
  Definition force_uf (uf : union_find idx (idx_map idx) (idx_map nat)) :=
    list_Miter uf_find_stateful (map.keys uf.(parent _ _ _)) uf.
    
  Definition force_equiv {X} : state (instance X) unit :=
    fun '(Build_instance _ _ _ _ _ _ db equiv parents epoch wl an) =>
      let equiv' := snd (force_uf equiv) in
      (tt,Build_instance _ _ _ _ _ _ db equiv' parents epoch wl an).

  (*TODO: move to utils*)
  Ltac get_goal :=
    lazymatch goal with |- ?G => G end.

  Notation union_find_ok := (union_find_ok lt).
  
  Lemma force_uf_ok equiv x
    : union_find_ok equiv x ->
      union_find_ok (snd (force_uf equiv)) x.
  Proof.
    clear idx_succ.
    unfold force_uf.
    revert x equiv.
    enough (forall l x equiv,
               incl l (map.keys (parent equiv)) ->
               union_find_ok equiv x ->
               union_find_ok (snd (list_Miter uf_find_stateful l equiv)) x).
    { intros; eapply H; eauto with utils. }
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    unfold uf_find_stateful; cbn.
    case_match; cbn.
    eapply find_spec in case_match_eqn; eauto; try Lia.lia.
    2:{ eapply map_keys_in'; eauto. }
    break.
    eapply IHl; eauto.
    repeat intro.
    eapply map_keys_in'; eauto.
    eapply H2 in H8.
    eapply map_keys_in' in H8; eauto.
    eapply H7 in H8.
    auto.
  Qed.

  
  Lemma force_uf_same_domain equiv l
    : union_find_ok equiv l ->
      forall x, Sep.has_key x (snd (force_uf equiv)).(parent _ _ _)
                <-> Sep.has_key x equiv.(parent _ _ _).
  Proof.
    clear idx_succ.
    unfold force_uf.
    revert equiv.
    enough (forall l x equiv,
               incl l (map.keys (parent equiv)) ->
               union_find_ok  equiv x ->
               forall x, Sep.has_key x (snd (list_Miter uf_find_stateful l equiv)).(parent _ _ _)
                         <-> Sep.has_key x equiv.(parent _ _ _)).
    { intros; eapply H; eauto with utils. }
    induction l0;
      basic_goal_prep.
    { basic_utils_crush. }
    unfold uf_find_stateful at 1; cbn.
    case_match; cbn.
    eapply find_spec in case_match_eqn; eauto; try Lia.lia.
    2:{ eapply map_keys_in'; eauto; eapply H; basic_goal_prep; eauto. }
    break.
    rewrite IHl0; try symmetry; eauto.
    repeat intro.
    eapply map_keys_in'; eauto.
    eapply H6.
    eapply map_keys_in'; eauto.
    eapply H; cbn; eauto.
  Qed.
  
  Lemma force_uf_equivalent equiv roots
    : union_find_ok equiv roots ->
      forall i1 i2, uf_rel_PER idx (idx_map idx) (idx_map nat)
                      (snd (force_uf equiv)) i1 i2
                    <-> uf_rel_PER idx (idx_map idx) (idx_map nat) equiv i1 i2.
  Proof.
    clear idx_succ.
    unfold force_uf.
    revert equiv.
    enough (forall l equiv,
               incl l (map.keys (parent equiv)) ->
               union_find_ok equiv roots ->
               forall i1 i2, uf_rel_PER idx (idx_map idx) (idx_map nat)
                               (snd (list_Miter uf_find_stateful l equiv)) i1 i2
                         <-> uf_rel_PER idx (idx_map idx) (idx_map nat) equiv i1 i2).
    { intros; eapply H; eauto with utils. }
    induction l;
      basic_goal_prep.
    { basic_utils_crush. }
    unfold uf_find_stateful at 1; cbn.
    case_match; cbn.
    eapply find_spec in case_match_eqn; eauto; try Lia.lia.
    2:{ eapply map_keys_in'; eauto; eapply H; basic_goal_prep; eauto. }
    break.
    rewrite IHl; eauto.
    2:{
      repeat intro.
      eapply map_keys_in'; eauto.
      eapply H6.
      eapply map_keys_in'; eauto.
      eapply H; cbn; eauto.
    }
    {
      unfold uf_rel_PER.
      etransitivity;
        [eapply forest_PER_shared_parent;
         eauto using uf_forest, forest_closed with utils; try Lia.lia
        |symmetry].
      etransitivity;
        [eapply forest_PER_shared_parent;
         eauto using uf_forest, forest_closed with utils; try Lia.lia
        |].
      intuition break; eexists; intuition eauto.
      all: eapply H5; eauto.
    }
  Qed.

  (*TODO: duplicated: move to utils*)
  Hint Resolve Properties.map.extends_refl : utils.
  
  Lemma force_equiv_sound X m i
    : state_sound_for_model (analysis_result:=X) lt m i force_equiv (fun i' _ => i = i').
  Proof.
    open_ssm'.
    intuition cbn; eauto with utils.
    {
      destruct e, e0; constructor; basic_goal_prep; eauto.
      eexists; eauto using force_uf_ok.
    }
    {
      destruct e, e1; constructor; basic_goal_prep; eauto.
      { destruct e0 as [ [] ]; eapply force_uf_same_domain; eauto. }
      {
        apply rel_interpretation;
          destruct e0 as [ [] ];
          eapply force_uf_equivalent; eauto.
      }
    }
  Qed.
  
  (*TODO: duplicated*)  
  Ltac iss_case :=
    lazymatch goal with
    | H : ?ma <$> _ |- _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn in H;[| tauto]
    | |- ?ma <?> _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn;[| tauto]
    end.

  Lemma remove_atom_sound X m i a
   : state_sound_for_model lt m i (remove_atom a (A:=X))
       (fun (i'' : idx_map (domain symbol m)) (_ : unit) => i = i'').
  Proof.
    open_ssm; destruct e; cbn.
    { destruct e0; constructor; intuition eauto. }
    {
      destruct e1; constructor; intuition eauto.
      apply atom_interpretation.
      unfold atom_in_egraph, atom_in_db in *; cbn in *.
      intros; repeat iss_case.
      eqb_case (atom_fn a) (atom_fn a0).
      {
        rewrite H0 in *.
        rewrite get_update_same in Hma; eauto.
        inversions.
        unfold default, map_default in Hma0.
        rewrite Properties.map.remove_empty in Hma0.
        case_match; rewrite ?map.get_empty in *; try congruence.
        cbn.
        eqb_case (atom_args a) (atom_args a0).
        {
          rewrite H1 in *.
          rewrite map.get_remove_same in *; congruence.
        }
        {
          rewrite map.get_remove_diff in * by auto.
          rewrite Hma0.
          cbn.
          eauto.
        }
      }
      {
        rewrite get_update_diff in Hma by auto.
        rewrite Hma; cbn.
        rewrite Hma0; cbn; auto.
      }
    }
  Qed.

  Lemma dedup_computation_sound X m i l `{model_ok _ m}
    (* TODO this assumption should be packaged somewhere*)
    : all (atom_sound_for_model idx symbol idx_map m i) l ->
      state_sound_for_model lt (analysis_result:=X) m i
        (list_Miter (fun a => Mbind (fun a => remove_atom a (A:=X))
                                (canonicalize a))
           l)
        (fun i' _ => i = i').
  Proof.
    intros.
    eapply state_sound_for_model_Miter; eauto.
    intros; subst.
    ssm_bind.
    {
      apply canonicalize_sound; eauto.
      eapply in_all; eauto.
    }
    cbn beta in *; break; subst.
    apply remove_atom_sound.
    Qed.

(* TODO: split in 2: egraph comps to sequent, and sequent to egraph comps *)
Section SequentOfStates.
  Context {X A} `{analysis idx symbol X}
    (assumptions : state (instance X) A)
    {B} (conclusions : A -> state (instance X) B) (r_fuel : nat).
  
  (* We keep around the egraph for use in the conclusion,
     but it suffices to discard the equations and just use the assumptions,
     since the atoms of the query will all use the canonical variables.

     TODO: make sure to take in a sufficient fuel.
     Must be an input to be sound.
   *)
  Let assumption_inst :=
        (@! let a <- assumptions in
           let _ <- rebuild r_fuel in
           ret a)
          (empty_egraph idx_zero X).
  Let assumption_atoms := db_to_atoms (snd assumption_inst).(db).

  (*
    Start the conclusion egraph from the assumption one to handle collapsing
    any conclusion variables that were unified by assumption simplification.

    This will leave a bunch of excess equations in the conclusion,
    but we optimize them out later, and even if we didn't, reflexive & fresh unions are cheap.

    Note: force_equiv guarantees that the union-find is rank 1
    (even if the rank map overapproximates wit higher numbers at run time).
    This means that when eliminating dead equations later,
    we do not need to consider transitivity.
   *)
  Let conclusion_inst :=
        let comp a :=(@! let b <- conclusions a in
                        let _ <- rebuild r_fuel in
                        let _ <- force_equiv in
                        ret b) in
        snd (uncurry comp assumption_inst).

  (* Remove the atoms of the assumptions.
     We remove them rather than not adding them in the first place
     because we also want to remove anything from the conclusion that duplicates
     an assumption.
   *)
  Let conclusion_inst_dedup :=
        snd (list_Miter
               (fun a => Mbind (fun a => remove_atom a (A:=X))
                           (canonicalize a))
               assumption_atoms
               conclusion_inst).

  (*
    Should be a correct conclusion, but contains a bunch of extra equations.
   *)
  Let conclusion_atoms := db_to_atoms conclusion_inst_dedup.(db).
  Let conclusion_eqs_verbose : list (_*_) :=
        map.tuples conclusion_inst.(equiv).(parent _ _ _).

  (* Check whether the variable is in any atoms (conclusion or assumptions) *)
  Let conclusion_var_in_atoms x :=
    existsb (fun a => orb (eqb a.(atom_ret) x)
                        (inb x a.(atom_args)))
      (assumption_atoms ++ conclusion_atoms).

  Let live_eqn x y :=
        (* filter out all reflexive equalities,
           as well as all equalities where one of the variables is not in the atomsz
         *)
        andb (andb (negb (eqb x y))
                   (*TODO: double check! should check query, not conclusion *)
                (conclusion_var_in_atoms x))
                (conclusion_var_in_atoms y).
  
  (*TODO: should be optimized more; current implementation unfinished*)
  Let conclusion_eqs_final :=
        (* filter out the obviously dead equations*)
       (*TODO: debug filter (fun '(x,y) => negb (can_erase y))  *)
        filter (fun '(x,y) => live_eqn x y)
          conclusion_eqs_verbose.

 
  (*A variant that preserves in the type that the assumption has no equations*)
  Definition sequent'_of_states := 
    (assumption_atoms, conclusion_atoms , conclusion_eqs_final).

  (* Generates an (optimized) sequent from two egraph state monad values *)
  Definition sequent_of_states := 
    Build_sequent _ _ (map atom_clause assumption_atoms)
      (map (uncurry eq_clause) conclusion_eqs_final++(map atom_clause conclusion_atoms)).

  Notation state_sound_for_model :=
    (state_sound_for_model _ idx_succ _ _ _ _ _).

  (*TODO: move to base utils*)
      Ltac inst_implication H :=
        unshelve
          let p := open_constr:(_) in
          specialize (H p).
      
      (*TODO: move to base utils *)
      Lemma all_map T1 T2 P (f : T1 -> T2) l
        : all P (map f l) <-> all (fun x => P (f x)) l.
      Proof using. clear. induction l; basic_goal_prep; basic_utils_crush. Qed.

      
      Lemma find_does_not_touch_db a (i : instance X) a0 i0
        : find a i = (a0, i0) ->
          db i = db i0.
      Proof.
        clear.
        destruct i; unfold find; cbn.
        case_match; basic_goal_prep;
          basic_utils_crush.
      Qed.
      
      Lemma canonicalize_does_not_touch_db a (i : instance X) a0 i0
        : canonicalize a i = (a0, i0) ->
          db i = db i0.
      Proof.
        clear.
        destruct a; cbn.
        case_match.
        assert (db i = db i1).
        {
          revert l i i1 case_match_eqn;
            induction atom_args;
            basic_goal_prep.
          1: basic_utils_crush.
          case_match.
          eapply find_does_not_touch_db in case_match_eqn0.
          rewrite  case_match_eqn0; clear  case_match_eqn0.
          case_match.
          eapply  IHatom_args in case_match_eqn0.
          congruence.
        }
        case_match.
        apply find_does_not_touch_db in case_match_eqn0.
        intros; autorewrite with inversion in *; break; subst.
        congruence.
      Qed.

      
      Lemma remove_atom_incl (i0 : instance X) a0 i1 u
        : remove_atom a0 i0 = (u, i1) ->
          incl (db_to_atoms (db i1))  (db_to_atoms (db i0)).
      Proof using lt symbol_map_ok idx_trie_ok Eqb_symbol_ok Eqb_symbol Eqb_idx_ok
Eqb_idx.
        clear conclusion_eqs_final live_eqn conclusion_var_in_atoms
          conclusion_eqs_verbose conclusion_atoms conclusion_inst_dedup
          conclusion_inst assumption_atoms  assumption_inst
          idx_zero idx_succ.
        unfold remove_atom.
        destruct i0; cbn.
        basic_goal_prep;
          basic_utils_crush.
        cbn.
        unfold map_update.
        case_match; unfold default, map_default; cbn.
        2:{
          rewrite Properties.map.remove_empty.
          unfold db_to_atoms.
          intros ? ?.
          rewrite in_flat_map in *.
          basic_goal_prep.
          apply Properties.map.tuples_spec in H0.
          eqb_case (atom_fn a0) s.
          {
            rewrite map.get_put_same in *.
            autorewrite with inversion in *; subst.
            unfold map.tuples in H1.
            cbn in H1.
            rewrite Properties.map.fold_empty in H1.
            basic_goal_prep;
              basic_utils_crush.
          }
          {
            rewrite map.get_put_diff in * by auto.
            rewrite in_map_iff in H1.
            basic_goal_prep; subst.
            exists (s,r).
            rewrite Properties.map.tuples_spec.
            intuition auto.
            unfold table_atoms.
            apply in_map with (f:= (row_to_atom idx symbol X s)) in H3.
            eauto.
          }
        }
        {
          intros ? ?.
          unfold db_to_atoms in *.
          rewrite in_flat_map in *.
          basic_goal_prep.
          apply Properties.map.tuples_spec in H0.
          eqb_case (atom_fn a0) s.
          {
            rewrite map.get_put_same in *.
            autorewrite with inversion in *; subst.
            rewrite in_map_iff in *.
            basic_goal_prep; subst.
            rewrite Properties.map.tuples_spec in *.
            eqb_case l (atom_args a0).
            {
              exfalso.
              rewrite map.get_remove_same in *.
              congruence.
            }
            rewrite map.get_remove_diff in * by auto.
            exists ((atom_fn a0), r).
            rewrite Properties.map.tuples_spec.
            basic_goal_prep;
              basic_utils_crush.
            let x := open_constr:(_) in
            replace ({| atom_fn := atom_fn a0; atom_args := l; atom_ret := entry_value idx X d |}) with x;[ eapply in_map |].
            {
              rewrite Properties.map.tuples_spec; eauto.
            }
            { reflexivity. }
          }
          {
            rewrite map.get_put_diff in * by auto.
            rewrite in_map_iff in H1.
            basic_goal_prep; subst.
            exists (s, r0).
            rewrite Properties.map.tuples_spec.
            intuition auto.
            unfold table_atoms.          
            let x := open_constr:(_) in
            replace ({| atom_fn := s; atom_args := l; atom_ret := entry_value idx X d |}) with x;[ eapply in_map |].
            { rewrite Properties.map.tuples_spec in *; eauto. }
            { reflexivity. }
          }          
        }
      Qed.
        
      Lemma incl_remove_atoms al (i : instance X)
        : incl ((db_to_atoms
                   (db
                      (snd
                         (list_Miter
                            (fun a : atom => @! let a0 <- canonicalize a in (remove_atom a0))
                            al i)))))
            (db_to_atoms
               (db
                  i)).
      Proof using lt symbol_map_ok idx_trie_ok Eqb_symbol_ok Eqb_symbol Eqb_idx_ok
Eqb_idx.
        clear conclusion_eqs_final live_eqn conclusion_var_in_atoms
          conclusion_eqs_verbose conclusion_atoms conclusion_inst_dedup
          conclusion_inst assumption_atoms  assumption_inst
          idx_zero idx_succ.
        revert i; induction al;
          intros.
        { cbn; eapply incl_refl. }
        {
          basic_goal_prep.
          destruct (canonicalize a i) eqn:Hc.
          eapply canonicalize_does_not_touch_db in Hc.
          rewrite Hc.
          case_match.
          apply remove_atom_incl in case_match_eqn.
          eapply incl_tran; try eassumption.
          clear case_match_eqn.
          eapply IHal.
        }
      Qed.

      Lemma all_in T (P : T -> _) l
        : (forall x, In x l -> P x) -> all P l.
      Proof using.
        clear.
        enough (forall l', (forall x, In x l' -> P x) -> incl l l' -> all P l).
        {
          intros; eapply H; eauto using incl_refl.
        }
        {
          intros ? ?.
          induction l; basic_goal_prep;
            basic_utils_crush.
        }
      Qed.
      
      (*TODO: move to list utils*)
      Lemma all_incl {T} (P : T -> Prop) l1 l2
        : incl l1 l2 ->
          all P l2 ->
          all P l1.
      Proof using.
        clear.
        unfold incl.
        intros.
        eapply all_in.
        intros.
        eapply in_all; eauto.
      Qed.

      
      Lemma state_Mbind_assoc
          : forall S (T1 T2 T3 : Type) (f : T1 -> state S T2)
                   (g : T2 -> state S T3) (ma : state S T1) s0,
            Mbind (fun a : T1 => @! let p <- f a in (g p)) ma s0
            = Mbind g (@! let p <- ma in (f p)) s0.
      Proof.
        clear.
        basic_goal_prep.
        repeat case_match.
        congruence.
      Qed.

      Notation egraph_sound_for_interpretation :=
        (egraph_sound_for_interpretation _ _ symbol_map _ _ _).


      Hint Rewrite @map.get_empty : utils.

      
      Lemma empty_egraph_sound m
        : egraph_sound_for_interpretation m map.empty (empty_egraph idx_zero X).
      Proof.
        revert idx_map_ok symbol_map_ok.
        clear.
        constructor; basic_goal_prep;
          basic_utils_crush.
        {
          exfalso.
          unfold atom_in_egraph, atom_in_db in *.
          basic_goal_prep;
            basic_utils_crush.
        }
        {
          exfalso; unfold uf_rel_PER in *.
          eapply PER_empty; try eassumption; eauto.
          basic_goal_prep;
            basic_utils_crush.
        }
      Qed.

      
      
    Lemma sequent_of_states_sound m (*Post_i Post Post2 i3*)
      : (* state_sound_for_model m map.empty assumptions Post_i Post ->
        (forall a i2, (Post_i a i2) ->
                      Post a ->
                      state_sound_for_model m i2 (conclusions a) i3 Post2) ->*)
        model_satisfies_rule m sequent_of_states.
    Proof.      
      unfold model_satisfies_rule, sequent_of_states; cbn.
      intros.
      replace conclusion_eqs_final with conclusion_eqs_verbose by admit.
      (*
      TODO: ssm Pi -> forall i, Pi -> atom a e -> clause_sound a i.
      Will this work? not really soundness, more completeness. seems ok.
      eqns should be easy. actually, everything should be ok?

      relationship between ssm, model_satisfies_rule, and query sat assign.

      Idea: If add_ctx returns renaming R, and query matches w/ assignment R',
      then R . R' . i = subst




current understanding:
property of add_ctx: for all interps of the resulting e-graph,
the output renaming composed with the interp produces a subst that is wf at the ctx.

property of add_term: for ....,
the output id maps to the input term w/the subst applied





      
      rewrite all_map in H1; cbn in H1.
      eexists.
      autorewrite with utils; rewrite !all_map; cbn.
      TODO: where does out_assignment come from?.
      Intuitively, the output of a state triple.
      Start from conclusion and work backwards

TODO: like this outside section
Lemma sequent_of_states_sound A B m i1 s1 Post_i Post Post2 Post_i2
      (s2 : A -> state (instance _) B)
      : state_sound_for_model m i1 s1 Post_i Post ->
        (forall a i2, map.extends i2 i1 ->
                      (Post_i i2) ->
                      Post i2 a ->
                      state_sound_for_model m i2 (s2 a) Post_i2 Post2) ->
        model_satisfies_rule m (sequent_of_states s1 s2).
    Proof.
      
      unfold model_satisfies_rule.
      intros.
      eexists.
      cbn [sequent_of_states seq_conclusions seq_assumptions] in *.
      rewrite all_app, !all_map in *.
      unfold uncurry.
      (*TODO: more precise conditions*)
      (*
      assert (state_sound_for_model m map.empty
                (@! let a <- assumptions in
                   (Mbind (fun _ : unit => @! ret a) (rebuild 1000)))
                 (fun _ x => x = query_assignment (*TODO: should be out_assign*))
                  (fun _ => True)).
      {
        eapply state_triple_bind.
        *)
        (*
        TODO: what is the right assumption?
      }
      cbn [assignment_satisfies_clause].
      assert (forall A B C, (A /\ (A -> B) /\ (A -> C)) -> A /\ B /\ C) as HP
        by intuition auto.
      apply HP; clear HP.
      repeat split; intros.
      3:{
        unfold conclusion_atoms.
        unfold conclusion_inst_dedup.
        eapply all_incl.
        1:eapply incl_remove_atoms.
        unfold conclusion_inst, uncurry.
        unfold assumption_inst.
        change (let '(x,y) := ?ma ?s0 in @?f x y)
          with (Mbind f ma s0).
        rewrite !state_Mbind_assoc.
        enough (state_sound_for_model m map.empty
                  ((@!
               let p <-
               @!
               let p <-
               @! let a <- assumptions in (Mbind (fun _ : unit => @! ret a) (rebuild 1000))
               in (conclusions p)
               in (Mbind (fun _ : unit => @! let _ <- force_equiv in ret p) (rebuild 1000))))
                  (fun _ x => x = query_assignment (*TODO: should be out_assign*))
                  (fun _ => True)).
        {
          specialize (H3 (empty_egraph idx_zero X) (empty_egraph_sound _)).
          cbn beta in H3.
          destruct H3 as [x [ Heq [H3 [? ?] ] ] ].
          subst x.
          destruct H3.
          assignment_satisfies_atom =
fun (idx symbol : Type) (idx_map : forall A : Type, map.map idx A) 
  (m : model symbol) (assignment : idx_map (domain symbol m)) (a : Defs.atom idx symbol) =>
eval_atom idx symbol idx_map m assignment (atom_fn a) (atom_args a) <$>
(fun r : domain symbol m => map.get assignment (atom_ret a) <$> domain_eq symbol m r)
     : forall (idx symbol : Type) (idx_map : forall A : Type, map.map idx A) (m : model symbol),
    idx_map (domain symbol m) -> Defs.atom idx symbol -> Prop

                                                           atom_sound_for_model =
fun (idx symbol : Type) (idx_map : forall A : Type, map.map idx A) 
  (m : model symbol) (idx_interpretation : idx_map (domain symbol m))
  (a : Defs.atom idx symbol) =>
list_Mmap (map.get idx_interpretation) (atom_args a) <$>
(fun args : list (domain symbol m) =>
 map.get idx_interpretation (atom_ret a) <$>
 (fun out : domain symbol m => interprets_to symbol m (atom_fn a) args out))
     : forall (idx symbol : Type) (idx_map : forall A : Type, map.map idx A) (m : model symbol),
       idx_map (domain symbol m) -> Defs.atom idx symbol -> Prop
          break.
          cbn in H3.
          break.
          basic_goal_prep.
          
        TODO: transition to state_sound goal
        (*TODO: fix constraints on output*)
        assert (state_sound_for_model m map.empty assumptions
                  (fun _ x => x = query_assignment)
                  (fun _ => True)) by admit.
        state_sound_for_model
        assert (assumptions).
        cbn -[rebuild assumption_inst].
        unfold assumption_atoms in *.
        cbn -[rebuild assumption_inst] in H1.
        assert((fst assumption_inst, snd assumption_inst) = assumption_inst).
        {
          clear.
          destruct assumption_inst.
          reflexivity.
        }
        rewrite <- H3.
        cbn -[rebuild assumption_inst].
        
        cbn.
        case_match.
        cbn in H1.
        rewrite all_map in *.
        cbn in
        incl ((db_to_atoms
       (db
          (snd
             (list_Miter
                (fun a : atom => @! let a0 <- canonicalize a in (remove_atom a0))
                assumption_atoms conclusion_inst)))))
                conclusion_inst
        TODO: prove invariant over remove_atom.
        then prove invariant over force_equiv.
        Then
        enough (exists i, egraph_sound_for_interpretation m conclusion_inst_dedup i
                          /\ extends i (map.of_list query_assignment ++ out_assignment)).
        enough (forall i, egraph_sound_for_interpretation m assumption_atoms i ->
                          domain i `intersect` out_fvs = empty ->
                          exists i, extends i' i
                                    /\ egraph_sound_for_interpretation m conclusion i').
        High level idea: quantify over interpretations,
            relate assignments to interpretations.
        The two are basically the same thing.
        Question: should the interpretation just be an assoc list?.
        It's not computational.
        Then the two would be literally the same.
        An assignment for an egraph would be a 'minimal' interpretation.
        is the ++out_assignment good? I think a better approach might be to say
               exists out, extends out in, ...
        
      rew
      have: a set of assumptions, that comes from a graph.
      have: an assignment that satisfies them (and so should be sound wrt the graph).
      have a set of conclusions that comes from a related graph.
      need: an extended assignment that is sound wrt the conclusions (graph)
      notes: assignments in domain, not between graphs

      Fail.

      TODO:soundness of assumptions insufficient for conclusion?.
      need a completeness-like statement
             want something like this:
          for all DBs g where model_of m i g
          (interpretations are arrows from dbs to models)
          for s in hom(a,g), i += s : g' -> m.

         *)
    Qed.*)
    Abort.

    (*
    Lemma sequent_of_states_sound m Post_i Post Post2 i3
      : state_sound_for_model m map.empty assumptions Post_i Post ->
        (forall a i2, (Post_i a i2) ->
                      Post a ->
                      state_sound_for_model m i2 (conclusions a) i3 Post2) ->
        model_satisfies_rule _ _ _ m sequent_of_states.
    Proof.
      intros.
      unfold sequent_of_states, model_satisfies_rule.
      cbn.
      intros.
      specialize (H0 (empty_egraph idx_zero X)).
      inst_implication H0.
      { eapply empty_sound_for_interpretation; eauto. }
      intuition auto.
      destruct H0.
      intuition auto.
      (*
      TODO: prove composition of assumptions, rebuild before plugging in empty?.
      TODO: high-level question: what property do' I want of the assumptions?.
      it need to be precise, not just monotone; in other words, there is some sort of completeness property
      break.
        edestruct empty_sound; cycle 2.
        {
          destruct sound_egraph_for_model.
          eapply H4.
      }
      cbn beta in *.
      basic_goal_prep.
      unfold curry.
      cbn [fst curry uncurry snd].
       *)
    Admitted.
*)
  

  (* Diagnostics. For debugging only*)

  Definition seq_of_S_assumption_atoms := assumption_atoms.
  Definition seq_of_S_assumption_eqns := map.tuples (snd assumption_inst).(equiv).(parent _ _ _).
  Definition seq_of_S_conclusion_atoms :=  db_to_atoms conclusion_inst.(db).
  Definition seq_of_S_live_eqn := live_eqn.
  Definition seq_of_S_in_atom := conclusion_var_in_atoms.
  Definition seq_of_S_verbose := conclusion_eqs_verbose.

  (************************)

End SequentOfStates.

Section Optimize.
  Context (s : sequent).

  
  (*TODO: make sure to choose sufficient fuel to totally rebuild.
    Also, if this is it, compute more efficiently.
   *)
  Let fuel :=
        let var_count :=
          (length (flat_map (clause_vars _ _) s.(seq_assumptions)
                   ++ flat_map (clause_vars _ _) s.(seq_conclusions)))
        in
        var_count * var_count.


  Notation clauses_to_instance :=
    (clauses_to_instance idx_succ (analysis_result:=unit)).
  
  Let sub_and_assumptions :=
        @! let (_,sub) <- clauses_to_instance s.(seq_assumptions) [] in
         (* let _ <- rebuild fuel in TODO: rebuilds above already *)
          ret sub.

  Let conclusions (p : named_list idx idx) : state (instance unit) _ :=
        (*Mseq *) (clauses_to_instance s.(seq_conclusions) p) (* (rebuild fuel) *). 
 
  (*A variant that preserves in the type that the assumption has no equations*)
  Definition optimize_sequent' := sequent'_of_states sub_and_assumptions conclusions.
  
  Definition optimize_sequent := sequent_of_states sub_and_assumptions conclusions.

  
  (* Diagnostics. For debugging only*)

  Definition opt_assumption_atoms := seq_of_S_assumption_atoms sub_and_assumptions.
  Definition opt_assumption_eqns := seq_of_S_assumption_eqns sub_and_assumptions.
  Definition opt_conclusion_atoms := seq_of_S_conclusion_atoms sub_and_assumptions conclusions.
  Definition opt_live_eqn := seq_of_S_live_eqn sub_and_assumptions conclusions.
  Definition opt_in_atom := seq_of_S_in_atom sub_and_assumptions conclusions.
  Definition opt_verbose := seq_of_S_verbose  sub_and_assumptions conclusions.

  (************************)

End Optimize.


  Definition atom_fvs (a : atom) := a.(atom_ret)::a.(atom_args).

  Notation rule_set := (rule_set idx symbol symbol_map idx_map).
  (* TODO: Using ST' instead of ST because of some weird namespacing *)
  Local Notation ST' := (state (symbol_map (idx * idx_map (list nat * nat)))).

  (* Sorts the elements in the first list, viewed as a set, by their position in the second.
     Assumes the second list has no duplicates.
   *)
  Definition sort_by_position_in (l1 l2 : list idx) :=
    filter (fun x => inb x l1) l2.

  (* Returns `Some k` for some k such that (k,v) is in m, if any such pair exists.
     Expect this to be slow. *)
  Definition map_inverse_get {key value} {map : map.map key value} `{Eqb value}
    (m : map) (v : value) : option key :=
    map.fold (fun acc k v' => if eqb v v' then Some k else acc) None m.

  Definition hash_clause (a : Defs.atom nat symbol) : ST' idx :=
    let (f, args, out) := a in
    fun S : symbol_map (idx * idx_map (list nat * nat)) =>
      match map.get S f with
      | Some (last, m) =>
          match map_inverse_get m (args,out) with
          | Some i => (i, S)
          | None =>
              let new_id := idx_succ last in
              let S' := map.put S f (new_id, map.put m new_id (args,out)) in
              (new_id, S')
          end
      | None => (idx_zero, map.put S f (idx_zero, map.singleton idx_zero (args,out)))
      end.

  Local Notation idx_of_nat := (idx_of_nat _ idx_succ idx_zero).

  Definition compile_query_clause (qvs : list idx) (a : atom)
    : ST' (erule_query_ptr idx symbol) :=
    let (f, args, out) := a in
    let clause_vars := sort_by_position_in (out::args) qvs in
    let indices : list nat := (seq 0 (length clause_vars)) in
    let sub : named_list idx nat := combine clause_vars indices in
    let compiled_clause := Build_atom f (map (named_list_lookup 0 sub) args)
                             (named_list_lookup 0 sub out) in
    @! let i <- hash_clause compiled_clause in
      ret (Build_erule_query_ptr _ _ f i clause_vars).

  Local Notation erule := (erule idx symbol).
  Local Notation const_rule := (const_rule idx symbol).

  
  Definition clauses_fvs l rem_list :=
    filter (fun x => negb (inb x rem_list))
      (dedup (eqb (A:=_)) (flat_map (clause_vars idx symbol) l)).

  Definition compile_rule rf (r : sequent) : ST' (erule + const_rule) :=
    let '(assumptions, conclusion_atoms, conclusion_eqs) :=
      optimize_sequent' r rf in
    (*TODO: optimize order somewhere*)
    let qvs := dedup (eqb (A:=_)) (flat_map atom_fvs assumptions) in
    (*TODO: simplify *)
    let conclusion_vars :=
      (clauses_fvs (map (uncurry eq_clause) conclusion_eqs
                      ++ map atom_clause conclusion_atoms) qvs) in
    @! let {ST'} qcls_ptrs <- list_Mmap (compile_query_clause qvs) assumptions in
      (* Assume it must be nonempty to be useful.
         TODO: how to handle empty rules?
         essentially just add a term to the egraph, can be run once and discarded.
       *)
      match qcls_ptrs with
      | [] => Mret (inr (Build_const_rule _ _ conclusion_vars
                           conclusion_atoms conclusion_eqs))
      | c::cs => Mret (M:=ST') (inl (Build_erule _ _ qvs (c,cs) conclusion_vars
                              conclusion_atoms conclusion_eqs))
      end.

  (*TODO: put in Utils.v*)
  Definition split_sum_list {A B} (l : list (A + B)) : (list A * list B) :=
    List.fold_right (fun e acc => match e with
                                  | inl e' => (e'::fst acc, snd acc)
                                  | inr e' => (fst acc,e'::snd acc)
                                  end) ([],[]) l.
  
  
  Definition build_rule_set rf (rules : list sequent) : rule_set :=
    let (crs, clauses_plus) := list_Mmap (compile_rule rf) rules map.empty in
    let (erules, consts) := split_sum_list crs in
    Build_rule_set (map_map snd clauses_plus) erules consts.
  
End WithMap.


Arguments build_rule_set {idx}%type_scope {Eqb_idx} idx_succ%function_scope idx_zero 
  {symbol}%type_scope {symbol_map}%function_scope {symbol_map_plus} 
  {idx_map}%function_scope {idx_trie}%function_scope rf rules%list_scope.

Arguments QueryOpt.sequent_of_states {idx}%type_scope {Eqb_idx} 
  {idx_zero} {symbol}%type_scope {symbol_map idx_map}%function_scope
  {idx_trie}%function_scope {X A}%type_scope {H} 
  assumptions {B}%type_scope conclusions%function_scope r_fuel.
