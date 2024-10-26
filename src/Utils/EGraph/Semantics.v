(* An implementation of the core of egglog

   TODO: benchmark, then use plist everywhere feasible and retest
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind.
From Utils.EGraph Require Import Defs QueryOpt.
From Utils Require TrieMap.
Import Sets.
Import StateMonad.


(*TODO: move somewhere*)
Definition Is_Some_satisfying {A} (P : A -> Prop) x :=
  match x with
  | Some x => P x
  | None => False
  end.
Notation "x <$> P" :=
  (Is_Some_satisfying P x)
    (at level 56,left associativity).


Ltac match_some_satisfying :=
  lazymatch goal with
  | H : ?e <$> ?f |- _ =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  | |- context ctx [?e <$> ?f] =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  end.

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)

      (*TODO: just extend to Natlike?*)
      (idx_succ : idx -> idx)
      (idx_zero : idx)
      (*TODO: any reason to have separate from idx?*)
      (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol).

  Notation atom := (atom idx symbol).

  Definition atom_subst (sub : named_list idx idx) (a : atom) :=
    Build_atom
      a.(atom_fn)
      (map (fun x => named_list_lookup x sub x) a.(atom_args))
      (named_list_lookup a.(atom_ret) sub a.(atom_ret)).


(* Alternate approach: consider the initial model of the theory.
   Terms added at the start form a no-premise rule, so can be ignored.
 *)
  Record model : Type :=
    {
      (* represents the quotiented idx.
         TODO: to realize the quotient, should I include a domain equiv?
         - would let me use e.g. terms as the domain
         - alternatively, I can use idx as the domain, and take the quotient
           to be implied by the non-bijectivity of constants.
       *)
      domain : Type;
      (* included to support setoids *)
      domain_eq : domain -> domain -> Prop;
      (*constants : idx -> domain; TODO: do I have any constants? *)
      interpretation : symbol -> list domain -> option domain;
    }.

  Definition eval_atom m (assignment : named_list idx m.(domain)) f args : option m.(domain) :=
    @!let args' <- list_Mmap (named_list_lookup_err assignment) args in
      (m.(interpretation) f args').
      
  Definition assignment_satisfies m
    (assignment : named_list idx m.(domain)) : list atom -> Prop :=
    all (fun a => (eval_atom m assignment a.(atom_fn) a.(atom_args)) <$>
                    (fun r => (named_list_lookup_err assignment a.(atom_ret)) <$>
                    (m.(domain_eq) r))).

  Definition assignment_unifies m
    (assignment : named_list idx m.(domain)) : list (idx * idx) -> Prop :=
    all (fun '(x,y) => named_list_lookup_err assignment x <$>
                         (fun xv => named_list_lookup_err assignment y <$>
                                      (m.(domain_eq) xv))).
  
  (* TODO: rewrite properties to be easier to read
   *)
  Record model_of
    (m : model)
    (rw : list (log_rule idx symbol)) : Prop :=
    {
      (* wf_model conditions *)
      (* TODO: does it need to be an equivalence? *)
      domain_eq_PER : PER m.(domain_eq);
      (* TODO: do I want this?
      interpretation_in_eq :
      forall f args i, m.(interpretation) f args = Some i ->
                     m.(domain_eq) i i;
       *)

      (* model_of conditions *)
      rules_sound : all (fun r =>
                           forall query_assignment,
                             map fst query_assignment = r.(query_vars _ _) ->
                             assignment_satisfies m query_assignment r.(query_clauses _ _) ->
                             exists out_assignment,
                               (* query assignment first eliminates the need for an all_fresh condition*)
                               assignment_satisfies m (query_assignment ++ out_assignment)
                                 r.(write_clauses _ _)
                               /\ assignment_unifies m (query_assignment ++ out_assignment)
                                 r.(write_unifications _ _))
                      rw
    }.

  
  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_plus : map_plus symbol_map)
    (symbol_map_ok : forall A, map.ok (symbol_map A)).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: check that we don't need weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_ok : forall A, map.ok (idx_trie A))
        (idx_trie_plus : map_plus idx_trie).

  Notation instance := (instance idx symbol symbol_map idx_map idx_trie).
  (*TODO: many of these relations can be functions. what's the best way to define them?*)
  Definition atom_in_egraph a (i : instance) :=
    (map.get i.(db _ _ _ _ _) a.(atom_fn)) <$>
      (fun tbl => (map.get tbl a.(atom_args)) <$>
                    (fun r => snd r = a.(atom_ret))).

  Definition SomeRel {A B} (R : A -> B -> Prop) ma mb :=
    match ma, mb with
    | Some a, Some b => R a b
    | _, _ => False
    end.
  
  Record egraph_sound_for_model e m (idx_interpretation : idx -> option m.(domain)) : Prop :=
    {
      (*TODO: needed?
      idx_interpretation_in_domain
      : forall i d, idx_interpretation i = Some d ->
                  m.(domain_eq) d d;
       *)
      (* TODO: write in a more natural way*)
      atom_interpretation :
      forall a,
        atom_in_egraph a e ->
        (Mbind (m.(interpretation) a.(atom_fn))
           (list_Mmap idx_interpretation a.(atom_args))) <$>
          (fun d => (idx_interpretation a.(atom_ret)) <$> (m.(domain_eq) d));
      rel_interpretation :
      forall i1 i2,
        Is_Some (idx_interpretation i1) ->
        Is_Some (idx_interpretation i2) ->
        uf_rel _ _ _ e.(equiv _ _ _ _ _) i1 i2 ->
         SomeRel m.(domain_eq) (idx_interpretation i1) (idx_interpretation i2)
    }.

  Section EGraphSound.
    (*
      A list of parents for which the invariant (temporarily) does not hold
     *)
    Context (excluded_parents : list (symbol * list idx)).

    Definition excluded a :=
      exists p, In p excluded_parents
                /\ fst p = atom_fn a
                /\ snd p = atom_args a.

    Record egraph_ok (e : instance) : Prop :=
      {
        egraph_equiv_ok : exists roots, forest _ _ roots (parent _ _ _ e.(equiv));
        egraph_parents_exist :
        (*TODO: loosen atom_in_egraph to be up to canonicalization/atom_rel?
        TODO: excluded list should just contain atom_fn, atom_args?
         *)
        forall i l, map.get e.(parents) i = Some l ->
                    all (fun a => atom_in_egraph a e \/ excluded a) l
      }.

    Record egraph_sound e rs : Prop :=
      {
        sound_egraph_ok :> egraph_ok e;
        sound_egraph_for_model :
        forall m : model,
          model_of m rs ->
          exists interp, egraph_sound_for_model e m interp;
      }.
  End EGraphSound.

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).

  Theorem empty_sound pe rs : egraph_sound pe (empty_egraph idx_zero) rs.
  Proof.
    unfold empty_egraph.
    constructor.
    { cbn; econstructor; cbn.
      { econstructor; apply empty_forest_rooted. }
      { destruct pe; intros; eauto; rewrite map.get_empty in *; congruence. }
    }
    
    intros; exists (fun _ => None).
    constructor.
    {
      unfold atom_in_egraph;
        destruct a;
        basic_goal_prep.
      rewrite map.get_empty in *.
      basic_goal_prep.
      tauto.
    }
    { cbn; tauto. }
  Qed.

  
  Notation saturate_until := (saturate_until idx_succ idx_zero spaced_list_intersect).

  Notation run1iter :=
    (run1iter idx Eqb_idx idx_succ idx_zero symbol Eqb_symbol symbol_map symbol_map_plus
       idx_map idx_map_plus idx_trie spaced_list_intersect).
  Notation rebuild := (rebuild idx Eqb_idx symbol Eqb_symbol symbol_map idx_map idx_trie).


  (*TODO: include the egraph soundness at all?
    If no, move to Monad
   *)
  Definition state_triple {A} (P : instance -> Prop) (c : state instance A) (Q : A * instance -> Prop) :=
    forall e, P e -> Q (c e).

  
  Definition inst_computation_sound {A} excl_in excl_out (P : state instance A) rs :=
    state_triple (fun e => egraph_sound excl_in e rs) P
      (fun p => egraph_sound excl_out (snd p) rs).

  Lemma state_triple_bind A B P Q H (f : A -> state instance B) c
    : state_triple P c Q ->
      (forall a, state_triple (curry Q a) (f a) H) ->
      state_triple P (Mbind f c) H.
  Proof.
    unfold curry, state_triple, Mbind in *.
    cbn.
    intuition eauto.
    specialize (H0 e).
    specialize (H1 (fst (c e)) (snd (c e))).
    destruct (c e); cbn in *.
    apply H1.
    eauto.
  Qed.

  Lemma increment_epoch_sound rs exl
    : inst_computation_sound exl exl (increment_epoch idx idx_succ symbol symbol_map idx_map idx_trie) rs.
  Proof.
    unfold increment_epoch, inst_computation_sound, state_triple.
    destruct e; cbn; destruct 1; constructor.
    { destruct sound_egraph_ok0; constructor; unfold atom_in_egraph; cbn; eauto. }
    intros m H; specialize (sound_egraph_for_model0 m H); destruct sound_egraph_for_model0.
    exists x.
    destruct H0.
    constructor; eauto.
  Qed.

  Lemma pull_worklist_sound rs exl
    : inst_computation_sound exl exl (pull_worklist idx symbol symbol_map idx_map idx_trie) rs.
  Proof.
    unfold pull_worklist, inst_computation_sound, state_triple.
    destruct e; cbn; destruct 1; constructor.
    { destruct sound_egraph_ok0; constructor; eauto. }
    intros m H; specialize (sound_egraph_for_model0 m H); destruct sound_egraph_for_model0.
    exists x.
    destruct H0.
    constructor; eauto.
  Qed.
  
  Lemma state_triple_ret A (a:A) P
    : state_triple P (@! ret a) (fun p => (fst p = a) /\ P (snd p)).
  Proof.
    unfold increment_epoch, inst_computation_sound, state_triple.
    cbn; eauto.
  Qed.

  Lemma state_triple_wkn_post A P e (Q1 Q2 : A * instance -> Prop)
    : (forall p, Q1 p -> Q2 p) ->
      state_triple P e Q1 ->
      state_triple P e Q2.
  Proof.
    unfold state_triple; firstorder.
  Qed.

  Lemma state_triple_wkn_ret A (a:A) P (Q : _ -> Prop)
    : (forall p, fst p = a /\ P (snd p) -> Q p) ->
        state_triple P (@! ret a) Q.
  Proof.
    intros.
    eapply state_triple_wkn_post.
    2: apply state_triple_ret.
    firstorder.
  Qed.
  

  Lemma state_triple_strengthen_pre A (P1 P2 : _ -> Prop) e (Q: A * instance -> Prop)
    : (forall i, P1 i -> P2 i) ->
      state_triple P2 e Q ->
      state_triple P1 e Q.
  Proof.
    unfold state_triple; firstorder.
  Qed.

  Lemma state_triple_loosen A (P1 P2 : _ -> Prop) e (Q1 Q2 : A * instance -> Prop)
    : (forall p, Q1 p -> Q2 p) ->
      (forall i, P1 i -> P2 i) ->
      state_triple P2 e Q1 ->
      state_triple P1 e Q2.
  Proof.
    intros; eapply state_triple_strengthen_pre; eauto.
    eapply state_triple_wkn_post; eauto.
  Qed.

  Lemma state_triple_lift_pre A (H : Prop) P e (Q: A * instance -> Prop)
    : (H -> state_triple P e Q) ->
      state_triple (fun i => H /\ P i) e Q.
  Proof.
    unfold state_triple; firstorder.
  Qed.

  
  Lemma state_triple_lift_post A (H : Prop) P e (Q: A * instance -> Prop)
    : H ->
      state_triple P e Q ->      
      state_triple P e (fun p => H /\ Q p).
  Proof.
    unfold state_triple; firstorder.
  Qed.
  
  
  Lemma state_triple_frame_const A H P e (Q: A * instance -> Prop)
    : state_triple P e Q -> 
      state_triple (fun i => H /\ P i) e (fun p => H /\ Q p).
  Proof.
    intros. apply state_triple_lift_pre.
    intros. apply state_triple_lift_post; eauto.
  Qed.


  (*TODO:  move*)
  Lemma state_triple_list_Mmap A B (f : A -> state instance B) l P (Q : B -> Prop) (H : A -> Prop)
    : (forall a, H a -> state_triple P (f a) (fun p => Q (fst p) /\ P (snd p))) ->
      all H l ->
      state_triple P (list_Mmap f l) (fun p => all Q (fst p) /\ P (snd p)).
  Proof.
    intro Hf.
    induction l.
    {
      cbn; intros.
      apply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_goal_prep; subst.
      eauto.
    }
    {
      cbn [list_Mmap all].
      intros; break.
      eapply state_triple_bind; eauto.
      intros; break.
      unfold curry.
      eapply state_triple_bind; eauto.
      {
        cbn.
        apply state_triple_frame_const.
        eapply IHl; eauto.
      }
      {
        intros.
        eapply state_triple_wkn_ret.
        unfold curry.
        basic_goal_prep; subst.
        basic_goal_prep; subst.
        intuition eauto.
      }
    }
  Qed.
  
  Lemma state_triple_list_Miter A (f : A -> state instance unit) l P (*(H : A -> Prop)*)
    : (forall a, (*H a ->*) state_triple P (f a) (fun p => P (snd p))) ->
      (*all H l -> TODO: include in P*)
      state_triple P (list_Miter f l) (fun p => P (snd p)).
  Proof.
    intro Hf.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_goal_prep; subst.
      eauto.
    }
    {
      cbn [all list_Miter]; intros; break.
      eapply state_triple_bind; eauto.
      unfold curry.
      destruct a0.
      eapply state_triple_bind; eauto.
      destruct a0.
      eapply state_triple_wkn_ret.
      basic_goal_prep; eauto.
    }
  Qed.

  
  Lemma find_sound pe rs a
    : state_triple (fun e => egraph_sound pe e rs)
        (find idx Eqb_idx symbol symbol_map idx_map idx_trie a)
        (fun p => egraph_sound pe (snd p) rs /\ uf_rel _ _ _ (snd p).(equiv) (fst p) a).
  Proof.
    unfold find, inst_computation_sound, state_triple.
    destruct e; destruct 1; cbn.
    case_match.
    2:{
      cbn; split;[constructor|]; intuition eauto.
      apply reachable_rel_Reflexive.
    }
    basic_goal_prep.
    symmetry in HeqH; break.
    destruct sound_egraph_ok0; break.
    eapply find_spec in HeqH; eauto; [| Lia.lia]; cbn in *; break.
    split;[| apply H2; eauto; eapply reachable_rel_Symmetric; eauto].
    constructor.
    { constructor; cbn; [eexists; eauto | eauto]. }
    intros m Hm.
    specialize (sound_egraph_for_model0 m Hm).
    destruct sound_egraph_for_model0 as [ interp [] ];
      exists interp; constructor; intros.
    {
      eapply atom_interpretation0; 
        clear atom_interpretation0.
      destruct a0.
      cbn in *; eauto.
    }
    {
      cbn in *.
      intros.
      eapply rel_interpretation0; eauto.
      eapply H2; eauto.
    }
  Qed.

  (* TODO: include output invariant in postcondition*)
  Lemma get_parents_sound pe a rs
    : state_triple (fun e => egraph_sound pe e rs)
        (get_parents idx symbol symbol_map idx_map idx_trie a)
        (fun p => egraph_sound pe (snd p) rs /\ all (fun a => atom_in_egraph a (snd p)) (fst p)).
  Proof.
    unfold get_parents,state_triple.
    destruct e; cbn;
      destruct 1 as [ [ [?  egraph_equiv_ok0] ] ].
    split.
    {
      constructor; [constructor; eauto |].
      intros m H; specialize (sound_egraph_for_model0 m H);
        destruct sound_egraph_for_model0 as [interp [] ].
      exists interp.
      constructor.
      {
        intros; eapply atom_interpretation0.
        destruct a0; cbn in *; eauto.
      }
      { cbn in *;  eauto. }
    }
    {
      unfold unwrap_with_default; case_match; cbn; eauto.
     (* TODO: parents invariant *)
   
  Admitted.

  (*TODO: move *)
  Lemma get_update_if_exists_same K V (mp : map.map K V) {H : map.ok mp} (m : mp) k f
    : map.get (map_update_if_exists m k f) k
      = option_map f (map.get m k).
  Proof.
    unfold map_update_if_exists.
    case_match; cbn; eauto.
    rewrite map.get_put_same; eauto.
  Qed.
    
  (*TODO: move *)
  Lemma get_update_if_exists_diff K V (mp : map.map K V) {H : map.ok mp} (m : mp) k k' f
    : k <> k' -> map.get (map_update_if_exists m k f) k'
                 = (map.get m k').
  Proof.
    unfold map_update_if_exists.
    intro.
    case_match; cbn; eauto.
    rewrite map.get_put_diff; eauto.
  Qed.
  
    
  (*TODO: move *)
  Lemma get_update_diff K V (mp : map.map K V) {H : map.ok mp} `{WithDefault V} (m : mp) k k' f
    : k <> k' -> map.get (map_update m k f) k'
                 = (map.get m k').
  Proof.
    unfold map_update.
    intro.
    case_match; cbn; eauto.
    all:rewrite map.get_put_diff; eauto.
  Qed.
  
  (*TODO: move *)
  Lemma get_update_same K V (mp : map.map K V) {H : map.ok mp} `{WithDefault V} (m : mp) k f
    : map.get (map_update m k f) k
      = Some match map.get m k with
          | Some x => f x
          | None => f default
          end.
  Proof.
    unfold map_update.
    case_match; cbn; eauto.
    all:rewrite map.get_put_same; eauto.
  Qed.

  (* TODO: move to Utils*)
  Lemma all_wkn A l (P Q : A -> Prop)
    : (forall x, In x l -> P x -> Q x) -> all P l -> all Q l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma atoms_functional a1 a2 e
    :  atom_in_egraph a1 e ->
       atom_in_egraph a2 e ->
       a1.(atom_fn) = a2.(atom_fn) ->
       a1.(atom_args) = a2.(atom_args) ->
       a1 = a2.
  Proof.
    clear idx_succ.
    unfold atom_in_egraph;
      destruct a1, a2;
      basic_goal_prep;
      subst.
    f_equal.
    repeat (match_some_satisfying; cbn; try tauto;[]).
    basic_goal_prep;
      subst.
    reflexivity.
  Qed.

  Lemma atom_in_egraph_excluded a e
    : atom_in_egraph a e \/ ~ atom_in_egraph a e.
  Proof.
    clear idx_succ.
    unfold atom_in_egraph.
    repeat (match_some_satisfying; cbn;[]).
    basic_goal_prep.
    eqb_case i0 (atom_ret a); intuition eauto.
  Qed.
  
  Lemma remove_node_sound exl a_fn a_args rs
    : inst_computation_sound exl ((a_fn,a_args)::exl)
        (remove_node idx symbol symbol_map idx_map idx_trie
                                a_fn a_args)
        rs.
  Proof.
    unfold remove_node, inst_computation_sound, state_triple.
    destruct e; cbn;
      destruct 1 as [ [ [?  egraph_equiv_ok0] ] ].
    constructor.
    {
      constructor.
      { eexists; apply egraph_equiv_ok0. }
      {
        cbn in *.
        intros.
        eapply egraph_parents_exist0 in H.
        eapply all_wkn; try eassumption.
        cbn.
        intros a' Hina'.
        intuition eauto.
        (*pose proof (atom_in_egraph_excluded a
                                          {|
                                            db := db;
                                            equiv := equiv;
                                            parents := parents;
                                            epoch := epoch;
                                            worklist := worklist
                                          |}) as Hor.*)
        {
          unfold atom_in_egraph in H1;
            unfold atom_in_egraph;
            basic_goal_prep;
            eauto.
          eqb_case a_fn a'.(atom_fn).
          2:{
            rewrite get_update_if_exists_diff;
              intuition eauto.
          }          
          repeat (match_some_satisfying; cbn;[]).
          basic_goal_prep; subst.
          rewrite get_update_if_exists_same; eauto.
          eqb_case a_args a'.(atom_args); cbn;
            rewrite Hsat; cbn.
          2:{
            rewrite map.get_remove_diff;
              intuition eauto.
            rewrite Hsat0; cbn; eauto.
          }
          {
            rewrite map.get_remove_same; cbn;
              intuition eauto.
            unfold excluded.
            right.
            eexists; cbn; intuition eauto.
          }
        }
        {
          right.
          unfold excluded in *;
            basic_goal_prep;
            eauto.
        }
      }
    }
    intros m H; specialize (sound_egraph_for_model0 m H);
      destruct sound_egraph_for_model0 as [interp [] ].
    exists interp.
    constructor.
    {
      unfold atom_in_egraph; cbn.
      intros a'.      
      eqb_case a_fn a'.(atom_fn).
      2:{
        rewrite get_update_if_exists_diff in *; eauto.
      }
      rewrite get_update_if_exists_same; cbn; eauto.
      eqb_case a_args a'.(atom_args).
      2:{
        intros.
        repeat (match_some_satisfying; cbn; []).
        basic_goal_prep;
           subst.        
        intros; eapply atom_interpretation0.
        unfold atom_in_egraph; cbn.
        destruct (map.get db (atom_fn a')) eqn:Hfn;
          cbn in *; try congruence.
        safe_invert Hsat.
        rewrite map.get_remove_diff in Hsat0; eauto.
        rewrite Hsat0; cbn.
        reflexivity.
      }
      {
        destruct (map.get db (atom_fn a')) eqn:Hfn;
          cbn in *; try tauto;[].
        rewrite map.get_remove_same; cbn; tauto.
      }
    }
    { cbn in *;  eauto. }
  Qed.

  Definition node_in_denotation m (idx_interpretation : idx -> option (domain m)) a :=
              (@! let p <- list_Mmap idx_interpretation (atom_args a) in
                  (interpretation m (atom_fn a) p)) <$>
                (fun d : domain m => idx_interpretation (atom_ret a) <$> m.(domain_eq) d).

  Record put_precondition exl_in a (rs : list (log_rule idx symbol)) (e : instance) : Prop :=
    {
      put_precondition_sound_egraph_ok : egraph_ok exl_in e;
      put_precondition_sound_egraph_for_model : forall m : model,
        model_of m rs ->
        exists interp : idx -> option (domain m),
          egraph_sound_for_model e m interp
          /\ node_in_denotation m interp a
    }.

  Lemma put_node_sound exl atom_f args out rs
    : state_triple (put_precondition exl (Build_atom atom_f args out) rs)
        (put_node idx symbol symbol_map idx_map idx_trie atom_f args out)
        (fun p => egraph_sound (removeb (eqb (A:=_)) (atom_f, args) exl)
                    (snd p) rs).
  Proof.
    unfold put_node, state_triple.
    destruct e; cbn;
      destruct 1 as [ [ [?  egraph_equiv_ok0] ] ].
    constructor.
    {
      constructor; cbn in *; eauto.
      intros i l Hi;
        eapply egraph_parents_exist0 in Hi.
      eapply all_wkn; try eassumption.
      clear Hi.
      cbn.
      unfold atom_in_egraph; cbn; intros; eauto.
      eqb_case atom_f x0.(atom_fn);
        basic_goal_prep; subst.
      2:{
        rewrite get_update_diff; intuition eauto.
        right; unfold excluded in *;
          basic_goal_prep;
          subst.
        unshelve econstructor; [ constructor; shelve|];
          cbn; intuition eauto.
        eapply remove_In_ne; eauto.
        congruence.
      }
      rewrite get_update_same; cbn; eauto.
      eqb_case args x0.(atom_args);
          basic_goal_prep; subst.
      2:{
        (intuition eauto).       
        2:{
          right; unfold excluded in *;
          basic_goal_prep;
          subst.
          unshelve econstructor; [ constructor; shelve|];
            cbn; intuition eauto.
          eapply remove_In_ne; eauto.
          congruence.
        }
        case_match; cbn in *; try tauto; [].    
        rewrite map.get_put_diff; eauto.
      }
      repeat (match_some_satisfying; cbn; try tauto;[]).
      
      clear H0; left.
      (*TODO: exclude list should include out since it needs to match parent list.
              Else, this proof won't go through
       *)
      (*
      Dual of prior problem
      case_match; cbn;
        rewrite map.get_put_same; cbn; eauto.
      repeat (match_some_satisfying; cbn; try tauto;[]).

        admit
          (*TODO: is this an implementation issue?.
        Should the parent list only be 2 elts, no ret val?.
        Makes more sense that way.
        On the other hand: need a returning remove op to make that make sense
           *).
      }
      {        
        eqb_case atom_f x0.(atom_fn);
          basic_goal_prep; subst.
        2:{
          rewrite get_update_diff; eauto.
          rewrite Hsat; cbn.
          rewrite Hsat0; cbn.
          left;reflexivity.
        }
        rewrite get_update_same; cbn; eauto.
        rewrite Hsat; cbn.
        eqb_case args x0.(atom_args);
          basic_goal_prep; subst.
        2:{
          rewrite map.get_put_diff; eauto.
          rewrite Hsat0; cbn.
          left;reflexivity.
        }
        right.
        unfold excluded in *;
          basic_goal_prep; subst.
        exists (atom_fn x0, atom_args x0);
          cbn;
          intuition eauto.
        TODO: not necessarily true
      }
    }
    [constructor; eauto |].
    {
    intros m H; specialize (put_precondition_sound_egraph_for_model0 m H);
      destruct put_precondition_sound_egraph_for_model0 as [interp [ [] ? ] ].
    unfold node_in_denotation in *.
    exists interp.
    constructor.
    {
      intros.
      eqb_case atom_f a.(atom_fn).
      2:{
        eapply atom_interpretation0.
        destruct a; cbn in *; eauto.
        rewrite get_update_diff in *; eauto.
      }
      eqb_case args a.(atom_args).

      {
        clear atom_interpretation0.
        destruct a; cbn in *; eauto.

        rewrite get_update_same in *; eauto.
        cbn in *.
        revert H0.
        case_match; cbn; eauto.
        revert H1; case_match;
        rewrite map.get_put_same;
          basic_goal_prep; subst; auto.
      }
      {
        apply atom_interpretation0. 
        destruct a; cbn in *; eauto.
        rewrite get_update_same in *;
          basic_goal_prep; subst; eauto.
        revert H1;
          case_match; cbn.
        all: rewrite map.get_put_diff; eauto.
        unfold default, map_default.
        rewrite map.get_empty.
        cbn; eauto.
      }
    }
    { cbn in *;  eauto. }
  Qed.
       *)
  Admitted.
    
  
  Lemma repair_sound a rs exl
    : inst_computation_sound exl exl
        (repair idx Eqb_idx symbol Eqb_symbol symbol_map idx_map idx_trie a) rs.
  Proof.
    unfold repair.
    eapply state_triple_bind; intros.
    (*TODO: does this lemma need a stronger postcondition?*)
    1:apply get_parents_sound.
    eapply state_triple_bind; intros.
    {
      (*TODO: get H from get_parents if needed
        TODO: need H to depend on the state
       *)
      eapply state_triple_list_Miter.
      {
        intros.
        destruct a1.
        eapply state_triple_bind; intros.
        (*TODO: how do I handle passing the 'all' through the 'remove'?*)
        (*
        1: apply remove_node_sound.
        
        eapply state_triple_bind with (Q:= fun p => egraph_sound (snd p) rs); intros.
        2:eapply state_triple_bind
          with (Q :=(fun p =>put_precondition
                               {| atom_fn := atom_fn; atom_args := a2; atom_ret := (fst p) |} rs (snd p)));
        unfold curry;
        intros;
        cbn [fst snd].
        
        3:eapply put_node_sound.
        2:{
          eapply state_triple_loosen;[ | | eapply find_sound]; cbn; eauto.
          basic_goal_prep.
          destruct H0.
          constructor; eauto.
          intros m H'; specialize (sound_egraph_for_model0 m H').
          break; eexists; split; eauto.
          destruct H0.
          specialize (atom_interpretation0
                        {| atom_fn := atom_fn; atom_args := a2; atom_ret := i |}).
          unfold node_in_denotation.
          cbn in *.

          (* TODO: in fact, this probably holds up to uf_rel (makes sense to be H)*)
          assert (a2 = atom_args) by admit; subst.
          eapply atom_interpretation0; clear atom_interpretation0.
          Ltac match_some_satisfying :=
            lazymatch goal with
              |- context ctx [?e <$> ?f] =>
                let Hsat := fresh "Hsat" in
                destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
            end.
          match_some_satisfying.
          2:admit (*TODO: rule out*).
          match_some_satisfying.
          2:admit (*TODO: rule out*).
          break; cbn.
          TODO: get info on r, i2
          TODO: show uf_rel rather than eq?
          eapply rel_interpretation0 in H1.
          
          destruct (map.get (db i0) atom_fn); cbn in *.
          TODO: need facts about a2, a1, atom_fn
          unshelve econstructor.
          1: eapply X; eauto.
          TODO: need to know what a2 and i are (related to H), apply H.
          unfold curry;intros.
          exact X.
        4:{
          unfold curry.
          intros.
          Unshelve.
          2: shelve.
          3: shelve.
          2:{ exact(fun p =>
                     put_precondition {| atom_fn := atom_fn; atom_args := a2; atom_ret := (fst p) |} rs (snd p)).
          exact X.
      {
        eapply state_triple_list_Mmap with (H:=fun x => True) (Q:= fun x => True); intros.
        2:admit.
        eapply state_triple_loosen;[ | | eapply find_sound with (rs := rs)].
        all:unfold curry; cbn; intuition auto.
      }
      unfold curry.
      cbn [fst snd].
      eapply state_triple_bind; intros.
      1: eapply state_triple_strengthen_pre;[ | eapply find_sound with (rs := rs)];
      basic_goal_prep; eauto.
      eapply state_triple_strengthen_pre;[ | eapply put_node_sound ].
      unfold put_precondition, curry; cbn; intuition auto.
      intros.

      
      apply inst_computation_sound_bind
        with (P := fun x => True). (*TODO: pick the right P*)
      2: eauto.
      {
        apply list_Mmap_sound.
        intro.
        apply find_sound.
      }
      intros.
      apply inst_computation_sound_bind
        with (P := fun x => True). (*TODO: pick the right P*)
      2: eauto.
      { apply find_sound. }
      intros.
              *)
  Abort.
  
  Lemma rebuild_sound exl n rs
    :  inst_computation_sound exl exl (rebuild n) rs.
  Proof.
    (*
    induction n.
    {
      unfold inst_computation_sound; cbn; eauto.
    }
    {
      cbn [rebuild].
      apply inst_computation_sound_bind
        with (P := fun x => True). (*TODO: pick the right P*)
      1: apply pull_worklist_sound.
      1: eauto.
      intros.
      destruct x;[ apply Mret_sound |].
      apply inst_computation_sound_bind
        with (P := fun x => True). (*TODO: pick the right P*)
      {
        apply list_Mmap_sound.
        intro.
        apply find_sound.
      }
      1: eauto.
      intros.
      apply inst_computation_sound_bind
        with (P := fun x => True); eauto.
      eapply list_Miter_sound.
      intros.
      TODO: repair_sound
      
    }
     *)
  Abort.
    

    
  Lemma run1iter_sound exl rs rs'
    : inst_computation_sound exl exl (run1iter rs') rs.
  Proof.
    unfold run1iter.
    (*
    apply inst_computation_sound_bind
      with (P := fun x => True). (*TODO: pick the right P*)
    2: eauto.
    {
      admit (*Lemma *).
    }
    {
      intros.
      apply inst_computation_sound_bind
        with (P := fun x => True).
      2: eauto.
      1:apply increment_epoch_sound.
      {
        intros.
        apply inst_computation_sound_bind
          with (P := fun x => True).
        2: eauto.
        1:admit (*Lemma *).
        {
          intros.
          admit (*Lemma *).
        }
      }
    }
  Qed.
     *)
    Admitted.
  
  Theorem saturation_sound e rs rs' P fuel b e'
    : inst_computation_sound [] [] P rs ->
      egraph_sound [] e rs ->
      (*TODO: relationship between compiled rs' and uncompiled rs? incl rs' rs ->*)
      saturate_until rs' P fuel e = (b, e') ->
      egraph_sound [] e' rs.
  Proof.
    intro HP.
    revert e.
    induction fuel;
      basic_goal_prep;
      basic_utils_crush;[].
    specialize (HP _ H).
    destruct (P e) as [ [ | ] ? ];
      basic_goal_prep;
      basic_utils_crush;
      subst.
    specialize (run1iter_sound [] rs rs' i).
    destruct (run1iter rs' i); cbn.
    eauto.
  Qed.

End WithMap.

Arguments atom_in_egraph {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  a i.

Arguments model_of {idx}%type_scope {Eqb_idx} {symbol}%type_scope m rw%list_scope.

Arguments assignment_satisfies {idx}%type_scope {Eqb_idx} {symbol}%type_scope 
  m assignment%list_scope _%list_scope.
Arguments assignment_unifies {idx}%type_scope {Eqb_idx} {symbol}%type_scope 
  m assignment%list_scope _%list_scope.
