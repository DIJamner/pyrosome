(* TODO: separate semantics and theorems
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


Definition If_Some_satisfying {A} (P : A -> Prop) x :=
  match x with
  | Some x => P x
  | None => True
  end.
Notation "x <?> P" :=
  (If_Some_satisfying P x)
    (at level 56,left associativity).


Ltac match_some_satisfying :=
  lazymatch goal with
  | H : ?e <$> ?f |- _ =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  | |- context ctx [?e <$> ?f] =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  | H : ?e <?> ?f |- _ =>
      let Hsat := fresh "Hsat" in
      destruct e eqn:Hsat; cbn [Is_Some_satisfying] in *; try tauto
  | |- context ctx [?e <?> ?f] =>
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
      (* wf_model conditions
         TODO: any reason to break these out?
       *)
      (* TODO: does it need to be an equivalence? *)
      domain_eq_PER : PER m.(domain_eq);
      interpretation_preserving
      : forall f args args' d,
        m.(interpretation) f args = Some d ->
        match m.(interpretation) f args' with
        | Some d' => m.(domain_eq) d d'
        | None => False
        end;
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

  

  Notation match_clause := (match_clause idx _).
  Notation match_clause' := (match_clause' idx _).

  (*TODO: duplicate. find other def and move to better location*)
  Fixpoint nat_to_idx n :=
    match n with
    | 0 => idx_zero
    | S n => idx_succ (nat_to_idx n)
    end.

  Definition assign_sub (assignment : list idx) :=
    combine (seq 0 (List.length assignment)) assignment.

  Fixpoint compatible_assignment pa a :=
    match pa, a with
    | [], _ => True
    | None::pa', _::a' => compatible_assignment pa' a'
    | (Some x)::pa', y::a' => x = (y : idx) /\ compatible_assignment pa' a'
    | _, _ => False
    end.
  
  (*TODO: how to describe a as smallest list?*)
  Definition assignment_correct l1 l2 a :=
      forall default,
      map (fun x => named_list_lookup default (assign_sub a) x) l1 = l2.
  
  (*TODO: how to describe as smallest list?*)
  Definition passignment_ex l1 l2 pa :=
    exists assignment,
      assignment_correct l1 l2 assignment
      /\ compatible_assignment pa assignment.
  
  Definition passignment_forall l1 l2 pa :=
    forall assignment,
      assignment_correct l1 l2 assignment ->
      compatible_assignment pa assignment.
  
  Lemma empty_passignment a
    : compatible_assignment [] a.
  Proof. exact I. Qed.

  
  Lemma match_clause'_complete cargs cv args v acc a
    : match_clause' cargs cv args v acc = None ->
      passignment_forall (cv::cargs) (v::args) acc ->
      forall default,
      map (fun x => named_list_lookup default (assign_sub a) x) (cv::cargs) <> (v::args).
  Proof.
    (*
    revert args acc a.induction cargs;
      destruct args;
      unfold passignment_forall,
      assignment_correct;
      basic_goal_prep;
      basic_utils_crush.
     *)
    Abort.
    
  (*TODO: too strong a statement.
    The passignment doesn't have to stay compatible in the case where there are no compatible assignments
   *)
  Lemma match_clause'_compat_preserving cargs cv args v acc passignment
    : match_clause' cargs cv args v acc = Some passignment ->
      passignment_ex (cv::cargs) (v::args) acc ->
      passignment_ex (cv::cargs) (v::args) passignment.
  Proof.
    revert args; induction cargs;
      destruct args;
      unfold passignment_forall,
      assignment_correct;
      basic_goal_prep;
      basic_utils_crush.
    { (*TODO: insert correctness *) shelve. }
    {
      revert H; case_match; try congruence.
      intros.

      (*
      Lemma insert_correct
        : Some l = insert idx Eqb_idx acc a i ->
          passignment_forall l1 l2 acc ->
          passignment_forall l1 l2 acc ->
          
    
  Lemma match_clause_correct default cargs cv args v assignment
    : let sub := assign_sub assignment in
      match_clause (cargs, cv) args v = Some assignment
      -> map (fun x => named_list_lookup default sub x) (cv::cargs)
         = v::args.
  Proof.*)
      Abort.
  
  Lemma match_clause_correct default cargs cv args v assignment
    : let sub := assign_sub assignment in
      match_clause (cargs, cv) args v = Some assignment
      -> map (fun x => named_list_lookup default sub x) (cv::cargs)
         = v::args.
  Proof.
    cbn -[map].
    case_match; cbn -[map]; try congruence.
    remember [] as acc.
    
    revert dependent l.
    revert args.
    (*
    symmetry in HeqH.
    eapply match_clause'_correct in HeqH.
    rewrite <- HeqH.
    intros.
    autorewrite with utils in *.
    subst.
    eapply map_ext.
    clear HeqH.
    intros.
    (*TODO: need assumption that r is dense
    cbn.
     *)
     *)
Abort.


  

  Notation instance := (instance idx symbol symbol_map idx_map idx_trie).
  (*TODO: many of these relations can be functions. what's the best way to define them?*)
  Definition atom_in_egraph a (i : instance) :=
    (map.get i.(db _ _ _ _ _) a.(atom_fn)) <$>
      (fun tbl => (map.get tbl a.(atom_args)) <$>
                    (fun r => snd r = a.(atom_ret))).

  (*
  (*Defined separately for proof convenience.
    Equivalent to a term using ~ atom_in_egraph
   *)
  Definition not_key_in_egraph a (i : instance) :=
    (map.get i.(db _ _ _ _ _) a.(atom_fn)) <?>
      (fun tbl => (map.get tbl a.(atom_args)) <?>
                    (fun r => False)).
  *)

  Definition SomeRel {A B} (R : A -> B -> Prop) ma mb :=
    match ma, mb with
    | Some a, Some b => R a b
    | _, _ => False
    end.

  Section ForModel.

    Context m (idx_interpretation : idx -> option m.(domain)).

    Definition atom_sound_for_model a :=      
      (Mbind (m.(interpretation) a.(atom_fn))
         (list_Mmap idx_interpretation a.(atom_args))) <$>
        (fun d => (idx_interpretation a.(atom_ret)) <$> (m.(domain_eq) d)).
    
    Record egraph_sound_for_model e : Prop :=
      {
        (*TODO: needed?
      idx_interpretation_in_domain
      : forall i d, idx_interpretation i = Some d ->
                  m.(domain_eq) d d;
         *)
        (* TODO: write in a more natural way*)
        atom_interpretation : forall a, atom_in_egraph a e -> atom_sound_for_model a;
        rel_interpretation :
        forall i1 i2,
          Is_Some (idx_interpretation i1) ->
          (*Is_Some (idx_interpretation i2) ->*)
          uf_rel _ _ _ e.(equiv _ _ _ _ _) i1 i2 ->
          SomeRel m.(domain_eq) (idx_interpretation i1) (idx_interpretation i2);      
        parents_interpretation :
        (* Parents do not have to exist in the egraph (and may not, during rebuilding)
           but they must be valid in the model or rebuilding is unsound.
         *)
        forall i l, map.get e.(parents) i = Some l -> all atom_sound_for_model l;
      }.

  End ForModel.

  (* TODO: is this record needed? other fields may not be necessary *)
  Record egraph_ok (e : instance) : Prop :=
    {
      egraph_equiv_ok : exists roots, forest _ _ roots (parent _ _ _ e.(equiv));
      (* TODO: not an invariant that parents exist?
           Can be broken in many places.
           What is the invariant?
           - that the parent could exist
       *)
    }.

  Record egraph_sound e rs : Prop :=
    {
      sound_egraph_ok :> egraph_ok e;
      sound_egraph_for_model :
      forall m : model,
        model_of m rs ->
        exists interp, egraph_sound_for_model m interp e;
    }.

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).

  Theorem empty_sound rs : egraph_sound (empty_egraph idx_zero) rs.
  Proof.
    unfold empty_egraph.
    constructor.
    { cbn; do 2 econstructor; apply empty_forest_rooted. }
    intros; exists (fun _ => None).
    constructor; cbn; try tauto;
      unfold atom_in_egraph;
      basic_goal_prep;
      rewrite map.get_empty in *;
      basic_goal_prep;
      try tauto;
      congruence.
  Qed.

  
  Notation saturate_until' := (saturate_until' idx_succ idx_zero spaced_list_intersect).
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

  
  Definition inst_computation_sound {A} (P : state instance A) rs :=
    state_triple (fun e => egraph_sound e rs) P
      (fun p => egraph_sound (snd p) rs).

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

  Lemma increment_epoch_sound rs
    : inst_computation_sound (increment_epoch idx idx_succ symbol symbol_map idx_map idx_trie) rs.
  Proof.
    unfold increment_epoch, inst_computation_sound, state_triple.
    destruct e; cbn; destruct 1; constructor.
    { destruct sound_egraph_ok0; constructor; unfold atom_in_egraph; cbn; eauto. }
    intros m H; specialize (sound_egraph_for_model0 m H); destruct sound_egraph_for_model0.
    exists x.
    destruct H0.
    constructor; eauto.
  Qed.

  Lemma pull_worklist_sound rs
    : inst_computation_sound (pull_worklist idx symbol symbol_map idx_map idx_trie) rs.
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

  
  Lemma state_triple_list_Mmap1 A B (f : A -> state instance B) l P
    : (forall l1 a l2, l = l1 ++ a::l2 -> state_triple (P (a::l2)) (f a) (fun p => P l2 (snd p))) ->
      state_triple (P l) (list_Mmap f l) (fun p => P [] (snd p)).
  Proof.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_goal_prep; subst.
      eauto.
    }
    {
      cbn [all list_Mmap]; intros; break.
      eapply state_triple_bind; eauto.
      {
        apply H with (l1:=[]).
        reflexivity.
      }
      {
        unfold curry.
        intro a0.
        eapply state_triple_bind; eauto.
        {
          apply IHl.
          intros.
          eapply H with (l1:=a::l1).
          cbn; congruence.
        }
        intro l'.
        eapply state_triple_wkn_ret.
        basic_goal_prep; eauto.
      }
    }
  Qed.

  (* TODO: loses some info about the provenance of fl1; ok? *)
  Lemma state_triple_list_Mmap2 A B (f : A -> state instance B) l Q fl
    : (forall fl1 a, In a l -> state_triple (Q fl1) (f a) (fun p => Q (fl1++[fst p]) (snd p))) ->
      state_triple (Q fl) (list_Mmap f l) (fun p => Q (fl++fst p) (snd p)).
  Proof.
    revert fl.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_utils_crush.
    }
    {
      cbn [all list_Mmap]; intros; break.
      eapply state_triple_bind; [basic_utils_crush |].
      unfold curry.
      intro b.
      eapply state_triple_bind; unfold curry.     
      { intros; cbn in *; eauto. }
      {
        intros.
        eapply state_triple_wkn_ret.
        basic_goal_prep; subst.
        rewrite <- app_assoc in H1.
        eauto.
      }
    }
  Qed.

  Lemma state_triple_conjunction A (c : state instance A) P1 P2 Q1 Q2
    : state_triple P1 c Q1 ->
      state_triple P2 c Q2 ->
      state_triple (fun e => P1 e /\ P2 e) c (fun e => Q1 e /\ Q2 e).
  Proof.
    unfold state_triple.
    intuition eauto.
  Qed.

  Lemma state_triple_list_Mmap' A B (f : A -> state instance B) l P fl
    : (forall fl1 l1 a l2, l = l1 ++ a::l2 ->
                           state_triple (fun e => P (a::l2) fl1 e)
                             (f a)
                             (fun p => P l2 (fl1++[fst p]) (snd p))) ->
      state_triple (fun e => P l fl e) (list_Mmap f l) (fun p => P [] (fl++fst p) (snd p)).
  Proof.
    revert fl.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_utils_crush.
    }
    {
      cbn [all list_Mmap]; intros; break.
      eapply state_triple_bind.
      { eapply H with (l1:=[]); eauto. }
      unfold curry.
      intro b.
      eapply state_triple_bind; unfold curry.     
      {
        intros; cbn in *.
        eapply IHl; intros.
        eapply H with (l1:=a::l1).
        cbn.
        congruence.
      }
      {
        intros.
        eapply state_triple_wkn_ret.
        basic_goal_prep; subst.
        rewrite <- app_assoc in *.
        eauto.
      }
    }
  Qed.

  
  Lemma state_triple_list_Mmap A B (f : A -> state instance B) l P
    : (forall fl1 l1 a l2, l = l1 ++ a::l2 ->
                           state_triple (fun e => P (a::l2) fl1 e)
                             (f a)
                             (fun p => P l2 (fl1++[fst p]) (snd p))) ->
      state_triple (fun e => P l [] e) (list_Mmap f l) (fun p => P [] (fst p) (snd p)).
  Proof. apply state_triple_list_Mmap'. Qed.    
  
  Lemma state_triple_list_Miter A (f : A -> state instance unit) l P
    : (forall l1 a l2, l = l1 ++ a::l2 -> state_triple (P (a::l2)) (f a) (fun p => P l2 (snd p))) ->
      (*all H l -> TODO: include in P*)
      state_triple (P l) (list_Miter f l) (fun p => P [] (snd p)).
  Proof.
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
      {
        apply H with (l1:=[]).
        reflexivity.
      }
      {
        unfold curry.
        destruct a0.
        (*
        eapply state_triple_bind; eauto.
        {
          apply IHl.
          intros.
          eapply H with (l1:=a::l1).
          cbn; congruence.
        }
        destruct a0.
        eapply state_triple_wkn_ret.
        basic_goal_prep; eauto.
      }
    }
  Qed.
         *)
  Admitted.
  
  Lemma state_triple_list_Miter_simple A (f : A -> state instance unit) l P
    : (forall a, In a l -> state_triple P (f a) (fun p => P (snd p))) ->
      state_triple P (list_Miter f l) (fun p => P (snd p)).
  Proof.
    intros.
    eapply state_triple_list_Miter with (P := fun _ => P).
    intros l1 a l2;
      specialize (H a).
    basic_goal_prep; subst; apply H.
    basic_utils_crush.
  Qed.

  (*
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
   *)

  
  Lemma find_sound (P : _ -> Prop) a
    : (forall e, P e -> exists l,
            forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) e.(equiv))) ->
      (forall db equiv equiv' parents epoch worklist l,
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv) ->
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv') ->
          iff2 (uf_rel _ _ _ equiv) (uf_rel _ _ _ equiv') ->
          P (Build_instance _ _ _ _ _ db equiv parents epoch worklist) ->
          (* TODO: how to express that the roots are the same?*)
          P (Build_instance _ _ _ _ _ db equiv' parents epoch worklist)) ->
      state_triple P
        (find idx Eqb_idx symbol symbol_map idx_map idx_trie a)
        (fun p => P (snd p) /\ uf_rel _ _ _ (snd p).(equiv) (fst p) a).
  Proof.
    intros Hforest Hequiv.
    unfold find, state_triple.
    destruct e; basic_goal_prep.
    case_match; basic_goal_prep.
    {
      symmetry in HeqH0.
      specialize (Hforest _ H).
      break.
      eapply find_spec in HeqH0; eauto.
      2:Lia.lia.
      {
        intuition eauto.
        {
          apply reachable_rel_Symmetric; eauto.
          apply H2; eauto.
        }
      }
    }
    {
      intuition eauto.
      eapply reachable_rel_Reflexive.
    }
  Qed.
    
  (*
  Lemma find_sound rs a
    : state_triple (fun e => egraph_sound e rs)
        (find idx Eqb_idx symbol symbol_map idx_map idx_trie a)
        (fun p => egraph_sound (snd p) rs /\ uf_rel _ _ _ (snd p).(equiv) (fst p) a).
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
    { constructor; cbn; [eexists; eauto]. }
    intros m Hm.
    specialize (sound_egraph_for_model0 m Hm).
    destruct sound_egraph_for_model0 as [ interp [] ];
      exists interp; constructor; basic_goal_prep.
    {
      eapply atom_interpretation0; 
        clear atom_interpretation0.
      destruct a0.
      cbn in *; eauto.
    }
    {
      eapply rel_interpretation0; eauto.
      eapply H2; eauto.
    }
    {
      eapply parents_interpretation0; eauto.
    }
  Qed.
   *)

  Record get_parents_postcondition (rs : list (log_rule idx symbol)) (p : list atom  * instance) : Prop :=
    {
      get_parents_postcondition_sound_egraph_ok : egraph_ok (snd p);
      get_parents_postcondition_sound_egraph_for_model : forall m : model,
        model_of m rs ->
        exists interp : idx -> option (domain m),
          egraph_sound_for_model m interp (snd p)
          /\ all (atom_sound_for_model m interp) (fst p)
    }.
  
  Lemma get_parents_sound a rs
    : state_triple (fun e => egraph_sound e rs)
        (get_parents idx symbol symbol_map idx_map idx_trie a)
        (get_parents_postcondition rs).
        (*(fun p => egraph_sound (snd p) rs /\ all (fun a => atom_in_egraph a (snd p)) (fst p)).*)
  Proof.
    unfold get_parents,state_triple.
    destruct e; cbn;
      destruct 1 as [ [ [?  egraph_equiv_ok0] ] ].
    split.
    { constructor; cbn; eauto. }
    {
      intros m Hm;
        specialize (sound_egraph_for_model0 _ Hm).
      destruct sound_egraph_for_model0 as [interp [] ].
      exists interp; cbn in *.
      constructor; [constructor; eauto |].
      unfold unwrap_with_default; case_match; cbn; eauto.
    }
  Qed.

  (*
  (*TODO: generalize this to an extensional description of what conditions it preserves?*)
  Lemma find_sound' l rs a
    : state_triple (fun e => get_parents_postcondition rs (l,e))
        (find idx Eqb_idx symbol symbol_map idx_map idx_trie a)
        (fun p => get_parents_postcondition rs (l, (snd p))
                  /\ uf_rel _ _ _ (snd p).(equiv) (fst p) a).
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
    destruct get_parents_postcondition_sound_egraph_ok0; break.
    eapply find_spec in HeqH; eauto; [| Lia.lia]; cbn in *; break.
    split;[| apply H2; eauto; eapply reachable_rel_Symmetric; eauto].
    constructor.
    { constructor; cbn; [eexists; eauto]. }
    intros m Hm.
    specialize (get_parents_postcondition_sound_egraph_for_model0 m Hm).
    destruct get_parents_postcondition_sound_egraph_for_model0 as [ interp [ [] ] ];
      exists interp; constructor; [constructor|]; basic_goal_prep; eauto.
    {
      eapply rel_interpretation0; eauto.
      eapply H2; eauto.
    }
  Qed.
   *)
    
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

  (*TODO: update
  Lemma remove_node_sound a_fn a_args rs l
    : state_triple (fun e => get_parents_postcondition rs (l,e))
        (remove_node idx symbol symbol_map idx_map idx_trie a_fn a_args)
        (fun p => get_parents_postcondition rs (l, (snd p))).
(*    inst_computation_sound (remove_node idx symbol symbol_map idx_map idx_trie a_fn a_args) rs.*)
  Proof.
    unfold inst_computation_sound, remove_node, state_triple.
    destruct e; cbn in *.
    destruct 1 as [ [ [?  egraph_equiv_ok0] ] ].
    cbn in *.
    constructor.
    { constructor; eexists; apply egraph_equiv_ok0. }
    {
      intros m H; specialize (get_parents_postcondition_sound_egraph_for_model0 m H);
        destruct get_parents_postcondition_sound_egraph_for_model0
        as [interp [ [] ?] ].
      exists interp.
      constructor; cbn in *; eauto.
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
      all: cbn in *; now eauto.
    }
  Qed.
   *)


  Record put_precondition a (rs : list (log_rule idx symbol)) (e : instance) : Prop :=
    {
      put_precondition_sound_egraph_ok : egraph_ok e;
      put_precondition_sound_egraph_for_model : forall m : model,
        model_of m rs ->
        exists interp : idx -> option (domain m),
          egraph_sound_for_model m interp e
          /\ atom_sound_for_model m interp a
    }.

  (*TODO: move to Defs*)
  Instance atom_eqb : Eqb atom :=
    fun a b =>
      (eqb a.(atom_fn) b.(atom_fn))
      && (eqb a.(atom_args) b.(atom_args))
      && (eqb a.(atom_ret) b.(atom_ret)).

  Instance atom_eqb_ok : Eqb_ok atom_eqb.
  Proof.
    intros [f a o] [f' a' o']; unfold eqb, atom_eqb; cbn.
    eqb_case f f'; cbn; try congruence.
    eqb_case a a'; cbn; try congruence.
    eqb_case o o'; cbn; try congruence.
  Qed.

  (*
  Lemma put_node_sound atom_f args out rs
    : state_triple (put_precondition (Build_atom atom_f args out) rs)
        (put_node idx symbol symbol_map idx_map idx_trie atom_f args out)
        (fun p => egraph_sound (snd p) rs).
  Proof.
    unfold put_node, state_triple.
    destruct e; cbn;
      destruct 1 as [ [ [?  egraph_equiv_ok0] ] ].
    constructor.
    { constructor; cbn in *; eauto. }
    {
      intros m Hm.
      specialize (put_precondition_sound_egraph_for_model0 m Hm).
      basic_goal_prep.
      exists x0.
      destruct H; constructor;
        basic_goal_prep; eauto.
      eqb_case atom_f (atom_fn a).
      2:{
        apply atom_interpretation0.
        unfold atom_in_egraph in *; basic_goal_prep; eauto.
        rewrite get_update_diff in *; intuition eauto.
      }
      eqb_case args (atom_args a).
      2:{
        apply atom_interpretation0.
        unfold atom_in_egraph in *; basic_goal_prep; eauto.
        rewrite get_update_same in *; basic_goal_prep; eauto.
        revert H; case_match; basic_goal_prep.
        all: rewrite ?map.get_put_diff in *; basic_goal_prep; subst; eauto.
        unfold default, map_default in *; rewrite map.get_empty in *; tauto.
      }
      unfold atom_in_egraph in *; basic_goal_prep; subst; eauto.
      rewrite get_update_same in *; basic_goal_prep; eauto.
      revert H; case_match; basic_goal_prep.
      all: rewrite ?map.get_put_same in *; basic_goal_prep; subst; eauto.
    }
  Qed.
   *)

  Lemma all2_iff2 A B (R1 R2 : A -> B -> Prop) l1 l2
    : iff2 R1 R2 ->
      all2 R1 l1 l2 ->
      all2 R2 l1 l2.
  Proof using.
    clear.
    unfold iff2;
      intro Hr.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
    firstorder.
  Qed.

  
  Lemma args_rel_interpretation m interp e
    : egraph_sound_for_model m interp e ->
      forall args1 args2,
        Is_Some (list_Mmap interp args1) ->
        all2 (uf_rel _ _ _ e.(equiv)) args1 args2 ->
        SomeRel (all2 m.(domain_eq)) (list_Mmap interp args1) (list_Mmap interp args2).
  Proof.
    destruct e,1; cbn in *.
    clear atom_interpretation0 parents_interpretation0.
    unfold SomeRel.
    induction args1;
      destruct args2;
      basic_goal_prep;
      try tauto.
    specialize (IHargs1 args2).
    case_match.
    2:{ basic_goal_prep; basic_utils_crush. }
    assert (Is_Some (interp a)) as HiaS.
    { unfold Is_Some; rewrite <- HeqH1; eauto. }
    eapply rel_interpretation0 in HiaS; intuition eauto.
    unfold SomeRel in HiaS.
    rewrite <- HeqH1 in *.
    revert HiaS; case_match; try tauto.
    case_match; basic_goal_prep; basic_utils_crush.
    case_match; basic_goal_prep; basic_utils_crush.
  Qed.

  (*TODO: update
  Lemma put_node_sound fn args out a0 rs a2 a3
    : In {| atom_fn := fn; atom_args := args; atom_ret := out |} a0 ->
      state_triple
        (fun y : instance =>
           (get_parents_postcondition rs (a0, y) /\
              all2 (uf_rel idx (idx_map idx) (idx_map nat) (equiv y)) args a2) /\
             uf_rel idx (idx_map idx) (idx_map nat) (equiv y) a3 out)
        (put_node idx symbol symbol_map idx_map idx_trie fn a2 a3)
        (fun p : unit * instance => get_parents_postcondition rs (a0, snd p)).
  Proof.
    unfold state_triple, put_node; cbn.
    destruct e;
      destruct 1 as [ [ [ [ [roots ?] ] ] ] ?]; cbn in *.
    repeat (constructor; cbn; eauto).
    intros m Hm; specialize (get_parents_postcondition_sound_egraph_for_model0 _ Hm).
    
    destruct get_parents_postcondition_sound_egraph_for_model0
      as [ interp [ Hmodel ?] ].
    pose proof (args_rel_interpretation _ _ _ Hmodel) as Hargsrel.
    destruct Hmodel.
    exists interp; repeat (constructor; cbn in *; eauto).
    intros a' Hain.
    unfold atom_in_egraph in *; cbn in *.
    eqb_case fn a'.(atom_fn).
    2:{ rewrite get_update_diff in *; eauto. }
    rewrite get_update_same in *; eauto.
    eqb_case a2 a'.(atom_args).
    2:{
      specialize (atom_interpretation0 a').
      revert Hain; case_match; cbn in *.
      all: rewrite map.get_put_diff; cbn in *; eauto.
      unfold default, map_default; rewrite map.get_empty; eauto.
    }
    eapply in_all in H; eauto.
    pose proof (atom_interpretation0 a').
    unfold atom_sound_for_model in *.
    cbn in *.

    revert H; case_match; cbn; try tauto.
    assert (Is_Some (list_Mmap interp args)) as HargsS.
    { rewrite <- HeqH; cbn; eauto. }
    eapply Hargsrel in HargsS; eauto.
    unfold SomeRel in HargsS.
    rewrite <- HeqH in *.
    revert HargsS; case_match; try tauto; intro HargsS.
    destruct (interpretation m (atom_fn a') l) eqn:Hinterpl;
      cbn; try tauto.
    eapply interpretation_preserving with (args':=l0) in Hinterpl; eauto.
    revert Hinterpl; case_match; cbn; try tauto.
    intros.
    cbn in*.
    revert Hain.
    case_match; rewrite map.get_put_same;
      cbn in *;
      intros; subst.
    all:eapply reachable_rel_Symmetric in H2.
    all:eapply rel_interpretation0 in H2.
    all: unfold Is_Some.
    all: destruct (interp out) eqn:Hout; cbn in *; try tauto.
    all:  match_some_satisfying ; basic_goal_prep; try tauto.
    all: eapply PER_Transitive; try eassumption.
    all: eapply PER_Transitive; try eassumption.
    all: eapply PER_Symmetric; try eassumption.
    Unshelve.
    all: eapply domain_eq_PER; eauto.
  Qed.
*)

  
  Definition atom_rel (equiv : union_find idx (idx_map idx) (idx_map nat)) (a1 a2 : atom) : Prop :=
    a1.(atom_fn) = a2.(atom_fn)
    /\ all2 (uf_rel _ _ _ equiv) a1.(atom_args) a2.(atom_args)
    /\ uf_rel _ _ _ equiv a1.(atom_ret) a2.(atom_ret).

  Lemma atom_rel_refl equiv : Reflexive (atom_rel equiv).
  Proof using.
    clear idx_succ idx_zero.
    unfold atom_rel.
    intro a; destruct a; cbn; intuition eauto.
    1:eapply all2_refl.
    all: apply reachable_rel_Reflexive.
  Qed.
  
  Lemma atom_rel_sym equiv : Symmetric (atom_rel equiv).
  Proof using.
    clear idx_succ idx_zero.
    unfold atom_rel.
    intros a b; destruct a, b; cbn; intuition eauto.
    1:eapply all2_Symmetric.
    all: try apply reachable_rel_Symmetric; eauto.
  Qed.
  
  Lemma canonicalize_sound (P : _ -> Prop) a
    : (forall e, P e -> exists l,
            forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) e.(equiv))) ->
      (forall db equiv equiv' parents epoch worklist l,
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv) ->
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv') ->
          iff2 (uf_rel _ _ _ equiv) (uf_rel _ _ _ equiv') ->
          P (Build_instance _ _ _ _ _ db equiv parents epoch worklist) ->
          (* TODO: how to express that the roots are the same?*)
          P (Build_instance _ _ _ _ _ db equiv' parents epoch worklist)) ->
      state_triple P
        (canonicalize idx Eqb_idx symbol symbol_map idx_map idx_trie a)
        (fun p => P (snd p) /\ atom_rel (snd p).(equiv) (fst p) a).
  Proof.
    intros Hforest Hequiv.
    unfold canonicalize.
    destruct a.
    eapply state_triple_bind; intros.
    {
      eapply state_triple_strengthen_pre;
        [ |eapply state_triple_list_Mmap
        with 
        (P := fun atom_args_out atom_args' e =>
                P e /\ all2 (uf_rel _ _ _ e.(equiv)) atom_args (atom_args' ++ atom_args_out))].
      { basic_goal_prep; intuition eauto using all2_refl, reachable_rel_Reflexive. }        
      {
        intros; subst.
         eapply state_triple_wkn_post;
           [ |eapply find_sound]; basic_goal_prep; intuition eauto.
         {
           rewrite <- app_assoc; cbn.
           apply all2_app_shared_tail in H1; eauto using reachable_rel_Reflexive.
           eapply all2_app; cbn;
             intuition eauto using all2_refl, reachable_rel_Reflexive.
           apply reachable_rel_Symmetric; eauto.
         }
         { eapply all2_iff2; eauto. }
      }
    }
    unfold curry; cbn [fst snd].
    eapply state_triple_bind; intros.
    {
      eapply find_sound; basic_goal_prep; intuition eauto.
      eapply all2_iff2; eauto.
    }
    unfold curry; cbn [fst snd].
    eapply state_triple_wkn_ret;
      basic_goal_prep;
      subst;
      intuition eauto.
    unfold atom_rel;
      basic_goal_prep;
      subst;
      intuition eauto.
    eapply all2_Symmetric; eauto using reachable_rel_Symmetric.
    basic_utils_crush.
  Qed.

  
  Lemma get_parents_postcondition_equiv_update db equiv equiv' parents epoch worklist l rs roots
    : forest idx (idx_map idx) roots (parent idx (idx_map idx) (idx_map nat) equiv) ->
      forest idx (idx_map idx) roots (parent idx (idx_map idx) (idx_map nat) equiv') ->
      iff2 (uf_rel idx (idx_map idx) (idx_map nat) equiv)
        (uf_rel idx (idx_map idx) (idx_map nat) equiv') ->
      get_parents_postcondition rs (l,
          {| db := db; equiv := equiv; parents := parents; epoch := epoch; worklist := worklist |}) ->
      get_parents_postcondition rs
        (l, {| db := db; equiv := equiv'; parents := parents; epoch := epoch; worklist := worklist |}).
  Proof.
    clear idx_zero idx_succ.
    destruct 4 as [ [ ] ?]; cbn in *.
    repeat (constructor; cbn; eauto).
    intros m Hm.
    specialize (get_parents_postcondition_sound_egraph_for_model0 _ Hm).
    basic_goal_prep.
    exists x.
    intuition eauto.
    destruct H2; constructor; cbn in *; eauto.
    intros; eapply rel_interpretation0; eauto.
    eapply H1; eauto.
  Qed.

  
  Lemma iff2_atom_rel equiv equiv'
    : iff2 (uf_rel idx (idx_map idx) (idx_map nat) equiv)
        (uf_rel idx (idx_map idx) (idx_map nat) equiv') ->
      iff2 (atom_rel equiv) (atom_rel equiv').
  Proof.
    clear idx_zero idx_succ.
    unfold atom_rel.
    intros Huf [] [];
      basic_goal_prep;
      intuition eauto.
    all: try eapply all2_iff2; try eassumption.
    all: try eapply Huf; eauto.
    unfold iff2 in *; firstorder.
  Qed.
  
  Lemma state_triple_list_Mfoldl A B f l P acc
    : (forall (acc : B) (l1 : list A) (a : A) (l2 : list A),
          l = l1 ++ a :: l2 ->
          state_triple
            (fun e : instance => P (a :: l2) acc e)
            (f acc a)
            (fun p => P l2 (fst p) (snd p))) ->
      state_triple (fun e => P l acc e) (list_Mfoldl f l acc)
        (fun p => P [] (fst p) (snd p)).
  Proof.
    revert acc.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_utils_crush.
    }
    {
      cbn [all list_Mfoldl]; intros; break.
      eapply state_triple_bind.
      { eapply H with (l1:=[]); eauto. }
      unfold curry.
      intro b.
      cbn.
      eapply IHl;
        basic_goal_prep.
      eapply H with (l1:= a::l1).
      basic_utils_crush.
    }
  Qed.
    
  
  Lemma repair_sound a rs
    : inst_computation_sound (repair idx Eqb_idx symbol Eqb_symbol symbol_map idx_map idx_trie a) rs.
  Proof.
    (*TODO: update
    unfold repair.
    eapply state_triple_bind; intros.
    (*TODO: does this lemma need a stronger postcondition?*)
    1:apply get_parents_sound.
    eapply state_triple_bind; intros.
    {
      (*TODO: get H from get_parents if needed
        TODO: need H to depend on the state

        TODO: need a in assumption to be in a0
       *)
      eapply state_triple_list_Miter_simple.
      {
        destruct a1; intro Hin.
        eapply state_triple_bind; intros.
        {
          unfold curry; cbn.
          (* TODO: fix proof
          eapply state_triple_strengthen_pre;[| apply remove_node_sound with (rs:=rs)].
          intros i []; basic_goal_prep.
          constructor; eauto.
          (*
          intros m Hm;
            specialize (get_parents_postcondition_sound_egraph_for_model0 _ Hm).
          break.
          exists x.
          intuition eauto. *)
        }
        unfold curry; cbn beta.
        eapply state_triple_bind; intros; cbn [fst snd].
        1: eapply state_triple_loosen;
        [ | |eapply state_triple_list_Mmap
        with 
        (P := fun  atom_args_out atom_args' e =>
                get_parents_postcondition rs (a0, e)
                /\ all2 (uf_rel _ _ _ e.(equiv)) atom_args (atom_args' ++ atom_args_out))].
        { exact (fun p H => H). }
        {
          intros i [ [ [roots ?] ] ?].
          cbn in *.
          unfold uf_rel.
          split; [repeat constructor |];eauto.
          basic_utils_crush.
          eapply all2_refl; apply reachable_rel_Reflexive.
        }
        {
          intros; subst.
          eapply state_triple_wkn_post;[| apply find_sound];
            basic_goal_prep;
            rewrite <- ?app_assoc; cbn;
            basic_utils_crush.
          {
            apply all2_app_shared_tail in H1;[| apply reachable_rel_Reflexive].
            apply all2_app; eauto.
            cbn; split;
              [ apply reachable_rel_Symmetric; eauto
              | eapply all2_refl; apply reachable_rel_Reflexive].
          }
          {
            destruct H as [ [ [roots ?] ] ?].
            exists roots; eauto.
          }
          {
            (*TODO: lemma?*)            
            destruct H2 as [ [ [roots ?] ] ?]; cbn in *.
            repeat (constructor; cbn; eauto).
            intros m Hm.
            specialize (get_parents_postcondition_sound_egraph_for_model0 _ Hm).
            basic_goal_prep.
            exists x.
            intuition eauto.
            destruct H4; constructor; cbn in *; eauto.
            intros; eapply rel_interpretation0; eauto.
            eapply H1; eauto.
          }              
          {
            eapply all2_iff2; eauto.
          }
        }
        {
          unfold curry; cbn beta.
          eapply state_triple_bind; intros; cbn [fst snd].
          {
            autorewrite with utils.
            (*TODO: copied; deduplicate*)
            apply find_sound;
              basic_goal_prep;
              rewrite <- ?app_assoc; cbn;
              basic_utils_crush.
            {
              destruct H as [ [ [roots ?] ] ?].
              exists roots; eauto.
            }
            { eapply get_parents_postcondition_equiv_update; cycle 2; eauto. }
            {
              eapply all2_iff2; eauto.
            }
          }
          {
            unfold curry; cbn [fst snd].
            eapply put_node_sound; eauto.
          }
        }
      }
    }
    {
      unfold curry.
      eapply state_triple_bind; intros; cbn [fst snd].
      {
        eapply state_triple_strengthen_pre;
        [ |eapply state_triple_list_Mmap
        with 
        (P := fun atom_args_out atom_args' e =>
                get_parents_postcondition rs (a0, e)
                /\ all2 (atom_rel e.(equiv)) a0 (atom_args' ++ atom_args_out))].
        {
          cbn.
          intuition eauto using all2_refl, atom_rel_refl.
        }
        {
          intros; subst.
          eapply state_triple_wkn_post;
            [|eapply canonicalize_sound];
            basic_goal_prep;
            rewrite <- ? app_assoc;
            basic_goal_prep;
            intuition eauto.
          {
            apply all2_app_shared_tail in H1; eauto using atom_rel_refl.
            eapply all2_app; cbn;
             intuition eauto using all2_refl, atom_rel_refl.
            apply atom_rel_sym; eauto.
          }
          { destruct H as [ [] _]; eauto. }
          { eapply get_parents_postcondition_equiv_update; cycle 2; eauto. }
          { eapply all2_iff2; eauto using iff2_atom_rel. }
        }
      }
      unfold curry.
      eapply state_triple_bind; intros; cbn [fst snd].
      {
        eapply state_triple_strengthen_pre.
        {
          intros i H.
          destruct H as [ H' _].
          replace a0 with (a0++[]) in H' by basic_utils_crush.
          apply H'.
        }
        clear a2.
        (*TODO: right condition for add_parent?
          all2 is dead, since it uses set-like lists, doesn't guarantee order or multiplicity.
          TODO: ?Q scope issues?
         *)
        (*
        eapply state_triple_list_Mfoldl
          with
          (l := a0)
          (P:= fun acc l e =>
                      get_parents_postcondition rs (acc++l, e)).
           *)
           *)
           *)
  Abort.
  
  Lemma rebuild_sound n rs
    :  inst_computation_sound (rebuild n) rs.
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
    
(*
    
  Lemma run1iter_sound rs rs' n
    : inst_computation_sound (run1iter rs' n) rs.
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
*)
  (*
  Theorem saturation'_sound e rs rs' P fuel rebuild_fuel b e'
    : inst_computation_sound P rs ->
      egraph_sound e rs ->
      (*TODO: relationship between compiled rs' and uncompiled rs? incl rs' rs ->*)
      saturate_until' rs' P fuel rebuild_fuel e = (b, e') ->
      egraph_sound e' rs.
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
    specialize (run1iter_sound rs rs' rebuild_fuel i).
    destruct (run1iter rs' rebuild_fuel i); cbn.
    eauto.
  Qed.
*)

End WithMap.

Arguments atom_in_egraph {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  a i.

Arguments model_of {idx}%type_scope {Eqb_idx} {symbol}%type_scope m rw%list_scope.

Arguments assignment_satisfies {idx}%type_scope {Eqb_idx} {symbol}%type_scope 
  m assignment%list_scope _%list_scope.
Arguments assignment_unifies {idx}%type_scope {Eqb_idx} {symbol}%type_scope 
  m assignment%list_scope _%list_scope.
