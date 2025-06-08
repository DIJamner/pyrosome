(* TODO: separate semantics and theorems
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind.
From Utils.EGraph Require Import Defs.
From Utils Require TrieMap.
Import Sets.
Import StateMonad.


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
      (idx_zero : WithDefault idx)
      (*TODO: any reason to have separate from idx?*)
      (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol).

  Existing Instance idx_zero.

  Notation atom := (atom idx symbol).

  (*TODO: really should just assign a name to eq.
    Long term, eq shouldn't be special.
   *)
  Variant clause := eq_clause (x y : idx) | atom_clause (a:atom).

  Definition clause_vars c :=
    match c with
    | eq_clause x y => [x;y]
    | atom_clause a =>
        a.(atom_ret)::a.(atom_args)
    end.

  (* Represents a logical sequent of the form
     x1,...,xn, P1, ... , Pn |- y1,...,yn, Q1, ... , Qn
     or alternately
     forall x1...xn, P1 /\ ... /\ Pn -> exists y1...yn, Q1 /\ ... /\ Qn

     TODO: leave vars as components or infer?
   *)
  Record sequent : Type :=
    {
      (*forall_vars : list idx;*)
      seq_assumptions : list clause;
      (* exist_vars : list idx *)
      seq_conclusions : list clause;
    }.

  Definition forall_vars (s : sequent) := flat_map clause_vars s.(seq_assumptions).
  Definition exists_vars (s : sequent) :=
    filter (fun x => negb (inb x (forall_vars s)))
      (flat_map clause_vars s.(seq_conclusions)).

  Definition sequent_vars s :=
    (flat_map clause_vars (s.(seq_assumptions)++s.(seq_conclusions))).
    

  Definition atom_subst (sub : named_list idx idx) (a : atom) :=
    Build_atom
      a.(atom_fn)
      (map (fun x => named_list_lookup x sub x) a.(atom_args))
      (named_list_lookup a.(atom_ret) sub a.(atom_ret)).

  (*
    TODO: is there a straightforward SMT encoding of these logical expressions?

    Preamble:
    declare an unknown type T
    declare each function symbol as an uninterpreted function of the approriate arity,
    from Ts to T

    translate clauses to expressions as follows:
    (= x y) ~> (= x y)
    (f x1...xn -> y) ~> (= (f x1 ... xn) y)

    for each sequent, generate:
    (assert (forall x1...xn, (and |P1| ... |Pn|) => exist y1...yn, (and |Q1|..|Qn|)))


    Should be able to do type checking, inference, equations, etc.

    Issue: is this correct? SMT might assume decidable equality

   *)

  
  (* clause lists are isomorphic to DBs/egraphs,
     up to some egraph state

   *)
  Section AsInstance.

  Context (symbol_map : forall A, map.map symbol A)
        (symbol_map_plus : map_plus symbol_map).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_plus : map_plus idx_trie)
        (analysis_result : Type)
        `{analysis idx symbol analysis_result}.

    
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie analysis_result).

  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).

  
  Notation alloc :=
    (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result).
  
  Definition rename_lookup (x : idx) : stateT (named_list idx idx) (state instance) idx :=
    fun sub =>
      match named_list_lookup_err sub x with
      | Some y => Mret (y, sub)
      | None => @! let y <- alloc in
                  ret (y, (x,y)::sub)
      end.

  Definition rename_atom (a : atom) : stateT (named_list idx idx) (state instance) atom :=
    let (f, args, out) := a in
    @! let args' <- list_Mmap rename_lookup args in
      let out' <- rename_lookup out in
      ret Build_atom f args' out'.

  (*TODO: output type? should be unit, but doesn't really matter *)
  Definition add_clause_to_instance c
    : stateT (named_list idx idx) (state instance) unit :=
    match c with
    | eq_clause x y =>
        @! let x' <- rename_lookup x in
          let y' <- rename_lookup y in
          (Mseq (lift (Defs.union x' y')) (Mret tt))
    | atom_clause a =>
        @! let a' <- rename_atom a in
        (lift (update_entry a'))
    end.

  Definition clauses_to_instance := list_Miter add_clause_to_instance.

  Definition uf_to_clauses (u : union_find) :=
    map (uncurry eq_clause) (map.tuples u.(parent _ _ _)).


  Definition row_to_atom f (p : list idx * db_entry idx analysis_result) : atom :=
    let '(k,e) := p in
    Build_atom f k e.(entry_value _ _).
  
  Definition table_atoms '(f,tbl) : list atom :=
    map (row_to_atom f) (map.tuples tbl).
  
  Definition db_to_atoms (d : db_map idx symbol symbol_map idx_trie analysis_result) :=
    (flat_map table_atoms (map.tuples d)).
  
  Definition instance_to_clauses i :=
    (uf_to_clauses i.(equiv)) ++ (map atom_clause (db_to_atoms i.(db))).

  (* Note: instance_to_clauses and clauses_to_instance
     are intended to be isomorphic up to egraph bookkeeping
   *)
  
  End AsInstance.

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
      domain_wf x := domain_eq x x;
      (*constants : idx -> domain; TODO: do I have any constants? *)
      interpretation : symbol -> list domain -> option domain;
      interprets_to f args d := exists d', interpretation f args = Some d' /\ domain_eq d' d;
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

  
  Section ForModel.

    Context m (idx_interpretation : idx_map m.(domain)).

    Definition atom_sound_for_model a :=
      (list_Mmap (map.get idx_interpretation) a.(atom_args)) <$> (fun args =>
      (map.get idx_interpretation a.(atom_ret)) <$> (fun out =>      
      m.(interprets_to) a.(atom_fn) args out)).
  
  Definition eq_sound_for_model x y : Prop :=
    map.get idx_interpretation x <$> (fun x' =>
    (map.get idx_interpretation y) <$>
      (m.(domain_eq) x')).

   Definition clause_sound_for_model (c : clause) : Prop :=
    match c with
    | eq_clause x y => eq_sound_for_model x y
    | atom_clause a => atom_sound_for_model a
    end.

  End ForModel.

  Definition model_satisfies_rule m r :=
    forall query_assignment,
      set_eq (map.keys query_assignment) (forall_vars r) ->
      all (clause_sound_for_model m query_assignment) r.(seq_assumptions) ->
      exists out_assignment,
        map.extends out_assignment query_assignment
        /\ all (clause_sound_for_model m out_assignment)
          r.(seq_conclusions).
  
  Record model_of
    (m : model)
    (rw : list sequent) : Prop :=
    {
      (* wf_model conditions
         TODO: any reason to break these out?
       *)
      (* TODO: does it need to be an equivalence? *)
      domain_eq_PER : PER m.(domain_eq);
      interpretation_preserving
      : forall f args args' d d',
        all2 m.(domain_eq) args args' ->
        m.(interprets_to) f args d ->
        m.(interprets_to) f args' d' ->
        m.(domain_eq) d d';
      (* model_of conditions *)
      rules_sound : all (model_satisfies_rule m) rw;
    }.
  

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


  
  Context (analysis_result : Type).

  Notation instance :=
    (instance idx symbol symbol_map idx_map idx_trie analysis_result).
  (*TODO: many of these relations can be functions. what's the best way to define them?*)
  
  Definition atom_in_egraph a (i : instance) :=
    (map.get i.(db) a.(atom_fn)) <$>
      (fun tbl => (map.get tbl a.(atom_args)) <$>
                    (fun r => r.(entry_value _ _) = a.(atom_ret))).

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
    ma <$> (fun x => mb <$> (R x)).
  
  Inductive le (n : idx) : idx -> Prop :=
    le_n : le n n | le_S : forall m, le n m -> le n (idx_succ m).

  Section ForModel.

    Context m (idx_interpretation : idx_map m.(domain)).

    Local Notation atom_sound_for_model :=
      (atom_sound_for_model m idx_interpretation).

    Definition worklist_entry_sound e :=
      match e with
      | union_repair _ old_idx new_idx improved_new_analysis =>
          eq_sound_for_model m idx_interpretation old_idx new_idx
      | analysis_repair _ i => True (* these don't affect soundness of the egraph *)
      end.
    
    Record egraph_sound_for_interpretation e : Prop :=
      {
        idx_interpretation_wf : forall i d, map.get idx_interpretation i = Some d -> m.(domain_wf) d;
        (*TODO: rather than functions, should I just use a finite map here?*)
        interpretation_bounded : forall i, le e.(equiv).(next _ _ _) i ->
                                           map.get idx_interpretation i = None;
        atom_interpretation : forall a, atom_in_egraph a e -> atom_sound_for_model a;
        rel_interpretation :
        forall i1 i2,
          (* TODO: should every index be required to map to a domain value?
             (e.g. to allow flexibility when initially allocating them)
           *)
          uf_rel_PER _ _ _ e.(equiv) i1 i2 ->
          eq_sound_for_model m idx_interpretation i1 i2;
        parents_interpretation :
        (* Parents do not have to exist in the egraph (and may not, during rebuilding)
           but they must be valid in the model or rebuilding is unsound.
         *)
        forall i l, map.get e.(parents) i = Some l -> all atom_sound_for_model l;
        worklist_sound : all worklist_entry_sound e.(worklist)
      }.

  End ForModel.

  (* TODO: is exists right?
     Possibly: f is probably sufficiently unique up to equivalence
   *)
  Definition egraph_sound_for_model m e : Prop :=
    exists f, egraph_sound_for_interpretation m f e.

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

  Record egraph_sound e m : Prop :=
    {
      sound_egraph_ok :> egraph_ok e;
      sound_egraph_for_model : egraph_sound_for_model m e;
    }.

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).


  Hint Rewrite @map.get_empty : utils.

  (*
  Lemma PER_empty (j k : idx)
    : reachable_plus map.empty j k <-> False.
  Proof.
    unfold reachable_plus.
    intuition (subst; eauto with utils).
    induction H;
      basic_goal_prep;
      basic_utils_crush.
    all: 
      basic_utils_crush.
  Qed.
  Hint Rewrite reachable_empty : utils.
   *)
  
  Lemma PER_empty A (a b : A) R 
    : (forall a b, ~ R a b) -> ~ PER_closure R a b.
  Proof.
    intros ? ?.
    induction H0;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Theorem empty_sound m : egraph_sound (empty_egraph idx_zero analysis_result) m.
  Proof.
    unfold empty_egraph.
    constructor.
    { cbn; do 2 econstructor; apply empty_forest_rooted. }
    intros; exists map.empty.
    constructor; cbn; try tauto;
      unfold atom_in_egraph;
      basic_goal_prep;
      rewrite ? map.get_empty in *;
      basic_goal_prep;
      try tauto;
      try congruence.
    exfalso.
    unfold uf_rel_PER in *.
    cbn in *.
    eapply PER_empty; cycle 1; eauto.
    basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Theorem empty_sound_for_interpretation m
    (*: egraph_sound (empty_egraph idx_zero analysis_result) m.*)
    : egraph_sound_for_interpretation m map.empty (empty_egraph idx_zero _).
  Proof.
    constructor; cbn; try tauto;
      unfold atom_in_egraph;
      basic_goal_prep;
      rewrite ? map.get_empty in *;
      basic_goal_prep;
      try tauto;
      try congruence.
    {
      exfalso; eapply PER_empty; try eassumption.
      basic_goal_prep;
        basic_utils_crush.
    }
  Qed.

  
  Notation saturate_until' := (saturate_until' idx_succ idx_zero spaced_list_intersect).
  Notation saturate_until := (saturate_until idx_succ idx_zero spaced_list_intersect).

  Notation run1iter :=
    (run1iter idx Eqb_idx idx_succ idx_zero symbol Eqb_symbol symbol_map symbol_map_plus
       idx_map idx_map_plus idx_trie spaced_list_intersect).
  (*
  Notation rebuild := (rebuild idx Eqb_idx symbol Eqb_symbol symbol_map idx_map idx_trie).
  *)

  (*TODO: include the egraph soundness at all?
    If no, move to Monad
   *)

  
  Definition inst_computation_sound {A} (P : state instance A) rs :=
    state_triple (fun e => egraph_sound e rs) P
      (fun p => egraph_sound (snd p) rs).


  Lemma increment_epoch_sound m
    : inst_computation_sound (increment_epoch idx idx_succ symbol symbol_map idx_map idx_trie analysis_result) m.
  Proof.
    unfold increment_epoch, inst_computation_sound, state_triple.
    destruct e; cbn; destruct 1; constructor.
    { destruct sound_egraph_ok0; constructor; unfold atom_in_egraph; cbn; eauto. }
    destruct sound_egraph_for_model0.
    exists x.
    destruct H.
    constructor; eauto.
  Qed.

  Lemma pull_worklist_sound_deprecated rs
    : inst_computation_sound (pull_worklist idx symbol symbol_map idx_map idx_trie analysis_result) rs.
  Proof.
    unfold pull_worklist, inst_computation_sound, state_triple.
    destruct e; cbn; destruct 1; constructor.
    { destruct sound_egraph_ok0; constructor; eauto. }
    destruct sound_egraph_for_model0.
    exists x.
    destruct H.
    constructor; cbn; eauto.
  Qed.

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

  
  Lemma find_sound_deprecated (P : _ -> Prop) a
    : (forall e, P e -> exists l,
            forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) e.(equiv))) ->
      (forall db equiv equiv' parents epoch worklist analyses l,
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv) ->
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv') ->
          iff2 (uf_rel _ _ _ equiv) (uf_rel _ _ _ equiv') ->
          P (Build_instance _ _ _ _ _ _ db equiv parents epoch worklist analyses) ->
          (* TODO: how to express that the roots are the same?*)
          P (Build_instance _ _ _ _ _ _ db equiv' parents epoch worklist analyses)) ->
      state_triple (S:= instance) P
        (find a)
        (fun p => P (snd p) /\ uf_rel _ _ _ (snd p).(equiv) (fst p) a).
  Proof.
    intros Hforest Hequiv.
    unfold find, state_triple.
    destruct e; basic_goal_prep.
    case_match; basic_goal_prep.
    {
      specialize (Hforest _ H).
      break.
      eapply find_spec' in  case_match_eqn; eauto.
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

  Record get_parents_postcondition m (p : list atom  * instance) : Prop :=
    {
      get_parents_postcondition_sound_egraph_ok : egraph_ok (snd p);
      get_parents_postcondition_sound_egraph_for_model :
        exists interp,
          egraph_sound_for_interpretation m interp (snd p)
          /\ all (atom_sound_for_model m interp) (fst p)
    }.
  
  Lemma get_parents_sound a rs
    : state_triple (fun e => egraph_sound e rs)
        (get_parents idx symbol symbol_map idx_map idx_trie analysis_result a)
        (get_parents_postcondition rs).
        (*(fun p => egraph_sound (snd p) rs /\ all (fun a => atom_in_egraph a (snd p)) (fst p)).*)
  Proof.
    unfold get_parents,state_triple.
    destruct e; cbn;
      destruct 1 as [ [ [?  egraph_equiv_ok0] ] ].
    split.
    { constructor; cbn; eauto. }
    {
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
    destruct d; cbn.
    eqb_case entry_value (atom_ret a); intuition eauto.
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


  Record put_precondition a m (e : instance) : Prop :=
    {
      put_precondition_sound_egraph_ok : egraph_ok e;
      put_precondition_sound_egraph_for_model :
        exists interp,
          egraph_sound_for_interpretation m interp e
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

  (*TODO: move*)
  Lemma all2_impl A B (R S : A -> B -> Prop) l1 l2
    : (forall a b, R a b -> S a b) -> all2 R l1 l2 -> all2 S l1 l2.
  Proof.
    intro.
    revert l2; induction l1; destruct l2;
      basic_goal_prep; basic_utils_crush.
  Qed.

  Lemma all2_Is_Some_satisfying_l A B (R : A -> B -> Prop) l1 l2
      : all2 (fun x y => x <$> (fun x' => R x' y)) l1 l2
        <-> option_all l1 <$> (fun l1' => all2 R l1' l2).
  Proof.
    revert l2; induction l1; destruct l2;
      basic_goal_prep; (repeat case_match; basic_goal_prep); basic_utils_crush.
    { eapply IHl1; eauto. }
    { eapply IHl1; eauto. } 
    { eapply IHl1; eauto. }
  Qed.
  
  Lemma all2_Is_Some_satisfying_r A B (R : A -> B -> Prop) l1 l2
      : all2 (fun x y => y <$> (fun y' => R x y')) l1 l2
        <-> option_all l2 <$> (fun l2' => all2 R l1 l2').
  Proof.
    revert l1; induction l2; destruct l1;
      basic_goal_prep; (repeat case_match; basic_goal_prep); basic_utils_crush.
    { eapply IHl2; eauto. }
    { eapply IHl2; eauto. } 
    { eapply IHl2; eauto. }
  Qed.
  
  
  Lemma args_rel_interpretation m interp e
    : egraph_sound_for_interpretation m interp e ->
      forall args1 args2,
        all2 (uf_rel_PER _ _ _ e.(equiv)) args1 args2 ->
        option_relation (all2 m.(domain_eq)) (list_Mmap (map.get interp) args1)
          (list_Mmap (map.get interp) args2).
  Proof.
    destruct e,1; cbn in *.
    clear atom_interpretation0 parents_interpretation0.
    unfold SomeRel.
    induction args1;
      destruct args2;
      basic_goal_prep;
      try tauto.
    specialize (IHargs1 args2).
    break.
    eapply rel_interpretation0 in H.
    unfold eq_sound_for_model in H.
    case_match; destruct (map.get interp i) eqn:Hi.
    all:cbn in H; try tauto.
    rewrite !TrieMap.Mmap_option_all.
    eapply all2_impl in H0; try eapply rel_interpretation0.
    unfold eq_sound_for_model in H0.
    change
      (all2
         (fun x y =>
            (fun x y =>
               (fun x y => x <$> (fun x' => y <$> domain_eq m x')) x (map.get interp y))
              (map.get interp x) y)
        args1 args2)
      in H0.
    rewrite <- TrieMap.all2_map_l in H0.
    change
      (all2 (fun x y =>
               (fun x y => x <$> (fun x' => y <$> domain_eq m x')) x (map.get interp y))
         (map (map.get interp) args1) args2)
      in H0.
    rewrite <- TrieMap.all2_map_r in H0.
    rewrite all2_Is_Some_satisfying_l in H0.
    case_match; cbn in *; try tauto.
    rewrite all2_Is_Some_satisfying_r in H0.
    case_match; cbn in *; tauto.
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
      (forall db equiv equiv' parents epoch worklist analyses l,
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv) ->
          forest idx (idx_map idx) l (parent idx (idx_map idx) (idx_map nat) equiv') ->
          iff2 (uf_rel _ _ _ equiv) (uf_rel _ _ _ equiv') ->
          P (Build_instance _ _ _ _ _ _ db equiv parents epoch worklist analyses) ->
          (* TODO: how to express that the roots are the same?*)
          P (Build_instance _ _ _ _ _ _ db equiv' parents epoch worklist analyses)) ->
      state_triple (S:=instance) P
        (canonicalize a)
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
           [ |eapply find_sound_deprecated]; basic_goal_prep; intuition eauto.
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
      eapply find_sound_deprecated; basic_goal_prep; intuition eauto.
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


  (*TODO: just use nat?*)
  Lemma le_trans a b c : le a b -> le b c -> le a c.
  Proof.
    intros H1 H2; revert a H1; induction H2;
      basic_goal_prep; try constructor; eauto.
  Qed.

  (*TODO: what is this for?
  Lemma get_parents_postcondition_equiv_update db equiv equiv' parents epoch worklist analyses l rs roots
    : forest idx (idx_map idx) roots (parent idx (idx_map idx) (idx_map nat) equiv) ->
      forest idx (idx_map idx) roots (parent idx (idx_map idx) (idx_map nat) equiv') ->
      iff2 (uf_rel idx (idx_map idx) (idx_map nat) equiv)
        (uf_rel idx (idx_map idx) (idx_map nat) equiv') ->
      le equiv.(next _ _ _) equiv'.(next _ _ _) ->
      get_parents_postcondition rs (l,
          {| db := db; equiv := equiv; parents := parents; epoch := epoch; worklist := worklist; analyses:= analyses |}) ->
      get_parents_postcondition rs
        (l, {| db := db; equiv := equiv'; parents := parents; epoch := epoch; worklist := worklist; analyses:= analyses  |}).
  Proof.
    clear idx_zero.
    destruct 5 as [ [ ] ?]; cbn in *.
    repeat (constructor; cbn; eauto).
    basic_goal_prep.
    exists x.
    intuition eauto.
    destruct H3; constructor; cbn in *; eauto.
    {
      intros.
      eapply interpretation_bounded0.
      eapply le_trans; eauto.
    }
    {
      intros; eapply rel_interpretation0; eauto.
      eapply H1; eauto.
    }
  Qed.
*)

  
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

  Context `{analysis idx symbol analysis_result}.
  
  Lemma repair_sound a rs
    : inst_computation_sound (repair idx Eqb_idx _ symbol Eqb_symbol symbol_map idx_map idx_trie analysis_result a) rs.
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

  (*TODO: deprecate inst_computation_sound
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
   *)
    
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

  Definition monotone {A} P : Prop :=
    (forall i i' : idx_map A, map.extends i i' -> P i' -> P i).

  Definition monotone1 {A B} (P : _ -> B -> _) : Prop :=
    (forall a (i i' : idx_map A), map.extends i i' -> P i' a -> P i a).

  Definition monotone2 {A B C} (P : _ -> B -> C -> _) : Prop :=
    (forall a b (i i' : idx_map A), map.extends i i' -> P i' a b -> P i a b).
  
  Lemma monotone2_fix_l {A B C} (P : idx_map A -> B -> C -> _) x
    : monotone2 P ->
      monotone1 (fun i => P i x).
  Proof.
    unfold monotone2, monotone1.
    basic_goal_prep.
    eapply H0; eauto.
  Qed.

  
  Definition state_sound_for_model {A} (m : model) i
    (* TODO: what data should Post take?*)
    (s : state instance A) Post_i Post_mono :=
    state_triple (egraph_sound_for_interpretation m i) s
      (*TODO: make sure that i' can depend on x *)
      (fun x => exists i', (Post_i i')
                           /\ egraph_sound_for_interpretation m i' (snd x)
                           /\ map.extends i' i
                           /\ Post_mono i' (fst x))
    /\ monotone1 Post_mono.

  Hint Resolve Properties.map.extends_refl : utils.
  
  Lemma worklist_entry_sound_mono m
    : monotone1 (worklist_entry_sound m).
  Proof.
    intros x ? ?.
    destruct x; basic_goal_prep; auto.
    revert H1.
    unfold eq_sound_for_model, Is_Some_satisfying in *; case_match; try tauto.
    case_match; try tauto.
    eapply H0 in case_match_eqn, case_match_eqn0.
    rewrite case_match_eqn, case_match_eqn0.
    auto.
  Qed.
        
  Lemma pull_worklist_sound m i
    : state_sound_for_model m i
        (pull_worklist idx symbol symbol_map idx_map idx_trie analysis_result) 
        (fun i' => i = i') (fun i wl => all (worklist_entry_sound m i) wl).
  Proof.
    cbv -[map.rep domain map.get all worklist_entry_sound map.extends];
      split; intros.
    {
      eexists; intuition eauto; destruct e; cbn in *;
      destruct H0; cbn in *; eauto with utils.
      constructor; intuition (cbn; eauto).
    }
    {
      eapply all_wkn; try eassumption.
      basic_goal_prep.
      eapply worklist_entry_sound_mono; eauto.
    }     
  Qed.

  Lemma map_extends_trans {key value : Type} {map : map.map key value} (m1 m2 m3 : map)
    : map.extends m1 m2 -> map.extends m2 m3 -> map.extends m1 m3.
  Proof. unfold map.extends; intuition eauto. Qed.

  Lemma state_sound_for_model_bind A B m i c Pi Pmono Qi Qmono (f : A -> _ B)
    : state_sound_for_model m i c Pi Pmono ->
      (forall (a:A) i', map.extends i' i ->
                        Pi i' ->
                        Pmono i' a ->
                        state_sound_for_model m i' (f a) Qi Qmono) ->
      monotone1 Qmono ->
       state_sound_for_model m i (@! let p <- c in (f p)) Qi Qmono.
  Proof.
    basic_goal_prep.
    split; intros; auto.
    destruct H0 as [H0 ?].
    intros e He.
    specialize (H0 e He).
    repeat basic_goal_prep.
    destruct (c e) eqn:Hce.
    repeat basic_goal_prep.
    clear c Hce.
    eapply H1 in H0; eauto with utils.
    eapply H0 in H4.
    repeat basic_goal_prep.
    eexists; intuition eauto using map_extends_trans.
  Qed.

  Lemma monotone1_all A m (Pmono : _ -> A -> _)
    : monotone1 Pmono ->
      monotone1 (fun i' : idx_map (domain m) => all (Pmono i')).
  Proof.
    intros; intros l.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Resolve monotone1_all : utils.
  
  Lemma state_sound_for_model_Mmap A B m i Pi Pmono l (f : A -> _ B) 
    : (forall (a:A) i', In a l ->
                        map.extends i' i ->
                        Pi i' ->
                        state_sound_for_model m i' (f a) Pi Pmono) ->
      Pi i ->
      monotone1 Pmono ->
      state_sound_for_model m i (list_Mmap f l)
        Pi
        (fun i' => all (Pmono i')).
  Proof.
    revert i.
    induction l.
    {
      intros.
      split; auto using monotone1_all.
      eapply state_triple_wkn_ret;
        basic_goal_prep; subst;
        eexists; cbn; intuition eauto with utils.
    }
    {
      intros.
      cbn [list_Mmap].
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        basic_goal_prep;
          basic_utils_crush.
      }
      intros.
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        eapply IHl; auto.
        basic_goal_prep;
          basic_utils_crush.
        eapply H0.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply map_extends_trans; eauto.
      }
      {
        intros; split; eauto using monotone1_all.
        eapply state_triple_wkn_ret;
          basic_goal_prep; subst;
          eexists; intuition eauto using Properties.map.extends_refl.
        basic_goal_prep;
          basic_utils_crush.
      }
    }
  Qed.

  Lemma eq_sound_monotone m
    : monotone2 (eq_sound_for_model m).
  Proof.
    unfold monotone2, eq_sound_for_model.
    intros.
    destruct (map.get i' a) eqn:Hi';
      basic_goal_prep; try tauto.
    eapply H0 in Hi'.
    rewrite Hi' in *.
    cbn.
    destruct (map.get i' b) eqn:Hb;
      basic_goal_prep; try tauto.
    eapply H0 in Hb.
    rewrite Hb in *.
    cbn; auto.
  Qed.

  
  Lemma find_next_const x u u' i0
    : UnionFind.find idx Eqb_idx (idx_map idx) (idx_map nat) u x =
        Some (u', i0) ->
      (next idx (idx_map idx) (idx_map nat) u)
      = (next idx (idx_map idx) (idx_map nat) u').
  Proof.
    unfold UnionFind.find.
    destruct u.
    cbn.
    case_match; cbn; try congruence.
    eqb_case i x.
    { basic_goal_prep; basic_utils_crush. }
    {
      case_match; cbn; try congruence.
      basic_goal_prep.
      basic_utils_crush.
    }
  Qed.

  (*
  Lemma uf_rel_implies_sound_for_model m e i x i0
    : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e) x i0 ->
      egraph_sound_for_interpretation m i e ->
      eq_sound_for_model m i x i0.
  Proof.
    intros Huf [].
    unfold eq_sound_for_model, Is_Some_satisfying.
    case_match.
    {
      eapply rel_interpretation0 in Huf;
        rewrite ?case_match_eqn in *; cbn; auto.
    }
    {
      TODO: do I allow the uf to relate things that arent i nthe interpretation?
                 that seems like a mistake
      revert case_match_eqn
    }
*)

  Lemma find_sound m i x
    : Is_Some (map.get i x) ->
      state_sound_for_model m i (find x) (eq i)
        (fun i => eq_sound_for_model m i x).
  Proof.
    unfold find.
    split.
    2:{ eapply monotone2_fix_l; apply eq_sound_monotone. }
    {
      intros ? ?.
      eexists; intuition eauto with utils.
      {
        case_match; basic_goal_prep; auto.
        destruct H1; constructor; basic_goal_prep; intuition eauto.
        {
          eapply interpretation_bounded0.
          eapply find_next_const in case_match_eqn; eauto.
          congruence.
        }
        {
          eapply rel_interpretation0; eauto.
          (*TODO: make, use the better spec*)
          eapply find_spec' in case_match_eqn; basic_goal_prep; eauto; try Lia.lia.
          2:{
            admit.
          }
          eapply closed_graph_equiv_to_PER in H1.
          2:{ eapply forest_closed; eauto. }
          intuition.
  Abort.
  (*
          2,3:admit (*TODO*).
          eapply H5; eauto.
        }
      }
      {
        case_match; basic_goal_prep; try congruence.
        2:{
          (*TODO: find = None lemma *)
          admit.
        }
        eapply find_spec in case_match_eqn; basic_goal_prep; eauto.
        2,3:admit (*TODO*).
        eapply H5; eauto.
        
      }
  Qed. *)
  
  Lemma ret_sound_for_model A m i (x:A)
    : state_sound_for_model m i (Mret x) (eq i) (fun _ => eq x).
  Proof.
    split; unfold monotone1; basic_goal_prep; basic_utils_crush.
    intros ? ?.
    eexists; basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma ret_sound_for_model' A m i (x:A) Pi Pmono
    : Pi i -> Pmono i x ->
      monotone1 Pmono ->
      state_sound_for_model m i (Mret x) Pi Pmono.
  Proof.
    split; unfold monotone1; basic_goal_prep; basic_utils_crush.
    intros ? ?.
    eexists; basic_goal_prep; basic_utils_crush.
  Qed.

  Context m (m_PER : PER (domain_eq m)).
  
  Lemma eq_sound_for_model_trans i x y z
    : eq_sound_for_model m i x y ->
      eq_sound_for_model m i y z ->
      eq_sound_for_model m i x z.
  Proof.
    unfold  eq_sound_for_model, Is_Some_satisfying.
    repeat case_match; basic_goal_prep; auto.
    all: try tauto.
    all: etransitivity; eassumption.
  Qed.
  
  Lemma canonicalize_worklist_entry_sound i a
    : (worklist_entry_sound m i a) ->
      state_sound_for_model m i
        (canonicalize_worklist_entry idx Eqb_idx symbol
           symbol_map idx_map idx_trie
           analysis_result a)
        (eq i) (worklist_entry_sound m).
  Proof.
    intro.
    destruct a; cbn -[Mbind].
    2:{
        split; eauto using worklist_entry_sound_mono.
        eapply state_triple_wkn_ret;
          basic_goal_prep; subst;
          eexists; cbn; intuition eauto using Properties.map.extends_refl.
    }
    {
      eapply state_sound_for_model_bind; eauto using worklist_entry_sound_mono.
      (*
      1: apply find_sound.
      basic_goal_prep; subst.
      eapply ret_sound_for_model'; eauto using worklist_entry_sound_mono.
      cbn.
      eauto.
      eapply eq_sound_for_model_trans; eassumption.
    }
  Qed. *)
  Abort.

  Lemma rebuild_sound i n
    : state_sound_for_model m i (rebuild n) (fun i' => i = i') (fun _ _ => True).
  Proof.
    induction n.
    {
      basic_goal_prep.
      cbv -[map.rep domain map.get]; intros.
      eexists; intuition eauto.
    }
    {
      cbn [rebuild].
      eapply state_sound_for_model_bind;
      [eapply pull_worklist_sound
      | repeat basic_goal_prep; subst
      | unfold monotone1; auto].
      destruct a.
      {
        split; unfold monotone1; eauto.
        eapply state_triple_wkn_ret;
          basic_goal_prep; subst;
          eexists; intuition eauto using Properties.map.extends_refl.
      }      
      eapply state_sound_for_model_bind;
        [ | | unfold monotone1; auto].
      {
        eapply state_sound_for_model_Mmap.
        {
          intros.
          (*
        state_triple_list_Mmap
     : forall (A B : Type) (f : A -> state ?S B) (l : list A)
         (P : list A -> list B -> ?S -> Prop),
       (forall (fl1 : list B) (l1 : list A) (a0 : A) (l2 : list A),
        l = l1 ++ a0 :: l2 ->
        state_triple (fun e : ?S => P (a0 :: l2) fl1 e) (f a0)
          (fun p : B * ?S => P l2 (fl1 ++ [fst p]) (snd p))) ->
       state_triple (fun e : ?S => P l [] e) (list_Mmap f l)
         (fun p : list B * ?S => P [] (fst p) (snd p))
        
        TODO: avoid unfolding to state_triple?
        eapply state_triple_list_Mmap
          with (P:= ?).
        TODO: a good, applicable list_Mmap lemma
        cbn.
        TODO: what do I know about w, a?.
                      Need to know that the worklist entries are sound.
                                       
        eapply state_triple list_Mmap
          p. 2.
      }
      
      TODO: fun x is no good
      repeat (cbn beta in *; intros; break; subst).
      
      intros g Hg.
      specialize (IHn g Hg).
      repeat (cbn beta in *; intros; break; subst).
      repeat basic_goal_prep; subst.
      eexists; split; eauto.
      case_match; basic_goal_prep.
      {
        basic_utils_crush.
        *)

  Abort.
      
      
End WithMap.

Arguments atom_in_egraph {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope
  a i.

Arguments model_of {idx}%type_scope {symbol}%type_scope {idx_map}%function_scope m rw%list_scope.


Arguments seq_assumptions {idx symbol}%type_scope s.
Arguments seq_conclusions {idx symbol}%type_scope s.

Arguments forall_vars {idx symbol}%type_scope s.
Arguments exists_vars {idx}%type_scope {Eqb_idx} {symbol}%type_scope s.
Arguments sequent_vars {idx symbol}%type_scope s.

Arguments eq_clause {idx symbol}%type_scope x y.
Arguments atom_clause {idx symbol}%type_scope a.


Arguments clauses_to_instance {idx}%type_scope {Eqb_idx}
  idx_succ%function_scope {idx_zero}
  {symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope
  {H}
  l%list_scope _ _.


Arguments instance_to_clauses {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope i.


Arguments db_to_atoms {idx symbol}%type_scope
  {symbol_map idx_trie}%function_scope 
  {analysis_result}%type_scope
  d.


Arguments uf_to_clauses {idx symbol}%type_scope {idx_map}%function_scope u.
