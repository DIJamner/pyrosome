(* TODO: separate semantics and theorems
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps Relations Maps UnionFind.
From Utils.EGraph Require Import Defs.
From Utils Require TrieMap.
Import Sets.
Import StateMonad.


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
      (lt : idx -> idx -> Prop)
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
   TODO: make a class?
 *)
  Record model : Type :=
    {
      domain : Type;
      (* included to support setoids *)
      domain_eq : domain -> domain -> Prop;
      domain_wf x := domain_eq x x;
      (*constants : idx -> domain; TODO: do I have any constants? *)
      interpretation : symbol -> list domain -> option domain;
      interprets_to f args d := exists d', interpretation f args = Some d' /\ domain_eq d' d;
    }.

  Class model_ok (m : model) : Prop :=
    {
      interpretation_preserving
      : forall f args1 args2,
        all2 m.(domain_eq) args1 args2 ->
        option_relation m.(domain_eq) (m.(interpretation) f args1) (m.(interpretation) f args2)
    }.
  
  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_plus : map_plus symbol_map)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus)
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
  Notation db_map :=
    (db_map idx symbol symbol_map idx_trie analysis_result).
  (*TODO: many of these relations can be functions. what's the best way to define them?*)
  
  Definition atom_in_db a (d : db_map) :=
    (map.get d a.(atom_fn)) <$>
      (fun tbl => (map.get tbl a.(atom_args)) <$>
                    (fun r => r.(entry_value _ _) = a.(atom_ret))).
  (*TODO: is this useful anymore? *)
  Definition atom_in_egraph a i := atom_in_db a i.(db). 
  
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
    
    (*TODO: move to defining file*)
    Arguments parent {idx}%type_scope {idx_map rank_map} u.
    
    Record egraph_sound_for_interpretation e : Prop :=
      {
        idx_interpretation_wf : forall i d, map.get idx_interpretation i = Some d -> m.(domain_wf) d;
        interpretation_exact : forall x,
          Is_Some (map.get idx_interpretation x) -> Sep.has_key x (parent (equiv e));
        (* inferrable
        interpretation_bounded : forall i, le e.(equiv).(next _ _ _) i ->
                                           map.get idx_interpretation i = None;
         *)
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
      egraph_equiv_ok : exists roots, union_find_ok lt e.(equiv) roots;
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
            : forall {B} `{WithDefault B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).


  Hint Rewrite @map.get_empty : utils.  
  
  Theorem empty_sound_for_interpretation m
    (*: egraph_sound (empty_egraph idx_zero analysis_result) m.*)
    : egraph_sound_for_interpretation m map.empty (empty_egraph idx_zero _).
  Proof.
    constructor; cbn; try tauto;
      unfold atom_in_egraph, atom_in_db;
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

  
  Lemma has_key_empty A k
    : Sep.has_key k (map.empty : idx_map A) <-> False.
  Proof. clear idx_succ. unfold Sep.has_key; basic_utils_crush. Qed.
  Hint Rewrite has_key_empty : utils.
  
  Theorem empty_sound m : egraph_sound (empty_egraph idx_zero analysis_result) m.
  Proof.
    unfold empty_egraph.
    constructor.
    { cbn; do 3 econstructor; basic_goal_prep; basic_utils_crush.
      { apply empty_forest_rooted. }
    }
    intros; exists map.empty.
    apply empty_sound_for_interpretation.
  Qed.
  
  Notation saturate_until' := (saturate_until' idx_succ idx_zero (spaced_list_intersect)).
  Notation saturate_until := (saturate_until idx_succ idx_zero spaced_list_intersect).

  Notation run1iter :=
    (run1iter idx Eqb_idx idx_succ idx_zero symbol Eqb_symbol symbol_map symbol_map_plus
       idx_map idx_map_plus idx_trie spaced_list_intersect).
  (*
  Notation rebuild := (rebuild idx Eqb_idx symbol Eqb_symbol symbol_map idx_map idx_trie).
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
    unfold atom_in_egraph, atom_in_db;
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
    unfold atom_in_egraph, atom_in_db.
    repeat (match_some_satisfying; cbn;[]).
    basic_goal_prep.
    destruct d; cbn.
    eqb_case entry_value (atom_ret a); intuition eauto.
  Qed.

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
  Proof using.
    clear.
    intro.
    revert l2; induction l1; destruct l2;
      basic_goal_prep; basic_utils_crush.
  Qed.

  Lemma all2_Is_Some_satisfying_l A B (R : A -> B -> Prop) l1 l2
      : all2 (fun x y => x <$> (fun x' => R x' y)) l1 l2
        <-> option_all l1 <$> (fun l1' => all2 R l1' l2).
  Proof.
    clear idx_succ idx_zero.
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
    clear idx_succ idx_zero.
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
  
  Definition atom_rel (equiv : union_find idx (idx_map idx) (idx_map nat)) (a1 a2 : atom) : Prop :=
    a1.(atom_fn) = a2.(atom_fn)
    /\ all2 (uf_rel _ _ _ equiv) a1.(atom_args) a2.(atom_args)
    /\ uf_rel _ _ _ equiv a1.(atom_ret) a2.(atom_ret).

  Lemma atom_rel_refl equiv : Reflexive (atom_rel equiv).
  Proof using.
    clear lt idx_succ idx_zero.
    unfold atom_rel.
    intro a; destruct a; cbn; intuition eauto.
    1:eapply all2_refl.
    all: apply reachable_rel_Reflexive.
  Qed.
  
  Lemma atom_rel_sym equiv : Symmetric (atom_rel equiv).
  Proof using.
    clear lt idx_succ idx_zero.
    unfold atom_rel.
    intros a b; destruct a, b; cbn; intuition eauto.
    1:eapply all2_Symmetric.
    all: try apply reachable_rel_Symmetric; eauto.
  Qed.

  (*TODO: just use nat?*)
  Lemma le_trans a b c : le a b -> le b c -> le a c.
  Proof.
    intros H1 H2; revert a H1; induction H2;
      basic_goal_prep; try constructor; eauto.
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

  Context `{analysis idx symbol analysis_result}.
    

  Definition monotone {A} P : Prop :=
    (forall i i' : idx_map A, map.extends i i' -> P i' -> P i).

  Definition monotone1 {A B} (P : _ -> B -> _) : Prop :=
    (forall a (i i' : idx_map A), map.extends i i' -> P i' a -> P i a).

  Definition monotone2 {A B C} (P : _ -> B -> C -> _) : Prop :=
    (forall a b (i i' : idx_map A), map.extends i i' -> P i' a b -> P i a b).

  Definition monotone3 {A B C D} (P : _ -> B -> C -> D -> _) : Prop :=
    (forall a b c (i i' : idx_map A), map.extends i i' -> P i' a b c -> P i a b c).
  
  Definition monotone4 {A B C D E} (P : _ -> B -> C -> D -> E -> _) : Prop :=
    (forall a b c d (i i' : idx_map A), map.extends i i' -> P i' a b c d -> P i a b c d).
  
  Lemma monotone2_fix_l {A B C} (P : idx_map A -> B -> C -> _) x
    : monotone2 P ->
      monotone1 (fun i => P i x).
  Proof.
    unfold monotone2, monotone1.
    basic_goal_prep.
    eapply H0; eauto.
  Qed.

  
  Definition state_sound_for_model {A} (m : model) i
    (s : state instance A) Post :=
    state_triple (Sep.and1 egraph_ok (egraph_sound_for_interpretation m i)) s
      (*TODO: make sure that i' can depend on x *)
      (fun x => exists i', (Post i' (fst x))
                           /\ egraph_ok (snd x)
                           /\ egraph_sound_for_interpretation m i' (snd x)
                           /\ map.extends i' i).

  Hint Resolve Properties.map.extends_refl : utils.
  
  Lemma worklist_entry_sound_mono m
    : monotone1 (worklist_entry_sound m).
  Proof.
    clear idx_zero idx_succ.
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
        (fun i' wl => i = i' /\ all (worklist_entry_sound m i) wl).
  Proof.
    cbv -[map.rep domain map.get all worklist_entry_sound map.extends];
      intros; break.
    {
      eexists; intuition eauto; destruct e; cbn in *.
      { destruct H1; basic_utils_crush. }
      { destruct H0; constructor; cbn in *; eauto with utils. }
      { destruct H1; constructor; cbn in *; intuition (cbn; eauto). }
      { basic_utils_crush. }
    } 
  Qed.

  Lemma map_extends_trans {key value : Type} {map : map.map key value} (m1 m2 m3 : map)
    : map.extends m1 m2 -> map.extends m2 m3 -> map.extends m1 m3.
  Proof using. clear; unfold map.extends; intuition eauto. Qed.

  Lemma state_sound_for_model_bind A B m i c P Q (f : A -> _ B)
    : state_sound_for_model m i c P ->
      (forall (a:A) i', map.extends i' i ->
                        P i' a ->
                        state_sound_for_model m i' (f a) Q) ->
      state_sound_for_model m i (@! let p <- c in (f p)) Q.
  Proof.
    clear idx_succ idx_zero.
    basic_goal_prep.
    intros; auto.
    intros e He.
    specialize (H0 e He).
    repeat basic_goal_prep.
    destruct (c e) eqn:Hce.
    repeat basic_goal_prep.
    clear c Hce.
    eapply H1 in H0; eauto with utils; clear H1.
    
    specialize (H0 i0).
    unfold Sep.and1 in *; intuition break.
    eexists; intuition eauto using map_extends_trans.
  Qed.

  Lemma monotone1_all A m (Pmono : _ -> A -> _)
    : monotone1 Pmono ->
      monotone1 (fun i' : idx_map (domain m) => all (Pmono i')).
  Proof.
    clear.
    intros; intros l.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Resolve monotone1_all : utils.
  
  Lemma state_sound_for_model_Mmap A B m i P_const P_elt l (f : A -> _ B) 
    : (forall (a:A) i', In a l ->
                        map.extends i' i ->
                        P_const i' ->
                        state_sound_for_model m i' (f a)
                          (fun i' a => P_const i' /\ P_elt i' a)) ->
      P_const i ->
      monotone1 P_elt ->
      state_sound_for_model m i (list_Mmap f l)
        (fun i' l => P_const i' /\ all (P_elt i') l).
  Proof.
    cleanup_context.
    revert i.
    induction l.
    {
      intros.
      eapply state_triple_wkn_ret;
        unfold Sep.and1 in *;
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
        all:basic_goal_prep;
          basic_utils_crush.
        eapply H0.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply map_extends_trans; eauto.
      }
      {
        intros.
        eapply state_triple_wkn_ret;
          unfold Sep.and1 in *;
          basic_goal_prep; subst;
          eexists; intuition eauto using Properties.map.extends_refl.
        basic_goal_prep;
          basic_utils_crush.
      }
    }
  Qed.
  

  
  Lemma ret_sound_for_model A m i (x:A)
    : state_sound_for_model m i (Mret x) (fun i' a => i = i' /\ a = x).
  Proof.
    unfold state_sound_for_model, Sep.and1; basic_goal_prep; basic_utils_crush.
    intros ? ?.
    eexists; basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma ret_sound_for_model' A m i (x:A) P
    : P i x ->
      state_sound_for_model m i (Mret x) P.
  Proof.
    clear idx_succ idx_zero.
    unfold state_sound_for_model, monotone1, Sep.and1; basic_goal_prep; basic_utils_crush.
    intros ? ?.
    eexists; basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma state_sound_for_model_Mmap_dep A B m i P_const P_elt l (f : A -> _ B) 
    : (forall (a:A) i', In a l ->
                        map.extends i' i ->
                        P_const i' ->
                        state_sound_for_model m i' (f a)
                          (fun i' a' => P_const i' /\ P_elt a i' a')) ->
      P_const i ->
      (forall a, monotone1 (P_elt a)) ->
      state_sound_for_model m i (list_Mmap f l)
        (fun i' l' => P_const i' /\ all2 (fun a => P_elt a i') l l').
  Proof.
    cleanup_context.
    revert i.
    induction l.
    {
      intros.
      eapply state_triple_wkn_ret;
        unfold Sep.and1 in *;
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
        all:basic_goal_prep;
          basic_utils_crush.
        eapply H0.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply map_extends_trans; eauto.
      }
      {
        intros.
        eapply ret_sound_for_model'; eauto with utils.
        {
          basic_goal_prep; intuition eauto.
          eapply H2; eauto.
        }
      }
    }
  Qed.
  
  Lemma const_monotone1 A B
    : monotone1 (fun (_ : idx_map A) (_ : B) => True).
  Proof. repeat intro; auto. Qed.
  Hint Resolve const_monotone1 : utils.
  
  Lemma state_sound_for_model_Miter A B m i (P : _ -> _ -> Prop)
    l (f : A -> state instance B) 
    : (forall (a:A) i', In a l ->
                        map.extends i' i ->
                        P i' tt ->
                        state_sound_for_model m i' (f a) (fun i'' _ => P i'' tt)) ->
      P i tt ->
      state_sound_for_model m i (list_Miter f l) P.
  Proof.
    clear idx_succ idx_zero.
    revert i.
    induction l.
    { intros; eapply ret_sound_for_model'; eauto with utils. }
    {
      intros.
      cbn [list_Miter].
      eapply state_sound_for_model_bind.
      {
        eapply H0;basic_goal_prep;
          basic_utils_crush.
      }
      {
        intros.
        eapply IHl; eauto.        
        all:basic_goal_prep;
          basic_utils_crush.
        eapply H0.
        all:basic_goal_prep;
          basic_utils_crush.
        eapply map_extends_trans; eauto.
      }
    }
  Qed.

  Lemma eq_sound_monotone m
    : monotone2 (eq_sound_for_model m).
  Proof using.
    clear.
    unfold monotone2, eq_sound_for_model.
    intros.
    destruct (map.get i' a) eqn:Hi';
      basic_goal_prep; try tauto.
    eapply H in Hi'.
    rewrite Hi' in *.
    cbn.
    destruct (map.get i' b) eqn:Hb;
      basic_goal_prep; try tauto.
    eapply H in Hb.
    rewrite Hb in *.
    cbn; auto.
  Qed.

  
  Lemma find_next_const x u u' i0
    : UnionFind.find u x = (u', i0) ->
      (next idx (idx_map idx) (idx_map nat) u)
      = (next idx (idx_map idx) (idx_map nat) u').
  Proof.
    unfold UnionFind.find.
    destruct u.
    cbn.
    case_match; cbn; try congruence.
    {
      eqb_case i x.
      { basic_goal_prep; basic_utils_crush. }
      {
        case_match; cbn; try congruence.
        basic_goal_prep.
        basic_utils_crush.
      }
    }
    {
      basic_goal_prep; basic_utils_crush.
    }
  Qed.
  
  (*TODO: still needed? *)
  (*Existing Instance iff2_rel. *)
  
  Lemma trans_to_PER_natural u u'
    : subrelation (parent_rel idx (idx_map idx) (parent u))
        (parent_rel idx (idx_map idx) (parent u')) ->
      subrelation (uf_rel_PER idx (idx_map idx) (idx_map nat) u)
        (uf_rel_PER idx (idx_map idx) (idx_map nat) u').
  Proof.
    clear.
    intro H; eapply subrelation_PER_closure in H.
    unfold parent_rel in H.
    rewrite !PER_closure_of_trans in H.
    exact H.
  Qed.
  
  Lemma find_sound m i x
    : Sep.has_key x i ->
      state_sound_for_model m i (find x) (fun i' a => i = i' /\ eq_sound_for_model m i x a).
  Proof.
    cleanup_context.
    unfold find.
    {
      intros ? ? ?.
      case_match; cbn.
      unfold Sep.and1 in *; break.
      destruct H1; break.
      pose proof case_match_eqn.
      eapply find_spec in case_match_eqn;
        try Lia.lia; eauto.
      2:{ eapply interpretation_exact; eauto. }
      break.
      eexists; intuition eauto with utils.
      {
        eapply rel_interpretation; eauto.
        eapply H7 in H6.
        eapply trans_PER_subrel; eauto.
      }
      { constructor; eauto. }
      {
        destruct H2; constructor; basic_goal_prep; intuition eauto.
        {
          eapply interpretation_exact0 in H2.
          eapply find_preserves_domain in H3; eauto.
          eapply H3; eauto.
        }
        {
          eapply rel_interpretation0; eauto.
          eapply trans_to_PER_natural; eauto.
        }
      }
    }
  Qed.

  (*TODO: this should be implied by model_ok*)
  Context m (m_PER : PER (domain_eq m)).
  
  Lemma eq_sound_for_model_trans i x y z
    : eq_sound_for_model m i x y ->
      eq_sound_for_model m i y z ->
      eq_sound_for_model m i x z.
  Proof using m_PER.
    clear lt idx_succ.
    unfold  eq_sound_for_model, Is_Some_satisfying.
    repeat case_match; basic_goal_prep; auto.
    all: try tauto.
    all: etransitivity; eassumption.
  Qed.

  Lemma eq_sound_has_key_r i old_idx new_idx
          : eq_sound_for_model m i old_idx new_idx ->
            Sep.has_key new_idx i.
  Proof using.
    clear lt idx_succ idx_zero.
    unfold eq_sound_for_model, Sep.has_key, Is_Some_satisfying.
    repeat case_match; tauto.
  Qed.
  Hint Resolve eq_sound_has_key_r : utils.
  
  Lemma canonicalize_worklist_entry_sound i a
    : (worklist_entry_sound m i a) ->
      state_sound_for_model m i
        (canonicalize_worklist_entry idx Eqb_idx symbol
           symbol_map idx_map idx_trie
           analysis_result a)
        (fun i' a => i = i' /\ worklist_entry_sound m i' a).
  Proof.
    intro.
    destruct a; cbn -[Mbind].
    2:{ eapply ret_sound_for_model'; eauto using worklist_entry_sound_mono. }
    {
      eapply state_sound_for_model_bind; eauto using worklist_entry_sound_mono.
      { eapply find_sound; eauto with utils. }
      basic_goal_prep; subst.
      eapply ret_sound_for_model'; eauto using worklist_entry_sound_mono.
      cbn.
      intuition subst.
      eapply eq_sound_for_model_trans; eauto.
    }
  Qed.
  

  Arguments repair {idx}%type_scope {Eqb_idx} idx_zero {symbol}%type_scope {Eqb_symbol}
    {symbol_map idx_map idx_trie}%function_scope {analysis_result}%type_scope 
    {H} e _.
  
  Arguments get_parents {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
    {analysis_result}%type_scope x _.

  Lemma atom_sound_monotone
    : monotone1 (atom_sound_for_model m).
  Proof using.
    clear.
    unfold atom_sound_for_model.
    repeat intro.
    unfold Is_Some_satisfying in H0.
    repeat case_match; try tauto.
    rewrite !TrieMap.Mmap_option_all in *.
    eapply Properties.map.getmany_of_list_extends in case_match_eqn; eauto.
    unfold map.getmany_of_list in case_match_eqn;
      rewrite case_match_eqn.
    eapply H in case_match_eqn0; rewrite case_match_eqn0.
    cbn.
    auto.
  Qed.
  Hint Resolve atom_sound_monotone : utils.
  Hint Resolve monotone1_all : utils.

  
  (*TODO: lift upwards, use as needed *)
  Ltac open_ssm' :=
    cleanup_context;
    lazymatch goal with
    | |- state_sound_for_model _ _ ?e _ =>
        let h := get_head e in
        unfold h; unfold state_sound_for_model, Sep.and1; repeat intro;
        eexists; eauto with utils;
        break; cbn[fst snd]
    end.
  
  Ltac open_ssm :=
    open_ssm';
    intuition eauto with utils;
    break; cbn[fst snd];
    try lazymatch goal with
      | H : egraph_ok _ |- egraph_ok _ =>
          destruct H; constructor; eauto with utils
      | H : egraph_sound_for_interpretation _ _ _
        |- egraph_sound_for_interpretation _ _ _ =>
          destruct H; constructor; eauto with utils
    end.
  
  Lemma get_parents_sound i old_idx
    : state_sound_for_model m i (get_parents old_idx)
         (fun i' a => i = i' /\ all (atom_sound_for_model m i) a).
  Proof.
    open_ssm.
    unfold unwrap_with_default; case_match; [| exact I].
    eapply parents_interpretation in case_match_eqn; eauto.
  Qed.

  Hint Rewrite @map.get_remove_same: utils.
  (*Hint Rewrite @map.get_remove_diff using tauto: utils.*)
  
  Lemma remove_parents_sound i old_idx
    : state_sound_for_model m i
        (remove_parents idx symbol symbol_map idx_map idx_trie analysis_result old_idx) 
        (fun i' _ => i' = i).
  Proof.
    open_ssm.
    basic_goal_prep.
    eqb_case i0 old_idx;
      basic_utils_crush.
    rewrite map.get_remove_diff in H0; try tauto.
    eauto.
  Qed.
  
  Ltac iss_case :=
    lazymatch goal with
    | H : ?ma <$> _ |- _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn in H;[| tauto]
    | |- ?ma <?> _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn;[| tauto]
    end.
  
  Lemma db_remove_sound i a1
    : state_sound_for_model m i
        (db_remove idx symbol symbol_map idx_map idx_trie analysis_result a1)
        (fun i' _ => i' = i).
  Proof.
    open_ssm.
    basic_goal_prep.
    eapply atom_interpretation0.
    unfold atom_in_egraph, atom_in_db in *.
    basic_goal_prep.
    basic_utils_crush.
    repeat iss_case.
    eqb_case (atom_fn a1) (atom_fn a).
    {
      rewrite H1 in *.
      rewrite get_update_same in Hma; eauto.
      autorewrite with inversion in *.
      unfold Basics.flip in *.
      case_match.
      2:{
        change (map.remove map.empty (atom_args a1) = r) in Hma.
        rewrite Properties.map.remove_empty in *.
        basic_utils_crush.
      }
      cbn; subst.        
      eqb_case (atom_args a1) (atom_args a).
      {
        rewrite H2 in *.
        basic_utils_crush.
      }
      {
        rewrite map.get_remove_diff in Hma0; eauto.
        rewrite Hma0; cbn; eauto.
      }
    }
    {
      rewrite get_update_diff in Hma; eauto.
      rewrite Hma; cbn; eauto.
      rewrite Hma0; cbn; eauto.
    }
  Qed.

  Definition eq_atom_in_interpretation i (a1 a2 : atom) :=
    atom_fn a1 = atom_fn a2 /\
      all2 (eq_sound_for_model m i) (atom_args a1) (atom_args a2) /\
      eq_sound_for_model m i (atom_ret a1) (atom_ret a2).

  
  Lemma all2_flip A B (R : A -> B -> Prop) l1 l2
    : all2 R l1 l2 = all2 (fun a b => R b a) l2 l1.
  Proof using.
    clear.
    revert l2; induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Instance eq_sound_for_model_Symmetric i : Symmetric (eq_sound_for_model m i).
  Proof using m_PER .
    clear lt idx_succ idx_zero.
    unfold eq_sound_for_model.
    repeat intro.
    repeat iss_case.
    cbn.
    symmetry; auto.
  Qed.

  Lemma eq_atom_monotone
    : monotone2 eq_atom_in_interpretation.
  Proof using.
    clear.
    unfold eq_atom_in_interpretation.
    repeat intro.
      basic_goal_prep;
        basic_utils_crush.
      1: eapply all2_impl; try eassumption.
      all:intros; eapply eq_sound_monotone; eauto.
  Qed.


  Lemma canonicalize_sound i a1
    : atom_sound_for_model m i a1 ->
      state_sound_for_model m i (canonicalize a1)
        (fun i' a => i = i' /\ eq_atom_in_interpretation i a a1).
  Proof.
    cleanup_context.
    unfold canonicalize.
    destruct a1.
    intros.
    eapply state_sound_for_model_bind; eauto with utils.
    {
      eapply state_sound_for_model_Mmap_dep with (P_const:= eq i); auto.
      {
        cbn beta;intros; subst.
        eapply find_sound.
        unfold atom_sound_for_model in *.
        repeat iss_case.
        basic_goal_prep.
        rewrite TrieMap.Mmap_option_all in *.
        
        eapply In_option_all in Hma; eauto.
        2: eapply in_map; eauto.
        break.
        unfold Sep.has_key; rewrite H3; auto.
      }
      {
        repeat intro; 
        eapply eq_sound_monotone; eauto with utils.
      }
    }
    {
      cbn beta;intros; subst.
      eapply state_sound_for_model_bind; eauto with utils.
      {
        eapply find_sound.
        unfold atom_sound_for_model in *.
        repeat iss_case.
        basic_goal_prep.
        rewrite TrieMap.Mmap_option_all in *.
        subst.
        unfold Sep.has_key; rewrite Hma0; auto.
      }
      {
        cbn beta;intros; subst.
        eapply ret_sound_for_model'; eauto with utils.
        {
          unfold eq_atom_in_interpretation;
            basic_goal_prep;
            intuition subst; eauto.
          {
            eapply all2_Symmetric; eauto.
            apply eq_sound_for_model_Symmetric.
          }
          { apply eq_sound_for_model_Symmetric; auto. }
        }      
      }
    }
  Qed.
  
  Arguments db_lookup {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
    {analysis_result}%type_scope f args%list_scope _.

  
  (*TODO: preconditions?*)
  Lemma db_lookup_sound i f args
    : state_sound_for_model m i
        (db_lookup f args)
        (fun i' mx => i = i'
                      /\ mx <?> (fun x => atom_sound_for_model m i (Build_atom f args x))).
  Proof.
    open_ssm.
    basic_goal_prep;
      basic_utils_crush.
    case_match; cbn; try tauto.
    case_match; cbn; try tauto.
    unfold atom_sound_for_model; cbn.
    assert (atom_in_egraph (Build_atom f args (entry_value idx analysis_result d)) e).
    {
      unfold atom_in_egraph, atom_in_db; cbn.
      rewrite case_match_eqn; cbn;
        rewrite case_match_eqn0; cbn.
      reflexivity.
    }
    eapply atom_interpretation in H0; eauto.
  Qed.

  Lemma state_sound_for_model_Mseq A B (i : idx_map (domain m)) (c1 : state instance A)
    P Q (c2 : state instance B)
    : state_sound_for_model m i c1 P ->
      (forall a (i' : idx_map (domain m)),
          map.extends i' i -> P i' a -> state_sound_for_model m i' c2 Q) ->
      state_sound_for_model m i (@! c1; c2) Q.
  Proof.
    intros.
    change (@! c1; c2) with (@! let _ <- c1 in c2).
    eapply state_sound_for_model_bind; eauto.
  Qed.
  
  Lemma same_domain_has_key A (m1 m2 : idx_map A)
    : map.same_domain m1 m2 <->
        (forall x : idx, Sep.has_key x m1 <-> Sep.has_key x m2).
  Proof using.
    clear lt idx_succ idx_zero.
    unfold map.same_domain, map.sub_domain,  Sep.has_key.
    intuition repeat case_match; eauto;
      try eapply H2 in case_match_eqn0; try eapply H1 in case_match_eqn;
      try eapply H1 in case_match_eqn0; try eapply H2 in case_match_eqn;
      try specialize (H0 k);
      rewrite ? H1, ?H2 in *;
      repeat case_match;
      break; try eexists; intuition eauto; try congruence.
    Unshelve.
    all: auto.
  Qed.
  
  (*TODO: move to UnionFind.v*)
  Lemma union_same_domain u u' x y i0 l
    : union_find_ok lt u l ->
      Sep.has_key x u.(parent) ->
      Sep.has_key y u.(parent) ->
      UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) u x y
      = (u', i0) ->
      map.same_domain u.(parent) u'.(parent).
  Proof using idx_map_ok Eqb_idx_ok.
    clear idx_succ idx_zero.
    unfold UnionFind.union.
    intros.
    eapply same_domain_has_key.
    intro k.
    do 2 case_match.
    pose proof case_match_eqn.
    pose proof case_match_eqn0.
    eapply find_spec in H4; eauto; break; try Lia.lia.
    eapply find_spec in H5; eauto; break; try Lia.lia.
    2:{ eapply H10; eauto. }
    eapply find_preserves_domain with (x:=k) in case_match_eqn, case_match_eqn0;
      eauto.
    2:{ eapply H10; eauto. }
    rewrite H10.
    case_match; autorewrite with inversion in *; break; subst; eauto.
    
    assert (Sep.has_key i (parent u)).
    {
      unfold Sep.has_key.      
      eapply forest_root_iff with (m:= parent u) in H6; eauto using uf_forest.
      rewrite H6; eauto.
    }
    assert (Sep.has_key i1 (parent u)).
    {
      unfold Sep.has_key.      
      eapply forest_root_iff with (m:= parent u) in H11; eauto using uf_forest.
      rewrite H11; eauto.
    }
    case_match; cbn in *; autorewrite with inversion in *; break; subst; cbn in *; eauto.
    all: rewrite H15.
    all: rewrite has_key_put.
    all: intuition subst; eauto.
  Qed.

  
  Lemma union_closure_implies_PER A R `{PER A R} R1 R2
    : (impl2 R1 R) -> (impl2 R2 R) -> impl2 (union_closure_PER R1 R2) R.
  Proof using.
    clear idx_succ idx_zero.
    unfold impl2;
      induction 3;
      basic_goal_prep;
      basic_utils_crush.
    { etransitivity; eassumption. }
    { symmetry; auto. }
  Qed.

  Instance eq_sound_for_model_PER i
    : PER (eq_sound_for_model m i).
  Proof using m_PER.
    clear lt idx_succ idx_zero.
    unfold eq_sound_for_model.
    constructor; repeat intro; repeat iss_case; cbn.
    { symmetry; auto. }
    { etransitivity; eassumption. }
  Qed.

  (*TODO: move to UnionFInd.v *)
  Arguments parent_rel [idx]%type_scope [idx_map] m _ _.
  
  (*TODO: move to UnionFind.v*)
  Lemma union_output l uf x y uf' z
    :  union_find_ok lt uf l ->
       Sep.has_key x (parent uf) ->
       Sep.has_key y (parent uf) ->
       UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) uf x y = (uf', z) ->
       parent_rel uf'.(parent) x z
       /\ parent_rel uf'.(parent) y z.
  Proof using idx_map_ok Eqb_idx_ok.
    clear idx_succ idx_zero.
    unfold UnionFind.union.
    intros.
    do 2 case_match.
    eapply find_spec in case_match_eqn; eauto; break; try Lia.lia.
    eapply find_spec in case_match_eqn0; eauto; break; try Lia.lia.
    2:{ eapply H9; eauto. }
    eqb_case i i0.
    {
      autorewrite with inversion in *; break; subst.
      intuition eauto.
      eapply H14.
      eapply union_find_limit; eauto.
      Lia.lia.
    }
    case_match.
    all: autorewrite with inversion in *; break; subst.
    all: basic_goal_prep.
    all: intuition eauto.
    all:lazymatch goal with
      |- parent_rel (map.put _ ?i0 _) ?x _ =>
        eqb_case x i0; [ eapply parent_rel_put_same; now eauto |]
    end.
    all: try now (eapply unloop_parent; eauto using uf_forest;
                  eapply H14; eapply union_find_limit; eauto; Lia.lia).
    all: eapply transitive_closure_transitive;
      [now (eapply unloop_parent; eauto using uf_forest;
            eapply H14; eapply union_find_limit; eauto; Lia.lia)|].
    all: eapply parent_rel_put_same; now eauto.
  Qed.
    
  Lemma union_sound i x y
    : eq_sound_for_model m i x y ->
      state_sound_for_model m i (Defs.union x y)
        (fun i' a => i = i' /\ eq_sound_for_model m i' x a).
  Proof.
    intros; open_ssm'.
    basic_goal_prep.
    eqb_case x y.
    { basic_goal_prep; intuition eauto with utils. }
    case_match.
    destruct (egraph_equiv_ok _ e0).
    pose proof case_match_eqn as Hdom.
    eapply union_spec in case_match_eqn; try Lia.lia; eauto.
    2:{
      eapply interpretation_exact; eauto.
      eapply eq_sound_has_key_r; symmetry; eauto.
    }
    2:{
      eapply interpretation_exact; eauto.
      eapply eq_sound_has_key_r; eauto.
    }
    break.
    eqb_case x i0; basic_goal_prep.
    {
      intuition eauto with utils.
      { eapply eq_sound_for_model_trans; try eassumption; symmetry; now eauto. }
      {
        constructor; cbn.
        eexists; eauto.
      }
      {
        destruct e1; constructor; cbn; eauto.
        {
          intros x H'; apply interpretation_exact0 in H'.
          eapply union_same_domain in Hdom; eauto.
          { eapply same_domain_has_key in Hdom; eapply Hdom; eauto. }
          {
            symmetry in H0; eapply eq_sound_has_key_r in H0.
            eapply interpretation_exact0; eauto.
          }
          {
            eapply eq_sound_has_key_r in H0.
            eapply interpretation_exact0; eauto.
          }
        }
        {
          intros.
          eapply H6 in H7.
          revert H7; eapply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
          unfold singleton_rel, impl2; basic_goal_prep; subst; eauto.
        }
        { split; auto; symmetry; auto. }
      }
    }
    intuition try constructor; basic_goal_prep; intuition eauto with utils.    
    { eapply union_output in Hdom; eauto.
      2:{
        symmetry in H0; eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      2:{
        eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      break.
      eapply trans_PER_subrel in H8; eapply H6 in H8.
      revert H8; apply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
      {
        repeat intro.
        eapply rel_interpretation; eauto.
      }
      { unfold singleton_rel, impl2; basic_goal_prep; subst; auto. }
    }
    { eapply idx_interpretation_wf; eauto. }
    {
      eapply interpretation_exact in H8; eauto.
      eapply union_same_domain in Hdom; eauto.
      { eapply same_domain_has_key in Hdom; eapply Hdom; eauto. }
      {
        symmetry in H0; eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      {
        eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
    }
    { eapply atom_interpretation in e1; eauto. }
    {
      eapply H6 in H8.
      revert H8; apply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
      {
        repeat intro.
        eapply rel_interpretation; eauto.
      }
      { unfold singleton_rel, impl2; basic_goal_prep; subst; auto. }
    }
    { eapply parents_interpretation; eauto. }
    2:{ eapply worklist_sound; eauto. }    
    { eapply union_output in Hdom; eauto.
      2:{
        symmetry in H0; eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      2:{
        eapply eq_sound_has_key_r in H0.
        eapply interpretation_exact; eauto.
      }
      break.
      eapply trans_PER_subrel in H8; eapply H6 in H8.
      revert H8; apply union_closure_implies_PER; eauto using eq_sound_for_model_PER.
      {
        repeat intro.
        eapply rel_interpretation; eauto.
      }
      { unfold singleton_rel, impl2; basic_goal_prep; subst; auto. }
    }
  Qed.

  
  Lemma interprets_to_functional f args d d'
    : interprets_to m f args d ->
      interprets_to m f args d' ->
      m.(domain_eq) d d'.
  Proof.
    unfold interprets_to.
    basic_goal_prep.
    replace x0 with x in * by congruence.
    etransitivity; eauto; symmetry; eauto.
  Qed.

  
  Lemma state_sound_for_model_wkn i A (s : state instance A) P Q
    : state_sound_for_model m i s P ->
      (forall i' a, map.extends i' i -> P i' a -> Q i' a) ->
      state_sound_for_model m i s Q.
  Proof.
    clear idx_zero idx_succ.
    unfold state_sound_for_model, state_triple, Sep.and1; basic_goal_prep;
      intuition eauto.
    specialize (H0 e).
    intuition break.
    eexists; intuition eauto.
  Qed.

  
  Lemma get_analysis_sound i a
    : state_sound_for_model m i
        (get_analysis idx symbol symbol_map idx_map idx_trie analysis_result a)
        (fun i' _ => i = i').
  Proof.
    open_ssm'.
    split; eauto.
    case_match; cbn; intuition eauto with utils.
    { destruct e0; constructor; intros; intuition eauto. }
    { destruct e1; constructor; intros; cbn; intuition eauto. }
  Qed.

  Lemma get_analyses_sound i args
    : state_sound_for_model m i
         (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result args) 
         (fun i' _ => i = i').
  Proof.
    clear idx_zero idx_succ.
    unfold get_analyses.
    eapply state_sound_for_model_wkn.
    1:apply state_sound_for_model_Mmap with
      (P_const := fun i' => i = i')
      (P_elt := fun _ _ => True); auto with utils.
    {
      intros; subst.
      eapply state_sound_for_model_wkn; [apply get_analysis_sound |].
      basic_goal_prep; subst; intuition auto.
    }
    basic_goal_prep; subst; intuition auto.
  Qed.

  Lemma update_analyses_sound i o a
    : state_sound_for_model m i
        (update_analyses idx symbol symbol_map idx_map idx_trie analysis_result o a)
         (fun i' _ => i = i').
  Proof.
    open_ssm.
  Qed.
  
  Lemma set_eq_empty_l A (l : list A) : set_eq [] l <-> l = [].
  Proof using.
    clear.
    unfold set_eq, incl; 
      basic_goal_prep;
      basic_utils_crush.
    destruct l; auto.
    basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite set_eq_empty_l : utils.

  Lemma all_incl A (l1 l2 : list A) P
    : incl l1 l2 -> all P l2 -> all P l1.
  Proof using.
    clear.
    revert l2; induction l1;
      basic_goal_prep;
      basic_utils_crush.
    eapply in_all; eauto.
  Qed.
      
  Lemma db_set_sound i a
    : atom_sound_for_model m i a ->
      state_sound_for_model m i
        (db_set idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result a)
        (fun i' _ => i = i').
  Proof.
    cleanup_context.
    unfold db_set.
    intros.
    eapply state_sound_for_model_bind; eauto using get_analyses_sound with utils.
    cbn beta; intros; subst.
    eapply state_sound_for_model_bind; eauto using update_analyses_sound with utils.
    cbn beta; intros; subst.
    unfold db_set'.
    unfold state_sound_for_model, Sep.and1.
    repeat intro; eexists; split; cbn; intuition eauto.
    { destruct H4; constructor; basic_goal_prep; intuition eauto. }
    {
      destruct H5; constructor; basic_goal_prep; intuition eauto.
      {
        unfold atom_in_egraph, atom_in_db in H3; cbn in H3.
        eqb_case (atom_fn a) (atom_fn a2);
          [ rewrite H5 in *; rewrite get_update_same in *
          | rewrite get_update_diff in * ]; eauto.
        basic_goal_prep.
        case_match.
        {
          eqb_case (atom_args a) (atom_args a2);
          [ rewrite H6 in *; rewrite map.get_put_same in *
          | rewrite map.get_put_diff in * ]; repeat iss_case;
            autorewrite with inversion in *; break; subst; cbn in *; eauto.
          { replace a2 with a in * by (destruct a, a2; cbn in *; congruence); eauto. }
          {
            apply atom_interpretation0; unfold atom_in_egraph, atom_in_db.
            rewrite case_match_eqn; cbn.
            rewrite Hma; cbn.
            eauto.
          }
        }
        {
          eqb_case (atom_args a) (atom_args a2);
          [ rewrite H6 in *; rewrite map.get_put_same in *
          | rewrite map.get_put_diff in * ]; repeat iss_case;
            autorewrite with inversion in *; break; subst; cbn in *; eauto.
          { replace a2 with a in * by (destruct a, a2; cbn in *; congruence); eauto. }
          {
            change (map.get map.empty (atom_args a2) = Some d) in Hma.
            basic_utils_crush.
          }
        }
      }
      {
        change (map.get
                  (fold_left (fun m x => map_update m x (cons a))
                     (dedup (eqb (A:=_)) (a.(atom_ret)::a.(atom_args))) e.(parents))
                  i = Some l) in H3.
        destruct (map.get (parents e) i) eqn:Hpe.
        2:{
          assert (incl l [a]).
          {
            assert (map.get (parents e) i <?> (fun l => incl l [a])).
            { rewrite Hpe; cbn; auto. }
            revert H5 l H3.
            generalize (parents e);
            generalize (dedup eqb (atom_ret a :: atom_args a)).
            induction l;
              basic_goal_prep;
              basic_utils_crush.
            { rewrite H3 in *; cbn in *; auto. }
            {
              eapply IHl in H3; eauto.
              eqb_case i a1.
              {
                rewrite get_update_same; cbn; eauto.
                case_match; cbn in *; eauto with utils.
                basic_utils_crush.
              }
              { rewrite get_update_diff; cbn; eauto. }
            }
          }
          eapply all_incl; eauto; cbn; intuition eauto.
        }
        assert (incl l (cons a l0)).
        {
          revert H3 Hpe.
          revert l l0;
            generalize (parents e);
            generalize (dedup eqb (atom_ret a :: atom_args a)).
          induction l;
            basic_goal_prep;
            basic_utils_crush.
          { replace l0 with l by congruence; eauto with utils. }
          {
            eqb_case i a1; eapply IHl with (r:=(map_update r a1 (cons a))) in H3.
            2:{ rewrite get_update_same, Hpe; eauto. }
            3:{ rewrite get_update_diff, Hpe; eauto. }
            2: now eauto with utils.
            revert H3; clear; unfold incl; cbn; intuition eauto.
            eapply H3 in H.
            intuition subst; eauto.
          }
        }
        eapply all_incl; try eassumption.
        cbn; intuition eauto.
      }
    }    
  Qed.
  
  Lemma update_entry_sound i a
    : atom_sound_for_model m i a ->
      state_sound_for_model m i (update_entry a)
        (fun i' _ => i = i').
  Proof.
    cleanup_context.
    unfold update_entry.
    intros.
    eapply state_sound_for_model_bind; eauto using db_lookup_sound with utils.
    cbn beta;intros; subst.
    case_match; cbn in H2.
    {
      eapply state_sound_for_model_Mseq; eauto with utils.
      {
        apply union_sound.
        unfold atom_sound_for_model in *; basic_goal_prep; repeat iss_case.
        autorewrite with inversion in *; subst.
        eapply interprets_to_functional in H3; try apply H0.
        unfold eq_sound_for_model.
        rewrite Hma0; cbn; rewrite Hma2; cbn; symmetry; eauto.
      }
      {
        intros; subst.
        eapply ret_sound_for_model'; intuition subst; eauto with utils.
        break; subst; eauto.
      }
    }        
    { break; subst; eapply db_set_sound; eauto. }
  Qed.

  Context `{model_ok m}.
  
  Lemma eq_atom_implies_sound_l i a3 a1 
    : eq_atom_in_interpretation i a3 a1 ->
      atom_sound_for_model m i a3 -> atom_sound_for_model m i a1.
  Proof.
    clear idx_succ idx_zero.
    unfold eq_atom_in_interpretation, eq_sound_for_model, atom_sound_for_model, interprets_to.
    intuition eauto.
    rewrite <- TrieMap.all2_map_l
      with (f:= map.get i)
           (R:= (fun x y => x <$> (fun x' : domain m => map.get i y <$> domain_eq m x')))
      in H1.
    eapply all2_Is_Some_satisfying_l in H1.
    rewrite !TrieMap.Mmap_option_all in *.
    repeat iss_case; cbn in *.
    rewrite <- TrieMap.all2_map_r
      with (f:= map.get i)
           (R:= fun x y => y <$> domain_eq m x)
      in H1.
    eapply all2_Is_Some_satisfying_r in H1.
    repeat iss_case; cbn in *; break.
    rewrite H3 in *.
    apply interpretation_preserving with (f:=(atom_fn a1)) in H1.
    autorewrite with inversion in *; break; subst.
    erewrite H2 in *.
    cbn in *; case_match; try tauto.
    eexists; split; eauto.
    repeat (etransitivity; try eassumption;[]).
    symmetry; eauto.
  Qed.
  
  
  Instance eq_atom_interp_sym i : Symmetric (eq_atom_in_interpretation i).
  Proof.
    clear idx_succ idx_zero.
    unfold eq_atom_in_interpretation; repeat intro; basic_goal_prep;
      repeat (iss_case; cbn in * ).
    intuition eauto.
    {
      apply all2_Symmetric; eauto.
      apply eq_sound_for_model_Symmetric; eauto.
    }
    { symmetry; eauto. }
  Qed.

  

    
  Lemma db_lookup_entry_sound i f args
    : state_sound_for_model m i
        (db_lookup_entry idx symbol symbol_map idx_map idx_trie analysis_result
           f args) (fun i' e => i' = i
                                /\ e <?> (fun e => atom_sound_for_model m i
                                        (Build_atom f args e.(entry_value _ _)))).
  Proof.
    open_ssm.
    intuition eauto with utils.
    basic_goal_prep.
    case_match; cbn; auto.
    case_match; cbn; auto.
    assert (atom_in_egraph (Build_atom f args d.(entry_value _ _)) e).
    {
      unfold atom_in_egraph, atom_in_db; cbn.
      rewrite case_match_eqn; cbn.
      rewrite case_match_eqn0; cbn.
      reflexivity.
    }
    eapply atom_interpretation; eauto.
  Qed.
  
  
  Lemma push_worklist_sound_analysis i o
    : state_sound_for_model m i
        (push_worklist idx symbol symbol_map idx_map idx_trie analysis_result
           (analysis_repair idx o)) 
        (fun i' _ => i = i').
  Proof.
    open_ssm.
    cbn; eauto.
  Qed.

  Ltac bind_with_fn H :=
    eapply state_sound_for_model_bind;
    eauto using H with utils;
    cbn beta;intros; subst; cleanup_context.
  
  Ltac ssm_bind :=
    eapply state_sound_for_model_bind;
    eauto with utils;
    cbn beta in *;intros; subst; cleanup_context.

  Lemma db_set_entry_sound i f args entry_epoch entry_value a
    : atom_sound_for_model m i (Build_atom f args entry_value) ->
      state_sound_for_model m i
       (db_set_entry idx symbol symbol_map idx_map idx_trie analysis_result 
          f args entry_epoch entry_value a) 
         (fun i' _ => i = i').
  Proof.
    intro Hsound.
    open_ssm.
    intuition eauto with utils.
    unfold atom_in_egraph,atom_in_db in *; cbn in *.
    repeat iss_case.
    eqb_case f (atom_fn a0).
    {
      rewrite get_update_same in* by eauto.
      inversions.
      case_match.
      all: eqb_case args (atom_args a0).
      all: rewrite ?map.get_put_same in * by eauto; inversions; cbn in *; subst; eauto.
      all: rewrite  ?map.get_put_diff in * by eauto; inversions;cbn in *; subst; eauto.
      {
        eapply atom_interpretation0; rewrite case_match_eqn; cbn.
        rewrite Hma0; cbn.
        eauto.
      }
      {
        exfalso.
        change (map.get map.empty (atom_args a0) = Some d) in Hma0.
        rewrite map.get_empty in *.
        congruence.
      }
    }
    {
      rewrite get_update_diff in * by eauto.
      apply atom_interpretation0.
      rewrite Hma; cbn.
      rewrite Hma0;cbn.
      eauto.
    }   
  Qed.    

  Lemma repair_parent_analysis_sound i a
    : state_sound_for_model m i
        (repair_parent_analysis idx symbol
           symbol_map idx_map idx_trie analysis_result a)
         (fun i' _ => i = i').
  Proof.
    cleanup_context.
    unfold repair_parent_analysis.
    bind_with_fn db_lookup_entry_sound.
    case_match; break; subst.
    2:{ eapply ret_sound_for_model'; eauto with utils. }
    case_match.
    cbn in H3.
    bind_with_fn get_analyses_sound.
    cbn beta;intros; subst.
    case_match.
    { eapply ret_sound_for_model'; eauto with utils. }
    bind_with_fn update_analyses_sound.
    bind_with_fn push_worklist_sound_analysis.
    apply db_set_entry_sound; auto.
  Qed.

  Lemma state_sound_for_model_Mfoldl A B i P_const P_acc l (f : B -> A -> state instance B) acc
    : (forall (a:A) acc i', In a l ->
                            map.extends i' i ->
                            P_const i' ->
                            P_acc i' acc ->
                            state_sound_for_model m i' (f acc a)
                              (fun i' acc => P_const i' /\ P_acc i' acc)) ->
      P_const i ->
      P_acc i acc ->
      monotone1 P_acc ->
      state_sound_for_model m i (list_Mfoldl f l acc)
        (fun i' acc => P_const i' /\ P_acc i' acc).
  Proof.
    cleanup_context.
    revert i acc.
    induction l.
    {
      intros.
      eapply state_triple_wkn_ret;
        unfold Sep.and1 in *;
        basic_goal_prep; subst;
        eexists; cbn; intuition eauto with utils.
    }
    {
      intros.
      cbn [list_Mfoldl].
      eapply state_sound_for_model_bind; eauto using monotone1_all.
      {
        basic_goal_prep;
          basic_utils_crush.
      }
      intros.
      eapply IHl; eauto.
      all:basic_goal_prep;
        basic_utils_crush.
      eapply H1.
      all:basic_goal_prep;
        basic_utils_crush.
      eapply map_extends_trans; eauto.
    }
  Qed.
  
  Lemma atom_sound_functional i f args r1 r2
    : atom_sound_for_model m i (Build_atom f args r1) ->
      atom_sound_for_model m i (Build_atom f args r2) ->
      eq_sound_for_model m i r1 r2.
  Proof.
    clear idx_succ idx_zero.
    unfold atom_sound_for_model, eq_sound_for_model; cbn.
    intros; repeat iss_case; inversions; cbn.
    eapply interprets_to_functional; eauto.
  Qed.
  Hint Resolve atom_sound_functional : utils.
  
  Lemma add_parent_sound i ps p
    : atom_sound_for_model m i p ->
      all (atom_sound_for_model m i) ps ->
      state_sound_for_model m i
        (add_parent idx Eqb_idx idx_zero symbol Eqb_symbol symbol_map idx_map idx_trie
           analysis_result ps p)
        (fun i' a => i = i' /\ all (atom_sound_for_model m i') a).
  Proof.
    intro.
    induction ps; cbn [add_parent]; intros.
    { eapply ret_sound_for_model'; cbn; eauto with utils. }
    {
      case_match.
      cbn [all Defs.atom_ret] in *; break.
      case_match.
      eqb_case atom_fn0 atom_fn; 
        cbn - [Mbind Mret].
      1:eqb_case atom_args0 atom_args; 
        cbn - [Mbind Mret].
      {
        ssm_bind.
        {
          eapply union_sound; eauto.
          eapply atom_sound_functional; eauto.
        }
        cbn beta in *; subst.
        eapply ret_sound_for_model'; break; subst; eauto with utils.
        cbn; intuition eauto with utils.
        unfold atom_sound_for_model; cbn in *.
        unfold atom_sound_for_model in H1; cbn in *; subst.
        unfold eq_sound_for_model in H6.
        repeat (iss_case; cbn).
        unfold interprets_to in *; break; subst.
        exists x; intuition eauto.
        etransitivity; eauto.
      }
      {
        ssm_bind.
        eapply ret_sound_for_model'; break; subst; eauto with utils.
        cbn; intuition eauto.
      }
      {
        ssm_bind.
        eapply ret_sound_for_model'; break; subst; eauto with utils.
        cbn; intuition eauto.
      }
    }
  Qed.

  Lemma set_parents_sound i new_idx l
    : all (atom_sound_for_model m i) l ->
      state_sound_for_model m i
        (set_parents idx symbol symbol_map idx_map idx_trie analysis_result new_idx l) 
        (fun i' _ => i = i').
  Proof.
    intros.
    open_ssm.
    intuition cbn in *; eauto with utils.
    eqb_case i0 new_idx.
    { rewrite map.get_put_same in *; inversions; eauto. }
    { rewrite map.get_put_diff in *; eauto. }
  Qed.
        
  
  Lemma repair_sound i a
    : state_sound_for_model m i
        (repair idx_zero a)
        (fun i' _ => i = i').
  Proof.
    cleanup_context.
    destruct a; cbn [repair].
    {
      unfold repair_union.
      eapply state_sound_for_model_bind;
        [ eapply get_parents_sound |].
      cbn beta;intros; subst.
      eapply state_sound_for_model_bind; eauto with utils.
      { eapply remove_parents_sound. }
      cbn beta;intros; subst.
      eapply state_sound_for_model_bind; break; subst; eauto with utils.
      {
        eapply state_sound_for_model_Mmap with (P_const:= eq i'); auto with utils.
        cbn beta;intros; subst.
        eapply state_sound_for_model_bind; eauto with utils.
        { eapply db_remove_sound. }
        cbn beta;intros; subst.
        eapply state_sound_for_model_bind; eauto with utils.
        {
          eapply canonicalize_sound.
          eapply in_all; eassumption.
        }
        {
          cbn beta;intros; break; subst.
          eapply state_sound_for_model_bind; eauto with utils.
          {
            eapply update_entry_sound; eauto with utils.
            eapply eq_atom_implies_sound_l; try symmetry; eauto.
            eapply in_all; eauto.
          }
          cbn beta;intros; break; subst.
          eapply ret_sound_for_model'; intuition eauto with utils.
          eapply eq_atom_implies_sound_l; try symmetry; eauto.
          eapply in_all; eauto.
        }
      }
      cbn beta;intros; subst.
      bind_with_fn get_parents_sound.
      eapply state_sound_for_model_Mseq; break; subst; eauto with utils.
      {
        case_match.
        {
          eapply state_sound_for_model_Miter with (P:= fun i' _ => i'1 = i'); auto with utils.
          cbn beta;intros; subst.
          cleanup_context.
          apply repair_parent_analysis_sound.
        }
        { eapply ret_sound_for_model'; eauto with utils. }
      }
      cbn beta;intros; subst.
      ssm_bind.
      {
        eapply state_sound_for_model_Mfoldl with (P_const:= eq i'); auto.
        {
          cbn beta;intros; subst.
          eapply add_parent_sound; eauto.
          eapply in_all;[| eauto]; auto.
        }
        { cbn; auto. }
        { cbn; eauto with utils. }
      }
      {
        cbn in *; break; subst.
        apply set_parents_sound; eauto.
      }        
    }
    {
      bind_with_fn get_parents_sound.
      eapply state_sound_for_model_Miter; break; subst; auto.
      cbn beta;intros; break; subst.
      eapply repair_parent_analysis_sound.
    }
  Qed. 

  Lemma rebuild_sound i n
    : state_sound_for_model m i (rebuild n) (fun i' _ => i = i').
  Proof.
    induction n.
    {
      basic_goal_prep.
      cbv -[map.rep domain map.get]; intuition.
      eexists; intuition eauto.
    }
    {
      cbn [rebuild].
      eapply state_sound_for_model_bind;
      [eapply pull_worklist_sound
      | intros; subst].
      destruct a.
      { eapply ret_sound_for_model'; break; subst; eauto with utils. }
      eapply state_sound_for_model_bind; eauto with utils.
      {
        eapply state_sound_for_model_Mmap with (P_const:= eq i'); auto.
        {
          intros; break; subst.
          eapply canonicalize_worklist_entry_sound.
          eapply in_all; eauto.
        }
        { eauto using worklist_entry_sound_mono. }
      }
      cbn beta; intros; repeat subst.
      eapply state_sound_for_model_bind; break; subst; eauto with utils.
      {
        eapply state_sound_for_model_Miter with (P:= fun i _ => i'0 = i); auto.
        {
          intros; break; subst.
          cleanup_context.
          eapply repair_sound.
        }
      }
      cbn beta; intros; repeat subst.
      eauto.
    }
  Qed.

  
  (*TODO: move to coqutil *)
  Lemma extends_put_None {key value : Type} {map : map.map key value} `{@map.ok _ _ map}
                         `{Eqb_ok key}
    (i : map) k v
    : map.get i k = None -> map.extends (map.put i k v) i.
  Proof.
    repeat intro.
    eqb_case x k;
      [ rewrite map.get_put_same | rewrite map.get_put_diff by eauto ];
      congruence.
  Qed.

  (*TODO: move to UnionFind.v*)
  Arguments UnionFind.alloc {idx}%type_scope {idx_map rank_map} succ%function_scope pat.

  
  Lemma forest_cons l u (x : idx)
    : forest _ _ l u ->
      ~ Sep.has_key x u ->
      forest _ _ (x::l) (map.put u x x).
  Proof.
    clear idx_zero idx_succ.
    exists (map.singleton x x), u;
      basic_goal_prep;
      basic_utils_crush.
    {
      eapply Sep.map_split_singleton_l; intuition eauto.
      unfold Sep.has_key in *; case_match; tauto.
    }
    { eapply tree_singleton; eauto. }
  Qed.

  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (idx_succ x))
    (lt_trans : Transitive lt).

  Existing Instance lt_trans.

  Lemma asymmetric_unequal a b
    : lt a b -> a <> b.
  Proof. repeat intro; subst; eapply asymmetry; eauto. Qed.
  Hint Resolve asymmetric_unequal : utils.
  
  (*TODO: move to UnionFind.v*)
  Lemma alloc_preserves_ok u l u' x
    : union_find_ok lt u l ->
      UnionFind.alloc idx_succ u = (u', x) ->
      union_find_ok lt u' (x::l).
  Proof.
    clear idx_zero.
    destruct u;
    unfold UnionFind.alloc;
      basic_goal_prep; inversions.
    destruct H1; constructor; basic_goal_prep; eauto.
    { eapply forest_cons; eauto. }
    {
      eqb_case k x.
      { exists 0; rewrite map.get_put_same; auto. }
      {
        rewrite !map.get_put_diff in * by eauto.
        apply rank_covers_domain in H1; eauto.
      }
    }
    {
      eqb_case i x; [ repeat (rewrite !map.get_put_same in *; auto; inversions; tauto)
                    | rewrite !map.get_put_diff in * by eauto].
      pose proof H1 as H1';
        eapply forest_closed in H1'; eauto.
      eapply next_upper_bound in H1'.
      assert (j <> x) by auto with utils.
      rewrite !map.get_put_diff in * by eauto.
      eapply rank_increasing in H1; eauto.
    }
    { 
      eqb_case i x; [ repeat (rewrite !map.get_put_same in *; auto; inversions)
                    | rewrite !map.get_put_diff in * by eauto];
        eauto; Lia.lia.
    }
    {
      rewrite has_key_put in *; eauto.
      intuition subst; eauto.
    }
  Qed.

  (*TODO: move to UnionFind.v*)
  Arguments next {idx}%type_scope {idx_map rank_map} u.
  
  Lemma alloc_next u u' i0
    : UnionFind.alloc idx_succ u = (u', i0) ->
      i0 = u.(next).
  Proof.
    destruct u;
      unfold UnionFind.alloc; cbn; intros; inversions.
    reflexivity.
  Qed.

  Hint Rewrite has_key_put : utils.

  (*TODO: move to Sep*)
  Lemma get_put_None A (i : idx_map A) k x v v'
    : map.get i x = None ->
      map.get i k = Some v' ->
      map.get (map.put i x v) k = Some v'.
  Proof.
    eqb_case k x; [congruence |].
    rewrite map.get_put_diff; eauto.
  Qed.
  
  Lemma Mmap_get_put_None A (i : idx_map A) l l' x v
    : map.get i x = None ->
      list_Mmap (map.get i) l = Some l' ->
      list_Mmap (map.get (map.put i x v)) l = Some l'.
  Proof.
    revert l';
      induction l;
      basic_goal_prep;
      repeat case_match; try tauto;
      inversions;
      intuition eauto using get_put_None.
    {
      eapply get_put_None with (v:=v) in case_match_eqn1; eauto.
      replace a0 with a1 by congruence.
      f_equal.
      eapply IHl with (l':=l1) in H1; inversions; eauto.
    }
    {
      eapply IHl with (l':=l0) in H1; inversions; eauto.
    }
    {
      eapply get_put_None with (v:=v) in case_match_eqn0; eauto.
      congruence.
    }
  Qed.


  Ltac key_case x y :=
    eqb_case x y; [ rewrite !map.get_put_same in *
                  | rewrite !map.get_put_diff in * by eauto ].
  
  
  (*TODO: move to union_find *)
  Arguments closed_graph {idx}%type_scope {idx_map} m. 
  
  Lemma PER_closure_put parent x i1 i2
    : closed_graph parent ->
      map.get parent x = None ->
      PER_closure (fun i j : idx => map.get (map.put parent x x) i = Some j) i1 i2
      <-> PER_closure (fun i j : idx => map.get parent i = Some j) i1 i2
          \/ (i1 = x /\ i2 = x).
  Proof.
    intuition subst.
    2:{
      eapply subrelation_PER_closure; eauto.
      repeat intro.
      key_case x0 x; congruence.
    }
    2:{ constructor 1; rewrite map.get_put_same; auto. }
    {
      induction H3; basic_goal_prep; basic_utils_crush.
      key_case x a; inversions; basic_utils_crush.
    }
  Qed.

  
  Lemma next_None uf l
    : union_find_ok lt uf l ->
      map.get uf.(parent) uf.(next) = None.
  Proof.
    destruct uf, 1; basic_goal_prep.
    destruct (map.get parent next) eqn:H'; try congruence.
    exfalso.
    assert (Sep.has_key next parent).
    { unfold Sep.has_key in *; rewrite H' in *; auto. }
    apply next_upper_bound in H1.
    eapply asymmetric_unequal; eauto.
  Qed.

  
  Lemma map_get_None_contradiction A (i : idx_map A) next
    : (~Is_Some (map.get i next)) -> map.get i next = None.
  Proof. unfold Is_Some; destruct (map.get i next); intuition congruence. Qed.
  
  Lemma alloc_sound i time_travel_term
    : m.(domain_wf) time_travel_term ->
      state_sound_for_model m i
        (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result)
        (fun i' x => map.get i' x = Some time_travel_term).
  Proof.
    clear idx_zero.
    unfold alloc.
    repeat intro.
    unfold Sep.and1 in *; break.
    case_match; cbn.
    pose proof case_match_eqn as H';
      eapply alloc_next in H'; subst.
    exists (map.put i (equiv e).(next) time_travel_term).
    basic_goal_prep; intuition auto.
    { rewrite map.get_put_same; eauto. }
    {
      destruct H2 as [ [] ].
      eapply alloc_preserves_ok in case_match_eqn; eauto.
      constructor; eexists; cbn; eauto.
    }
    2:{
      eapply extends_put_None.
      destruct (map.get i (next (equiv e))) eqn:Hget; auto.
      exfalso.
      assert (Is_Some (map.get i (next (equiv e)))) as Hsome
          by (rewrite Hget; cbn; auto).
      clear d Hget.
      eapply interpretation_exact in Hsome; eauto.
      
      destruct H2 as [ [] ].
      eapply next_upper_bound in Hsome; eauto.
    }
    {
      destruct H3; constructor; basic_goal_prep; eauto.
      {
         unfold UnionFind.alloc in *; destruct e; destruct equiv;cbn in *;
           inversions.
         eqb_case next i0;
           [rewrite !map.get_put_same in *
           |rewrite !map.get_put_diff in * by eauto ];
           inversions; eauto.
      }
      {
        unfold UnionFind.alloc in *; destruct e; destruct equiv;cbn in *;
          inversions; cbn in *.
        eqb_case next x;
          [rewrite !map.get_put_same in *
          |rewrite !map.get_put_diff in * by eauto ];
          inversions; basic_utils_crush.
      }
      {
        unfold atom_in_egraph in *; cbn in *.
        eapply atom_interpretation0 in H3.
        eapply atom_sound_monotone; eauto.
        apply extends_put_None.
        destruct H2 as [ [] ].
        enough (~ Sep.has_key (next (equiv e)) i).
        { unfold Sep.has_key in *; case_match; try congruence; tauto. }
        intro.
        apply interpretation_exact0 in H4.
        eapply next_upper_bound in H4; eauto.
      }
      {
        destruct e; destruct equiv;
        unfold uf_rel_PER, UnionFind.alloc in *;
          basic_goal_prep; inversions; basic_goal_prep.
        eapply PER_closure_put in H3.
        2:{
          destruct H2 as [ [? H2] ].
          eapply uf_forest in H2; cbn in *; eauto.
          eapply forest_closed; eauto.
        }
        2:{
          destruct H2 as [ [? H2] ]; cbn in H2.
          eapply next_None in H2; cbn in H2; auto.
        }
        intuition subst.
        { eapply rel_interpretation0 in H4.
          eapply eq_sound_monotone; eauto.
          apply extends_put_None.
          destruct H2 as [ [? H2] ]; cbn in H2.
          eapply next_None in H2; cbn in H2; auto.
          apply map_get_None_contradiction; repeat intro.
          apply interpretation_exact0 in H3.
          unfold Sep.has_key in *; rewrite H2 in *; auto.
        }
        {
          unfold eq_sound_for_model; rewrite map.get_put_same; cbn.
          auto.
        }
      }
      {
        eapply monotone1_all; [apply atom_sound_monotone | | eauto].
        apply extends_put_None.
        destruct H2 as [ [? H2] ]; cbn in H2.
        eapply next_None in H2; cbn in H2; auto.
        apply map_get_None_contradiction; repeat intro.
        apply interpretation_exact0 in H4.
        unfold Sep.has_key in *; rewrite H2 in *; auto.
      }
      {
        eapply monotone1_all; [apply worklist_entry_sound_mono| | eauto].
        apply extends_put_None.
        destruct H2 as [ [? H2] ]; cbn in H2.
        eapply next_None in H2; cbn in H2; auto.
        apply map_get_None_contradiction; repeat intro.
        apply interpretation_exact0 in H3.
        unfold Sep.has_key in *; rewrite H2 in *; auto.
      }
    }        
  Qed.

  (*
  Lemma list_Mfoldl_map A B C (g : A -> B) M `{Monad M} (f : C -> B -> M C) l acc
    : list_Mfoldl f (map g l) acc = list_Mfoldl (fun acc x => f acc (g x)) l acc.
  Proof using.
    revert acc; induction l;
      basic_goal_prep;
      basic_utils_crush.
    (*TODO: needs Mbind_ext?*)
  Admitted. *)

  (* TODO: Define and implement monad.ok *)
  (*TODO: avoid depending on funext if possible *)
  Lemma Mbind_assoc (T1 T2 T3 : Type) S (f : T1 -> state S T2) (g : T2 -> state S T3) ma
    : Mbind (fun a : T1 => @! let p <- f a in (g p)) ma = Mbind g (@! let p <- ma in (f p)).
  Proof.
    (*TODO: primitive pairs would validate this. *)
    cbn.
    apply FunctionalExtensionality.functional_extensionality;
      intros; repeat case_match; eauto.
  Qed.
  Lemma Mbind_Mret : forall (T1 T2 : Type) S (f : T1 -> state S T2) v,
      Mbind f (Mret v) = f v.
  Proof. intros; reflexivity. Qed.

  
  (*TODO: Move to a better spot*)
  Lemma set_eq_refl A (l : list A) : set_eq l l.
  Proof. unfold set_eq, incl; intuition auto. Qed.
  Hint Resolve set_eq_refl : utils.
  
  Lemma set_eq_trans A : Transitive (A:=list A) set_eq.
  Proof. unfold set_eq, incl; repeat intro; intuition auto. Qed.
  
  Lemma set_eq_sym A : Symmetric (A:=list A) set_eq.
  Proof. unfold set_eq, incl; repeat intro; intuition auto. Qed.

  Add Parametric Relation {A : Type} : (list A) (set_eq)
    reflexivity proved by (set_eq_refl _)
    symmetry proved by (set_eq_sym _)
    transitivity proved by (set_eq_trans _)
      as set_eq_rel.

  Instance perm_set_eq_subrel {A} : subrelation (Permutation.Permutation (A:=A)) (set_eq (A:=A)).
  Proof.
    unfold set_eq, incl.
    repeat intro.
    intuition auto.
    { rewrite <- H1; auto. }
    { rewrite H1; auto. }
  Qed.
  
  Lemma map_keys_put A (acc : idx_map A) a a0
    : set_eq (map.keys (map.put acc a a0)) (a::map.keys acc).
  Proof.
    unfold set_eq, incl.
    repeat intro; cbn in *.
    intuition auto; cbn; rewrite map_keys_in' in *.
    all: key_case a a1; inversions; intuition auto.
  Qed.

  
  (*TODO: move *)
  Instance set_eq_cons_Proper {A}
    : Proper (eq ==> set_eq ==> set_eq) (@ cons A).
  Proof. unfold set_eq, incl; repeat intro; cbn in *; subst; intuition eauto. Qed.
  
  (*TODO: move *)
  Instance set_eq_app_Proper {A}
    : Proper (set_eq ==> set_eq ==> set_eq) (@ app A).
  Proof.
    unfold set_eq, incl; repeat intro; cbn in *; subst.
    basic_goal_prep.
    basic_utils_crush.
  Qed.
  
  (*TODO: move *)
  Instance set_eq_in_Proper {A}
    : Proper (eq ==> set_eq ==> iff) (@ In A).
  Proof. unfold set_eq, incl; repeat intro; cbn in *; subst; intuition eauto. Qed.

  
  Lemma in_all_iff {A} (P : A -> Prop) l
    : all P l <-> (forall x, In x l -> P x).
  Proof.
    induction l;
    basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  (*TODO: move *)
  Instance set_eq_all_Proper {A}
    : Proper (Sep.Uiff1 ==> set_eq ==> iff) (@all A).
  Proof.
    unfold set_eq, incl, Sep.Uiff1;
      repeat intro; cbn in *; subst;
      intuition eauto;
      rewrite !in_all_iff in *;
      firstorder auto.    
  Qed.
  
  Instance set_eq_map_Proper {A B}
    : Proper (eq ==> set_eq ==> set_eq) (@map A B).
  Proof.
    unfold set_eq, incl;
      repeat intro; cbn in *; subst;
      intuition eauto; rewrite !in_map_iff in *; break; subst;
      rewrite <- in_map_iff;
      apply in_map; eauto.
  Qed.
    
  (* `time_travel_terms` should be a set of terms determined by code that is run later.
     Another way of looking at this lemma is that for any list of assignments for vars,
     fresh allocation is compatible with the evaluation determined by that list.
     TODO: see if this works.
   *)
  Lemma allocate_existential_vars_sound i vars acc time_travel_terms
    : Datatypes.length time_travel_terms = Datatypes.length vars ->
      all m.(domain_wf) time_travel_terms ->
      NoDup vars ->
      all (fun x => ~Sep.has_key x acc) vars ->
      state_sound_for_model m i
        (allocate_existential_vars idx idx_succ symbol symbol_map
           idx_map idx_trie analysis_result
           vars acc)
        (fun i a =>
           map.extends a acc
           /\ all2 (fun x t => map.get a x <$> (fun k => map.get i k = Some t))
                vars time_travel_terms
           /\ set_eq (map.keys a) (vars ++ (map.keys acc))).
  Proof.
    unfold allocate_existential_vars.
    intros.
    {
      revert i acc time_travel_terms H1 H2 H3 H4.
      induction vars; destruct time_travel_terms;
        cbn [list_Mfoldl Datatypes.length] in *; intros; try congruence.
      {
        eapply ret_sound_for_model';
          basic_goal_prep;
          basic_utils_crush.
      }
      rewrite <- !Mbind_assoc.
      ssm_bind.
      { apply alloc_sound with (time_travel_term:= d); basic_goal_prep; intuition eauto. }
      rewrite Mbind_Mret.
      eapply state_sound_for_model_wkn.
      {
        inversion H1; inversion H3; subst; basic_goal_prep.
        eapply IHvars; basic_goal_prep; intuition eauto.
        eapply all_wkn; try eassumption.
        intros.
        basic_utils_crush.
      }
      {
        inversion H1; inversion H3; break; subst.
        repeat basic_goal_prep.
        intuition eauto.
        {
          eapply map_extends_trans; eauto.
          apply extends_put_None.
          apply Sep.not1_has_key.
          auto.
        }
        {
          assert (map.get (map.put acc a a0) a = Some a0)
            by apply map.get_put_same.
          erewrite H9 by eassumption; cbn.
          erewrite H7 by eassumption; eauto.
        }
        {
          rewrite map_keys_put in H13.
          change (?a::?l) with ([a]++l) in H13.
          rewrite Permutation.Permutation_app_comm in H13.
          cbn in *. 
          rewrite Permutation.Permutation_app_comm in H13.
          auto.
        }
      }
    }
  Qed.

  (*TODO: move to utils.v *)
  Lemma all_True A P (l : list A)
    : (forall x, P x) -> all P l.
  Proof.
    intro.
    induction l;
      basic_goal_prep;
      eauto.
  Qed.

  Definition atom_subst_map (m : idx_map idx) (a : atom) : atom :=
    (Build_atom a.(atom_fn)
                    (map (fun x : idx => unwrap_with_default (map.get m x)) (atom_args a))
                    (unwrap_with_default (map.get m (atom_ret a)))).
  
  Lemma exec_clause_sound i acc a
    : (*TODO: should this be split in 2? *)
    (atom_sound_for_model m i (atom_subst_map acc a)) ->
    state_sound_for_model m i
      (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result acc a)
      (* no conclusion because the assumption takes care of making sure i is right
         by interacting with allocation's "time travel"
       *)
          (fun _ _ => True).
  Proof.
    unfold exec_clause.
    intros.
    ssm_bind.
    {      
      eapply state_sound_for_model_Mmap_dep with (P_const:= eq i); auto.
      {
        cbn beta;intros; subst.
        eapply find_sound.
        unfold atom_subst_map, atom_sound_for_model in *; basic_goal_prep.
        repeat iss_case.
        rewrite TrieMap.Mmap_option_all in *.
        eapply In_option_all in Hma; eauto.
        2:{ eapply in_map; eauto. }
        break.
        unfold Sep.has_key; rewrite H4; auto.
      }
      {
        repeat intro; cbn beta.
        eapply eq_sound_monotone; eauto with utils.
      }
    }
    cbn beta in *; intros; break; subst.
    ssm_bind.
    {
      apply find_sound.
      unfold atom_subst_map, atom_sound_for_model in *; basic_goal_prep.
      repeat iss_case.
      unfold Sep.has_key; rewrite Hma0; auto.
    }
    cbn beta in *; intros; break; subst.
    eapply state_sound_for_model_wkn.
    {
      eapply update_entry_sound; eauto.
      unfold atom_sound_for_model, atom_subst_map in *.
      basic_goal_prep.
      repeat iss_case.
      unfold eq_sound_for_model in *.
      rewrite Hma0 in *; cbn in *.
      repeat iss_case; cbn in *.
      rewrite <- TrieMap.all2_map_l
        with (f:= map.get i'0)
             (R:= (fun a a0 => a <$> (fun x' : domain m => map.get i'0 a0 <$> domain_eq m x')))
        in H4.
      rewrite all2_Is_Some_satisfying_l in H4.
      rewrite <- TrieMap.Mmap_option_all in *.
      rewrite Hma in *; cbn in*.
      rewrite <- TrieMap.all2_map_r
        with (f:= map.get i'0)
             (R:= (fun x a0 => a0 <$> domain_eq m x))
        in H4.
      rewrite all2_Is_Some_satisfying_r in H4.
      rewrite <- TrieMap.Mmap_option_all in *.
      repeat iss_case; cbn in *.
      unfold interprets_to in *; break.
      eapply interpretation_preserving with (f:=(atom_fn a)) in H4; eauto.
      rewrite H1 in *; cbn in *; case_match; try tauto.
      eexists; split; eauto.
      etransitivity; try eassumption.
      etransitivity; try apply H2.
      symmetry; eauto.
    }
    { eauto. }
  Qed.    

  (*TODO: move*)
  Arguments const_vars {idx symbol}%type_scope c.
  Arguments const_clauses {idx symbol}%type_scope c.
  Arguments const_unifications {idx symbol}%type_scope c.

  Definition clauses_of_const r :=
    (map atom_clause r.(const_clauses)) ++ (map (uncurry eq_clause) r.(const_unifications)).
  
  Record const_rule_sound_for_evaluation (*m*) i r : Prop :=
    {
      (* rule wfness properties *)
      const_vars_NoDup : NoDup r.(const_vars);
      const_vars_all_used : set_eq r.(const_vars) (flat_map clause_vars (clauses_of_const r));
      (* evaluation-related properties *)
      (* TODO: a field or an argument? *)
      const_rule_assignment : idx_map idx;
      const_rule_eval_dom : set_eq r.(const_vars) (map.keys const_rule_assignment);
      const_rule_assignment_sound
      : forall x y, map.get const_rule_assignment x = Some y ->
                    eq_sound_for_model m i y y;
      const_clauses_sound : all (fun a => atom_sound_for_model m i
                                      (atom_subst_map const_rule_assignment a))
                        r.(const_clauses);
      const_eqns_sound
      : all (fun '(x,y) =>
               map.get const_rule_assignment x <$> (fun x' =>
               map.get const_rule_assignment y <$> (fun y' =>
               eq_sound_for_model m i x' y')))
          r.(const_unifications);
    }.

  Hint Resolve const_vars_NoDup : utils.

  
  (*TODO: move*)
  Lemma all2_all A R (l : list A)
    : all2 R l l <-> all (fun x => R x x) l.
  Proof.
    clear.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite all2_all : utils.

  (*TODO: move*)
  
  Lemma all_map A B P (f : A -> B) l
    : all P (map f l) <-> all (fun x => P (f x)) l.
  Proof.
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma all_flat_map A B P (f : A -> list B) l
    : all P (flat_map f l) <-> all (fun x => all P (f x)) l.
  Proof.
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma domain_eq_wf_l d d'
    : domain_eq m d d' -> domain_wf m d.
  Proof.
    unfold domain_wf.
    intro H'; etransitivity;[| symmetry]; apply H'.
  Qed.
  Hint Resolve domain_eq_wf_l : utils.
  
  Lemma domain_eq_wf_r d d'
    : domain_eq m d d' -> domain_wf m d'.
  Proof.
    unfold domain_wf.
    intro H'; etransitivity;[symmetry |]; apply H'.
  Qed.
  Hint Resolve domain_eq_wf_r : utils.

  
  Lemma set_eq_empty A (l : list A)
    : set_eq [] l <-> l = [].
  Proof using.
    clear.
    unfold set_eq, incl;
    destruct l; cbn;
      intuition  subst; eauto; try congruence.
    specialize (H1 a); intuition.
  Qed.

  Lemma exec_const_sound i r
    : const_rule_sound_for_evaluation i r ->
      state_sound_for_model m i
        (exec_const idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie
           analysis_result r) (fun _ _ => True).
  Proof.
    intros.
    unfold exec_const.
    destruct H1.
    destruct
      (list_Mmap (fun x => Mbind (map.get i) (map.get const_rule_assignment x)) (const_vars r)) as [ d_lst |] eqn:Httt.
    2:{
      exfalso.
      rewrite TrieMap.Mmap_option_all in *.
      apply option_all_None in Httt.
      break.
      apply nth_error_In in H1.
      apply in_map_iff in H1; break.
      rewrite const_rule_eval_dom in H2.
      rewrite map_keys_in' in H2.
      case_match; try tauto; cbn in *.
      apply const_rule_assignment_sound in case_match_eqn.
      unfold eq_sound_for_model in *; rewrite H1 in *; cbn in *; tauto.
    }
    (*TODO: this is a circuitous proof *)
    destruct d_lst as [| d_hd d_tl].
    {
      rewrite TrieMap.Mmap_option_all in *.
      apply length_option_all in Httt.
      cbn in Httt.
      destruct r; cbn in *.
      destruct const_vars; cbn in *; try congruence.
      apply set_eq_empty in const_vars_all_used0.
      rewrite flat_map_app in const_vars_all_used0.
      apply app_eq_nil in const_vars_all_used0.
      unfold uncurry in const_vars_all_used0.
      replace const_clauses with (@nil atom) in *.
      1:replace const_unifications with (@nil (idx*idx)) in *.
      {
        cbn.
        eapply ret_sound_for_model'; auto.
      }
      {
        destruct const_unifications; try congruence; exfalso.
        break; cbn in *; congruence.
      }
      {
        destruct const_clauses; try congruence; exfalso.
        break; cbn in *; congruence.
      }
    }
    ssm_bind.
    1:eapply allocate_existential_vars_sound
      with (time_travel_terms :=
              map (fun x => unwrap_with_default (H:=_)
                              (Mbind (map.get i) (map.get const_rule_assignment x)))
                (const_vars r)); eauto with utils.
    3:{ eapply all_True; basic_goal_prep; rewrite has_key_empty; tauto. }
    3:{
      cbn beta in *; break; subst.
      rewrite TrieMap.all2_map_r in *.
      autorewrite with utils in *; eauto.
      assert (forall x i'0, In x (const_vars r) ->
                           map.extends i'0 i' ->
                            map.get i'0 (unwrap_with_default (map.get a x))
                            = map.get i'0 (unwrap_with_default (map.get const_rule_assignment x))).
          {
            intros.
            pose proof H5.
            eapply in_all in H5; eauto; cbn in *.
            repeat iss_case; cbn in *.
            eapply const_rule_eval_dom in H7.
            rewrite map_keys_in' in H7.
            case_match; try tauto.
            eapply H6 in H5; rewrite H5; cbn.
            eapply const_rule_assignment_sound in case_match_eqn.
            unfold eq_sound_for_model in *; repeat iss_case; cbn.
            eapply H1 in Hma0.
            eapply H6 in Hma0.
            cbn; congruence.
          }
      ssm_bind.
      {
        eapply state_sound_for_model_Miter with (P:=(fun (_ : idx_map (domain m)) (_ : unit) => True));
          auto.
        intros.
        eapply state_sound_for_model_wkn.
        {
          eapply exec_clause_sound.
          assert (forall l,
                     incl l (const_vars r) ->
                     list_Mmap (fun x => map.get i'0 (unwrap_with_default (map.get a x))) l
                     = list_Mmap (fun x => map.get i'0 (unwrap_with_default
                                                          (map.get const_rule_assignment x))) l).
          {
            induction l; basic_goal_prep; intuition eauto.
            rewrite H5 by (basic_goal_prep; basic_utils_crush).
            case_match; eauto.
            rewrite IHl by (basic_goal_prep; basic_utils_crush).
            reflexivity.
          }          
          eapply in_all in const_clauses_sound; eauto.
          unfold atom_sound_for_model, atom_subst_map in *; cbn in *.
          rewrite ?TrieMap.Mmap_option_all, ?List.map_map, <- ?TrieMap.Mmap_option_all in *.
          rewrite H9.
          2:repeat intro;           
            apply const_vars_all_used0;
              unfold clauses_of_const;
              rewrite flat_map_app,
              !flat_map_concat_map,
              !List.map_map,
              <- !flat_map_concat_map,
              in_app_iff,
              !in_flat_map;
              cbn;
              left;eexists; now intuition eauto.
          repeat iss_case.
          replace (list_Mmap (fun x : idx => map.get i'0 (unwrap_with_default
                                                            (map.get const_rule_assignment x)))
                     (atom_args a0))
            with (Some l).
          2:{
            rewrite TrieMap.Mmap_option_all in *.
            symmetry.
            rewrite <- Hma; f_equal.
            eapply map_ext_in.
            intros.
            eapply in_map in H10.
            eapply In_option_all in H10; eauto.
            break; subst.
            rewrite H10.
            eapply H1 in H10; eapply H7 in H10.
            auto.
          }
          cbn.
          rewrite H5; auto.
          2:repeat intro;           
            apply const_vars_all_used0;
              unfold clauses_of_const;
              rewrite flat_map_app,
              !flat_map_concat_map,
              !List.map_map,
              <- !flat_map_concat_map,
              in_app_iff,
              !in_flat_map;
              cbn;
          left;eexists; now intuition eauto.
          apply H1 in Hma0; apply H7 in Hma0.
          rewrite Hma0.
          cbn.
          auto.
        }
        cbn; auto.
      }
      apply state_sound_for_model_Miter with (P:=(fun (_ : idx_map (domain m)) (_ : unit) => True));
        auto.
      intros; break.
      eapply state_sound_for_model_wkn; auto.
      apply union_sound.
      eapply eq_sound_monotone; eauto.
      pose proof H8.
      eapply in_all in H8; eauto.
      cbn in H8.
      unfold eq_sound_for_model in *.
      repeat iss_case.
      rewrite !H5; eauto.
      2,3:
        apply const_vars_all_used0;
        unfold clauses_of_const;
        rewrite flat_map_app,
          !flat_map_concat_map,
          !List.map_map,
          <- !flat_map_concat_map,
          in_app_iff,
          !in_flat_map;
          cbn;
        right;eexists; intuition eauto;
        cbn; now intuition eauto.
      rewrite Hma, Hma0.
      cbn.
      eapply H1 in Hma1; eapply H6 in Hma1; rewrite Hma1; cbn.
      eapply H1 in Hma2; eapply H6 in Hma2; rewrite Hma2; cbn.
      auto.
    }
    { basic_utils_crush. }
    {
      pose proof const_vars_all_used0.
      eapply set_eq_map_Proper in const_vars_all_used0; eauto.
      eapply set_eq_all_Proper in const_vars_all_used0; [| repeat intro; reflexivity ].
      eapply const_vars_all_used0.
      unfold clauses_of_const.
      rewrite flat_map_app, map_app, all_app.
      clear const_vars_all_used0.
      repeat rewrite ?all_map, ?all_flat_map; split.
      2:{
        eapply all_wkn; try eassumption.
        basic_goal_prep.
        repeat iss_case; cbn.
        unfold eq_sound_for_model in *; repeat iss_case; cbn; intuition eauto with utils.
      }
      {
        eapply all_wkn; try eassumption.
        basic_goal_prep.
        assert (Sep.has_key (atom_ret x) const_rule_assignment).
        {
          apply map_keys_in'.
          rewrite <- const_rule_eval_dom.
          rewrite -> H1.
          unfold clauses_of_const.
          rewrite ?flat_map_app, ?map_app, ?all_app, in_app_iff.
          left.
          destruct r; cbn in *.
          rewrite in_flat_map.
          exists (atom_clause x).
          split; [ eapply in_map; eauto | destruct x; cbn; eauto].
        }
        unfold Sep.has_key in H4; case_match; try tauto.
        split.
        {
          apply const_rule_assignment_sound in case_match_eqn.
          unfold eq_sound_for_model in *;
            repeat iss_case; cbn; eauto with utils.
        }
        {
          apply in_all_iff.
          intros.
          assert (Sep.has_key x0 const_rule_assignment).
          {
            apply map_keys_in'.
            rewrite <- const_rule_eval_dom.
            rewrite -> H1.
            unfold clauses_of_const.
            rewrite ?flat_map_app, ?map_app, ?all_app, in_app_iff.
            left.
            destruct r; cbn in *.
            rewrite in_flat_map.
            exists (atom_clause x).
            split; [ eapply in_map; eauto | destruct x; cbn; eauto].
          }
          unfold Sep.has_key in H6; case_match; try tauto.
          apply const_rule_assignment_sound in case_match_eqn0.
          unfold eq_sound_for_model in *;
            repeat iss_case; cbn; eauto with utils.
        }
      }
    }
    Unshelve.
    exact d_hd.
  Qed.

  Lemma const_rule_sound_monotone : monotone1 const_rule_sound_for_evaluation.
  Proof.
    repeat intro.
    destruct H2; econstructor; intros; eauto with utils.
    { eapply eq_sound_monotone; eauto. }
    {
      eapply all_wkn; try eassumption.
      intros; eapply atom_sound_monotone; eauto.
    }
    {
      eapply all_wkn; try eassumption.
      basic_goal_prep; repeat iss_case; cbn.
      eapply eq_sound_monotone; eauto.
    }      
  Qed.
  
  Lemma process_const_rules_sound i rs
    : all (const_rule_sound_for_evaluation i)
        (compiled_const_rules idx symbol symbol_map idx_map rs) ->
      state_sound_for_model m i
        (process_const_rules idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie
           analysis_result rs)
        (fun _ _ => True).
  Proof.
    unfold process_const_rules.
    intros.
    eapply state_sound_for_model_Miter; eauto.
    intros.
    apply exec_const_sound.
    eapply in_all; eauto.
    eapply all_wkn; try eassumption.
    intros; eapply const_rule_sound_monotone; eauto.
  Qed.

  Lemma increment_epoch_sound i
    : state_sound_for_model m i
        (increment_epoch idx idx_succ symbol symbol_map idx_map idx_trie
           analysis_result) (fun _ _ => True).
  Proof.
    open_ssm; destruct e; break; try eexists; intros; cbn; eauto.
  Qed.

 

  Definition atom_of_access f (access : list nat * nat) args : atom :=
    Build_atom f (map (fun n => nth n args default) (fst access))
      (nth (snd access) args default).
  
  Definition trie_sound_for_model i f trie (access : list nat * nat) :=
    forall k, map.get trie k = Some tt ->
              atom_sound_for_model m i (atom_of_access f access k).
  
  Arguments query_ptr_symbol {idx symbol}%type_scope e.
  Arguments query_ptr_ptr {idx symbol}%type_scope e.
  
  Definition lookup_trie_sound_for_model i tries
    (query_clauses : symbol_map (idx_map (list nat * nat)%type)) f x :=
    forall qc' access,
      map.get query_clauses f = Some qc' ->
      map.get qc' x = Some access ->
      forall tries',
        map.get tries f = Some tries' ->
        forall t1 t2,
          map.get tries' x = Some (t1, t2) ->
          trie_sound_for_model i f t1 access
          /\ trie_sound_for_model i f t2 access.

  Definition ptr_trie_sound_for_model i tries
    (query_clauses : symbol_map (idx_map (list nat * nat)%type))
    (p : erule_query_ptr _ _) :=
    lookup_trie_sound_for_model i tries query_clauses p.(query_ptr_symbol) p.(query_ptr_ptr).

  Definition tries_sound_for_model i tries
    (query_clauses : symbol_map (idx_map (list nat * nat)%type)) :=
    forall f x, lookup_trie_sound_for_model i tries query_clauses f x.
  
  Arguments query_vars {idx symbol}%type_scope _.
  Arguments write_vars {idx symbol}%type_scope _.
  Arguments query_ptr_args {idx symbol}%type_scope _.

  (*
  Record rule_vars_wf (*i*) (*qc*) (r : erule symbol idx) :=
    {
      (* rule wfness properties *)
      query_vars_NoDup : NoDup r.(query_vars);
      write_vars_NoDup : NoDup r.(query_vars);
      rule_vars_disjoint
      : disjoint (fun x => In x r.(query_vars))
          (fun x => In x r.(write_vars));
    }.
   *)

  Definition assignment_sound_for_ptr i qc qa ptr :=
    incl ptr.(query_ptr_args) (map fst qa) /\
    match map.get qc ptr.(query_ptr_symbol) with
    | Some qc' =>
        match map.get qc' ptr.(query_ptr_ptr) with
        | Some access => 
            atom_sound_for_model m i
              (atom_subst qa
                 (atom_of_access ptr.(query_ptr_symbol) access ptr.(query_ptr_args)))
        | None => False
        end
    | None => False
    end.

  Definition as_list {A} (l : ne_list A) :=
    cons (fst l) (snd l).
  Arguments as_list {A}%type_scope !l.
  
  
  Definition query_assignment_sound i qc qa ptrs :=
    all (assignment_sound_for_ptr i qc qa) (as_list ptrs).
  
  Arguments query_clause_ptrs {idx symbol}%type_scope _.
  Arguments write_clauses {idx symbol}%type_scope _.
  Arguments write_unifications {idx symbol}%type_scope _.
      
  Record rule_sound_for_evaluation' i qc (r : erule idx symbol) : Prop :=
    {
      (* rule wfness properties *)
      vars_NoDup : NoDup (r.(write_vars)++r.(query_vars));
      write_clauses_well_scoped
      : incl (flat_map (fun a => atom_ret a :: atom_args a)
                r.(write_clauses)) (r.(query_vars) ++ r.(write_vars));
      write_unifications_well_scoped
      : incl (flat_map (fun p => [fst p; snd p])
                r.(write_unifications)) (r.(query_vars) ++ r.(write_vars));
      (*rule_vars_disjoint
      : disjoint (fun x => In x r.(query_vars))
          (fun x => In x r.(write_vars));*)
      rule_vars_covered : incl r.(query_vars)
                                   (flat_map query_ptr_args
                                      (as_list r.(query_clause_ptrs)));
      rule_assignment : named_list idx (named_list idx idx -> idx);
      rule_assignment_dom
      : r.(write_vars) = (map fst rule_assignment);
      rule_assignment_sound
      : forall x f, In (x,f) rule_assignment ->
                    forall qa, query_assignment_sound i qc qa r.(query_clause_ptrs) ->
                               eq_sound_for_model m i (f qa) (f qa);
      write_assignment :=
        fun qa => (named_map (fun f => f qa) rule_assignment) ++ qa;
      clauses_sound
      : forall qa, query_assignment_sound i qc qa r.(query_clause_ptrs) ->
                   all (fun c => atom_sound_for_model m i (atom_subst (write_assignment qa) c))
                     r.(write_clauses);
      eqns_sound
      : forall qa, query_assignment_sound i qc qa r.(query_clause_ptrs) ->
                   all (fun '(x,y) =>
                          exists vx vy,
                            In (x,vx) qa
                            /\ In (y,vy) qa
                            /\ eq_sound_for_model m i vx vy)
                     r.(write_unifications);
    }.

  
  Lemma in_flat_map_incl A B (f : A -> list B) a l
    : In a l -> incl (f a) (flat_map f l).
  Proof.
    clear.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Hint Rewrite NoDup_cons_iff : inversion.
  
  Lemma named_list_lookup_in A `{Eqb_ok A} B (x:A) (xv:B) l d
    : NoDup (map fst l) -> In (x,xv) l -> named_list_lookup d l x = xv.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
    eqb_case x a; basic_goal_prep; basic_utils_crush.
  Qed.
  
  (*Require Import Coq.Sorting.Permutation.*)

  (*TODO: move lemmas from this import to another *)
  Require Import Utils.PosListMap.

  (*TODO: move*)
  Lemma named_map_snd_eq:
    forall [S : Type] {A B : Type} (f : A -> B) (l : named_list S A),
      map snd (named_map f l) = map f (map snd l).
  Proof.
    clear.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma In_option_all_out [A : Type] {l1 : list (option A)} {l2 : list A} v1o
    : option_all l1 = Some l2 ->
      In v1o l2 -> In (Some v1o) l1.
  Proof.
    revert l2; induction l1;
      destruct l2;
      basic_goal_prep;
      repeat case_match;
      basic_utils_crush.
  Qed.

  Hint Resolve NoDup_app_remove_r NoDup_app_remove_l : utils.

  
  Lemma map_get_of_list_In A B `{map.ok A B} `{Eqb_ok A} (x : A) (v : B) l
    : map.get (map.of_list l) x = Some v -> In (x,v) l.
  Proof.
    induction l; 
      basic_goal_prep;
      repeat case_match;
      basic_utils_crush.
    eqb_case x a.
    {
      rewrite map.get_put_same in H4;
        inversions; intuition auto.
    }
    {
      right.
      rewrite map.get_put_diff in H4;
        inversions; intuition auto.
    }
  Qed.
  
   Lemma map_get_of_list_not_In A B `{map.ok A B} `{Eqb_ok A} (x : A) (l : named_list A B)
    : NoDup (map fst l) -> map.get (map.of_list l) x = None -> ~In x (map fst l).
  Proof.
    induction l; 
      basic_goal_prep;
      repeat case_match;
      basic_utils_crush.
    all: rewrite ?map.get_put_same in *;
        inversions; intuition auto.
    eqb_case x a.
    {
      rewrite map.get_put_same in *;
        inversions; intuition auto.
    }
    {
      rewrite map.get_put_diff in * by eauto.
      intuition auto.
    }
  Qed.

  Lemma in_named_map_iff [S : Type] {A B : Type} (f : A -> B) (l : list (S * A)) (n : S) (x : B)
    : In (n, x) (named_map f l) <-> exists y, x = f y /\ In (n, y) l.
  Proof.
    induction l;
      basic_goal_prep;
      repeat case_match;
      basic_utils_crush.
  Qed.
  
  Lemma map_extends_None A B {mp : map.map A B} `{@map.ok A B mp} `{Eqb_ok A} (x : A) (a b : mp)
    : map.extends a b -> map.get a x = None -> map.get b x = None.
  Proof.
    unfold map.extends.
    intro H'; specialize (H' x).
    destruct (map.get b x) eqn:Hget; try congruence.
    specialize (H' _ eq_refl).
    congruence.
  Qed.

  
  Lemma all_option_all A (P : A -> Prop) l l'
    : all P l ->
      Some l = option_all l' ->
      all (fun ma => ma <$> P) l'.
  Proof.
    revert l; induction l'; destruct l;
      basic_goal_prep;
      repeat case_match;
      basic_utils_crush.
  Qed.

  Lemma exec_write_sound' i r assign_vals qc
    : rule_sound_for_evaluation' i qc r ->
      Datatypes.length r.(query_vars) = Datatypes.length assign_vals ->
      query_assignment_sound i qc (combine r.(query_vars) assign_vals) r.(query_clause_ptrs) ->
      state_sound_for_model m i
        (exec_write idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map
           idx_trie analysis_result r assign_vals)
        (fun (_ : idx_map (domain m)) (_ : unit) => True).
  Proof.
    unfold exec_write; intros ? Hlen ?.
    destruct H1.
    rename H2 into H1.
    pose (named_map (fun f : named_list idx idx -> idx => f (combine (query_vars r) assign_vals))
            rule_assignment) as l.
    destruct (list_Mmap (map.get i) (map snd l)) as [ttt|] eqn:Httt.
    2:{
      exfalso.
      symmetry in Httt; apply list_Mmap_None in Httt; eauto.
      break.
      subst l.
      rewrite named_map_snd_eq, !List.map_map in H2.
      apply in_map_iff in H2; break.
      eapply rule_assignment_sound in H1; eauto;
        basic_goal_prep; subst.
      unfold eq_sound_for_model in H1; repeat iss_case.
      congruence.
    }
    ssm_bind.
    {
      apply allocate_existential_vars_sound
        with (time_travel_terms:= ttt).
      {
        apply TrieMap.list_Mmap_length in Httt.
        subst l.
        rewrite rule_assignment_dom.
        basic_utils_crush.
      }
      {
        pose proof (fun x y H => rule_assignment_sound x y H _ H1).
        apply in_all_iff; intros.
        rewrite !TrieMap.Mmap_option_all in *.
        eapply In_option_all_out in Httt; eauto.
        eapply in_map_iff in Httt.
        break.
        unfold l in H5.
        eapply in_map_iff in H5; break; subst; cbn in *.
        unfold named_map in H6.
        eapply in_map_iff in H6; break; subst; cbn in *.
        inversions.
        eapply H2 in H6.
        unfold eq_sound_for_model in H6.
        rewrite H4 in *; cbn in *.
        auto.
      }
      { eauto with utils. }
      {
        apply NoDup_app_iff in vars_NoDup0; break.
        eapply in_all_iff; intros.
        intro.
        enough (In x (query_vars r)) by firstorder.
        unfold Sep.has_key in H7.
        case_match; try tauto.
        assert (NoDup (map fst (combine (query_vars r) assign_vals))).
        { rewrite map_combine_fst; eauto. }
        apply Properties.map.all_gets_from_map_of_NoDup_list in H8.
        eapply map_get_of_list_In in case_match_eqn; eauto.
        eapply in_combine_l; eauto.
      }
    }
    ssm_bind.
    {
      eapply state_sound_for_model_Miter with (P := fun _ _ => True); auto.
      intros.
      eapply exec_clause_sound.
      break.
      pose proof H1 as Hclause;
        eapply clauses_sound in Hclause.
      eapply in_all in Hclause; eauto.
      eapply atom_sound_monotone in Hclause.
      2: eassumption.
      eapply atom_sound_monotone in Hclause.
      2: eassumption.
      assert (forall x d' d, In x (write_vars r ++ query_vars r) ->
                            map.get i'0 (unwrap_with_default (H:=d) (map.get a x))
                            = map.get i'0 (named_list_lookup d'
                                             (write_assignment (combine (query_vars r)
                                                                   assign_vals))
                                             x)).
      {
        intros.
        autorewrite with utils in*.
        destruct (map.get a x) eqn:Hget.
        2:{
          pose proof Hget.
          eapply map_extends_None in Hget; eauto.
          eapply map_get_of_list_not_In in Hget; eauto;
            rewrite map_combine_fst in *; eauto with utils.
          intuition.
          exfalso.
          eapply all2_combine in H7; unfold uncurry in H7; cbn in H7; break.
          replace (write_vars r) with (map fst (combine (write_vars r) ttt))
            in H11 by (rewrite map_combine_fst in *; eauto with utils).
          apply pair_fst_in_exists in H11; break.
          eapply in_all in H9; eauto.
          cbn in*.
          repeat iss_case.
          congruence.
        }
        destruct H9.
        2:{
          destruct (map.get (map.of_list (combine (query_vars r) assign_vals)) x) eqn:Hget'.
          {
            pose proof Hget'; eapply map_get_of_list_In in Hget'; eauto.
            eapply H3 in H10.
            replace i0 with i1 in * by congruence.
            assert (In (x,i1) (write_assignment (combine (query_vars r) assign_vals))).
            {
              unfold write_assignment.
              basic_utils_crush.
            }
            eapply named_list_lookup_in in H11; eauto.
            2:{
              unfold write_assignment.
              rewrite map_app, named_map_fst_eq.
              rewrite <- rule_assignment_dom.
              rewrite map_combine_fst; eauto.
            }
            rewrite H11.
            reflexivity.
          }
          {
            exfalso.
            eapply map_get_of_list_not_In in Hget';
              rewrite ?map_combine_fst in *; eauto with utils.
          }
        }
        {
          eapply all2_combine in H7; unfold uncurry in H7; cbn in H7; break.
          replace (write_vars r) with (map fst (combine (write_vars r) ttt))
            in H9 by (rewrite map_combine_fst in *; eauto with utils).
          pose proof H9.
          apply pair_fst_in_exists in H9; break.
          eapply in_all in H9; cbn in *; eauto; cbn in *.
          rewrite Hget in *; cbn in *.
          assert (exists i1, In (x,i1) l).
          {
            unfold l.
            rewrite map_combine_fst in *; eauto with utils.
            unfold write_assignment.
            rewrite rule_assignment_dom in H11.
            apply in_map_iff in H11; break; subst; cbn in *.
            eapply in_named_map in H12.
            eexists.
            autorewrite with utils.
            exact H12.
          }
          break.
          replace (named_list_lookup d'
                     (write_assignment (combine (query_vars r) assign_vals)) x)
            with x1.
          2:{
            subst l.
            epose proof (or_introl H12).
            apply in_app_iff in H13.
            eapply named_list_lookup_in with (d:=d) in H13; eauto.
            2:{
              rewrite map_app, named_map_fst_eq, map_combine_fst; eauto.
              change (list (?A*?B)) with (named_list A B).
              rewrite <- rule_assignment_dom; auto.
            }
            {
              symmetry; apply named_list_lookup_in; eauto.
              {
                unfold write_assignment.
                rewrite map_app, named_map_fst_eq, map_combine_fst; eauto.
                change (list (?A*?B)) with (named_list A B).
                rewrite <- rule_assignment_dom; auto.
              }
              {
                unfold write_assignment.
                autorewrite with utils; eauto.
              }
            }
          }
          assert (Some (combine (write_vars r) ttt)
                  = list_Mmap (M:=option)
                      (fun p => option_map (pair (fst p)) (map.get i (snd p))) l).
          {
            replace (write_vars r)
              with (map fst l).
            2:{
              subst l.
              rewrite named_map_fst_eq.
              auto.
            }
            clear H7 H10 H11.
            revert ttt Httt.
            clear.
            induction l; basic_goal_prep;              
              basic_utils_crush.
            destruct (map.get i i1) eqn:Hget; cbn in *; try congruence.
            destruct (list_Mmap (map.get i) (map snd l)); cbn in *; try congruence.
            inversions.
            erewrite <- IHl; eauto.
          }
          rewrite TrieMap.Mmap_option_all in *.
          eapply all_option_all in H13; eauto.
          rewrite all_map in H13.
          eapply in_all in H13; eauto.
          unfold option_map in H13; cbn in H13.
          case_match; cbn in *; try tauto.
          repeat iss_case.
          apply H2 in case_match_eqn; apply H5 in case_match_eqn.
          inversions.
          apply H5 in H13.
          congruence.
        }
      }
      unfold atom_sound_for_model in Hclause;
        unfold atom_sound_for_model.
      repeat iss_case.
      assert (incl (write_vars r) (map.keys a)) as Hwrite_keys.
      {
        revert H7 idx_map_ok Eqb_idx_ok; clear.
        revert ttt;
          induction (write_vars r);
          basic_goal_prep;
          repeat case_match;
          basic_utils_crush.
        repeat iss_case.
        rewrite map_keys_in'.
        rewrite Hma; auto.
      }
      assert (forall l , incl l (write_vars r ++ query_vars r) ->
                          list_Mmap (map.get i'0)
                            (map (fun x : idx => unwrap_with_default (map.get a x)) l)
                            = list_Mmap (map.get i'0)
                                (map (fun x : idx => named_list_lookup x
                                                       (write_assignment (combine (query_vars r)
                                                                             assign_vals)) x)
                                   l)).
      {
        induction l1; basic_goal_prep; auto.
        erewrite <- H9.
        2:{ eapply H10; cbn; eauto. }
        case_match; cbn; auto.
        {
          erewrite <- IHl1;
          clear IHl1.
          2: basic_utils_crush.
          case_match; auto.
        }
      }
      destruct a0; cbn in *.
      erewrite H10, Hma; cbn.
      1: erewrite H9, Hma0; cbn; eauto.
      all:repeat intro;
        rewrite Permutation.Permutation_app_comm;
        apply write_clauses_well_scoped0;
        apply in_flat_map;
        eexists; split; try eassumption;
        cbn; eauto.
    }
    eapply state_sound_for_model_Miter with (P := fun _ _ => True); auto.
    intros; break.
    eapply state_sound_for_model_wkn; auto.
    eapply union_sound.
    apply eqns_sound0 in H1.
    eapply in_all in H6; eauto; cbn in H6.
    break.
    apply Properties.map.get_of_list_In_NoDup in H6, H11.
    2,3: rewrite map_combine_fst; eauto.
    2,3: apply NoDup_app_iff in  vars_NoDup0; break; now eauto.
    apply H3 in H6, H11.
    rewrite H6, H11.
    cbn.
    repeat (eapply eq_sound_monotone; [eassumption| eauto]).
  Qed.

   Record wf_erule (r : erule idx symbol) : Prop :=
    {
      wf_vars_NoDup : NoDup (r.(write_vars)++r.(query_vars));
      wf_write_clauses_well_scoped
      : incl (flat_map (fun a => atom_ret a :: atom_args a)
                r.(write_clauses)) (r.(query_vars) ++ r.(write_vars));
      wf_write_unifications_well_scoped
      : incl (flat_map (fun p => [fst p; snd p])
                r.(write_unifications)) (r.(query_vars) ++ r.(write_vars));
      wf_rule_vars_covered : incl r.(query_vars)
                                   (flat_map query_ptr_args
                                      (as_list r.(query_clause_ptrs)));
      }.
      
   Record rule_sound_for_assignment i qc (r : erule idx symbol)
     (rule_assignment : named_list idx (named_list idx idx -> idx)): Prop :=
    {
      assign_rule_assignment_dom
      : r.(write_vars) = (map fst rule_assignment);
      assign_rule_assignment_sound
      : forall x f, In (x,f) rule_assignment ->
                    forall qa, query_assignment_sound i qc qa r.(query_clause_ptrs) ->
                               eq_sound_for_model m i (f qa) (f qa);
      assign_write_assignment :=
        fun qa => (named_map (fun f => f qa) rule_assignment) ++ qa;
      assign_clauses_sound
      : forall qa, query_assignment_sound i qc qa r.(query_clause_ptrs) ->
                   all (fun c => atom_sound_for_model m i (atom_subst (assign_write_assignment qa) c))
                     r.(write_clauses);
      assign_eqns_sound
      : forall qa, query_assignment_sound i qc qa r.(query_clause_ptrs) ->
                   all (fun '(x,y) =>
                          exists vx vy,
                            In (x,vx) qa
                            /\ In (y,vy) qa
                            /\ eq_sound_for_model m i vx vy)
                     r.(write_unifications);
    }.

   Definition rule_sound_for_evaluation i qc r : Prop :=
     wf_erule r /\ forall i', map.extends i' i -> exists a, rule_sound_for_assignment i' qc r a.

  
  Lemma exec_write_sound i r assign_vals qc
    : rule_sound_for_evaluation i qc r ->
      Datatypes.length r.(query_vars) = Datatypes.length assign_vals ->
      query_assignment_sound i qc (combine r.(query_vars) assign_vals) r.(query_clause_ptrs) ->
      state_sound_for_model m i
        (exec_write idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map
           idx_trie analysis_result r assign_vals)
        (fun (_ : idx_map (domain m)) (_ : unit) => True).
  Proof.
    intros; eapply exec_write_sound'; eauto.
    edestruct H1 as [ [] [? [] ] ]; eauto with utils.
    econstructor; eauto.
  Qed.

  Lemma monotone_rule_sound_for_evaluation
    : monotone2 rule_sound_for_evaluation.
  Proof.
    repeat intro.
    destruct H2; econstructor; intros; eauto.
    eapply map_extends_trans in H1; try eassumption.
    eapply H3 in H1; break.
    exists x; eauto.
  Qed.
    
  Lemma process_erule'_sound i tries frontier_idx (r : erule _ _) qc
    : tries_sound_for_model i tries qc ->
      rule_sound_for_evaluation i qc r ->
       state_sound_for_model m i
        (process_erule' idx Eqb_idx idx_succ idx_zero symbol symbol_map
           idx_map idx_trie analysis_result spaced_list_intersect tries r
           (idx_of_nat idx idx_succ idx_zero frontier_idx))
        (fun _ _ => True).
  Proof.
    unfold process_erule'.
    intros.
    apply state_sound_for_model_Miter with (P:= fun _ _ => True);
      intros; auto.
    eapply exec_write_sound; eauto.
    1: eapply monotone_rule_sound_for_evaluation; now eauto.
    {
      unfold intersection_keys in *.
      admit (*TODO: parameterized on spaced_list_intersect*).
    }
    {
      (*TODO: prove from tries_sound_for_model*)
      
      admit (*TODO: parameterized on spaced_list_intersect*).
    }
  Admitted.
  
  Lemma trie_sound_for_model_monotone
    : monotone3 trie_sound_for_model.
  Proof.
    unfold trie_sound_for_model.
    repeat intro.
    eapply atom_sound_monotone; eauto.
  Qed.

  Lemma lookup_trie_sound_for_model_monotone
    : monotone4 lookup_trie_sound_for_model.
  Proof.
    unfold lookup_trie_sound_for_model; repeat intro.
    specialize (H2 _ _ H3 H4 _ H5 _ _ H6).
    intuition (eapply trie_sound_for_model_monotone; eauto).
  Qed.    

  Lemma tries_sound_for_model_monotone
    : monotone2 tries_sound_for_model.
  Proof.
    unfold tries_sound_for_model.
    do 8 intro. eapply lookup_trie_sound_for_model_monotone; eauto.
  Qed.
  
  Lemma process_erule_sound i tries r qc
    :  tries_sound_for_model i tries qc ->
       rule_sound_for_evaluation i qc r ->
       state_sound_for_model m i
        (process_erule idx Eqb_idx idx_succ idx_zero symbol symbol_map
           idx_map idx_trie analysis_result spaced_list_intersect tries r)
        (fun _ _ => True).
  Proof.
    intros.
    unfold process_erule.
    apply state_sound_for_model_Miter with (P:= fun _ _ => True);
      intros; auto.
    eapply process_erule'_sound; eauto.
    { eapply tries_sound_for_model_monotone; eauto. }
    { eapply monotone_rule_sound_for_evaluation; eauto. }
  Qed.

  (*
    Definition ptr_trie_sound_for_model i tries (p : erule_query_ptr) :=
      forall tries' t1 t2,
        map.get tries p.(query_ptr_symbol) = tries' ->
        map.get tries' p.(query_ptr_ptr) = (t1, t2) ->
        todo: use qp args
        
    Definition tries_sound_for_model i tries access :=
      forall s tries', map.get tries s = Some tries' ->
                       forall x
    unfold process_erule.
    apply state_sound_for_model_Miter with (P:= fun _ _ => True);
      intros; auto.
    
query_clauses symbol_map (idx_map (list nat * nat))
*)

  (*TODO: move to defining file*)
  Arguments query_clauses {idx symbol}%type_scope {symbol_map idx_map}%function_scope r.

  Context (idx_map_plus_ok : @map_plus_ok _ _ idx_map_plus).

  Lemma empty_trie_sound_for_model i f p
    : trie_sound_for_model i f map.empty p.
  Proof.
    repeat intro;
      basic_utils_crush.
  Qed.
  Hint Resolve empty_trie_sound_for_model : utils.
  
  Lemma trie_sound_for_model_put i f r1 access l0
    : trie_sound_for_model i f r1 access ->
      atom_sound_for_model m i (atom_of_access f access l0) ->
      trie_sound_for_model i f (map.put r1 l0 tt) access.
  Proof.
    unfold trie_sound_for_model.
    intros.
    eqb_case k l0; eauto.
    rewrite map.get_put_diff in * by auto.
    eauto.
  Qed.

  
  Lemma insert_nth acc n v l1 d
    : insert idx Eqb_idx acc n v = Some l1 ->
      nth n l1 d = Some v.
  Proof.
    revert acc l1; induction n;
      basic_goal_prep;
      repeat case_match; inversions; try congruence;
      cbn; eauto;
      basic_utils_crush;
      unfold option_map in H1; case_match; try congruence;
      inversions;
      cbn; eauto.
  Qed.

  Lemma match_clause'_ret l n k v l1 acc d
    : match_clause' l n k v acc = Some l1 ->
      nth n l1 d = Some v.
  Proof.
    revert k l1 acc.
    induction l;
      basic_goal_prep;
      repeat case_match; try congruence; eauto using insert_nth.
  Qed.

  (*TODO: move to Base.v*)
  Ltac inject f :=
    lazymatch goal with
      |- ?A = ?B =>
        enough (f A = f B) by (cbn; congruence)
    end.

  Fixpoint match_list_leq (l1 l2 : list (option idx)) :=
    match l1, l2 with
    | [], _ => True
    | None::l1', _::l2' => match_list_leq l1' l2'
    | (Some x)::l1', (Some y)::l2' =>
        x = y /\ match_list_leq l1' l2'
    | _, _ => False
    end.

  Lemma match_list_leq_refl l : match_list_leq l l.
  Proof.
    induction l; basic_goal_prep; repeat case_match; basic_utils_crush.
  Qed.
  Hint Resolve match_list_leq_refl : utils.
  
  Lemma match_list_leq_trans : Transitive match_list_leq.
  Proof.
    intro l.
    induction l; basic_goal_prep;
      repeat (case_match; basic_goal_prep); basic_utils_crush.
  Qed.

  Add Parametric Relation : (list (option idx)) match_list_leq
    reflexivity proved by match_list_leq_refl
    transitivity proved by match_list_leq_trans
    as match_list_leq_rel.
  
  Lemma insert_monotone acc n v l'
    : insert idx Eqb_idx acc n v = Some l' ->
      match_list_leq acc l'.
  Proof.
    revert acc l'; induction n;
      basic_goal_prep; auto; inversions.
    {
      case_match; cbn; intuition auto with utils.
      case_match; inversions; cbn; intuition auto with utils.
      eqb_case v i; inversions; cbn; intuition auto with utils.
    }
    case_match; cbn; intuition auto with utils.
    case_match; cbn; intuition auto with utils.
    all: destruct (insert idx Eqb_idx acc n v) eqn:Hins;
      cbn in *; inversions; eauto; try tauto.
  Qed.

  Lemma match_clause'_monotone l n k v l' acc
    : match_clause' l n k v acc = Some l' ->
      match_list_leq acc l'.
  Proof.
    revert k l' acc;
    induction l;
      basic_goal_prep;
      repeat case_match; try congruence; cbn; eauto using insert_monotone.
    etransitivity; eauto using insert_monotone.
  Qed.

  Lemma match_list_leq_nth l1 l2 x n0
    : match_list_leq l1 l2 ->
      nth n0 l1 default = Some x ->
      nth n0 l2 default = Some x.
  Proof.
    unfold default, option_default.
    revert l1 l2;
      induction n0;
      destruct l1, l2;
      basic_goal_prep; subst; try tauto;
      try congruence.
    all: case_match; intuition subst; eauto.
    case_match; intuition subst; eauto.
  Qed.

  (*TODO: not true?, needs more conditions. specifically, acc*)
  Lemma match_clause'_args' l n k v l' acc
    : match_clause' l n k v acc = Some l' ->
      map (fun n0 : nat => nth n0 l' default) l = map Some k.
  Proof.
    revert k l' acc.
    induction l;
      basic_goal_prep;
      repeat case_match; try congruence; cbn; auto.
    f_equal; eauto.
    eapply match_list_leq_nth; eauto using match_clause'_monotone.
    eapply insert_nth; eauto.
  Qed.
  
  Lemma match_clause'_args l n k v acc l0
    : match_clause' l n k v acc = Some (map Some l0) ->
      map (fun n0 : nat => nth n0 l0 default) l = k.
  Proof.
    intros.
    apply match_clause'_args' in H1.
    revert k H1.
    induction l;
      destruct k;
      basic_goal_prep;
      basic_utils_crush.
    revert H2.
    clear.
    revert l0; induction a; destruct l0;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    
  Lemma match_clause_atom_of_access f access k entry_value l0
    : match_clause access k entry_value = Some l0 ->
      atom_of_access f access l0 = Build_atom f k entry_value.
  Proof.
    unfold match_clause; break.
    unfold atom_sound_for_model; cbn.
    case_match; try congruence; intros.
    unfold atom_of_access.
    apply option_all_map_Some in H1; subst.
    cbn.
    f_equal.
    2:{
      inject (@Some idx).
      rewrite <- map_nth.
      eapply match_clause'_ret; eauto.
    }      
    { eapply match_clause'_args; eauto. }
  Qed.

  (*TODO: move to coqutil *)
  Section MapFacts.
    Context (key value : Type) (map : map.map key value) `{@map.ok _ _ map}.
    
    Lemma map_extends_empty  (m0 : map)
      : map.extends map.empty m0 <-> m0 = map.empty.
    Proof.
      split; intros; subst; eauto with utils.
      apply map.map_ext.
      intros.
      basic_utils_crush; eauto.
      destruct (map.get m0 k) eqn:Hget; auto.
      exfalso.
      apply H2 in Hget.
      basic_utils_crush.
    Qed.
    Hint Rewrite map_extends_empty : utils.

    
    Lemma map_extends_put_wkn (m0 m1 : map) k v
      : map.get m1 k = None ->
        map.extends m0 (map.put m1 k v) ->
        map.extends m0 m1.
    Proof.
      repeat intro.
      assert (x <> k) by congruence.
      apply H3.
      rewrite map.get_put_diff by auto.
      auto.
    Qed.

    Lemma map_fold_spec_member' {R : Type} (P : map -> R -> Prop)
      (f : R -> key -> value -> R) (r0 : R) (m0 : map)
      : P map.empty r0 ->
        (forall (k : key) (v : value) (m : map) (r : R),
            map.get m0 k = Some v ->
            map.get m k = None -> P m r -> P (map.put m k v) (f r k v)) ->
        forall m, map.extends m0 m -> P m (map.fold f r0 m).
    Proof.
      intros ? ? m1.
      pattern (map.fold f r0 m1).
      revert m1.
      apply map.fold_spec;
        basic_goal_prep; basic_utils_crush.
      eapply H3; eauto.
      2:{
        apply H5.
        eapply map_extends_put_wkn; eauto.
      }
      {
        apply H6; rewrite map.get_put_same; auto.
      }
    Qed.
    
    Lemma map_fold_spec_member {R : Type} (P : map -> R -> Prop)
      (f : R -> key -> value -> R) (r0 : R) (m0 : map)
      : P map.empty r0 ->
        (forall (k : key) (v : value) (m : map) (r : R),
            map.get m0 k = Some v ->
            map.get m k = None -> P m r -> P (map.put m k v) (f r k v)) ->
        P m0 (map.fold f r0 m0).
    Proof.
      intros;eapply map_fold_spec_member'; eauto with utils.
    Qed.

  End MapFacts.
  Hint Rewrite map_extends_empty : utils.
  
  Lemma build_tries_for_symbol_sound i f qc' r0 x t1 t2 l n ep
    : (forall k v, map.get r0 k = Some v ->
                   atom_sound_for_model m i (Build_atom f k v.(entry_value _ _))) ->
      map.get (build_tries_for_symbol idx Eqb_idx idx_map idx_map_plus idx_trie analysis_result 
                 ep qc' r0) x = Some (t1, t2) ->
      map.get qc' x = Some (l, n) ->
      trie_sound_for_model i f t1 (l, n) /\ trie_sound_for_model i f t2 (l, n).
  Proof.
    intros Hsound Hget Hqc.
    revert Hget.
    unfold build_tries_for_symbol.
    revert t1 t2.
    apply map_fold_spec_member; eauto.
    {
      rewrite map_map_spec; eauto.
      unfold option_map; case_match; try congruence; repeat inversions.
      basic_goal_prep; subst; repeat inversions; intuition eauto with utils.
    }
    basic_goal_prep.
    destruct v.
    rewrite intersect_spec in *; eauto.
    case_match; try congruence.
    case_match; try congruence.
    break.
    inversions.
    case_match.
    2:{ apply H3; congruence. }
    specialize (H3 _ _ eq_refl); break.
    eqb_case entry_epoch ep; inversions; intuition eauto.
    all: apply trie_sound_for_model_put; auto.
    all: erewrite match_clause_atom_of_access; eauto.
  Qed.
  
  Lemma build_tries_sound i rs
    : state_sound_for_model m i
        (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus idx_map idx_map_plus
           idx_trie analysis_result rs)
        (fun i' tries => tries_sound_for_model i' tries rs.(query_clauses)).
  Proof.
    open_ssm.
    repeat intro.
    rewrite intersect_spec in *; eauto.
    repeat case_match; cbn; inversions; try tauto.
    eapply build_tries_for_symbol_sound; eauto.
    intros.
    eapply atom_interpretation; eauto.
    unfold atom_in_egraph, atom_in_db; cbn.
    unfold db_map.
    rewrite case_match_eqn0; cbn.
    rewrite H1; cbn.
    auto.
  Qed.
  
  (*TODO: move*)
  Arguments compiled_rules {idx symbol}%type_scope {symbol_map idx_map}%function_scope r.
  
  Lemma run1_iter_sound i rs rb_fuel
    : all (rule_sound_for_evaluation i (query_clauses rs)) rs.(compiled_rules) ->
      state_sound_for_model m i
        (Defs.run1iter idx Eqb_idx idx_succ idx_zero symbol Eqb_symbol
           symbol_map symbol_map_plus idx_map idx_map_plus idx_trie
           analysis_result spaced_list_intersect rs rb_fuel) 
        (fun _ _ => True).
  Proof.
    unfold Defs.run1iter.
    intros.
    ssm_bind.
    { apply build_tries_sound. }
    {
      ssm_bind.
      1: apply increment_epoch_sound.
      ssm_bind.
      2:{
        eapply state_sound_for_model_wkn; eauto.
        eapply rebuild_sound.
      }
      apply state_sound_for_model_Miter with (P:= fun _ _ => True);
        intros; eauto.
      eapply process_erule_sound; eauto.
      { repeat (eapply tries_sound_for_model_monotone; try eassumption). }
      {
        eapply in_all in H1; eauto.
        repeat (eapply monotone_rule_sound_for_evaluation; try eassumption).
      }
    }
  Qed.
    
  Lemma saturate_until'_sound i rb_fuel rs cond fuel P
    : all (rule_sound_for_evaluation i (query_clauses rs)) rs.(compiled_rules) ->
      (forall i', map.extends i' i ->
                  state_sound_for_model m i' cond (fun i2 (b:bool) => if b then P i2 else True)) ->
      monotone P ->
      forall i', map.extends i' i ->
      state_sound_for_model m i' (saturate_until' rs cond fuel rb_fuel)
        (fun i b => if b then P i else True).
  Proof.
    intros Hrule Hcond HP.
    induction fuel;
      cbn [Defs.saturate_until'].
    { intros; eapply ret_sound_for_model'; auto. }
    {
      intros.
      ssm_bind.
      destruct a.
      { eapply ret_sound_for_model'; auto. }
      eapply state_sound_for_model_Mseq.
      {
        apply run1_iter_sound.
        eapply all_wkn; try eassumption.
        intros.
        repeat (eapply monotone_rule_sound_for_evaluation; try eassumption).
      }
      {
        intros; eauto.
        eapply IHfuel.
        eapply map_extends_trans; try eassumption.
        eapply map_extends_trans; try eassumption.
      }
    }
  Qed.
  
  Lemma saturate_until_sound i rb_fuel rs cond fuel P
    (* TODO: package rs properties together*)
    : all (const_rule_sound_for_evaluation i)
        (compiled_const_rules idx symbol symbol_map idx_map rs) ->
      all (rule_sound_for_evaluation i (query_clauses rs)) rs.(compiled_rules) ->
      (forall i', map.extends i' i ->
                  state_sound_for_model m i' cond (fun i2 (b:bool) => if b then P i2 else True)) ->
      monotone P ->
      state_sound_for_model m i (saturate_until rb_fuel rs cond fuel)
        (fun i b => if b then P i else True).
  Proof.
    intros.
    unfold saturate_until.
    eapply state_sound_for_model_Mseq.
    1:eapply process_const_rules_sound; eauto.
    intros; break; cbn beta in *.
    eapply state_sound_for_model_Mseq.
    1: apply rebuild_sound.
    intros.
    eapply saturate_until'_sound; eauto.
    repeat (eapply map_extends_trans; try eassumption).
  Qed.
      
End WithMap.

Arguments atom_in_egraph {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope
  a i.

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


Arguments state_sound_for_model {idx} lt {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope {analysis_result}%type_scope 
  {A}%type_scope m i s (Post)%function_scope.


Arguments model_satisfies_rule {idx symbol}%type_scope {idx_map}%function_scope m r.


(*TODO: duplicated in section *)
Ltac open_ssm' :=
  cleanup_context;
  lazymatch goal with
  | |- state_sound_for_model _ _ _ ?e _ =>
      let h := get_head e in
      unfold h; unfold state_sound_for_model, Sep.and1; repeat intro;
      eexists; eauto with utils;
      break; cbn[fst snd]
  end.

Ltac open_ssm :=
  open_ssm';
  intuition eauto with utils;
  break; cbn[fst snd];
  try lazymatch goal with
    | H : egraph_ok _ |- egraph_ok _ =>
        destruct H; constructor; eauto with utils
    | H : egraph_sound_for_interpretation _ _ _
      |- egraph_sound_for_interpretation _ _ _ =>
        destruct H; constructor; eauto with utils
    end.


(*TODO: duplicated in section *)
Ltac bind_with_fn H :=
  eapply state_sound_for_model_bind;
  eauto using H with utils;
  cbn beta;intros; subst; cleanup_context.

(*TODO: duplicated in section *)
Ltac ssm_bind :=
  eapply state_sound_for_model_bind;
  eauto with utils;
  cbn beta in *;intros; subst; cleanup_context.
