(* TODO: separate semantics and theorems
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps Relations Maps UnionFind VC.
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
      interprets_to : symbol -> list domain -> domain -> Prop;
      (*interprets_to f args d := exists d', interpretation f args = Some d' /\ domain_eq d' d;*)
    }.

  Class model_ok (m : model) : Prop :=
    {
      domain_eq_PER :: PER (domain_eq m);
      interprets_to_functional
      : forall f args1 args2 d1 d2,
        m.(interprets_to) f args1 d1 ->
        m.(interprets_to) f args2 d2 ->
        all2 m.(domain_eq) args1 args2 ->
        m.(domain_eq) d1 d2;
      interprets_to_preserved
      : forall f args1 args2 d1 d2,
        m.(interprets_to) f args1 d1 ->
        all2 m.(domain_eq) args1 args2 ->
        m.(domain_eq) d1 d2 ->
        m.(interprets_to) f args2 d2;
      interprets_to_implies_wf_args
      : forall f args d,
        m.(interprets_to) f args d ->
        all m.(domain_wf) args;
      interprets_to_implies_wf_conclusion
      : forall f args d,
        m.(interprets_to) f args d ->
         m.(domain_wf) d;
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

   (*TODO: move*)
   Definition clause_subst s c :=
     match c with
     | eq_clause x y =>
         let x' := named_list_lookup x s x in
         let y' := named_list_lookup y s y in
         eq_clause x' y'
     | atom_clause a => atom_clause (atom_subst s a)
     end.
   
   (* should be seen as denoting a set of renamings for a given query
      and interpretation.
    *)
  Definition conjunct_denotation
    (q : list clause) (ren : named_list _ _) : Prop :=
    set_eq (flat_map clause_vars q) (map fst ren)
    /\ all clause_sound_for_model (map (clause_subst ren) q).

  End ForModel.

  (*

  TODO: map vs named_list. allfresh?
  Definition model_satisfies_rule m r :=
    forall i ren, conjunct_denotation m i r.(seq_assumptions) ren ->
                  exists ren' i',
                    (* Not specific enough about dom i'.
                       Probably has some issues w/ alloc
                     *)
                    map.extends i' i
                    /\ dom i' = dom i & codom (ren')
                    /\ map.extends ren' ren
                    /\ conjunct_denotation m i'
                         r.(seq_conclusions) ren'.
                  
    forall query_assignment,
      set_eq (map.keys query_assignment) (forall_vars r) ->
      all (clause_sound_for_model m query_assignment) r.(seq_assumptions) ->
      exists out_assignment,
        map.extends out_assignment query_assignment
        /\ all (clause_sound_for_model m out_assignment)
             r.(seq_conclusions).
*)

  (*
    graph_ok g i
    (dom g = dom i)
    i[x] = e
    (dom (query(g)) = canonize (dom g))

    graph_ok g' i' ->
    matches g' query(g) = Some l_s ->
    In s l_s ->
    (dom s = dom query(g))
    ...
    graph_ok g[/canon^-1 s/] i'
   *)
  

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

  
  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).

  Definition worklist_entry_ok (equiv : union_find) ent :=
    match ent with
    | union_repair _ old_idx new_idx improved_new_analysis =>
        uf_rel_PER _ _ _ equiv old_idx new_idx
    | analysis_repair _ i => True
    end.

  (* Two atoms have the same canonical representation in [e] iff they
     share a function symbol and their args/ret are pointwise equivalent
     in [e]'s union-find. *)
  Definition atom_canonical_equiv (e : instance) (a1 a2 : atom) : Prop :=
    a1.(atom_fn) = a2.(atom_fn)
    /\ all2 (uf_rel_PER _ _ _ e.(equiv)) a1.(atom_args) a2.(atom_args)
    /\ uf_rel_PER _ _ _ e.(equiv) a1.(atom_ret) a2.(atom_ret).

  (* [a] need not literally be in [e.(db)]; it is sufficient that some
     atom with the same canonical representation is. *)
  Definition atom_in_egraph_up_to_equiv (a : atom) (e : instance) : Prop :=
    exists a', atom_canonical_equiv e a a' /\ atom_in_egraph a' e.

  (* TODO: is this record needed? other fields may not be necessary *)
  Record egraph_ok (e : instance) : Prop :=
    {
      egraph_equiv_ok : exists roots, union_find_ok lt e.(equiv) roots;
      worklist_ok : all (worklist_entry_ok e.(equiv)) e.(worklist);
      (* For every atom [a] recorded as a parent, there must exist some
         canonically-equivalent atom in the database. This is weaker than
         requiring [atom_in_egraph a e] directly: db_remove followed by
         canonicalize+update_entry replaces a parent atom with a
         canonically-equivalent one without scrubbing the parents map. *)
      parents_ok : forall x s, map.get e.(parents) x = Some s ->
                             all (fun a => atom_in_egraph_up_to_equiv a e) s;
    }.

  Section ForModel.

    Context m (idx_interpretation : idx_map m.(domain)).

    Local Notation atom_sound_for_model :=
      (atom_sound_for_model m idx_interpretation).

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
      }.
    
    Definition worklist_entry_sound e :=
      match e with
      | union_repair _ old_idx new_idx improved_new_analysis =>
          eq_sound_for_model m idx_interpretation old_idx new_idx
      | analysis_repair _ i => True (* these don't affect soundness of the egraph *)
      end.    

  End ForModel.
  

  (* Todo: is exists right?
     Possibly: f is probably sufficiently unique up to equivalence
   *)
  Definition egraph_sound_for_model m e : Prop :=
    egraph_ok e /\ exists f, egraph_sound_for_interpretation m f e.

  (* parents_interpretation and worklist_sound moved below to where
     [model_ok m] is in scope, since the relaxed [parents_ok] requires
     [interprets_to_preserved] to lift atom soundness across canonical
     equivalence. *)

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} `{WithDefault B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).


  Hint Rewrite @map.get_empty : utils.

  (*TODO: move *)
  Lemma union_find_empty_ok
    : union_find_ok lt (empty (WithDefault idx) (idx_map idx) (idx_map nat) idx_zero) [].
  Proof.
    constructor; cbn; eauto.
    1:apply empty_forest_rooted.
    all: basic_goal_prep; basic_utils_crush.
    rewrite has_key_empty in H; eauto; tauto.
  Qed.
  
  Theorem empty_sound_for_interpretation m
    (*: egraph_sound (empty_egraph idx_zero analysis_result) m.*)
    : egraph_ok (empty_egraph idx_zero _) /\
      egraph_sound_for_interpretation m map.empty (empty_egraph idx_zero _).
  Proof.
    split.
    { constructor; cbn; auto.
      - exists []; cbn; apply union_find_empty_ok.
      - intros; basic_utils_crush. }
    constructor; cbn; try tauto;
      unfold atom_in_egraph, atom_in_db;
      basic_goal_prep;
      rewrite ? map.get_empty in *;
      basic_goal_prep;
      try tauto;
      try congruence.
    exfalso; eapply PER_empty; try eassumption.
    basic_goal_prep; basic_utils_crush.
  Qed.
  
  Lemma has_key_empty A k
    : Sep.has_key k (map.empty : idx_map A) <-> False.
  Proof. clear idx_succ. unfold Sep.has_key; basic_utils_crush. Qed.
  Hint Rewrite has_key_empty : utils.
  
  Theorem empty_sound m : egraph_sound_for_model m (empty_egraph idx_zero analysis_result).
  Proof.
    unfold empty_egraph, egraph_sound_for_model.
    destruct (empty_sound_for_interpretation m) as [Hok Hsound].
    split; [exact Hok | exists map.empty; exact Hsound].
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
      basic_goal_prep; (repeat case_match; basic_goal_prep); basic_utils_crush;
      eapply IHl1; eauto.
  Qed.

  Lemma all2_Is_Some_satisfying_r A B (R : A -> B -> Prop) l1 l2
      : all2 (fun x y => y <$> (fun y' => R x y')) l1 l2
        <-> option_all l2 <$> (fun l2' => all2 R l1 l2').
  Proof.
    clear idx_succ idx_zero.
    revert l1; induction l2; destruct l1;
      basic_goal_prep; (repeat case_match; basic_goal_prep); basic_utils_crush;
      eapply IHl2; eauto.
  Qed.

  Lemma args_rel_interpretation m interp e
    : egraph_ok e /\ egraph_sound_for_interpretation m interp e ->
      forall args1 args2,
        all2 (uf_rel_PER _ _ _ e.(equiv)) args1 args2 ->
        option_relation (all2 m.(domain_eq)) (list_Mmap (map.get interp) args1)
          (list_Mmap (map.get interp) args2).
  Proof.
    intros [_ Hsnd].
    destruct e, Hsnd; cbn in *.
    clear atom_interpretation0.
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
  
  Definition atom_rel (equiv : union_find) (a1 a2 : atom) : Prop :=
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
  
  Context `{analysis idx symbol analysis_result}.

  (*TODO: move*)
  Record forall_nonempty {A} P Q : Prop :=
    {
      fne_elt : A;
      fne_elt_in : P fne_elt;
      fne_all : forall x, P x -> Q x;
    }.

  Notation "'forall_ne' p | P , Q" :=
    (forall_nonempty (fun p => P) (fun p => Q))
      (at level 200, p binder).

  Section __.
    Context {key value : Type} {map : map.map key value}.
    
    Definition ne_set_maps_to (s1 s2 : map -> Prop) := 
      forall_ne i' | s2 i', exists i, s1 i /\ map.extends i' i.
    
    Definition upwards_closed P : Prop :=
      forall s s', P s -> ne_set_maps_to s s' -> P s'.
    
    Lemma map_extends_trans 
      (m1 m2 m3 : map)
      : map.extends m1 m2 -> map.extends m2 m3 -> map.extends m1 m3.
    Proof using. clear; unfold map.extends; intuition eauto. Qed.

    Lemma ne_set_maps_to_trans s1 s2 s3
      : ne_set_maps_to s1 s2 ->
        ne_set_maps_to s2 s3 ->
        ne_set_maps_to s1 s3.
    Proof.
      clear idx_zero idx_succ.
      unfold ne_set_maps_to.
      intros [] [].
      econstructor; eauto.
      intros.
      eapply fne_all0 in H0; break.
      eapply fne_all in H0; break.
      eexists; intuition eauto using map_extends_trans.
    Qed.

    
    Lemma ne_set_maps_to_refl x P
      : P x -> ne_set_maps_to P P.
    Proof.
      clear idx_succ idx_zero.
      econstructor; eauto.
      intros.
      eexists; intuition eauto using Properties.map.extends_refl.
    Qed.
    
  End __.

  Context (m : model).
  
  #[local] Notation abs_set := (idx_map (domain m) -> Prop).

  #[local] Notation denote e :=
    (fun i => egraph_sound_for_interpretation m i e).


  (*TODO: move*)
  Hint Resolve Properties.map.extends_refl : utils.
  
  From Stdlib Require Import Logic.PropExtensionality
    Logic.FunctionalExtensionality.

  
  Lemma set_ext A (S S' : A -> Prop)
    : (forall x, S x <-> S' x) -> S = S'.                                        
  Proof.
    intros.
    eapply functional_extensionality; intros.
    eapply propositional_extensionality; eauto.
  Qed.
  
  Lemma set_pred_ext A (S S' : A -> Prop) (P : (A -> Prop) -> Prop)
    : (forall x, S x <-> S' x) -> P S -> P S'.                                        
  Proof.
    intros.
    erewrite <- set_ext; try eassumption.
  Qed.
  



  
          
  (*
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
   *)
  


  

  Definition pure P {A} (_ : A) : Prop := P.

  Definition forall_lift {A B} (P : B -> Prop) (f : A -> B) : Prop :=
    forall a, P (f a).


  (* Mmap requires monotonicity of [P_elt] under interpretation
     extension: when we process the head, we produce [P_elt i b] for
     some [i]; subsequent recursive iterations may refine the
     interpretation to [i']. The user must supply this monotonicity
     so the head's P_elt fact survives the tail. *)



  (*
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
   *)

  
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
  
  Lemma egraph_sound_for_interpretation_iff_equiv i g1 g2 l
    : g1.(db) = g2.(db) ->
      union_find_ok lt g1.(equiv) l ->
      union_find_ok lt g2.(equiv) l ->
      (iff2 (limit (parent_rel _ _ g1.(equiv).(parent)))
         (limit (parent_rel _ _ g2.(equiv).(parent)))) ->
      g1.(parents) = g2.(parents) ->
      g1.(worklist) = g2.(worklist) ->
      (egraph_ok g1 /\ egraph_sound_for_interpretation m i g1)
      <-> (egraph_ok g2 /\ egraph_sound_for_interpretation m i g2).
  Proof.
    intros Hdb Huf1 Huf2 Hlim Hpar Hwl.
    pose proof Huf1 as [Hf1 ? ? ? ?].
    pose proof Huf2 as [Hf2 ? ? ? ?].
    cbn in Hf1, Hf2.
    assert (lt_trans_nat : forall a b c : nat, a < b -> b < c -> a < c)
      by (intros; Lia.lia).
    assert (Hkey : forall x, Sep.has_key x (parent g1.(equiv))
                             <-> Sep.has_key x (parent g2.(equiv))).
    {
      intro x.
      rewrite (@forest_root_limit _ _ _ _ _ _ default lt_trans_nat _ _ Hf1 x).
      rewrite (@forest_root_limit _ _ _ _ _ _ default lt_trans_nat _ _ Hf2 x).
      split; intros (r & Hin & Hl); exists r; intuition (try apply Hlim; auto).
    }
    assert (HPER : iff2 (uf_rel_PER _ _ _ g1.(equiv))
                        (uf_rel_PER _ _ _ g2.(equiv))).
    {
      unfold uf_rel_PER.
      intros x y.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat _ _ Hf1 x y) as HP1.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat _ _ Hf2 x y) as HP2.
      rewrite HP1, HP2.
      split; intros (r & Hl1 & Hl2); exists r;
        intuition (try apply Hlim; auto).
    }
    split; intros [He_ok He]; destruct He as [Hwf Hexact Hatom Hrel];
      destruct He_ok as [Hg_eq Hg_wl Hg_par];
      split; [| constructor; eauto | | constructor; eauto].
    - constructor.
      + exists l; assumption.
      + rewrite <- Hwl.
        eapply all_wkn; [|exact Hg_wl].
        intros [old new improved | i'] _ He; cbn in *; auto.
        apply HPER; assumption.
      + rewrite <- Hpar.
        intros x s Hg.
        pose proof (Hg_par _ _ Hg) as Hall.
        eapply all_wkn; [|exact Hall].
        intros a Hin Hex.
        cbv beta in Hex.
        unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv in Hex.
        destruct Hex as (aa & Hcanon & Ha_aa).
        destruct Hcanon as (Hfn & Hargs & Hret).
        unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv.
        exists aa; split.
        * split; [exact Hfn|]. split.
          -- eapply all2_impl; [|exact Hargs]. intros; apply HPER; auto.
          -- apply HPER; exact Hret.
        * unfold atom_in_egraph in *. rewrite <- Hdb. exact Ha_aa.
    - intros x Hi. apply Hkey. apply Hexact. exact Hi.
    - intros a Ha.
      apply Hatom. unfold atom_in_egraph in *. rewrite Hdb. exact Ha.
    - intros i1 i2 Hr.
      apply Hrel. apply HPER. exact Hr.
    - constructor.
      + exists l; assumption.
      + rewrite Hwl.
        eapply all_wkn; [|exact Hg_wl].
        intros [old new improved | i'] _ He; cbn in *; auto.
        apply HPER; assumption.
      + rewrite Hpar.
        intros x s Hg.
        pose proof (Hg_par _ _ Hg) as Hall.
        eapply all_wkn; [|exact Hall].
        intros a Hin Hex.
        cbv beta in Hex.
        unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv in Hex.
        destruct Hex as (aa & Hcanon & Ha_aa).
        destruct Hcanon as (Hfn & Hargs & Hret).
        unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv.
        exists aa; split.
        * split; [exact Hfn|]. split.
          -- eapply all2_impl; [|exact Hargs]. intros; apply HPER; auto.
          -- apply HPER; exact Hret.
        * unfold atom_in_egraph in *. rewrite Hdb. exact Ha_aa.
    - intros x Hi. apply Hkey. apply Hexact. exact Hi.
    - intros a Ha.
      apply Hatom. unfold atom_in_egraph in *. rewrite <- Hdb. exact Ha.
    - intros i1 i2 Hr.
      apply Hrel. apply HPER. exact Hr.
  Qed.

  Definition P_guarantees
    {A} (P : (A -> Prop) -> Prop) Q : Prop :=
    forall s, P s -> forall i, s i -> Q i.
  

  Context `{model_ok m}.
  
  Lemma eq_sound_for_model_trans i x y z
    : eq_sound_for_model m i x y ->
      eq_sound_for_model m i y z ->
      eq_sound_for_model m i x z.
  Proof using H0.
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

  Section WithEGraph.
    Context e i `{Hok : egraph_ok e} `{Hsoundeg : egraph_sound_for_interpretation m i e}.

    Lemma parents_interpretation
      :forall y l, map.get e.(parents) y = Some l -> all (atom_sound_for_model m i) l.
    Proof.
      intros y l Hpar.
      apply parents_ok in Hpar; eauto.
      eapply all_wkn; try exact Hpar.
      intros a Hin Hex.
      cbv beta in Hex.
      unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv in Hex.
      destruct Hex as (aa & Hcanon & Ha_aa).
      destruct Hcanon as (Hfn & Hargs & Hret).
      pose proof (atom_interpretation _ _ _ Hsoundeg _ Ha_aa) as Hsa.
      pose proof (args_rel_interpretation _ _ _ (conj Hok Hsoundeg) _ _ Hargs) as Hopt.
      pose proof (rel_interpretation _ _ _ Hsoundeg _ _ Hret) as Hret_eq.
      unfold atom_sound_for_model in Hsa |- *.
      unfold eq_sound_for_model in Hret_eq.
      unfold Is_Some_satisfying in Hsa, Hret_eq |- *.
      unfold option_relation in Hopt.
      destruct (list_Mmap (map.get i) (atom_args aa)) as [margs_aa|] eqn:Hma_aa;
        cbn in *; [| exfalso; exact Hsa].
      destruct (map.get i (atom_ret aa)) as [out_aa|] eqn:Hmret_aa;
        cbn in *; [| exfalso; exact Hsa].
      destruct (list_Mmap (map.get i) (atom_args a)) as [margs|] eqn:Hma;
        cbn in *; [| discriminate Hopt].
      destruct (map.get i (atom_ret a)) as [out|] eqn:Hmret;
        cbn in *; [| exfalso; exact Hret_eq].
      rewrite Hfn.
      eapply interprets_to_preserved with (args1 := margs_aa) (d1 := out_aa); eauto.
      - apply all2_Symmetric; [typeclasses eauto | exact Hopt].
      - symmetry; exact Hret_eq.
    Qed.

    Lemma worklist_sound : all (worklist_entry_sound m i) e.(worklist).
    Proof.
      eapply all_wkn.
      2: apply worklist_ok; eauto.
      cbn; intros x Hwl.
      destruct x; cbn in *; auto.
      eauto using rel_interpretation.
    Qed.

  End WithEGraph.

  (* TODO: canonicalize_worklist_entry_sound. Previously formulated
     against set-level [Pre] using [P_guarantees]. *)


  (*TODO: move to Defs.v*)
  Arguments pull_parents {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope x _.
  (*TODO: move to Defs.v*)
  Arguments remove_parents {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope x _.


  Ltac iss_case :=
    lazymatch goal with
    | H : ?ma <$> _ |- _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn in H;[| tauto]
    | |- ?ma <?> _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn;[| tauto]
    end.

  (*TODO: move to Defs.v*)
  Arguments db_remove {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope
  {analysis_result}%type_scope a _.

  (* [db_remove a] only modifies the [db] field, removing the entry
     at [(atom_fn a, atom_args a)]. All other instance fields
     (equiv, parents, epoch, worklist, analyses, log) are unchanged,
     and the only db fact lost is exactly that one entry. The
     postcondition records every such preserved fact, so callers can
     reason about the post-state without re-deriving them. Note that
     [db_remove] does NOT preserve egraph_ok in general (parents may
     refer to a now-missing atom), which is why the original
     [Pre]-preserving formulation was abandoned. *)
  Lemma db_remove_sound a
    : vc (db_remove a)
        (fun e res =>
           fst res = tt
           /\ (snd res).(equiv) = e.(equiv)
           /\ (snd res).(parents) = e.(parents)
           /\ (snd res).(epoch) = e.(epoch)
           /\ (snd res).(worklist) = e.(worklist)
           /\ (snd res).(analyses) = e.(analyses)
           /\ forall x,
               atom_in_egraph x (snd res)
               <-> atom_in_egraph x e
                   /\ (atom_fn x, atom_args x) <> (atom_fn a, atom_args a)).
  Proof.
    unfold vc, db_remove.
    intros e.
    cbv beta zeta.
    cbn [fst snd Defs.equiv Defs.parents Defs.epoch
         Defs.worklist Defs.analyses Defs.db].
    do 6 (split; [reflexivity|]).
    intros x.
    unfold atom_in_egraph, atom_in_db.
    cbn [Defs.db].
    unfold map_update.
    destruct (map.get e.(db) (atom_fn a)) as [tbl|] eqn:Htbl.
    - (* atom_fn a was in the original db with table [tbl] *)
      pose proof (eqb_spec (atom_fn x) (atom_fn a)) as Hfn.
      destruct (eqb (atom_fn x) (atom_fn a)).
      + (* atom_fn x = atom_fn a *)
        rewrite Hfn.
        rewrite map.get_put_same.
        cbn [Is_Some_satisfying].
        unfold Basics.flip.
        pose proof (eqb_spec (atom_args x) (atom_args a)) as Hargs.
        destruct (eqb (atom_args x) (atom_args a)).
        * (* both fn and args equal: removed entry *)
          rewrite Hargs.
          rewrite map.get_remove_same.
          cbn [Is_Some_satisfying].
          split; [tauto|].
          intros [_ Hne]. exfalso. apply Hne. reflexivity.
        * (* atom_args x <> atom_args a: lookup unchanged in tbl *)
          rewrite map.get_remove_diff by exact Hargs.
          rewrite Htbl. cbn [Is_Some_satisfying].
          split.
          -- intros HX. split; [exact HX|].
             intros Hpair. inversion Hpair; subst; auto.
          -- intros [HX _]; exact HX.
      + (* atom_fn x <> atom_fn a: lookup unchanged *)
        rewrite map.get_put_diff
          by (intros Heq; apply Hfn; exact Heq).
        split.
        * intros HX. split; [exact HX|].
          intros Hpair. inversion Hpair; subst; auto.
        * intros [HX _]; exact HX.
    - (* atom_fn a was NOT in the original db originally *)
      pose proof (eqb_spec (atom_fn x) (atom_fn a)) as Hfn.
      destruct (eqb (atom_fn x) (atom_fn a)).
      + (* atom_fn x = atom_fn a: the new table is empty after
           removing [atom_args a] *)
        rewrite Hfn.
        rewrite map.get_put_same.
        cbn [Is_Some_satisfying].
        unfold Basics.flip.
        unfold default, map_default.
        rewrite Htbl. cbn [Is_Some_satisfying].
        pose proof (eqb_spec (atom_args x) (atom_args a)) as Hargs.
        destruct (eqb (atom_args x) (atom_args a)).
        * rewrite Hargs.
          rewrite map.get_remove_same.
          cbn [Is_Some_satisfying]. tauto.
        * rewrite map.get_remove_diff by exact Hargs.
          rewrite map.get_empty.
          cbn [Is_Some_satisfying]. tauto.
      + (* atom_fn x <> atom_fn a *)
        rewrite map.get_put_diff
          by (intros Heq; apply Hfn; exact Heq).
        split.
        * intros HX. split; [exact HX|].
          intros Hpair. inversion Hpair; subst; auto.
        * intros [HX _]; exact HX.
  Qed.

  (* Predicate capturing the structural facts that [db_remove a]
     establishes about the relationship between its input state
     [e_ref] and its output state [e]: every non-db field is
     unchanged, and the db has lost exactly the entry at
     [(atom_fn a, atom_args a)]. This is the conjunction of
     conjuncts in the postcondition of [db_remove_sound]. *)
  Definition post_db_remove (e_ref : instance) (a : atom) (e : instance) : Prop :=
    e.(equiv) = e_ref.(equiv)
    /\ e.(parents) = e_ref.(parents)
    /\ e.(epoch) = e_ref.(epoch)
    /\ e.(worklist) = e_ref.(worklist)
    /\ e.(analyses) = e_ref.(analyses)
    /\ (forall x, atom_in_egraph x e
                  <-> atom_in_egraph x e_ref
                      /\ (atom_fn x, atom_args x) <> (atom_fn a, atom_args a)).

  (* [db_remove_sound]'s postcondition immediately rephrased as
     [post_db_remove], for use as a precondition of downstream
     [update_entry] lemmas. *)
  Lemma db_remove_sound_post a
    : vc (db_remove a)
        (fun e res => fst res = tt /\ post_db_remove e a (snd res)).
  Proof.
    eapply vc_consequence; [| exact (db_remove_sound a)].
    unfold post_db_remove; intuition.
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
  Proof using H0.
    clear lt idx_succ idx_zero.
    unfold eq_sound_for_model.
    repeat intro.
    repeat iss_case.
    cbn.
    symmetry; auto.
  Qed.

  
  (*TODO: backport*)
  Ltac break ::=
    repeat match goal with
   | H:unit |- _ => destruct H
   | H:_ * _ |- _ => destruct H
    | H:_ /\ _ |- _ =>
        (*TODO: why is this necessary *)
        let H1 := fresh in
        let H2 := fresh in
        destruct H as [H1 H2]; try clear H
   | H:exists x, _ |- _ => destruct H
      end.

 
  Lemma atom_sound_args_have_key i a
    : atom_sound_for_model m i a ->
      all (fun x => Sep.has_key x i) a.(atom_args).
  Proof.
    unfold atom_sound_for_model, Sep.has_key, Is_Some_satisfying.
    intros H1.
    destruct (list_Mmap (map.get i) a.(atom_args)) eqn:Hg; cbn in H1; try tauto.
    clear H1.
    revert l Hg.
    induction (atom_args a) as [| arg args IH]; cbn; intros.
    - exact I.
    - destruct (map.get i arg) eqn:Hgarg; cbn in *; try discriminate.
      destruct (list_Mmap (map.get i) args) eqn:Hgargs; cbn in *; try discriminate.
      split; auto.
      eapply IH; eauto.
  Qed.

  Lemma atom_sound_ret_has_key i a
    : atom_sound_for_model m i a ->
      Sep.has_key a.(atom_ret) i.
  Proof.
    unfold atom_sound_for_model, Sep.has_key, Is_Some_satisfying.
    intros H1.
    destruct (list_Mmap (map.get i) a.(atom_args)) eqn:Hg; cbn in H1; try tauto.
    destruct (map.get i a.(atom_ret)); cbn in *; tauto.
  Qed.

  
  Arguments db_lookup {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
    {analysis_result}%type_scope f args%list_scope _.

  Arguments db_set {idx}%type_scope {Eqb_idx} {symbol}%type_scope
    {symbol_map idx_map idx_trie}%function_scope
    {analysis_result}%type_scope {H} a _.

  (*

TODO: lemmas in the comment block are out of date

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
    eapply atom_interpretation in H1; eauto.
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
      try eapply H3 in case_match_eqn0; try eapply H2 in case_match_eqn;
      try eapply H2 in case_match_eqn0; try eapply H3 in case_match_eqn;
      try specialize (H1 k);
      rewrite ? H2, ?H3 in *;
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
    eapply find_spec in H5; eauto; break; try Lia.lia.
    eapply find_spec in H6; eauto; break; try Lia.lia.
    2:{ eapply H12; eauto. }
    eapply find_preserves_domain with (x:=k) in case_match_eqn, case_match_eqn0;
      eauto.
    2:{ eapply H12; eauto. }
    rewrite H12.
    case_match; autorewrite with inversion in *; break; subst; eauto.
    
    assert (Sep.has_key i (parent u)).
    {
      unfold Sep.has_key.      
      eapply forest_root_iff with (m:= parent u) in H5; eauto using uf_forest.
      rewrite H5; eauto.
    }
    assert (Sep.has_key i1 (parent u)).
    {
      unfold Sep.has_key.      
      eapply forest_root_iff with (m:= parent u) in H6; eauto using uf_forest.
      rewrite H6; eauto.
    }
    case_match; cbn in *; autorewrite with inversion in *; break; subst; cbn in *; eauto.
    all: rewrite H17.
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
  Proof using H0.
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
    2:{ eapply H11; eauto. }
    eqb_case i i0.
    {
      autorewrite with inversion in *; break; subst.
      intuition eauto.
      eapply H15.
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
                  eapply H15; eapply union_find_limit; eauto; Lia.lia).
    all: eapply transitive_closure_transitive;
      [now (eapply unloop_parent; eauto using uf_forest;
            eapply H15; eapply union_find_limit; eauto; Lia.lia)|].
    all: eapply parent_rel_put_same; now eauto.
  Qed.
    
  
  Lemma state_sound_for_model_wkn i A (s : state instance A) P Q
    : state_sound_for_model m i s P ->
      (forall i' a, map.extends i' i -> P i' a -> Q i' a) ->
      state_sound_for_model m i s Q.
  Proof.
    clear idx_zero idx_succ.
    unfold state_sound_for_model, state_triple, Sep.and1; basic_goal_prep;
      intuition eauto.
    specialize (H1 e).
    intuition break.
    eexists; intuition eauto.
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
    { destruct H5; constructor; basic_goal_prep; intuition eauto. }
    {
      destruct H6; constructor; basic_goal_prep; intuition eauto.
      {
        unfold atom_in_egraph, atom_in_db in H4; cbn in H4.
        eqb_case (atom_fn a) (atom_fn a2);
          [ rewrite H6 in *; rewrite get_update_same in *
          | rewrite get_update_diff in * ]; eauto.
        basic_goal_prep.
        case_match.
        {
          eqb_case (atom_args a) (atom_args a2);
          [ rewrite H7 in *; rewrite map.get_put_same in *
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
          [ rewrite H7 in *; rewrite map.get_put_same in *
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
                  i = Some l) in H4.
        destruct (map.get (parents e) i) eqn:Hpe.
        2:{
          assert (incl l [a]).
          {
            assert (map.get (parents e) i <?> (fun l => incl l [a])).
            { rewrite Hpe; cbn; auto. }
            revert H6 l H4.
            generalize (parents e);
            generalize (dedup eqb (atom_ret a :: atom_args a)).
            induction l;
              basic_goal_prep;
              basic_utils_crush.
            { rewrite H4 in *; cbn in *; auto. }
            {
              eapply IHl in H4; eauto.
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
          revert H4 Hpe.
          revert l l0;
            generalize (parents e);
            generalize (dedup eqb (atom_ret a :: atom_args a)).
          induction l;
            basic_goal_prep;
            basic_utils_crush.
          { replace l0 with l by congruence; eauto with utils. }
          {
            eqb_case i a1; eapply IHl with (r:=(map_update r a1 (cons a))) in H4.
            2:{ rewrite get_update_same, Hpe; eauto. }
            3:{ rewrite get_update_diff, Hpe; eauto. }
            2: now eauto with utils.
            revert H4; clear; unfold incl; cbn; intuition eauto.
            eapply H4 in H.
            intuition subst; eauto.
          }
        }
        eapply all_incl; try eassumption.
        cbn; intuition eauto.
      }
    }    
  Qed.

  (*TODO: move *)
  Lemma all2_same A R (l : list A)
    : all2 R l l <-> all (fun x => R x x) l.
  Proof.
    clear.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
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
        eapply interprets_to_functional in H5; try apply H1.
        {
          unfold eq_sound_for_model.
          rewrite Hma0; cbn; rewrite Hma2; cbn; symmetry; eauto.
        }
        {
          rewrite all2_same.
          eapply interprets_to_implies_wf_args; eauto.
        }
      }
      {
        intros; subst.
        eapply ret_sound_for_model'; intuition subst; eauto with utils.
        break; subst; eauto.
      }
    }        
    { break; subst; eapply db_set_sound; eauto. }
  Qed.
  
  Lemma eq_atom_implies_sound_l i a3 a1 
    : eq_atom_in_interpretation i a3 a1 ->
      atom_sound_for_model m i a3 -> atom_sound_for_model m i a1.
  Proof.
    clear idx_succ idx_zero.
    unfold eq_atom_in_interpretation, eq_sound_for_model, atom_sound_for_model.
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
    eapply interprets_to_preserved; eauto.
    inversions; eauto.
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


    
  
  
  Lemma push_worklist_sound_analysis i o
    : state_sound_for_model m i
        (push_worklist idx symbol symbol_map idx_map idx_trie analysis_result
           (analysis_repair idx o)) 
        (fun i' _ => i = i').
  Proof.
    open_ssm.
    cbn; eauto.
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
    eapply all2_same; eapply interprets_to_implies_wf_args; eauto.
  Qed.
  Hint Resolve atom_sound_functional : utils.

  (*
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
  *)

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

  
  (*TODO: move to Lists.v *)
  Lemma all_dedup A (P : A -> Prop) f l
    : all P l -> all P (dedup f l).
  Proof using.
    clear.
    induction l;
      basic_goal_prep;
      try case_match; cbn;
      basic_utils_crush.
  Qed.    
  
*)

  (* Predicate: every instance field except [equiv] is preserved
     verbatim, [equiv] may have been path-compressed but its key set
     and equivalence relation [uf_rel_PER] are preserved. *)
  Definition fields_preserved (e e' : instance) : Prop :=
    e'.(db) = e.(db)
    /\ e'.(parents) = e.(parents)
    /\ e'.(epoch) = e.(epoch)
    /\ e'.(worklist) = e.(worklist)
    /\ e'.(analyses) = e.(analyses)
    /\ (forall y, Sep.has_key y e.(equiv).(parent)
                  <-> Sep.has_key y e'.(equiv).(parent))
    /\ iff2 (uf_rel_PER _ _ _ e.(equiv))
            (uf_rel_PER _ _ _ e'.(equiv)).

  Lemma fields_preserved_refl (e : instance)
    : fields_preserved e e.
  Proof.
    unfold fields_preserved.
    repeat split; auto; intros; tauto.
  Qed.

  Lemma fields_preserved_trans (e1 e2 e3 : instance)
    : fields_preserved e1 e2 ->
      fields_preserved e2 e3 ->
      fields_preserved e1 e3.
  Proof.
    unfold fields_preserved.
    intros (Hd1 & Hp1 & Hep1 & Hw1 & Han1 & Hk1 & Hi1).
    intros (Hd2 & Hp2 & Hep2 & Hw2 & Han2 & Hk2 & Hi2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split; [congruence|]. split.
    + intros y; specialize (Hk1 y); specialize (Hk2 y); tauto.
    + intros i j; specialize (Hi1 i j); specialize (Hi2 i j); tauto.
  Qed.

  (* [find x] only modifies the [equiv] field through path
     compression. All non-equiv fields are preserved verbatim,
     union-find well-formedness is preserved with the same root
     list, and the equivalence relation [uf_rel_PER] together with
     the key set of [equiv.(parent)] is preserved up to pointwise
     iff.  Additionally, the returned canonical idx [v'] is
     [uf_rel_PER]-equivalent to the input [x] in the post-state's
     [equiv].  The extra conjunct comes from [find_spec]'s
     [parent_rel uf'.(parent) x v'], which is included in
     [PER_closure] via [trans_PER_subrel] and then symmetrized. *)
  Lemma find_preserves_fields_strong (x : idx)
    : vc (find x)
        (fun (e : instance) (res : (idx * instance)%type) =>
           (exists l, union_find_ok lt e.(equiv) l) ->
           Sep.has_key x e.(equiv).(parent) ->
           (exists l, union_find_ok lt (snd res).(equiv) l)
           /\ fields_preserved e (snd res)
           /\ uf_rel_PER _ _ _ (snd res).(equiv) (fst res) x).
  Proof.
    unfold vc, find, fields_preserved.
    intros e Hex Hkey.
    destruct Hex as [l Huf].
    destruct (UnionFind.find e.(equiv) x) as [uf' v'] eqn:Hfind.
    cbn [snd Defs.db Defs.parents Defs.epoch Defs.worklist
         Defs.analyses Defs.equiv].
    assert (lt_trans_nat : forall a b c : nat, a < b -> b < c -> a < c)
      by (intros; Lia.lia).
    pose proof (@find_spec _ _ _ _ _ _ _ default lt_trans_nat
                  _ _ _ _ _ Huf Hkey Hfind) as Hspec.
    destruct Hspec as (Huf' & _ & Hpr & _ & Hlim_iff & Hkey_iff).
    pose proof Huf as [Hf_old _ _ _ _].
    pose proof Huf' as [Hf_new _ _ _ _].
    cbn in Hf_old, Hf_new.
    split; [exists l; exact Huf'|].
    split.
    { repeat (split; [reflexivity|]).
      split.
      { intros y; split; intros Hk; apply Hkey_iff; exact Hk. }
      intros i j.
      unfold uf_rel_PER.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat
                    _ _ Hf_old i j) as HP1.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat
                    _ _ Hf_new i j) as HP2.
      rewrite HP1, HP2.
      split; intros (r & Hl1 & Hl2); exists r;
        intuition (try apply Hlim_iff; auto). }
    cbn [fst].
    unfold uf_rel_PER.
    apply PER_clo_sym.
    unfold parent_rel in Hpr.
    clear -Hpr.
    induction Hpr.
    - apply PER_clo_base; assumption.
    - eapply PER_clo_trans;
        [apply PER_clo_base; eassumption | exact IHHpr].
  Qed.

  (* Iterating [find] over a list of indices preserves the same
     structural facts as a single [find], and additionally the
     returned canonical idxs are [uf_rel_PER]-equivalent to their
     inputs (pointwise via [all2]) in the post-state's [equiv].
     Proven by direct induction on [xs] rather than via
     [vc_list_Mmap_inv], since the per-element canonical-equivalence
     outputs need to be carried through subsequent [find]s (using
     [iff2] of [uf_rel_PER] across path compression). *)
  Lemma list_Mmap_find_preserves_fields_strong (xs : list idx)
    : vc (list_Mmap find xs)
        (fun (e : instance) (res : (list idx * instance)%type) =>
           (exists l, union_find_ok lt e.(equiv) l) ->
           all (fun i => Sep.has_key i e.(equiv).(parent)) xs ->
           (exists l, union_find_ok lt (snd res).(equiv) l)
           /\ fields_preserved e (snd res)
           /\ all2 (uf_rel_PER _ _ _ (snd res).(equiv)) (fst res) xs).
  Proof.
    induction xs as [| x xs' IH].
    - unfold vc. intros e Hex _.
      cbn [list_Mmap Mret StateMonad.state_monad fst snd].
      split; [exact Hex|]. split; [apply fields_preserved_refl|]. exact I.
    - unfold vc. intros e Hex Hkeys.
      cbn [all] in Hkeys. destruct Hkeys as [Hkey_x Hkeys'].
      cbn [list_Mmap Mbind StateMonad.state_monad].
      pose proof (find_preserves_fields_strong x e Hex Hkey_x) as Hf.
      cbn beta in Hf.
      destruct (find x e) as [y e1] eqn:Hfind_x.
      cbn [fst snd] in Hf.
      destruct Hf as (Hex1 & Hf01 & Huf_yx).
      assert (Hkeys'_e1 :
                all (fun i => Sep.has_key i e1.(equiv).(parent)) xs').
      { destruct Hf01 as (_ & _ & _ & _ & _ & Hkey_iff & _).
        eapply all_wkn; [| exact Hkeys'].
        intros z _ Hz. apply Hkey_iff. exact Hz. }
      pose proof (IH e1 Hex1 Hkeys'_e1) as IHapp.
      cbn beta in IHapp.
      destruct (list_Mmap find xs' e1) as [ys' e2] eqn:Hmap.
      cbn [fst snd] in IHapp.
      destruct IHapp as (Hex2 & Hf12 & Hall_ys'_xs').
      cbn [Mret StateMonad.state_monad fst snd].
      split; [exact Hex2|].
      split; [eapply fields_preserved_trans; eauto|].
      cbn [all2].
      split.
      + destruct Hf12 as (_ & _ & _ & _ & _ & _ & Huf_iff).
        apply Huf_iff. exact Huf_yx.
      + exact Hall_ys'_xs'.
  Qed.

  (* [canonicalize a] is a sequence of [find] calls (one per arg
     and one for the return idx) followed by a [Build_atom]. As
     such, every instance field except [equiv] is preserved
     verbatim, [equiv] changes only by path compression (so
     [uf_rel_PER] is preserved up to pointwise iff), the returned
     atom [a'] has the same [atom_fn] as [a] (by construction of
     [Build_atom]), and its [atom_ret]/[atom_args] are pointwise
     [uf_rel_PER]-equivalent to those of [a] in the post-state's
     [equiv]. *)
  Lemma canonicalize_preserves_fields_strong (a : atom)
    : vc (canonicalize a)
        (fun (e : instance) (res : (atom * instance)%type) =>
           (exists l, union_find_ok lt e.(equiv) l) ->
           all (fun i => Sep.has_key i e.(equiv).(parent))
               a.(atom_args) ->
           Sep.has_key a.(atom_ret) e.(equiv).(parent) ->
           (exists l, union_find_ok lt (snd res).(equiv) l)
           /\ fields_preserved e (snd res)
           /\ atom_fn (fst res) = atom_fn a
           /\ uf_rel_PER _ _ _ (snd res).(equiv)
                (atom_ret (fst res)) (atom_ret a)
           /\ all2 (uf_rel_PER _ _ _ (snd res).(equiv))
                (atom_args (fst res)) (atom_args a)).
  Proof.
    destruct a as [fn args o]. cbn [atom_args atom_ret atom_fn] in *.
    unfold canonicalize.
    unfold vc.
    intros e Hex Hkey_args Hkey_o.
    cbn [Mbind StateMonad.state_monad].
    pose proof (list_Mmap_find_preserves_fields_strong args e Hex Hkey_args) as Hl.
    cbn beta in Hl.
    destruct (list_Mmap find args e) as [args' e1] eqn:Hmap.
    cbn [fst snd] in Hl.
    destruct Hl as (Hex1 & Hf01 & Hall_args').
    assert (Hkey_o_e1 : Sep.has_key o e1.(equiv).(parent)).
    { destruct Hf01 as (_ & _ & _ & _ & _ & Hkey_iff & _).
      apply Hkey_iff. exact Hkey_o. }
    pose proof (find_preserves_fields_strong o e1 Hex1 Hkey_o_e1) as Hfo.
    cbn beta in Hfo.
    destruct (find o e1) as [o' e2] eqn:Hfind_o.
    cbn [fst snd] in Hfo.
    destruct Hfo as (Hex2 & Hf12 & Huf_o'_o).
    cbn [Mret StateMonad.state_monad fst snd].
    cbn [Defs.atom_fn Defs.atom_ret Defs.atom_args].
    split; [exact Hex2|].
    split; [eapply fields_preserved_trans; eauto|].
    split; [reflexivity|].
    split; [exact Huf_o'_o|].
    destruct Hf12 as (_ & _ & _ & _ & _ & _ & Huf_iff).
    eapply all2_iff2; [exact Huf_iff | exact Hall_args'].
  Qed.

  (* Canonicalize step of [repair_each_sound]'s [canonicalize a >>=
     update_entry] body, packaged as a [state_triple] so that
     [repair_each_sound] is a clean [state_triple_bind] composition
     rather than a manual case-split.

     Given outer hypotheses witnessing that [a] is sound under [Pre]
     in some interpretation of [e_ref], and given a state [e]
     related to [e_ref] by [post_db_remove], [canonicalize a]
     produces an atom [a'] and a state [e1] such that the non-equiv
     fields are preserved verbatim, [equiv] changes only by path
     compression (preserving its key set and [uf_rel_PER]), and
     [a'] is canonically equivalent to [a] in [e1.(equiv)].

     Reduction.  Apply [canonicalize_preserves_fields_strong]; its
     [Sep.has_key] preconditions about [a]'s args/ret are derived
     from [HPa]+[Hne_ref] via
     [atom_sound_args_have_key]/[atom_sound_ret_has_key],
     [interpretation_exact], and [post_db_remove ⇒ e.(equiv) =
     e_ref.(equiv)].  Orthogonal to the deep semantic argument in
     [update_entry_canonicalized_after_db_remove_sound]. *)

  (* [db_lookup f args] reads [e.(db)] and returns either [Some r]
     (when [(f, args)] has a table-entry with value [r], i.e.,
     [Build_atom f args r] is literally in [e.(db)]), or [None]
     (when no such entry exists for any [r]).  The operation is
     read-only on the state. *)
  Lemma db_lookup_pure f args
    : vc (db_lookup f args)
        (fun e res =>
           snd res = e
           /\ match fst res with
              | Some r => atom_in_egraph (Build_atom f args r) e
              | None => forall r, ~ atom_in_egraph (Build_atom f args r) e
              end).
  Proof.
    unfold vc, db_lookup.
    intros e.
    cbn [fst snd].
    split; [reflexivity|].
    unfold atom_in_egraph, atom_in_db.
    cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret].
    destruct (map.get e.(db) f) as [tbl|] eqn:Htbl; cbn.
    - destruct (map.get tbl args) as [entry|] eqn:Hentry; cbn.
      + reflexivity.
      + intros r Hatom. exact Hatom.
    - intros r Hatom. exact Hatom.
  Qed.

  Definition union_worklist_rel (e e' : instance) x y :=
    e'.(worklist) = e.(worklist)
    \/ exists v_old v' a,
         e'.(worklist) = (union_repair _ v_old v' a) :: e.(worklist)
         /\ uf_rel_PER idx (idx_map idx) (idx_map nat) e'.(equiv) v_old x
         /\ uf_rel_PER idx (idx_map idx) (idx_map nat) e'.(equiv) v' y.

  Notation uf_rel_PER := (uf_rel_PER idx (idx_map idx) (idx_map nat)).

  (*TODO: move to Utils *)
  Definition map_equiv {K V} Rk Rv {m : map.map K V} (m1 m2 : m) : Prop :=
    forall k1 k2,
      Rk k1 k2
      <-> option_relation Rv (map.get m1 k1) (map.get m2 k2).  

  Definition db_equiv R : symbol_map (idx_trie (db_entry idx analysis_result)) -> _ -> Prop :=
    map_equiv eq (map_equiv (all2 R) (fun x y => R x.(entry_value _ _) y.(entry_value _ _))).

  Record egraph_extensional_eq (e1 e2 : instance) : Prop :=
    {
      db_eq : db_equiv (uf_rel_PER e1.(equiv)) e1.(db) e2.(db);
      equiv_eq : iff2 (uf_rel_PER e1.(equiv)) (uf_rel_PER e2.(equiv));
      parents_eq : e1.(parents) = e2.(parents); (*TODO: should be up to canonicity, but I might happen not to need that generallity*)
      worklist_eq : e1.(worklist) = e2.(worklist); (*TODO: same as parents*)      
    }.    

  Notation find := (find (symbol_map:= symbol_map) (analysis_result := analysis_result)).
  
  Lemma find_sound' x roots
    : vc (find x)
        (fun e res =>
           union_find_ok lt (equiv e) roots ->
           Sep.has_key x e.(equiv).(parent) ->
           e.(db) = (snd res).(db) /\
             union_find_ok lt (snd res).(equiv) roots /\
             iff2 (uf_rel_PER e.(equiv)) (uf_rel_PER (snd res).(equiv)) /\
             e.(parents) = (snd res).(parents) /\
             e.(worklist) = (snd res).(worklist) /\
             (forall z, Sep.has_key z e.(equiv).(parent)
                        <-> Sep.has_key z (snd res).(equiv).(parent)) /\
             In (fst res) roots /\
             uf_rel_PER (snd res).(equiv) x (fst res)).
  Proof.
    unfold vc, find.
    intros e Hok Hkx.
    destruct (UnionFind.find e.(equiv) x) as [uf' v'] eqn:Hfind.
    cbn [fst snd db parents worklist equiv analyses log epoch].
    assert (lt_trans_nat : forall a b c : nat, a < b -> b < c -> a < c)
      by (intros; Lia.lia).
    pose proof (@find_spec _ _ _ _ _ _ _ default lt_trans_nat
                  _ _ _ _ _ Hok Hkx Hfind) as Hspec.
    destruct Hspec as
      (Huf'_l & Hin_v' & Hpar_uf' & Hsubrel & Hlim_iff & Hkey_iff).
    split; [reflexivity|].
    split; [exact Huf'_l|].
    split.
    - (* iff2 PER: both forests, share limits, so PERs match *)
      pose proof Hok as [Hf_old _ _ _ _]; cbn in Hf_old.
      pose proof Huf'_l as [Hf_new _ _ _ _]; cbn in Hf_new.
      intros i j; unfold uf_rel_PER.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat
                    _ _ Hf_old i j) as Hold.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat
                    _ _ Hf_new i j) as Hnew.
      rewrite Hold, Hnew.
      split; intros (r0 & Hl1 & Hl2);
        exists r0; split; apply Hlim_iff; assumption.
    - split; [reflexivity|].
      split; [reflexivity|].
      split; [exact Hkey_iff|].
      split; [exact Hin_v'|].
      unfold uf_rel_PER.
      unfold parent_rel in Hpar_uf'.
      eapply trans_PER_subrel; exact Hpar_uf'.
  Qed.

  (* Both endpoints of a PER pair are has_key in the union-find. *)
  Lemma uf_rel_PER_has_key (uf : union_find) (l : list idx) i j
    : union_find_ok lt uf l ->
      uf_rel_PER uf i j ->
      Sep.has_key i uf.(parent) /\ Sep.has_key j uf.(parent).
  Proof.
    intros Huf Hij.
    pose proof Huf as [Hf _ _ _ _]; cbn in Hf.
    assert (lt_trans_nat : forall a b c : nat, a < b -> b < c -> a < c)
      by (intros; Lia.lia).
    (* Both directions: get the parent_rel chain via shared parent and
       inspect its first step to recover map.get. *)
    assert (Hkey_l : forall a b,
               uf_rel_PER uf a b ->
               Sep.has_key a uf.(parent)).
    { intros a b Hab.
      unfold uf_rel_PER in Hab.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat
                    _ _ Hf a b) as HP.
      apply HP in Hab.
      destruct Hab as (r0 & Hl1 & _).
      destruct Hl1 as [Hpr _].
      inversion Hpr as [aa bb Hget|aa bb cc Hget _]; subst;
        unfold Sep.has_key; rewrite Hget; exact I. }
    split; [eapply Hkey_l; exact Hij|].
    eapply Hkey_l. unfold uf_rel_PER in *. apply PER_clo_sym; exact Hij.
  Qed.

  (* Inner version of [union_sound] parameterized by an explicit
     [roots] list.  Callers that don't have a concrete [roots] in
     scope (the typical case after [vc_bind] / [vc_Mseq], where the
     state evar isn't yet introduced when the lemma is applied)
     should use [union_sound] below, which existentially quantifies
     over [roots]. *)
  Lemma union_sound_with_roots (x y : idx) roots
    : vc (Defs.union x y)
        (fun e res =>
           union_find_ok lt (equiv e) roots ->
           Sep.has_key x e.(equiv).(parent) ->
           Sep.has_key y e.(equiv).(parent) ->
           e.(db) = (snd res).(db) /\
             (exists roots', union_find_ok lt (snd res).(equiv) roots') /\
             iff2 (union_closure_PER (uf_rel_PER (equiv e)) (singleton_rel x y))
               (uf_rel_PER (snd res).(equiv)) /\
             e.(parents) = (snd res).(parents) /\
             union_worklist_rel e (snd res) x y /\
             uf_rel_PER (snd res).(equiv) x (fst res)).
  Proof.
    unfold Defs.union.
    vc_bind find_sound'.
    vc_bind find_sound'.
    eqb_case a a0.
    { (* Mret case: find x = find y = a0, no UnionFind.union *)
      unfold vc.
      intros s2 Hpost_y Hpost_x Hok Hkx Hky.
      cbn [fst snd] in *.
      specialize (Hpost_x Hok Hkx).
      destruct Hpost_x as
        (Hdb_x & Hok_s1 & Hiff_x & Hpa_x & Hwl_x & Hki_x & Hin_x & Hxa).
      specialize (Hpost_y Hok_s1 (proj1 (Hki_x y) Hky)).
      destruct Hpost_y as
        (Hdb_y & Hok_s2 & Hiff_y & Hpa_y & Hwl_y & Hki_y & Hin_y & Hya).
      cbn [Mret StateMonad.state_monad fst snd].
      assert (Hiff_02 : iff2 (uf_rel_PER (equiv s0)) (uf_rel_PER (equiv s2))).
      { intros i j; split; intro Hij;
          [ apply Hiff_y; apply Hiff_x; exact Hij
          | apply Hiff_x; apply Hiff_y; exact Hij]. }
      assert (Hxa_s2 : uf_rel_PER (equiv s2) x a0)
        by (apply Hiff_y; exact Hxa).
      assert (Hxy_s2 : uf_rel_PER (equiv s2) x y).
      { unfold uf_rel_PER in *.
        eapply PER_clo_trans; [exact Hxa_s2|].
        apply PER_clo_sym; exact Hya. }
      split; [congruence|].
      split; [exists roots; exact Hok_s2|].
      split.
      - intros i j; split; intro Hij.
        + induction Hij as [a' b [Hl|Hr]
                            |a' b c _ IHab _ IHbc
                            |a' b _ IHab].
          * apply Hiff_02; exact Hl.
          * destruct Hr as [Hax Hby]; subst; exact Hxy_s2.
          * unfold uf_rel_PER in *. eapply PER_clo_trans; eassumption.
          * unfold uf_rel_PER in *. apply PER_clo_sym; assumption.
        + apply PER_clo_base; left.
          apply Hiff_02; exact Hij.
      - split; [congruence|].
        split.
        + left; congruence.
        + exact Hxa_s2. }
    { (* UnionFind.union branch: find x = a, find y = a0, a <> a0 *)
      unfold vc.
      intros s2 Hpost_y Hpost_x Hok Hkx Hky.
      cbn [fst snd] in *.
      specialize (Hpost_x Hok Hkx).
      destruct Hpost_x as
        (Hdb_x & Hok_s1 & Hiff_x & Hpa_x & Hwl_x & Hki_x & Hin_x & Hxa).
      specialize (Hpost_y Hok_s1 (proj1 (Hki_x y) Hky)).
      destruct Hpost_y as
        (Hdb_y & Hok_s2 & Hiff_y & Hpa_y & Hwl_y & Hki_y & Hin_y & Hya).
      assert (Hiff_02 : iff2 (uf_rel_PER (equiv s0)) (uf_rel_PER (equiv s2))).
      { intros i j; split; intro Hij;
          [ apply Hiff_y; apply Hiff_x; exact Hij
          | apply Hiff_x; apply Hiff_y; exact Hij]. }
      assert (Hxa_s2 : uf_rel_PER (equiv s2) x a)
        by (apply Hiff_y; exact Hxa).
      assert (lt_trans_nat : forall a b c : nat, a < b -> b < c -> a < c)
        by (intros; Lia.lia).
      pose proof (uf_rel_PER_has_key _ _ _ _ Hok_s2 Hxa_s2) as [_ Hk_a_s2].
      pose proof (uf_rel_PER_has_key _ _ _ _ Hok_s2 Hya) as [_ Hk_a0_s2].
      pose proof Hok_s2 as [Hf_s2 _ _ _ _]; cbn in Hf_s2.
      assert (Hroot_a_s2 : map.get (equiv s2).(parent) a = Some a)
        by (apply (proj1 (@forest_root_iff _ _ _ _ _ a roots _ Hf_s2));
            exact Hin_x).
      assert (Hroot_a0_s2 : map.get (equiv s2).(parent) a0 = Some a0)
        by (apply (proj1 (@forest_root_iff _ _ _ _ _ a0 roots _ Hf_s2));
            exact Hin_y).
      destruct (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat)
                  (equiv s2) a a0) as [uf3 z'] eqn:Hunion.
      pose proof (@union_spec _ _ _ _ _ _ _ default lt_trans_nat
                    _ _ _ _ _ _ _ Hok_s2 Hk_a_s2 Hk_a0_s2 Hunion) as Hus.
      destruct Hus as [l' (Huf3_l' & Hin_z' & Hincl & Huf3_iff)].
      assert (Hz'_xy : z' = a \/ z' = a0).
      { revert Hunion.
        unfold UnionFind.union, UnionFind.find.
        destruct (equiv s2) as [rk pa mr nx].
        cbn [parent rank max_rank next] in *.
        assert (Hfa_a :
                  find_aux idx Eqb_idx (idx_map idx) (S mr) a pa = (a, pa)).
        { cbn [find_aux].
          rewrite Hroot_a_s2.
          replace (@eqb _ Eqb_idx a a) with true; [reflexivity|].
          symmetry. pose proof (Eqb.eqb_spec a a) as Hsp.
          destruct (eqb a a) eqn:He; intuition congruence. }
        rewrite Hfa_a.
        assert (Hfa_a0 :
                  find_aux idx Eqb_idx (idx_map idx) (S mr) a0 pa = (a0, pa)).
        { cbn [find_aux].
          rewrite Hroot_a0_s2.
          replace (@eqb _ Eqb_idx a0 a0) with true; [reflexivity|].
          symmetry. pose proof (Eqb.eqb_spec a0 a0) as Hsp.
          destruct (eqb a0 a0) eqn:He; intuition congruence. }
        rewrite Hfa_a0.
        cbn [fst snd].
        replace (@eqb _ Eqb_idx a a0) with false
          by (pose proof (Eqb.eqb_spec a a0) as Hsp;
              destruct (eqb a a0) eqn:He; intuition congruence).
        destruct (Nat.compare _ _);
          intros Hu; inversion Hu; subst; auto. }
      assert (Hxa_uf3 : uf_rel_PER uf3 x a)
        by (apply Huf3_iff; apply PER_clo_base; left; exact Hxa_s2).
      assert (Hya_uf3 : uf_rel_PER uf3 y a0)
        by (apply Huf3_iff; apply PER_clo_base; left; exact Hya).
      assert (Haa0_uf3 : uf_rel_PER uf3 a a0).
      { apply Huf3_iff. apply PER_clo_base; right.
        unfold singleton_rel; split; reflexivity. }
      assert (Hxy_uf3 : uf_rel_PER uf3 x y).
      { unfold uf_rel_PER in *.
        eapply PER_clo_trans; [exact Hxa_uf3|].
        eapply PER_clo_trans; [exact Haa0_uf3|].
        apply PER_clo_sym; exact Hya_uf3. }
      assert (Hiff_closure :
                iff2 (union_closure_PER (uf_rel_PER (equiv s0))
                                        (singleton_rel x y))
                     (uf_rel_PER uf3)).
      { intros i j; split; intro Hij.
        - induction Hij as [a' b [Hl|Hr]
                            |a' b c _ IHab _ IHbc
                            |a' b _ IHab].
          + apply Huf3_iff. apply PER_clo_base; left.
            apply Hiff_02; exact Hl.
          + destruct Hr as [Hax Hby]; subst; exact Hxy_uf3.
          + unfold uf_rel_PER in *. eapply PER_clo_trans; eassumption.
          + unfold uf_rel_PER in *. apply PER_clo_sym; assumption.
        - apply Huf3_iff in Hij.
          induction Hij as [a' b [Hl|Hr]
                            |a' b c _ IHab _ IHbc
                            |a' b _ IHab].
          + apply PER_clo_base; left.
            apply Hiff_02; exact Hl.
          + destruct Hr as [Hax Hby]; subst.
            unfold uf_rel_PER in *.
            eapply PER_clo_trans;
              [apply PER_clo_sym; apply PER_clo_base; left;
               apply Hiff_02; exact Hxa_s2|].
            eapply PER_clo_trans;
              [apply PER_clo_base; right;
               unfold singleton_rel; split; reflexivity|].
            apply PER_clo_base; left.
            apply Hiff_02; exact Hya.
          + unfold uf_rel_PER in *. eapply PER_clo_trans; eassumption.
          + unfold uf_rel_PER in *. apply PER_clo_sym; assumption. }
      destruct Hz'_xy as [Hz_eq | Hz_eq]; subst z'.
      - (* z' = a: rank chose a as the new root *)
        replace (@eqb _ Eqb_idx a a) with true.
        2: { symmetry. pose proof (Eqb.eqb_spec a a) as Hs.
             destruct (eqb a a) eqn:He; intuition congruence. }
        cbn [fst snd db parents worklist equiv].
        split; [congruence|].
        split; [exists l'; exact Huf3_l'|].
        split; [exact Hiff_closure|].
        split; [congruence|].
        split.
        { right. do 3 eexists.
          split; [rewrite Hwl_x, Hwl_y; reflexivity|].
          split.
          + unfold uf_rel_PER in *.
            apply PER_clo_sym.
            eapply PER_clo_trans; [exact Hxa_uf3 | exact Haa0_uf3].
          + unfold uf_rel_PER in *.
            eapply PER_clo_trans;
              [exact Haa0_uf3 | apply PER_clo_sym; exact Hya_uf3]. }
        exact Hxa_uf3.
      - (* z' = a0: rank chose a0 as the new root *)
        replace (@eqb _ Eqb_idx a a0) with false.
        2: { symmetry. pose proof (Eqb.eqb_spec a a0) as Hs.
             destruct (eqb a a0) eqn:He; intuition congruence. }
        cbn [fst snd db parents worklist equiv].
        split; [congruence|].
        split; [exists l'; exact Huf3_l'|].
        split; [exact Hiff_closure|].
        split; [congruence|].
        split.
        { right. do 3 eexists.
          split; [rewrite Hwl_x, Hwl_y; reflexivity|].
          split.
          + unfold uf_rel_PER in *. apply PER_clo_sym; exact Hxa_uf3.
          + unfold uf_rel_PER in *. apply PER_clo_sym; exact Hya_uf3. }
        unfold uf_rel_PER in *.
        eapply PER_clo_trans; [exact Hxa_uf3 | exact Haa0_uf3]. }
  Qed.

  (* Existential-roots form of [union_sound]: the precondition
     [union_find_ok lt (equiv e) roots] is bundled inside an
     [exists roots, ...].  This is the shape callers want when
     applying via [vc_bind] / [vc_Mseq], where the [e] being
     analyzed is only introduced after the lemma is eapplied. *)
  Lemma union_sound (x y : idx)
    : vc (Defs.union x y)
        (fun e res =>
           (exists roots, union_find_ok lt (equiv e) roots) ->
           Sep.has_key x e.(equiv).(parent) ->
           Sep.has_key y e.(equiv).(parent) ->
           e.(db) = (snd res).(db) /\
             (exists roots', union_find_ok lt (snd res).(equiv) roots') /\
             iff2 (union_closure_PER (uf_rel_PER (equiv e)) (singleton_rel x y))
               (uf_rel_PER (snd res).(equiv)) /\
             e.(parents) = (snd res).(parents) /\
             union_worklist_rel e (snd res) x y /\
             uf_rel_PER (snd res).(equiv) x (fst res)).
  Proof.
    unfold vc; intros e [roots Hok] Hkx Hky.
    exact (union_sound_with_roots x y roots e Hok Hkx Hky).
  Qed.


  (* Atom-level equality (under the interpretation) preserves
     soundness: if [a3] is sound and [a1] is i-equivalent to [a3]
     (same fn, args eq_sound pointwise, ret eq_sound), then [a1]
     is also sound.  (This duplicates the [eq_atom_implies_sound_l]
     defined inside the deprecated comment block at line ~2523.) *)
  Lemma eq_atom_implies_sound_l_active i a3 a1
    : eq_atom_in_interpretation i a3 a1 ->
      atom_sound_for_model m i a3 -> atom_sound_for_model m i a1.
  Proof.
    clear idx_succ idx_zero.
    unfold eq_atom_in_interpretation, eq_sound_for_model, atom_sound_for_model.
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
    eapply interprets_to_preserved; eauto.
    inversions; eauto.
  Qed.

  (* Two atoms in the e-graph (or just sound under [i]) with the same
     [atom_fn] and pointwise [eq_sound]-equal [atom_args] have
     [eq_sound]-equal [atom_ret].  Lift of [interprets_to_functional]
     to interpretation level. *)
  Lemma atom_sound_eq_ret i f args1 args2 r1 r2
    : atom_sound_for_model m i (Build_atom f args1 r1) ->
      atom_sound_for_model m i (Build_atom f args2 r2) ->
      all2 (eq_sound_for_model m i) args1 args2 ->
      eq_sound_for_model m i r1 r2.
  Proof.
    clear idx_succ idx_zero.
    intros Hsa1 Hsa2 Hargs.
    (* Convert (Build_atom f args1 r1) to (Build_atom f args2 r1)
       using eq_atom_implies_sound_l_active. *)
    pose proof Hsa1 as Hsa1_orig.
    apply (eq_atom_implies_sound_l_active i (Build_atom f args1 r1)
                                            (Build_atom f args2 r1))
      in Hsa1.
    2:{ unfold eq_atom_in_interpretation; cbn.
        split; [reflexivity|]; split; [exact Hargs |].
        (* eq_sound i r1 r1: from has_key r1 in i + interprets_to_implies_wf_conclusion. *)
        unfold atom_sound_for_model in Hsa1_orig. cbn in Hsa1_orig.
        destruct (list_Mmap (map.get i) args1) as [vs|] eqn:Hvs;
          cbn in Hsa1_orig; try tauto.
        unfold eq_sound_for_model.
        destruct (map.get i r1) as [r1v|] eqn:Hr1; cbn in Hsa1_orig; try tauto.
        cbn.
        eapply interprets_to_implies_wf_conclusion; eauto. }
    (* Now Hsa1 : atom_sound i (Build_atom f args2 r1) and
       Hsa2 : atom_sound i (Build_atom f args2 r2).  Direct. *)
    unfold atom_sound_for_model in Hsa1, Hsa2.
    cbn in Hsa1, Hsa2.
    destruct (list_Mmap (map.get i) args2) as [vs|] eqn:Hvs;
      cbn in Hsa1, Hsa2; try tauto.
    destruct (map.get i r1) as [v1|] eqn:Hv1; cbn in Hsa1; try tauto.
    destruct (map.get i r2) as [v2|] eqn:Hv2; cbn in Hsa2; try tauto.
    unfold eq_sound_for_model.
    rewrite Hv1, Hv2; cbn.
    pose proof (interprets_to_implies_wf_args _ _ _ Hsa1) as Hwf_vs.
    eapply interprets_to_functional with (args1 := vs) (args2 := vs); eauto.
    clear -Hwf_vs.
    induction vs; cbn in *; auto.
    intuition.
  Qed.


  (* Some-branch helper for [update_entry_canonicalized_after_db_
     remove_sound].  When [db_lookup (atom_fn a') (atom_args a')]
     returned [Some r] (so [Build_atom (atom_fn a') (atom_args a') r]
     is literally in [e1.(db)]), [update_entry] runs [union r
     (atom_ret a')] (and [Mret tt]).  The deep semantic argument
     reduces to a [state_triple]-level [union_sound]: [r] and
     [atom_ret a'] interpret to the same value under any [denote
     e_ref i], because both are values in the db for canonically-
     equivalent atom keys, and [HPa] gives soundness for [a]. *)

  (* None-branch helper for [update_entry_canonicalized_after_db_
     remove_sound].  When [db_lookup (atom_fn a') (atom_args a')]
     returned [None] (so no entry exists in [e1.(db)] for the
     canonicalized key), [update_entry] runs [db_set a'].  The deep
     semantic argument: by [Hatom_ref] there is some [aa] canonically
     equivalent to [a] in [e_ref.(db)]; combined with [post_db_
     remove e_ref a e0] (the only entry removed is at [(atom_fn a,
     atom_args a)]) and [fields_preserved e0 e1.db = e0.db] and the
     [None] hypothesis, [db_set a'] reinstalls the canonical witness
     in a way that preserves [Pre]/[ne_set_maps_to]/[side_l]. *)

  (* Update_entry step of [repair_each_sound]'s [canonicalize a >>=
     update_entry] body.  This is where the deep semantic-
     preservation argument lives, factored into branch-specific
     helpers ([union_after_canonicalize_sound] and
     [db_set_after_canonicalize_sound]).

     [update_entry] case-splits on [db_lookup a'.(atom_fn)
     a'.(atom_args)] applied to [e1]; the proof composes the read-
     only [db_lookup_pure], a case-split on the option result, and
     the appropriate branch helper, all via [state_triple_bind]
     and [state_triple_consequence].  [state_triple] is never
     unfolded. *)

  (* repair_each (the inner closure of repair_union) preserves Pre
     when called on a sound atom that is canonically represented in the
     input db, and simultaneously preserves [atom_in_egraph_up_to_equiv]
     for an arbitrary side-list [l] of other atoms. The semantic story
     is that db_remove followed by canonicalize+update_entry leaves the
     egraph's set of facts unchanged up to canonicalization, provided
     the entry being removed corresponds (up to canonical equivalence)
     to [a]. Note that db_remove alone does NOT preserve Pre
     (db_remove_sound is Aborted above), so this lemma is proved as a
     single unit rather than by composition.

     The proof composes three vc-form lemmas in sequence: [db_remove_
     sound_post] (giving a [post_db_remove] relation between the pre-
     and post-removal states), [canonicalize_after_db_remove_sound]
     (giving the structural facts about the canonicalized atom), and
     [update_entry_canonicalized_after_db_remove_sound] (the deep
     semantic argument). *)

  (* State-triple level Mmap of repair_each over a list of atoms.
     The structural invariant — every remaining atom is canonically
     represented in the current db — must hold initially and is
     preserved by each iteration: repair_each on one atom replaces a
     canonical-equivalence witness with another canonically-equivalent
     witness, so [atom_in_egraph_up_to_equiv] for the other atoms is
     maintained (modulo possibly enlarged [equiv]). The semantic
     soundness of all atoms is also preserved across repair_each by
     [ne_set_maps_to_trans] + monotone1_atom_sound.

     This statement bundles both invariants into the precondition;
     the inductive step is dispatched by [repair_each_sound], which
     bundles the per-step semantic soundness with the side-list
     [atom_in_egraph_up_to_equiv]-preservation needed for the tail. *)

  (* Primitives used by repair_parent_analysis. These are admitted because
     their existing proofs (in the comment block above, lines 2609-2702)
     are written in the old state_sound_for_model style and need to be
     translated. They are all "preserves Pre" lemmas modulo a soundness
     side condition for db_set_entry. *)






  (* Adding an entry (and its parent pointers) for a sound atom preserves
     any [Pre] every interpretation of the egraph satisfies.  The proof
     is structural — [db_set'] only enlarges the [atom_in_egraph] set and
     updates [parents] in lockstep — but is left admitted here, since the
     interesting composition is in [db_set_sound] below. *)

  (* Generic soundness for [db_set]: if all interpretations witnessing
     [Pre] also see [a] as sound, then writing [a] (with computed analysis)
     preserves [Pre].  Composes [get_analyses_sound'],
     [update_analyses_sound'], and [db_set'_sound] via [vc_bind].  The
     tail of the proof threads the three per-step [exists ie /\ map.extends]
     witnesses back to the input state. *)

  
  Arguments repair_parent_analysis {idx symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope {analysis_result}%type_scope
  {H} a _.

  Arguments repair_union {idx}%type_scope {Eqb_idx} {symbol}%type_scope
  {symbol_map idx_map idx_trie}%function_scope {analysis_result}%type_scope
  {H} _ _ _ _.

  (* Soundness of [list_Miter repair_parent_analysis ps] under the
     hypothesis that all atoms in [ps] are sound for the model. This
     is exactly the inner Miter chunk used in both branches of
     [repair_sound]. Factored out for reuse. *)




  (* [pull_worklist] only swaps the worklist field of the instance for
     [[]]; denote/egraph_ok don't read the worklist outside of
     [worklist_ok], which trivially holds for [[]]. *)
  Lemma pull_worklist_denote_iff
    : vc (pull_worklist idx symbol symbol_map idx_map idx_trie analysis_result)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold vc, pull_worklist; intros e Hok; cbn [fst snd].
    destruct e as [db_e equiv_e parents_e epoch_e wl_e analyses_e log_e]; cbn.
    destruct Hok as [Heq Hwl Hpa]; cbn in *.
    split.
    { constructor; cbn; auto. }
    intros j; split; intros [Hwf Hex Ha Hr]; constructor; cbn in *; auto.
  Qed.

  (* If [x] is not in [equiv]'s parent map, [UnionFind.find] returns
     the union-find unchanged. Used to handle the no-key case in
     [find_denote_iff]. *)
  Lemma find_no_key_identity (e : instance) x
    : map.get e.(equiv).(parent) x = None ->
      UnionFind.find e.(equiv) x = (e.(equiv), x).
  Proof.
    intros Hgx.
    unfold UnionFind.find.
    destruct e.(equiv) as [ra pa mr l] eqn:Heq.
    cbn in Hgx |- *.
    destruct mr; cbn; rewrite Hgx; reflexivity.
  Qed.

  (* [find] only updates [equiv] via path compression; both [egraph_ok]
     and [denote] are preserved. Path compression keeps the union-find
     well-formed with the same root list and preserves
     [uf_rel_PER] up to [iff2]. *)
  Lemma find_denote_iff x
    : vc (find x)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold vc, find; intros e Hok.
    destruct (UnionFind.find e.(equiv) x) as [uf' v'] eqn:Hfind.
    cbn [fst snd].
    destruct Hok as [Heq Hwl Hpa].
    destruct Heq as [roots Huf_l].
    pose (e' := {| db := db e; equiv := uf'; parents := parents e;
                   epoch := epoch e; worklist := worklist e;
                   analyses := analyses e;
                   log := log idx symbol symbol_map idx_map idx_trie
                            analysis_result e |}).
    change ({| db := db e; equiv := uf'; parents := parents e;
               epoch := epoch e; worklist := worklist e;
               analyses := analyses e;
               log := log idx symbol symbol_map idx_map idx_trie
                        analysis_result e |}) with e'.
    assert (lt_trans_nat : forall a b c : nat, a < b -> b < c -> a < c)
      by (intros; Lia.lia).
    assert (Hcommon : union_find_ok lt e'.(equiv) roots
                     /\ iff2 (limit (parent_rel idx (idx_map idx)
                                       (equiv e).(parent)))
                            (limit (parent_rel idx (idx_map idx)
                                      e'.(equiv).(parent)))).
    { destruct (map.get e.(equiv).(parent) x) as [px|] eqn:Hgx.
      - assert (Hkx : Sep.has_key x e.(equiv).(parent)).
        { unfold Sep.has_key. rewrite Hgx. exact I. }
        pose proof (@find_spec _ _ _ _ _ _ _ default lt_trans_nat
                      _ _ _ _ _ Huf_l Hkx Hfind) as Hspec.
        destruct Hspec as (Huf'_l & _ & _ & _ & Hlim_iff & _).
        subst e'; cbn. split; [exact Huf'_l | exact Hlim_iff].
      - rewrite (find_no_key_identity e x Hgx) in Hfind.
        injection Hfind; intros; subst uf' v'.
        subst e'; cbn.
        split; [exact Huf_l|].
        intros i j; reflexivity. }
    destruct Hcommon as [Huf'_l Hlim_iff].
    assert (Hiff : forall j, (egraph_ok e /\ denote e j)
                             <-> (egraph_ok e' /\ denote e' j)).
    { intros j. apply (egraph_sound_for_interpretation_iff_equiv j e e' roots);
        subst e'; cbn; auto. }
    assert (Hper_iff : iff2 (uf_rel_PER (equiv e)) (uf_rel_PER (equiv e'))).
    { pose proof Huf_l as [Hf_old _ _ _ _]; cbn in Hf_old.
      pose proof Huf'_l as [Hf_new _ _ _ _]; cbn in Hf_new.
      unfold uf_rel_PER.
      intros i j.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat
                    _ _ Hf_old i j) as HP1.
      pose proof (@forest_PER_shared_parent _ _ _ _ _ _ default lt_trans_nat
                    _ _ Hf_new i j) as HP2.
      cbn in *.
      rewrite HP1, HP2.
      split; intros (r & Hl1 & Hl2); exists r;
        intuition (try apply Hlim_iff; auto). }
    assert (Hok_e' : egraph_ok e').
    { constructor.
      - exists roots. exact Huf'_l.
      - subst e'; cbn.
        eapply all_wkn; [|exact Hwl].
        intros [old new improved | k] _ Hwentry; cbn in *; auto.
        apply Hper_iff; assumption.
      - subst e'; cbn.
        intros y s Hg.
        pose proof (Hpa _ _ Hg) as Hall.
        eapply all_wkn; [|exact Hall].
        intros a Hin Hex.
        cbv beta in Hex.
        unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv in *.
        destruct Hex as (aa & Hcanon & Ha_aa).
        destruct Hcanon as (Hfn & Hargs & Hret).
        exists aa; split.
        + split; [exact Hfn|]. split.
          * eapply all2_impl; [|exact Hargs]. intros; apply Hper_iff; auto.
          * apply Hper_iff. exact Hret.
        + unfold atom_in_egraph in *; cbn in *. exact Ha_aa. }
    split; [exact Hok_e'|].
    intros j; split; intros Hd.
    - apply (Hiff j). split; [|exact Hd]. constructor; auto.
      exists roots; exact Huf_l.
    - destruct (proj2 (Hiff j) (conj Hok_e' Hd)) as [_ Hde]. exact Hde.
  Qed.

  (* [canonicalize_worklist_entry] on a [union_repair] entry calls
     [find] on its [new_idx]; the [analysis_repair] case is a [Mret].
     Both preserve [egraph_ok] and [denote]. *)
  Lemma canonicalize_worklist_entry_denote_iff a
    : vc (canonicalize_worklist_entry idx Eqb_idx symbol
            symbol_map idx_map idx_trie analysis_result a)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold canonicalize_worklist_entry.
    destruct a as [old new improved | i_repair]; cbn beta iota.
    - vc_bind find_denote_iff.
      unfold vc, Mret, StateMonad.state_monad.
      intros s1 HPpost Hok_s0; cbn [fst snd] in *.
      exact (HPpost Hok_s0).
    - unfold vc, Mret, StateMonad.state_monad; cbn [fst snd].
      intros e Hok; split; [exact Hok|]. intros i; reflexivity.
  Qed.

  (* List-iterated [canonicalize_worklist_entry] preserves [egraph_ok]
     and [denote] pointwise; proved by induction on the list with
     [vc_bind] composing per-element preservation and the IH. *)
  Lemma list_Mmap_canonicalize_worklist_entry_denote_iff l
    : vc (list_Mmap
            (canonicalize_worklist_entry idx Eqb_idx symbol
               symbol_map idx_map idx_trie analysis_result) l)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_inv _
                  (fun _ s => egraph_ok s)
                  (fun s s' => forall i, denote s i <-> denote s' i))].
    - cbn beta. intros s res Hinv Hok. apply (Hinv Hok).
    - intros s _ i; reflexivity.
    - intros ? ? ? H1 H2 i; rewrite H1; auto.
    - intros a l_rest.
      eapply vc_consequence; [| apply (canonicalize_worklist_entry_denote_iff a)].
      cbn beta. intros s p Hone Hok. apply (Hone Hok).
  Qed.

  (* [get_parents] is read-only: returned parents are recorded as
     parents in the egraph, so they satisfy [atom_in_egraph_up_to_equiv]
     by [parents_ok]. *)
  Lemma get_parents_denote_iff x
    : vc (get_parents x)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ snd res = e
           /\ all (fun a => atom_in_egraph_up_to_equiv a e) (fst res)).
  Proof.
    unfold vc, get_parents; intros e Hok; cbn [fst snd].
    split; [exact Hok|].
    split; [intros i; reflexivity|].
    split; [reflexivity|].
    unfold unwrap_with_default.
    destruct (map.get e.(parents) x) as [s|] eqn:Hg.
    - destruct Hok as [_ _ Hpa]. eapply Hpa; exact Hg.
    - cbn. exact I.
  Qed.

  (* [remove_parents x] removes the entry for [x] from the parents map.
     db and equiv are unchanged, so denote (which doesn't read parents)
     is preserved. [parents_ok] still holds because removing entries
     only weakens the per-key invariant. *)
  Lemma remove_parents_denote_iff x
    : vc (remove_parents x)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ (snd res).(db) = e.(db)
           /\ (snd res).(equiv) = e.(equiv)).
  Proof.
    unfold vc, remove_parents; intros e Hok; cbn [fst snd].
    destruct Hok as [Heq Hwl Hpa].
    destruct e as [db_e equiv_e parents_e epoch_e wl_e analyses_e log_e];
      cbn in *.
    split.
    { constructor; cbn; auto.
      intros y s Hg.
      eqb_case x y.
      + rewrite map.get_remove_same in Hg. discriminate.
      + rewrite map.get_remove_diff in Hg by auto.
        pose proof (Hpa _ _ Hg) as Hall.
        eapply all_wkn; [|exact Hall].
        intros a Hin Hex.
        unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv,
          atom_in_egraph, atom_in_db in *.
        destruct Hex as (aa & Hcanon & Hain).
        exists aa; cbn in *; intuition. }
    split.
    { intros i; split; intros [Hwf Hex Hatom Hrel];
        constructor; cbn in *; auto. }
    split; reflexivity.
  Qed.

  (* [pull_parents] = [get_parents] composed with [remove_parents].
     The returned parents are still atoms in the post-state's egraph
     since [remove_parents] doesn't touch db or equiv. *)
  Lemma pull_parents_denote_iff x
    : vc (pull_parents x)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ all (fun a => atom_in_egraph_up_to_equiv a (snd res)) (fst res)).
  Proof.
    vc_bind get_parents_denote_iff.
    rename s0 into e, a into ps.
    vc_bind remove_parents_denote_iff.
    rename s0 into e0, a into u.
    unfold vc, Mret, StateMonad.state_monad; cbn [fst snd].
    intros s1 Hrm Hgp Hok.
    destruct (Hgp Hok) as (Hok_e0 & Hde_e0 & Hs0_eq & Hain_ps_e).
    subst e0.
    destruct (Hrm Hok) as (Hok_s1 & Hde_s1 & Hdb_eq & Hequiv_eq).
    split; [exact Hok_s1|].
    split; [intros i; rewrite Hde_s1; reflexivity|].
    eapply all_wkn; [|exact Hain_ps_e].
    intros a _ Hex.
    unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv,
      atom_in_egraph, atom_in_db in *.
    destruct Hex as (aa & Hcanon & Hain).
    exists aa.
    rewrite Hdb_eq, Hequiv_eq; auto.
  Qed.

  (* An atom that is canonically present in the egraph has all of its
     args and ret as keys in the union-find: pick the witness [aa] in
     the db (whose args/ret are in the equiv via egraph_ok), and the
     pairwise PER-equivalence with [a] transfers has_key. *)
  Lemma atom_in_egraph_up_to_equiv_has_key (e : instance) (a : atom)
    : egraph_ok e ->
      atom_in_egraph_up_to_equiv a e ->
      all (fun i => Sep.has_key i e.(equiv).(parent)) a.(atom_args)
      /\ Sep.has_key a.(atom_ret) e.(equiv).(parent).
  Proof.
    intros Hok Hex.
    destruct Hok as [Heq Hwl Hpa].
    destruct Heq as [roots Huf_l].
    unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv in Hex.
    destruct Hex as (aa & (Hfn & Hargs & Hret) & _).
    split.
    - clear Hret Hfn.
      remember (atom_args aa) as args_aa eqn:Eaa.
      clear Eaa aa.
      revert args_aa Hargs.
      induction a.(atom_args) as [|x xs IH];
        destruct args_aa as [|y ys]; cbn;
        try contradiction; auto.
      intros [Hxy Hxs_ys].
      split.
      + apply (uf_rel_PER_has_key _ _ _ _ Huf_l Hxy).
      + apply (IH ys); exact Hxs_ys.
    - apply (uf_rel_PER_has_key _ _ _ _ Huf_l Hret).
  Qed.

  (* TODO: prove. Denote-iff form of the [Some r] branch of
     [update_entry_canonicalized_denote_iff]: when [db_lookup] of the
     canonicalized atom returned [Some r], so a canonically-equivalent
     entry [(atom_fn a, atom_args a', r)] is still in [e1.db], the
     union [union r (atom_ret a')] preserves egraph_ok and the denote
     relation pointwise w.r.t. the pre-[db_remove] state [e_ref].
     This is the denote-iff analog of the proved
     [union_after_canonicalize_sound].

     The forward direction (denote e_ref i -> denote (snd res) i)
     generalizes the existing proof's [HiSSC_post] construction: the
     new PER pair [r ~ atom_ret a'] is implied by atom_in_db
     interpretations under any sound i.

     The backward direction (denote (snd res) i -> denote e_ref i)
     needs the congruence invariant the existing proof captures as
     the [Hcong] precondition: if [(atom_fn a, atom_args a, v)] is in
     [e_ref.db], then [v ~ atom_ret a] in [e_ref.equiv]. This is
     needed because the removed atom must be soundly interpretable by
     any i sound for the post-state, and the equivalence between the
     literal removed key's value and [atom_ret a] is not derivable
     from [egraph_ok e_ref] alone (egraph_ok doesn't include a
     congruence-closure invariant).

     To discharge this admit, either: (a) strengthen [egraph_ok] with
     a congruence-closure invariant and re-prove dependents, or (b)
     thread an explicit congruence precondition through the chain
     ([repair_each_denote_iff] -> [update_entry_canonicalized_denote_
     iff] -> branches). *)
  Lemma union_after_canonicalize_denote_iff
    a a' side_l (e_ref e0 : instance) (r : idx)
    : egraph_ok e_ref ->
      atom_in_egraph_up_to_equiv a e_ref ->
      all (fun a' => atom_in_egraph_up_to_equiv a' e_ref) side_l ->
      post_db_remove e_ref a e0 ->
      vc (Mseq (Defs.union r a'.(atom_ret)) (Mret tt))
        (fun e1 res =>
           (exists roots, union_find_ok lt e1.(equiv) roots) ->
           fields_preserved e0 e1 ->
           atom_fn a' = atom_fn a ->
           uf_rel_PER e1.(equiv) (atom_ret a') (atom_ret a) ->
           all2 (uf_rel_PER e1.(equiv))
                (atom_args a') (atom_args a) ->
           atom_in_egraph (Build_atom (atom_fn a') (atom_args a') r) e1 ->
           egraph_ok (snd res)
           /\ (forall i, denote e_ref i <-> denote (snd res) i)
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) side_l).
  Proof.
  Admitted.

  (* TODO: prove. Denote-iff form of the [None] branch: when
     [db_lookup] returned [None], we reinstall the canonicalized atom
     via [db_set a']. Mirrors the still-admitted
     [db_set_after_canonicalize_sound].

     Same congruence-closure issue as the union branch: the removed
     literal (atom_fn a, atom_args a) entry's value v_old needs to
     be PER-equivalent to atom_ret a in e_ref.equiv to interpret the
     removed atom soundly from a post-state interpretation. See the
     comment on [union_after_canonicalize_denote_iff] for the two
     resolution options. *)
  Lemma db_set_after_canonicalize_denote_iff
    a a' side_l (e_ref e0 : instance)
    : egraph_ok e_ref ->
      atom_in_egraph_up_to_equiv a e_ref ->
      all (fun a' => atom_in_egraph_up_to_equiv a' e_ref) side_l ->
      post_db_remove e_ref a e0 ->
      vc (db_set a')
        (fun e1 res =>
           (exists roots, union_find_ok lt e1.(equiv) roots) ->
           fields_preserved e0 e1 ->
           atom_fn a' = atom_fn a ->
           uf_rel_PER e1.(equiv) (atom_ret a') (atom_ret a) ->
           all2 (uf_rel_PER e1.(equiv))
                (atom_args a') (atom_args a) ->
           (forall r, ~ atom_in_egraph
                          (Build_atom (atom_fn a') (atom_args a') r) e1) ->
           egraph_ok (snd res)
           /\ (forall i, denote e_ref i <-> denote (snd res) i)
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) side_l).
  Proof.
  Admitted.

  (* Dispatcher: [update_entry a'] case-splits on [db_lookup a'.fn
     a'.args]; the [Some r] case uses [union_after_canonicalize_
     denote_iff] and the [None] case uses
     [db_set_after_canonicalize_denote_iff]. This is the denote-iff
     analog of [update_entry_canonicalized_after_db_remove_sound],
     proved by composing the two branch helpers. *)
  Lemma update_entry_canonicalized_denote_iff a a' side_l (e_ref e0 : instance)
    : vc (update_entry a')
        (fun e1 res =>
           egraph_ok e_ref ->
           atom_in_egraph_up_to_equiv a e_ref ->
           all (fun a' => atom_in_egraph_up_to_equiv a' e_ref) side_l ->
           post_db_remove e_ref a e0 ->
           (exists roots, union_find_ok lt e1.(equiv) roots) ->
           fields_preserved e0 e1 ->
           atom_fn a' = atom_fn a ->
           uf_rel_PER e1.(equiv) (atom_ret a') (atom_ret a) ->
           all2 (uf_rel_PER e1.(equiv)) (atom_args a') (atom_args a) ->
           egraph_ok (snd res)
           /\ (forall i, denote e_ref i <-> denote (snd res) i)
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) side_l).
  Proof.
    unfold update_entry.
    vc_bind db_lookup_pure.
    rename s0 into e1, a0 into mr.
    unfold vc.
    destruct mr as [r|]; cbn beta iota; cbn [fst snd];
      intros s_pre [Hs_eq Hatom_case]; subst s_pre;
      intros Hok_ref Hatom_ref Hatoms_ref Hpost
             Hex_e1 Hf01 Hfn_eq Hret_eq Hargs_eq.
    - (* Some r: invoke union branch *)
      pose proof (union_after_canonicalize_denote_iff
                    a a' side_l e_ref e0 r
                    Hok_ref Hatom_ref Hatoms_ref Hpost) as Hu.
      specialize (Hu e1).
      apply Hu; auto.
    - (* None: invoke db_set branch *)
      pose proof (db_set_after_canonicalize_denote_iff
                    a a' side_l e_ref e0
                    Hok_ref Hatom_ref Hatoms_ref Hpost) as Hd.
      specialize (Hd e1).
      apply Hd; auto.
  Qed.

  (* Composes the three pieces: [db_remove a] gives [post_db_remove],
     [canonicalize a] uses the has-key facts derived from
     [atom_in_egraph_up_to_equiv a e_ref] to produce a canonically-
     equivalent atom [a'] in a state with [equiv]-only changes, and
     [update_entry_canonicalized_denote_iff] finishes by restoring
     egraph_ok and denote w.r.t. the original [e_ref]. *)
  Lemma repair_each_denote_iff a l
    : vc (@! let _ <- db_remove a in
             let a' <- canonicalize a in
             (update_entry a'))
        (fun e res =>
           egraph_ok e ->
           atom_in_egraph_up_to_equiv a e ->
           all (fun a' => atom_in_egraph_up_to_equiv a' e) l ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) l).
  Proof.
    vc_bind db_remove_sound_post.
    rename s0 into e_ref, a0 into u_dbr.
    vc_bind canonicalize_preserves_fields_strong.
    rename s0 into e0, a0 into a'.
    eapply vc_consequence;
      [| apply (update_entry_canonicalized_denote_iff a a' l e_ref e0)].
    cbn beta. cbn [fst snd].
    intros e1 res Hupd Hcan Hdbr Hok_ref Hatom_ref Hatoms_ref.
    destruct Hdbr as [_ Hpost].
    pose proof Hpost as Hpost_full.
    destruct Hpost as (Hequiv_eq & _).
    pose proof (atom_in_egraph_up_to_equiv_has_key e_ref a Hok_ref Hatom_ref)
      as [Hkargs Hkret].
    assert (Hkargs_e0 : all (fun i => Sep.has_key i e0.(equiv).(parent))
                              a.(atom_args)).
    { rewrite Hequiv_eq. exact Hkargs. }
    assert (Hkret_e0 : Sep.has_key a.(atom_ret) e0.(equiv).(parent)).
    { rewrite Hequiv_eq. exact Hkret. }
    pose proof Hok_ref as Hok_ref_orig.
    destruct Hok_ref as [Heq_ref Hwl Hpa].
    destruct Heq_ref as [roots Huf_ref].
    assert (Hex_e0 : exists l, union_find_ok lt e0.(equiv) l).
    { exists roots. rewrite Hequiv_eq. exact Huf_ref. }
    specialize (Hcan Hex_e0 Hkargs_e0 Hkret_e0).
    destruct Hcan as (Hex_e1 & Hfp01 & Hfn_a' & Hret_a' & Hargs_a').
    apply Hupd; auto.
  Qed.

  (* Iterating [repair_each] over a list of atoms-in-egraph preserves
     egraph_ok and denote, by induction with [repair_each_denote_iff]
     threading the side-list invariant. *)
  Lemma list_Mmap_repair_each_denote_iff old_ps
    : vc (list_Mmap (fun a : atom =>
                       @! let _ <- db_remove a in
                          let a' <- canonicalize a in
                          (update_entry a'))
                    old_ps)
        (fun e res =>
           egraph_ok e ->
           all (fun a => atom_in_egraph_up_to_equiv a e) old_ps ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_inv _
                  (fun l s =>
                     egraph_ok s
                     /\ all (fun a => atom_in_egraph_up_to_equiv a s) l)
                  (fun s s' => forall i, denote s i <-> denote s' i))].
    - cbn beta. intros s res Hinv Hok Hall.
      specialize (Hinv (conj Hok Hall)).
      destruct Hinv as [Hp Hiff]. destruct Hp as [Hok_p _]. auto.
    - intros s _ i; reflexivity.
    - intros ? ? ? H1 H2 i; rewrite H1; auto.
    - intros a l_rest.
      eapply vc_consequence; [| apply (repair_each_denote_iff a l_rest)].
      cbn beta. intros s p Hone [Hok Hall].
      cbn [all] in Hall. destruct Hall as [Ha Hl_rest].
      destruct (Hone Hok Ha Hl_rest) as (Hok_p & Hde_p & Hl_p).
      split; [split; assumption | exact Hde_p].
  Qed.

  (* [update_analyses] only writes the [analyses] field, which doesn't
     affect egraph_ok or denote. *)
  Lemma update_analyses_denote_iff k v
    : vc (update_analyses idx symbol symbol_map idx_map idx_trie
            analysis_result k v)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ (snd res).(db) = e.(db)).
  Proof.
    unfold vc, update_analyses; intros e Hok; cbn [fst snd].
    destruct e as [db_e equiv_e parents_e epoch_e wl_e analyses_e log_e]; cbn.
    destruct Hok as [Heq Hwl Hpa]; cbn in *.
    split; [constructor; cbn; auto|].
    split;
      [intros i; split; intros [Hwf Hex Hatom Hrel];
         constructor; cbn in *; auto
      | reflexivity].
  Qed.

  (* [push_worklist (analysis_repair _)] adds a trivially-ok entry to
     the worklist. denote doesn't read the worklist. *)
  Lemma push_worklist_analysis_denote_iff o
    : vc (push_worklist idx symbol symbol_map idx_map idx_trie
            analysis_result (analysis_repair idx o))
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ (snd res).(db) = e.(db)).
  Proof.
    unfold vc, push_worklist; intros e Hok; cbn [fst snd].
    destruct e as [db_e equiv_e parents_e epoch_e wl_e analyses_e log_e]; cbn.
    destruct Hok as [Heq Hwl Hpa]; cbn in *.
    split; [constructor; cbn; auto|].
    split;
      [intros i; split; intros [Hwf Hex Hatom Hrel];
         constructor; cbn in *; auto
      | reflexivity].
  Qed.

  (* [get_analysis x]: read [analyses] for [x], or on miss run
     [update_analyses x default] + [push_worklist (analysis_repair x)].
     Both branches preserve egraph_ok and denote. *)
  Lemma get_analysis_denote_iff x
    : vc (get_analysis idx symbol symbol_map idx_map idx_trie analysis_result x)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold vc, get_analysis; intros e Hok.
    destruct (map.get e.(analyses) x) as [a|] eqn:Hga.
    - cbn [fst snd]. split; [exact Hok|]. intros i; reflexivity.
    - cbn [Mseq Mbind StateMonad.state_monad fst snd].
      pose proof (update_analyses_denote_iff x default e Hok) as Hu.
      destruct (update_analyses idx symbol symbol_map idx_map idx_trie
                  analysis_result x default e) as [u e1] eqn:Hue.
      cbn [fst snd] in Hu.
      destruct Hu as (Hok1 & Hde1 & _).
      pose proof (push_worklist_analysis_denote_iff x e1 Hok1) as Hp.
      destruct (push_worklist idx symbol symbol_map idx_map idx_trie
                  analysis_result (analysis_repair idx x) e1) as [u' e2] eqn:Hpe.
      cbn [fst snd] in Hp |- *.
      destruct Hp as (Hok2 & Hde2 & _).
      split; [exact Hok2|].
      intros i. rewrite Hde1. exact (Hde2 i).
  Qed.

  (* [get_analyses] = [list_Mmap get_analysis]. Inductive composition. *)
  Lemma get_analyses_denote_iff args
    : vc (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result args)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold get_analyses.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_inv _
                  (fun _ s => egraph_ok s)
                  (fun s s' => forall i, denote s i <-> denote s' i))].
    - cbn beta. intros s res Hinv Hok. apply (Hinv Hok).
    - intros s _ i; reflexivity.
    - intros ? ? ? H1 H2 i; rewrite H1; auto.
    - intros x xs.
      eapply vc_consequence; [| apply (get_analysis_denote_iff x)].
      cbn beta. intros s p Hone Hok. apply (Hone Hok).
  Qed.

  (* [get_analysis] preserves [db], [equiv], and [parents] verbatim:
     the [Some] branch is [Mret]; the [None] branch only writes
     [analyses] and [worklist]. *)
  Lemma get_analysis_preserves_fields x
    : vc (get_analysis idx symbol symbol_map idx_map idx_trie analysis_result x)
        (fun e res =>
           (snd res).(db) = e.(db)
           /\ (snd res).(equiv) = e.(equiv)
           /\ (snd res).(parents) = e.(parents)).
  Proof.
    unfold vc, get_analysis; intros e.
    destruct (map.get e.(analyses) x) as [a|] eqn:Hga.
    - cbn; intuition.
    - cbn [Mseq Mbind StateMonad.state_monad fst snd
           update_analyses push_worklist].
      intuition; cbn; reflexivity.
  Qed.

  (* [get_analyses] preserves [db], [equiv], and [parents] verbatim;
     used by [repair_parent_analysis_denote_iff] to transport
     [atom_in_egraph] across the [get_analyses] step. *)
  Lemma get_analyses_preserves_fields args
    : vc (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result args)
        (fun e res =>
           (snd res).(db) = e.(db)
           /\ (snd res).(equiv) = e.(equiv)
           /\ (snd res).(parents) = e.(parents)).
  Proof.
    unfold get_analyses.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_inv _
                  (fun _ _ => True)
                  (fun s s' =>
                     s'.(db) = s.(db)
                     /\ s'.(equiv) = s.(equiv)
                     /\ s'.(parents) = s.(parents)))].
    - cbn beta. intros s res Hinv. apply (Hinv I).
    - intros s _; intuition.
    - intros ? ? ? (?&?&?) (?&?&?); repeat split; congruence.
    - intros x xs.
      eapply vc_consequence; [| apply (get_analysis_preserves_fields x)].
      cbn beta. intros s p Hone _. split; [exact I | exact Hone].
  Qed.

  (* [db_lookup_entry] is read-only; if it returns [Some entry], the
     entry's value is recorded as a [Build_atom f args ·] in the db. *)
  Lemma db_lookup_entry_pure f args
    : vc (db_lookup_entry idx symbol symbol_map idx_map idx_trie
            analysis_result f args)
        (fun e res =>
           snd res = e
           /\ match fst res with
              | Some entry =>
                  atom_in_egraph
                    (Build_atom f args (entry_value idx analysis_result entry)) e
              | None => True
              end).
  Proof.
    unfold vc, db_lookup_entry; intros e; cbn [fst snd].
    split; [reflexivity|].
    unfold atom_in_egraph, atom_in_db; cbn.
    destruct (map.get e.(db) f) as [tbl|] eqn:Htbl; cbn; auto.
    destruct (map.get tbl args) as [entry|] eqn:Hentry; cbn; auto.
  Qed.

  (* [db_set_entry f args ep v an] preserves egraph_ok and denote when
     an entry at [(f, args)] with value [v] already exists: the new
     entry has the same [entry_value], so [atom_in_db] is unchanged
     for every atom; egraph_ok's [parents_ok] transfers via
     [atom_in_egraph_up_to_equiv] using the same iff. *)
  Lemma db_set_entry_denote_iff f args ep v an
    : vc (db_set_entry idx symbol symbol_map idx_map idx_trie
            analysis_result f args ep v an)
        (fun e res =>
           egraph_ok e ->
           atom_in_egraph (Build_atom f args v) e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold vc, db_set_entry; intros e Hok Hain; cbn [fst snd].
    destruct e as [db_e equiv_e parents_e epoch_e wl_e analyses_e log_e]; cbn.
    destruct Hok as [Heq Hwl Hpa]; cbn in *.
    unfold atom_in_egraph, atom_in_db in Hain; cbn in Hain.
    unfold map_update in *.
    destruct (map.get db_e f) as [tbl|] eqn:Htbl; cbn in Hain; [|tauto].
    destruct (map.get tbl args) as [old_entry|] eqn:Hold; cbn in Hain; [|tauto].
    assert (Hdb_iff : forall a',
               atom_in_db a' (map.put db_e f (map.put tbl args
                                (Build_db_entry idx analysis_result ep v an)))
               <-> atom_in_db a' db_e).
    { intros a'. unfold atom_in_db; cbn.
      eqb_case (atom_fn a') f.
      - rewrite !map.get_put_same. cbn.
        eqb_case (atom_args a') args.
        + rewrite !map.get_put_same. cbn. rewrite Htbl. cbn. rewrite Hold.
          cbn. rewrite Hain. reflexivity.
        + rewrite !map.get_put_diff by auto. rewrite Htbl. cbn. reflexivity.
      - rewrite map.get_put_diff by auto. reflexivity. }
    split.
    - constructor; cbn; auto.
      intros y s Hg. specialize (Hpa _ _ Hg).
      eapply all_wkn; [|exact Hpa].
      intros aa _ Hex.
      unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv,
        atom_in_egraph in *.
      destruct Hex as (a'' & Hcanon & Hain'').
      exists a''; cbn in *. split.
      + exact Hcanon.
      + apply Hdb_iff. exact Hain''.
    - intros i; split; intros [Hwf Hex Hatom Hrel];
        constructor; cbn in *; auto.
      + intros a' Ha'. apply Hatom. unfold atom_in_egraph in *.
        apply Hdb_iff. exact Ha'.
      + intros a' Ha'. apply Hatom. unfold atom_in_egraph in *.
        apply Hdb_iff in Ha'. exact Ha'.
  Qed.

  (* [repair_parent_analysis] reads the db entry for [a], computes a
     new analysis, and if it differs from the stored one, writes it
     back (preserving the entry's value [v]). The proof composes the
     primitive denote_iff lemmas above; [db_set_entry] is invoked with
     the same [v] that was read out, so [atom_in_egraph] is unchanged. *)
  Lemma repair_parent_analysis_denote_iff a
    : vc (repair_parent_analysis a)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold repair_parent_analysis.
    vc_bind db_lookup_entry_pure.
    rename s0 into e_ref, a0 into mr.
    unfold vc.
    destruct mr as [entry|]; cbn beta iota; cbn [fst snd];
      intros s_pre [Hs_eq Hain_or]; subst s_pre; intros Hok_ref;
      [| cbn beta iota; cbn [Mret StateMonad.state_monad fst snd];
         split; [exact Hok_ref|]; intros i; reflexivity].
    destruct entry as [v_epoch v old_a].
    cbn in Hain_or.
    cbn [Mbind StateMonad.state_monad].
    pose proof (get_analyses_denote_iff (atom_args a) e_ref Hok_ref) as Hga.
    pose proof (get_analyses_preserves_fields (atom_args a) e_ref) as Hgaf.
    destruct (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result
                (atom_args a) e_ref) as [arg_as e_g] eqn:Hge.
    cbn [fst snd] in Hga, Hgaf.
    destruct Hga as [Hok_g Hde_g].
    destruct Hgaf as (Hdb_g & Heq_g & Hpa_g).
    destruct (eqb (analyze idx symbol analysis_result a arg_as) old_a) eqn:Hcmp.
    - cbn [Mret StateMonad.state_monad fst snd].
      split; [exact Hok_g | exact Hde_g].
    - cbn [Mseq Mbind StateMonad.state_monad].
      pose proof (update_analyses_denote_iff (atom_ret a)
                    (analyze idx symbol analysis_result a arg_as) e_g Hok_g) as Hua.
      destruct (update_analyses idx symbol symbol_map idx_map idx_trie analysis_result
                  (atom_ret a) (analyze idx symbol analysis_result a arg_as) e_g) as [u e_u] eqn:Hue.
      cbn [fst snd] in Hua.
      destruct Hua as (Hok_u & Hde_u & Hdb_u).
      pose proof (push_worklist_analysis_denote_iff (atom_ret a) e_u Hok_u) as Hpw.
      destruct (push_worklist idx symbol symbol_map idx_map idx_trie analysis_result
                  (analysis_repair idx (atom_ret a)) e_u) as [u2 e_p] eqn:Hpe.
      cbn [fst snd] in Hpw.
      destruct Hpw as (Hok_p & Hde_p & Hdb_p).
      assert (Hain_p : atom_in_egraph (Build_atom (atom_fn a) (atom_args a) v) e_p).
      { unfold atom_in_egraph, atom_in_db in *; cbn in *.
        rewrite Hdb_p, Hdb_u, Hdb_g. exact Hain_or. }
      pose proof (db_set_entry_denote_iff (atom_fn a) (atom_args a) v_epoch v
                    (analyze idx symbol analysis_result a arg_as) e_p Hok_p Hain_p) as Hds.
      destruct (db_set_entry idx symbol symbol_map idx_map idx_trie analysis_result
                  (atom_fn a) (atom_args a) v_epoch v (analyze idx symbol analysis_result a arg_as) e_p)
        as [u3 e_s] eqn:Hse.
      cbn [fst snd] in Hds |- *.
      destruct Hds as [Hok_s Hde_s].
      split; [exact Hok_s|].
      intros i. rewrite Hde_g, Hde_u, Hde_p. exact (Hde_s i).
  Qed.

  (* Iterate [repair_parent_analysis] over a list. *)
  Lemma list_Miter_repair_parent_analysis_denote_iff ps
    : vc (list_Miter repair_parent_analysis ps)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Miter_inv _
                  (fun _ s => egraph_ok s)
                  (fun s s' => forall i, denote s i <-> denote s' i))].
    - cbn beta. intros s res Hinv Hok. apply (Hinv Hok).
    - intros s _ i; reflexivity.
    - intros ? ? ? H1 H2 i; rewrite H1; auto.
    - intros p ps'.
      eapply vc_consequence; [| apply (repair_parent_analysis_denote_iff p)].
      cbn beta. intros s pres Hone Hok. apply (Hone Hok).
  Qed.

  (* The optional analysis pass after the parent-canonicalization mmap.
     Both branches (run-analyses or skip) preserve egraph_ok and denote. *)
  Lemma repair_after_mmap_denote_iff x_canonical (improved : bool)
    : vc (if improved
          then (@! let canon_ps <- get_parents x_canonical in
                   (list_Miter repair_parent_analysis canon_ps))
          else Mret tt)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    destruct improved.
    - vc_bind get_parents_denote_iff.
      eapply vc_consequence;
        [|apply list_Miter_repair_parent_analysis_denote_iff].
      cbn beta. intros s1 res HIH Hgp Hok_s0.
      destruct (Hgp Hok_s0) as (Hok_s1 & Hde_s1 & _).
      destruct (HIH Hok_s1) as [Hok_res Hde_res].
      split; [exact Hok_res|].
      intros i. rewrite Hde_s1. exact (Hde_res i).
    - unfold vc, Mret, StateMonad.state_monad; cbn [fst snd].
      intros e Hok; split; [exact Hok|]. intros i; reflexivity.
  Qed.

  (* [repair_union] = [pull_parents] of [x_old], then [list_Mmap] of
     [repair_each] over those parents, then conditional analysis pass.
     Each piece preserves egraph_ok and denote; pull_parents gives the
     atom-in-egraph invariant that [list_Mmap_repair_each_denote_iff]
     consumes. *)
  Lemma repair_union_denote_iff x_old x_canonical improved
    : vc (repair_union x_old x_canonical improved)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    unfold repair_union.
    vc_bind pull_parents_denote_iff.
    vc_bind list_Mmap_repair_each_denote_iff.
    eapply vc_consequence;
      [|apply (repair_after_mmap_denote_iff x_canonical improved)].
    cbn beta. intros s2 res HIH Hmap Hpull Hok_s0.
    destruct (Hpull Hok_s0) as (Hok_s1 & Hde_s1 & Hains_s1).
    destruct (Hmap Hok_s1 Hains_s1) as [Hok_s2 Hde_s2].
    destruct (HIH Hok_s2) as [Hok_res Hde_res].
    split; [exact Hok_res|].
    intros i. rewrite Hde_s1, Hde_s2. exact (Hde_res i).
  Qed.

  (* Top-level [repair] dispatches by worklist-entry shape. Union
     repairs delegate to [repair_union_denote_iff]; analysis repairs
     run [list_Miter_repair_parent_analysis] over the parents of the
     analyzed index. *)
  Lemma repair_denote_iff a
    : vc (repair a)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    destruct a as [old new improved | i_repair]; cbn [repair].
    - apply repair_union_denote_iff.
    - vc_bind get_parents_denote_iff.
      eapply vc_consequence;
        [|apply list_Miter_repair_parent_analysis_denote_iff].
      cbn beta. intros s1 res HIH Hgp Hok_s0.
      destruct (Hgp Hok_s0) as (Hok_s1 & Hde_s1 & _).
      destruct (HIH Hok_s1) as [Hok_res Hde_res].
      split; [exact Hok_res|].
      intros i. rewrite Hde_s1. exact (Hde_res i).
  Qed.

  (* Iterate [repair] over a list of worklist entries. Used by
     [rebuild_sound]'s inner loop. *)
  Lemma list_Miter_repair_denote_iff l
    : vc (list_Miter repair l)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Miter_inv _
                  (fun _ s => egraph_ok s)
                  (fun s s' => forall i, denote s i <-> denote s' i))].
    - cbn beta. intros s res Hinv Hok. apply (Hinv Hok).
    - intros s _ i; reflexivity.
    - intros ? ? ? H1 H2 i; rewrite H1; auto.
    - intros a l_rest.
      eapply vc_consequence; [| apply (repair_denote_iff a)].
      cbn beta. intros s p Hone Hok. apply (Hone Hok).
  Qed.

  Lemma rebuild_sound (Pre : idx_map (domain m) -> Prop) n
    : vc (rebuild n)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ forall i, denote e i <-> denote (snd res) i).
  Proof.
    induction n.
    { unfold vc, rebuild. intros e Hok. split; [exact Hok|]. intros i; reflexivity. }
    cbn [rebuild].
    vc_bind pull_worklist_denote_iff.
    destruct a as [|w wl'].
    { unfold vc; cbn [Mret StateMonad.state_monad fst snd].
      intros s1 HPpull Hok_s0.
      apply HPpull. exact Hok_s0. }
    cbn [Mbind StateMonad.state_monad Mseq].
    vc_bind list_Mmap_canonicalize_worklist_entry_denote_iff.
    vc_bind list_Miter_repair_denote_iff.
    eapply vc_consequence; [|apply IHn].
    cbn beta. intros s3 res HIH Hmiter Hmap Hpull Hok_s0.
    destruct (Hpull Hok_s0) as [Hok_s1 Hde_s1].
    destruct (Hmap Hok_s1) as [Hok_s2 Hde_s2].
    destruct (Hmiter Hok_s2) as [Hok_s3 Hde_s3].
    destruct (HIH Hok_s3) as [Hok_res Hde_res].
    split; [exact Hok_res|].
    intros i. rewrite Hde_s1, Hde_s2, Hde_s3, Hde_res. reflexivity.
  Qed.

  (*TODO: do not read beyond this point. needs to be updated. *)
  (*
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
      destruct H3 as [ [] ].
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
      
      destruct H3 as [ [] ].
      eapply next_upper_bound in Hsome; eauto.
    }
    {
      destruct H4; constructor; basic_goal_prep; eauto.
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
        eapply atom_interpretation0 in H2.
        eapply atom_sound_monotone; eauto.
        apply extends_put_None.
        destruct H3 as [ [] ].
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
        eapply PER_closure_put in H2.
        2:{
          destruct H3 as [ [? H3] ].
          eapply uf_forest in H3; cbn in *; eauto.
          eapply forest_closed; eauto.
        }
        2:{
          destruct H3 as [ [? H3] ]; cbn in H3.
          eapply next_None in H3; cbn in H3; auto.
        }
        intuition subst.
        { eapply rel_interpretation0 in H4.
          eapply eq_sound_monotone; eauto.
          apply extends_put_None.
          destruct H3 as [ [? H3] ]; cbn in H3.
          eapply next_None in H3; cbn in H3; auto.
          apply map_get_None_contradiction; repeat intro.
          apply interpretation_exact0 in H2.
          unfold Sep.has_key in *; rewrite H3 in *; auto.
        }
        {
          unfold eq_sound_for_model; rewrite map.get_put_same; cbn.
          auto.
        }
      }
      {
        eapply monotone1_all; [apply atom_sound_monotone | | eauto].
        apply extends_put_None.
        destruct H3 as [ [? H3] ]; cbn in H3.
        eapply next_None in H3; cbn in H3; auto.
        apply map_get_None_contradiction; repeat intro.
        apply interpretation_exact0 in H4.
        unfold Sep.has_key in *; rewrite H3 in *; auto.
      }
      {
        eapply monotone1_all; [apply worklist_entry_sound_mono| | eauto].
        apply extends_put_None.
        destruct H3 as [ [? H3] ]; cbn in H3.
        eapply next_None in H3; cbn in H3; auto.
        apply map_get_None_contradiction; repeat intro.
        apply interpretation_exact0 in H2.
        unfold Sep.has_key in *; rewrite H3 in *; auto.
      }
    }        
  Qed.

    
  Lemma alloc_opaque_sound i time_travel_term
    : m.(domain_wf) time_travel_term ->
      state_sound_for_model m i
        (alloc_opaque idx idx_succ symbol symbol_map idx_map idx_trie analysis_result)
        (fun i' x => map.get i' x = Some time_travel_term).
  Proof.
    clear idx_zero.
    unfold alloc_opaque.
    repeat intro.
    unfold Sep.and1 in *; break.
    case_match; cbn.
    pose proof case_match_eqn as H';
      eapply alloc_next in H'; subst.
    exists (map.put i (equiv e).(next) time_travel_term).
    basic_goal_prep; intuition auto.
    { rewrite map.get_put_same; eauto. }
    {
      destruct H3 as [ [] ].
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
      
      destruct H3 as [ [] ].
      eapply next_upper_bound in Hsome; eauto.
    }
    {
      destruct H4; constructor; basic_goal_prep; eauto.
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
        eapply atom_interpretation0 in H2.
        eapply atom_sound_monotone; eauto.
        apply extends_put_None.
        destruct H3 as [ [] ].
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
        eapply PER_closure_put in H2.
        2:{
          destruct H3 as [ [? H3] ].
          eapply uf_forest in H3; cbn in *; eauto.
          eapply forest_closed; eauto.
        }
        2:{
          destruct H3 as [ [? H3] ]; cbn in H3.
          eapply next_None in H3; cbn in H3; auto.
        }
        intuition subst.
        { eapply rel_interpretation0 in H4.
          eapply eq_sound_monotone; eauto.
          apply extends_put_None.
          destruct H3 as [ [? H3] ]; cbn in H3.
          eapply next_None in H3; cbn in H3; auto.
          apply map_get_None_contradiction; repeat intro.
          apply interpretation_exact0 in H2.
          unfold Sep.has_key in *; rewrite H3 in *; auto.
        }
        {
          unfold eq_sound_for_model; rewrite map.get_put_same; cbn.
          auto.
        }
      }
      {
        eapply monotone1_all; [apply atom_sound_monotone | | eauto].
        apply extends_put_None.
        destruct H3 as [ [? H3] ]; cbn in H3.
        eapply next_None in H3; cbn in H3; auto.
        apply map_get_None_contradiction; repeat intro.
        apply interpretation_exact0 in H4.
        unfold Sep.has_key in *; rewrite H3 in *; auto.
      }
      {
        eapply monotone1_all; [apply worklist_entry_sound_mono| | eauto].
        apply extends_put_None.
        destruct H3 as [ [? H3] ]; cbn in H3.
        eapply next_None in H3; cbn in H3; auto.
        apply map_get_None_contradiction; repeat intro.
        apply interpretation_exact0 in H2.
        unfold Sep.has_key in *; rewrite H3 in *; auto.
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

  
  Lemma atom_sound_for_model_preserved i f args1 args2 o1 o2
    : atom_sound_for_model m i {| atom_fn := f; atom_args := args1; atom_ret := o1 |} ->
      all2 (eq_sound_for_model m i) args1 args2 ->
      eq_sound_for_model m i o1 o2 ->
      atom_sound_for_model m i {| atom_fn := f; atom_args := args2; atom_ret := o2 |}.
  Proof.
    unfold atom_sound_for_model.
    basic_goal_prep;
      repeat iss_case; cbn in *.
    unfold eq_sound_for_model in H2.
    rewrite <- TrieMap.all2_map_l
      with (f:= map.get i)
           (R := (fun x y => x <$> (fun x' : domain m => map.get i y <$> domain_eq m x')))
      in H2.
    rewrite all2_Is_Some_satisfying_l in H2; iss_case; cbn in *.
    rewrite <- TrieMap.all2_map_r
      with (f:= map.get i)
           (R := (fun x' y => y <$> domain_eq m x'))
      in H2.
    rewrite all2_Is_Some_satisfying_r in H2; iss_case; cbn in *.
    rewrite <- TrieMap.Mmap_option_all in *.
    replace l with l0 in * by congruence.
    rewrite Hma2; cbn.
    unfold eq_sound_for_model in H3.
    rewrite Hma0 in *; cbn in *.
    iss_case;cbn in *.
    eapply interprets_to_preserved; eauto.
  Qed.

  
  Lemma eq_sound_refl i a d
    : map.get i a = Some d ->
      m.(domain_wf) d ->
      eq_sound_for_model m i a a.
  Proof.
    unfold eq_sound_for_model;
      intros H' H0';
      rewrite H'; cbn.
    eauto.
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
  
  Lemma Mmap_extends A (i i' : idx_map A) args dargs
    : list_Mmap (map.get i) args = Some dargs ->
      map.extends i' i ->
      list_Mmap (map.get i') args = Some dargs.
  Proof.
    revert dargs;
      induction args;
      destruct dargs;
      basic_goal_prep;
      repeat case_match;
      basic_utils_crush;
      try congruence.
    { apply H2 in case_match_eqn1; congruence. }
    {
      specialize (IHargs _ eq_refl);
        intuition congruence.
    }
    {
      specialize (IHargs _ eq_refl);
        intuition congruence.
    }
    { eapply map_extends_None in case_match_eqn; eauto; congruence. }
  Qed.

  Lemma hash_entry_sound i f args dargs out
    : list_Mmap (map.get i) args = Some dargs ->
      m.(interprets_to) f dargs out ->
      state_sound_for_model m i (hash_entry idx_succ f args)
        (fun i x => atom_sound_for_model m i (Build_atom f args x)).
  Proof.
    intros.
    unfold hash_entry.
    ssm_bind.
    {
      eapply state_sound_for_model_Mmap_dep
        with (P_const := fun i' => i = i')
             (P_elt := fun a i a' => eq_sound_for_model m i a a'); auto.
      {
        intros; subst.
        eapply state_sound_for_model_wkn.
        {
          eapply find_sound.
          rewrite TrieMap.Mmap_option_all in *.
          apply in_map with (f:= map.get i') in H3.
          eapply In_option_all in H1; eauto.
          break.
          unfold Sep.has_key; rewrite H5; auto.
        }
        { repeat basic_goal_prep; subst; intuition auto. }
      }
      { repeat intro; eapply eq_sound_monotone; eauto. }
    }
    cbn beta in *; break; subst.
    ssm_bind.
    { apply db_lookup_sound. }
    cbn beta in *; break; subst.
    case_match;
      cbn in H7; break; subst.
    { eapply ret_sound_for_model'.
      repeat change (fun y => ?f y) with f in *.
      eapply atom_sound_for_model_preserved; eauto.
      { eapply all2_Symmetric; eauto; apply eq_sound_for_model_PER. }
      {
        unfold atom_sound_for_model in H7.
        repeat iss_case.
        unfold eq_sound_for_model; repeat (rewrite Hma0;cbn).
        eapply interprets_to_implies_wf_conclusion; eauto.
      }
    }
    ssm_bind.
    {
      apply alloc_sound with (time_travel_term := out).
      eauto using interprets_to_implies_wf_conclusion.
    }
    ssm_bind.
    {
      apply db_set_sound.
      repeat change (fun y => ?f y) with f in *.
      eapply atom_sound_for_model_preserved.
      2:{
        eapply all2_impl; try eassumption.
        intros ? ?; apply eq_sound_monotone; auto.
      }
      2:{
        eapply eq_sound_refl; eauto.
        eapply interprets_to_implies_wf_conclusion; eauto.
      }
      unfold atom_sound_for_model; cbn.
      eapply Mmap_extends in H1; eauto; rewrite H1;cbn.
      rewrite H5; cbn; auto.
    }
    cbn beta in *; break; subst.
    eapply ret_sound_for_model'.
    repeat change (fun y => ?f y) with f in *.
    unfold atom_sound_for_model; cbn.
    eapply Mmap_extends in H1; eauto; rewrite H1;cbn.
    rewrite H5; cbn; auto.
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
          erewrite H12 by eassumption; cbn.
          erewrite H7 by eassumption; eauto.
        }
        {
          rewrite map_keys_put in H14.
          change (?a::?l) with ([a]++l) in H14.
          rewrite Permutation.Permutation_app_comm in H14.
          cbn in *. 
          rewrite Permutation.Permutation_app_comm in H14.
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
        unfold Sep.has_key; rewrite H5; auto.
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
        in H5.
      rewrite all2_Is_Some_satisfying_l in H5.
      rewrite <- TrieMap.Mmap_option_all in *.
      rewrite Hma in *; cbn in*.
      rewrite <- TrieMap.all2_map_r
        with (f:= map.get i'0)
             (R:= (fun x a0 => a0 <$> domain_eq m x))
        in H5.
      rewrite all2_Is_Some_satisfying_r in H5.
      rewrite <- TrieMap.Mmap_option_all in *.
      repeat iss_case; cbn in *.
      eapply interprets_to_preserved; eauto.
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



  (*TODO: backport*)
  Ltac break ::=
    repeat match goal with
   | H:unit |- _ => destruct H
   | H:_ * _ |- _ => destruct H
    | H:_ /\ _ |- _ => destruct H
   | H:exists x, _ |- _ => destruct H
   end.
  
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

  
  Lemma max_id_sound i
    : state_sound_for_model m i
        (max_id idx symbol symbol_map idx_map idx_trie
           analysis_result) (fun _ _ => True).
  Proof.
    open_ssm; destruct e; break; try eexists; intros; cbn; eauto.
  Qed.
  
  Lemma worklist_empty_sound i
    : state_sound_for_model m i
        (worklist_empty idx symbol symbol_map idx_map idx_trie
           analysis_result) (fun _ _ => True).
  Proof.
    open_ssm; destruct e; break; try eexists; intros; cbn; eauto.
  Qed.

  
  Lemma run1_iter_sound i rs rb_fuel
    : all (rule_sound_for_evaluation i (query_clauses rs)) rs.(compiled_rules) ->
      state_sound_for_model m i
        (Defs.run1iter idx Eqb_idx idx_succ idx_zero symbol
           symbol_map symbol_map_plus idx_map idx_map_plus idx_trie
           analysis_result spaced_list_intersect rb_fuel rs) 
        (fun _ _ => True).
  Proof.
    unfold Defs.run1iter.
    intros.
    ssm_bind.
    { apply build_tries_sound. }
    {
      ssm_bind.
      1: apply max_id_sound.
      ssm_bind.
      1: apply increment_epoch_sound.
      ssm_bind.
      {        
        apply state_sound_for_model_Miter with (P:= fun _ _ => True);
          intros; eauto.
        eapply process_erule_sound; eauto.
        { repeat (eapply tries_sound_for_model_monotone; try eassumption). }
        {
          eapply in_all in H1; eauto.
          repeat (eapply monotone_rule_sound_for_evaluation; try eassumption).
        }
      }
      ssm_bind.
      1: apply max_id_sound.
      ssm_bind.
      1: apply worklist_empty_sound.
      ssm_bind.
      1:eapply rebuild_sound.
      eapply ret_sound_for_model'; auto.
    }
  Qed.
    
  Lemma saturate_until'_sound i rb_fuel rs cond fuel P
    : all (rule_sound_for_evaluation i (query_clauses rs)) rs.(compiled_rules) ->
      (forall i', map.extends i' i ->
                  state_sound_for_model m i' cond (fun i2 (b:bool) => if b then P i2 else True)) ->
      monotone P ->
      forall i', map.extends i' i ->
      state_sound_for_model m i' (saturate_until' rb_fuel rs cond fuel)
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
      ssm_bind.
      {
        apply run1_iter_sound.
        eapply all_wkn; try eassumption.
        intros.
        repeat (eapply monotone_rule_sound_for_evaluation; try eassumption).
      }
      case_match.
      { eapply ret_sound_for_model'; auto. }        
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
      *)
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
  idx_succ%function_scope
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


