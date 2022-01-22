(* A relational database implementation with conjunctive queries,
   for use in e-matching.
   TODO: profile, optimize performance.
   Use PArrays instead of lists in various spots 
   (can be fixed size, so don't need ArrayList, but that might be easiest first)
 *)
Require Import Equalities Orders ZArith List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.
From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps NatlikePos.
From Utils Require TrieMap.
Import Sets.


(*TODO: move to utils*)
Lemma invert_Forall2_nil_nil {A B} (f : A -> B -> Prop)
  : Forall2 f [] [] <-> True.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_nil_nil : utils.

Lemma invert_Forall2_nil_cons {A B} (f : A -> B -> Prop) e x
  : Forall2 f [] (e :: x) <-> False.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_nil_cons : utils.

Lemma invert_Forall2_cons_nil {A B} (f : A -> B -> Prop) e x
  : Forall2 f (e :: x) [] <-> False.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_cons_nil : utils.

Lemma invert_Forall2_cons_cons {A B} (f : A -> B -> Prop) e x e' x'
  : Forall2 f (e :: x) (e'::x')
    <-> (f e e') /\ Forall2 f x x'.
Proof using.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite @invert_Forall2_cons_cons : utils.

Section SetWithTop.
  Context {A : Type}
          {A_set : set A}.
  (* Includes top element, isomorphic to option *)
  Variant set_with_top := finite_set (m : A_set) | all_elements.

  Definition set_with_top_intersection p1 p2 :=
    match p1, p2 with
    | finite_set s1, finite_set s2 => finite_set (intersection s1 s2)
    | finite_set s1, all_elements => finite_set s1
    | all_elements, finite_set s2 => finite_set s2
    | all_elements, all_elements => all_elements
    end.
End SetWithTop.

Arguments set_with_top {A}%type_scope A_set.


(* We need to expose the map implelementation or query_trie is not strictly positive.
   We cordon it off into its own module so that the rest can be parametric over idx and elt.
 *)
Module PositiveQueryTrie.
  
  Open Scope positive.
  Inductive query_trie :=
  (*Necessary for when a variable does not appear in a clause *)
  | qt_unconstrained : query_trie -> query_trie
  (* need to expose map impl or inductive is not strictly positive *)
  | qt_tree : TrieMap.map query_trie -> query_trie
  (* used when there are no more variables left *)
  | qt_nil : query_trie.

  (* used when there are no possible instantiations *)
  Notation qt_empty := (qt_tree (PTree.Empty)).

  #[export] Instance trie_set : set positive :=
    {
      set_as_map := TrieMap.map _;
      intersection := PTree.combine (fun a b => if a then b else None);
      union := PTree.combine (fun a b => if a then Some tt else b);
    }.

  Definition values_of_next_var (t : query_trie) : set_with_top trie_set :=
    match t with
    | qt_tree m => finite_set (PTree.map_filter (fun _ => Some tt) m)
    | qt_unconstrained _ => all_elements
    (* shouldn't normally hit this case *)
    | qt_nil => finite_set map.empty
    end.

  Definition choose_next_val (v:positive) (t : query_trie) : query_trie :=
    match t with
    | qt_tree m => 
        match map.get m v with Some t => t | None => qt_empty end
    | qt_unconstrained t => t 
    (* shouldn't normally hit this case *)
    | qt_nil => qt_nil
    end.

  
End PositiveQueryTrie.


(* Make all functions parametric over the indices and elements *)
Section __.
  (*Idx type used for relation ids and variables *)
  Context (idx : Type) {natlike_idx : Natlike idx}.
  (* elt is the type of elements of a relation *)
  Context (elt : Type) {elt_eqb : Eqb elt}
          {elt_default : WithDefault elt (*not necessary, just convenient*)}.

  Context (elt_set : set elt).

  (*Parameterize by query trie since the inductive can't be defined generically *)
  Context (query_trie : Type)
          (qt_unconstrained : query_trie -> query_trie)
          (trie_map : map.map elt query_trie)
          (trie_map_ok : map.ok trie_map)
          (qt_tree : trie_map -> query_trie)
          (qt_nil : query_trie)
          (values_of_next_var : query_trie -> set_with_top elt_set)
          (choose_next_val : elt -> query_trie -> query_trie).

  Notation qt_empty := (qt_tree map.empty).

  Context (relation : set (list elt))
          (db : map.map idx relation)
          (arg_map : map.map idx elt).


  (* We establish a type for conjunctive queries *)

  (*TODO: use primitive pair?*)
  Definition atom : Type := idx (*Relation id*) * list idx.
  Record query :=
    {
      free_vars : list idx;
      (*TODO: list or set?*)
      clauses : list atom;
    }.


  (* TODO: figure out whether this can have duplicates
     {subst_set : set arg_map}.
   *)
  Definition subst_set := list arg_map.

  Fixpoint generic_join' (tries : @named_list idx query_trie)
           (vars : list idx) (acc : arg_map) : subst_set :=
    match vars with
    | [] => [acc]
    | (x::vars') =>
        let Rxs :=
          map (fun '(_,v) => values_of_next_var v) tries in
        let Dx := fold_left set_with_top_intersection Rxs all_elements in
        (*
        If Dx is all_positives, then the variable is unconstrained.
        We will probably only guarentee the behavior of generic_join
        when all free variables appear, so the result in this case doesn't matter
         *)
        match Dx with
        | finite_set Dx =>
            map.fold
              (fun l v _ =>
                 (generic_join' (named_map (choose_next_val v) tries) vars'
                                (map.put acc x v))
                   ++l)
              []
              Dx
        | all_positives => []
        end
    end.


  (* we need constants for residual queries in generic_join *)
  Variant argument := const_arg (c : elt) | var_arg (x : idx).

  Fixpoint match_args args tuple : option arg_map :=
    match args, tuple with
    | [], _ => Some map.empty
    | _,[] => Some map.empty
    | (var_arg x)::args, e::tuple =>
        @! let m <- match_args args tuple in
           match map.get m x with
           | Some e' => if eqb e e' then Some m else None
           | None => Some (map.put m x e)
           end
    | (const_arg c)::args, e::tuple =>
        if eqb c e then match_args args tuple else None
    end.

  Definition match_args_and_lookup args tuple (x : idx) : option elt :=
    @! let m <- match_args args tuple in
       let e <- map.get m x in
       ret e.

  Definition find_values_in_relation' (x : idx) (rel : relation) args
    : elt_set :=
    map.fold (fun acc tuple _ =>
                match match_args_and_lookup args tuple x with
                | Some e => add_elt acc e
                | None => acc
                end) map.empty rel.

  #[refine]
   Instance eqb_argument : Eqb argument :=
    {
      eqb a b :=
      match a,b with
      | var_arg ax, var_arg bx => eqb ax bx
      | const_arg ac, const_arg bc => eqb ac bc
      | _,_ => false
      end;
    }.
  all: eapply TODO.
  Defined.

  (*handle unconstrained variables*)
  Definition find_values_in_relation (x : idx) (rel : relation) args :=
    if existsb (eqb (var_arg x)) args
    then Some (find_values_in_relation' x rel args)
    else None.

  Definition arg_subst v x a :=
    match a with
    | const_arg c => const_arg c
    | var_arg x' =>
        if eqb x x' then const_arg v else var_arg x'
    end.


  Definition match_one_const a e :=
    match a with const_arg e' => eqb e e' | _ => false end.

  Definition args_in_rel  (rel: relation) (args : list argument) :=
    map.fold (fun acc tuple _ => acc || (all2 match_one_const args tuple))%bool false rel.
  
  (*TODO: filter rel on recursive calls?*)
  (* TODO: if a variable is unconstrained, need to handle it specially *)
  Fixpoint build_trie' (rel: relation) (vars : list idx) (args : list argument)
    : query_trie :=
    match vars with
    | [] => if args_in_rel rel args then qt_nil else qt_empty
    | x::vars' =>
        let vs := find_values_in_relation x rel args in
        match vs with
        | Some vs =>
            qt_tree (map.fold
                       (fun m v _ =>
                          map.put m v (build_trie' rel vars' (map (arg_subst v x) args)))
                       map.empty
                       vs)
        | None  =>
            qt_unconstrained (build_trie' rel vars' args)
        end
    end.

  Definition build_trie (d:db) (vars : list idx) (clause : atom) : idx * query_trie :=
    let rel_id := fst clause in
    match map.get d rel_id with
    | Some rel => (rel_id,build_trie' rel vars (map var_arg (snd clause)))
    | None => (rel_id, qt_empty)
    end.

  Definition build_tries (d:db) (vars : list idx) (clauses : list atom)
    : @named_list idx query_trie :=
    map (build_trie d vars) clauses.

  Definition generic_join (d : db) (q : query) : subst_set :=
    let tries := build_tries d q.(free_vars) q.(clauses) in
    generic_join' tries q.(free_vars) map.empty.

  (*Properties*)

  (*TODO: mention fvs? *)
  Definition satisfies_query d q (m : arg_map) :=
    forall i args,
      In (i,args) q.(clauses) ->
      exists R,
        map.get d i = Some R
        /\
        exists tuple,
          List.Forall2 (fun a e => map.get m a = Some e) args tuple
          /\
          member R tuple = true.

  
  Definition const_args_in_rel args (R : relation) :=
    exists tuple,
      map const_arg tuple = args
      /\ member R tuple = true.

  
  (* TODO: try using this? *)
  Inductive denote_query_trie : list idx -> query_trie -> arg_map -> Prop :=
  | denote_qt_nil : denote_query_trie [] qt_nil map.empty
  (* TODO: this does complicate things since it requires cross-trie reasoning
     To show that some trie fixes the value
   *)
  | denote_qt_unconstrained vars t m x v
    : denote_query_trie vars t m ->
      denote_query_trie (x::vars) (qt_unconstrained t) (map.put m x v)
  | denote_qt_cons vars t m x tm v
    : map.get tm v = Some t ->
      denote_query_trie vars t m ->
      denote_query_trie (x::vars) (qt_tree tm) (map.put m x v).
  (*TODO: new hintdb?*)
  Hint Constructors denote_query_trie : utils.

  (* TODO: still use anywhere?
  Inductive sound_trie_for_relation
            (R : relation) (args : _)
    : _ -> list idx -> Prop :=
  | sound_trie_qt_nil :
    const_args_in_rel args R ->
    sound_trie_for_relation R args qt_nil []
  | sound_trie_qt_empty :
    sound_trie_for_relation R args qt_empty []
  | sound_trie_qt_tree m x vars
    : (forall v t, map.get m v = Some t ->
                   sound_trie_for_relation R (map (arg_subst v x) args) t vars) ->
      sound_trie_for_relation R args (qt_tree m) (x::vars)
  | sound_trie_qt_unconstrained t x vars
    : (forall v, sound_trie_for_relation R (map (arg_subst v x) args) t vars) ->
      sound_trie_for_relation R args (qt_unconstrained t) (x::vars).

  (*TODO: new hintdb?*)
  Hint Constructors sound_trie_for_relation : utils. 

  
  Definition trie_sound_for_atom (d : db) vars '(i,t) '(i',args) :=
    i = i' /\
      exists R,
        map.get d i = Some R /\
        (sound_trie_for_relation R (map var_arg args) t vars).
*)

  Definition arg_from_vars vars a :=
    match a with
    | const_arg _ => True
    | var_arg x => In x vars
    end.

  Lemma all_args_from_empty_is_const args
    : all (arg_from_vars []) args ->
      exists tuple, map const_arg tuple = args.
  Proof.
    induction args; 
      basic_goal_prep; basic_utils_crush.
    - exists []; basic_utils_crush.
    - destruct a;
        basic_utils_crush.
      exists (c::x);
        basic_utils_crush.
  Qed.

  Definition one_arg_can_match a c :=
    match a with
    | var_arg _ => True
    | const_arg c' => c = c'
    end.

  Definition args_can_match R args :=
    exists tuple,
      member R tuple = true
      /\ Forall2 one_arg_can_match args tuple.

  (*
  Lemma args_match_const_eq tuple tuple'
    : Forall2 one_arg_can_match (map const_arg tuple') tuple ->
      tuple' = tuple.
  Proof.
    revert tuple;
      induction tuple';
      destruct tuple;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
*)

  (*TODO: move somewhere*)
  Hint Rewrite @map.get_empty : utils.

  Context (arg_map_ok : map.ok arg_map).

  
  Lemma match_args_sound' args tuple m
    : List.length args = List.length tuple ->
      Some m = match_args args tuple ->
      forall m',
        (forall x c, map.get m x = Some c -> map.get m' x = Some c) ->
      Forall2 (fun a c =>
                 match a with
                 | const_arg c' => c = c'
                 | var_arg x => map.get m' x = Some c
                 end)
              args
              tuple.
  Proof.
    revert m.
    revert tuple; induction args;
      destruct tuple;
      basic_goal_prep;
      autorewrite with utils in*;
      subst;
      auto 1.
    destruct a;
      basic_goal_prep.
    {
      revert H0; 
        case_match; [|congruence].
      basic_utils_crush.
    }
    {
      revert H0; 
        case_match; [|congruence].
      case_match.
      {
        case_match; [|congruence].
        basic_goal_prep;
          basic_utils_crush.
      }
      {
        basic_goal_prep;
          basic_utils_crush.
        - apply H1.
          apply map.get_put_same.
        - eapply IHargs; eauto.
          intros; apply H1.
          admit (*TODO: map solver*).
      }
    }
  Admitted.

  
  Lemma match_args_sound args tuple m
    : List.length args = List.length tuple ->
      Some m = match_args args tuple ->
      Forall2 (fun a c =>
                 match a with
                 | const_arg c' => c = c'
                 | var_arg x => map.get m x = Some c
                 end)
              args
              tuple.
  Proof.
    intros; eapply match_args_sound'; eauto.
  Qed.
      
  
  Lemma match_args_and_lookup_sound args k i e
    : List.length args = List.length k ->
      Some e = match_args_and_lookup args k i ->
      Forall2 one_arg_can_match (map (arg_subst e i) args) k.
  Proof.
    unfold match_args_and_lookup.
    simpl.
    case_match; [|congruence].
    case_match; [|congruence].
    intros Hlen H'; inversion H'; clear H'; subst.
    pose proof (match_args_sound _ _ _ Hlen HeqH) as H.
    revert H.
    clear Hlen HeqH.
    revert dependent r.
    revert dependent k.
    revert args.
    induction args;
      destruct k;
      basic_goal_prep;
      try destruct a;
      basic_goal_prep;
      basic_utils_crush.
    {
      case_match;
      basic_goal_prep;
        basic_utils_crush.
      congruence.
    }
  Qed.

  (*TODO: move to the right place*)
  Definition set_incl S S' := forall x, member S x = true -> member S' x = true.
  Lemma set_put_monotone m k
    : set_incl m (map.put m k tt).
  Proof.
    intro.
    unfold member in *.
    case_match; try congruence.
    intros _.
    (*TODO: implement/import list eqb*)
    assert (Eqb (list elt)) by admit.
    my_case Heq (eqb x k).
    {
      basic_goal_prep;
        basic_utils_crush.
      now erewrite map.get_put_same.
    }
    {
      basic_goal_prep;
        basic_utils_crush.
      erewrite map.get_put_diff; auto.
      now rewrite <- HeqH.      
    }
  Admitted.

  (*TODO: move to sets*)
  Lemma member_empty {A} {m : set A} {_ :map.ok m} (e : A)
    : member (map.empty (map:=m)) e = false.
  Proof.
    unfold member.
    erewrite map.get_empty.
    reflexivity.    
  Qed.
  Hint Rewrite @member_empty : utils.
  
  Lemma member_add_elt {A} `{Eqb A} {S : set A} {_ :map.ok S} (s : S) (e e' : A)
    : member (add_elt s e) e' = ((eqb e e') || (member s e'))%bool.
  Proof.
    unfold member.
    unfold add_elt.
    my_case Heqb (eqb e e');
      basic_goal_prep;
        basic_utils_crush.
    { rewrite map.get_put_same; reflexivity. }
    { rewrite map.get_put_diff; auto. }
  Qed.
  Hint Rewrite @member_add_elt : utils.

  (*TODO: do I want this in utils?*)
  Hint Rewrite Bool.orb_true_iff : utils.

  (*TODO: move up?*)
  Context {elt_set_ok : map.ok elt_set}.
  
  Lemma find_values_in_relation_some_sound i R args elts
    : find_values_in_relation i R args = Some elts ->
      forall e, member elts e = true ->
                forall R', set_incl R R' ->
                args_can_match R' (map (arg_subst e i) args).
  Proof.
    unfold find_values_in_relation.
    case_match; try congruence.
    intros fv; inversion fv; clear fv.
    clear HeqH elts H0.
    intros e.
    unfold find_values_in_relation'.
    eapply map.fold_spec.
    { basic_utils_crush. }
    intros.
    revert H1.     
    case_match.
    {
      my_case Heqe (eqb e e0);
        basic_goal_prep;
        autorewrite with utils in *; subst.
      {
        clear H0 H1.
        eapply match_args_and_lookup_sound in HeqH1.
        {
          exists k;
            basic_goal_prep;
            basic_utils_crush.
          apply H2.
          unfold member; now erewrite map.get_put_same.
        }
        admit (*TODO: relation arity*).
      }
      {
        erewrite member_add_elt in H1.
        autorewrite with utils in *.
        destruct H1.
        1:now basic_utils_crush.
        apply H0; auto.
        intros x mem.
        eapply H2.
        now eapply set_put_monotone.
      }
    }
    {
      intros; eapply H0; eauto.
      intros x mem.
      eapply H2.
      destruct v.
      now eapply set_put_monotone.
    }
  Admitted.

  (*TODO: what is the right property here?
  Lemma find_values_in_relation_none_sound i R args
    : find_values_in_relation i R args = None ->
      forall e, args_can_match R (map (arg_subst e i) args).
  Proof.
    unfold find_values_in_relation.
    case_match; try congruence.
    intros _.
    intros.
    assert (map (arg_subst e i) args = args) as Hargs_eq.
    {
      revert HeqH; induction args;
        basic_goal_prep; try destruct a; basic_utils_crush.
      {
        symmetry in HeqH.
        rewrite Bool.orb_false_iff in HeqH.
        basic_goal_prep; basic_utils_crush.
        case_match;
          basic_goal_prep; basic_utils_crush.
      }
      {
        symmetry in HeqH.
        rewrite Bool.orb_false_iff in HeqH.
        basic_goal_prep; basic_utils_crush.
      }
    }
    rewrite Hargs_eq.
    assumption.
  Qed.*)

  
  Lemma arg_from_vars_subst x a v vars
    : arg_from_vars (x :: vars) a ->
      arg_from_vars vars (arg_subst v x a).
  Proof.
    unfold arg_from_vars.
    destruct a; 
      basic_goal_prep; basic_utils_crush.
    case_match;
      basic_goal_prep; basic_utils_crush.
    revert HeqH.
    case_match;
      basic_goal_prep; basic_utils_crush.
    all:inversion HeqH0; subst; auto.
  Qed.
  Hint Resolve arg_from_vars_subst : utils.
  
  Lemma all_arg_from_vars_subst x args v vars
    : all (arg_from_vars (x :: vars)) args ->
      all (arg_from_vars vars) (map (arg_subst v x) args).
  Proof.
    induction args;
      basic_goal_prep; try now basic_utils_crush.
    destruct H.
    split; auto.
    apply arg_from_vars_subst; assumption.
  Qed.      

  (*TODO: move somewhere*)
  Hint Rewrite map.get_empty : utils.

  
  Lemma args_in_rel_sound R args
    : args_in_rel R args = true ->
      const_args_in_rel args R.
  Proof.
    unfold args_in_rel, const_args_in_rel.
    eapply map.fold_spec; try congruence.
    intros k v m r gmk IH.
    destruct r; simpl.
    {
      intros _; specialize (IH eq_refl);
        destruct IH as [tuple [? ?]].
      subst;
        eexists; split; eauto.
      destruct v;
        now eapply set_put_monotone.
    }
    {
      clear IH.
      intros; exists k.
      split; cycle 1.
      {
        destruct v;
          change ((map.put m k tt)) with (add_elt m k);
          erewrite member_add_elt;basic_utils_crush.
      }
      {
        revert H; clear.
        revert k;
          induction args;
          destruct k;
          basic_goal_prep; unfold  match_one_const in *;
          try destruct a; basic_utils_crush.
      }
    }
  Admitted.

  Definition maps_arg_to (m : arg_map) a e :=
    match a with
    | const_arg e' => e = e'
    | var_arg x => map.get m x = Some e
    end.

  Definition arg_map_sound_for_relation (R : relation) args (m : arg_map) :=
    exists tuple,
      Forall2 (maps_arg_to m) args tuple
      /\ member R tuple = true.

  Definition trie_sound_for_relation (R : relation) vars args t :=
    forall m, denote_query_trie vars t m ->
              arg_map_sound_for_relation R args m.
    
  Lemma const_args_map x0 args m
    : map const_arg x0 = args -> Forall2 (maps_arg_to m) args x0.
  Proof.
    revert x0; induction args; destruct x0;
      basic_goal_prep; unfold  maps_arg_to; basic_utils_crush.
  Qed.
  Local Hint Resolve const_args_map : core.

  (*TODO: prove above*)
  Context (invert_qt_nil_tree : forall m, qt_nil = qt_tree m <-> False).
  Hint Rewrite invert_qt_nil_tree : utils.
  Context (invert_qt_unconstrained_tree : forall t m, qt_unconstrained t = qt_tree m <-> False).
  Hint Rewrite invert_qt_unconstrained_tree : utils.
  Context (invert_qt_tree_unconstrained : forall t m, qt_tree m = qt_unconstrained t <-> False).
  Hint Rewrite invert_qt_tree_unconstrained : utils.
  
  Context (invert_qt_tree_tree : forall m m', qt_tree m = qt_tree m' <-> m = m').
  Hint Rewrite invert_qt_tree_tree : utils.
  Context (invert_qt_unconstrained_unconstrained
            : forall t t', qt_unconstrained t = qt_unconstrained t' <-> t = t').
  Hint Rewrite invert_qt_unconstrained_unconstrained : utils.

  Lemma empty_trie_sound R vars args
    : trie_sound_for_relation R vars args qt_empty.
  Proof.
    unfold trie_sound_for_relation.
    intros m dqt.
    inversion dqt;
      autorewrite with utils in *;
      try tauto.
    subst.
    rewrite map.get_empty in H0.
    congruence.
  Qed.
  Local Hint Resolve empty_trie_sound : utils.

  
  Lemma arg_map_sound_subst R v x args m
    : arg_map_sound_for_relation R (map (arg_subst v x) args) m ->
      arg_map_sound_for_relation R args (map.put m x v).
  Proof.
    unfold arg_map_sound_for_relation.
    intro H'; destruct H' as [tuple [? ?]].
    exists tuple.
    split; auto.
    revert H.
    clear H0.
    unfold maps_arg_to.
    revert tuple; induction args;
      destruct tuple;
      basic_goal_prep;
      try destruct a;
      basic_utils_crush.
    clear IHargs H1.
    revert H0.
    unfold arg_subst.
    my_case Heqb (eqb x x0);
      basic_utils_crush.
    - now rewrite map.get_put_same.
    - rewrite map.get_put_diff; eauto.
  Qed.
  
  Lemma tree_trie_sound R vars args x m
    : (forall v t, map.get m v = Some t ->
                   trie_sound_for_relation R vars (map (arg_subst v x) args) t) ->
    trie_sound_for_relation R (x::vars) args
                              (qt_tree m).
  Proof.
    unfold trie_sound_for_relation.
    intros H m' dqt.
    inversion dqt;
      autorewrite with utils in *;
      try tauto; subst.
    apply  arg_map_sound_subst.
    eapply H; eauto.
  Qed.
  Local Hint Resolve tree_trie_sound : utils.

  Lemma unconstrained_trie_sound R vars args t a
    : ~ In a vars ->
      all (arg_from_vars vars) args ->
      trie_sound_for_relation R vars args t ->
      trie_sound_for_relation R (a :: vars) args (qt_unconstrained t).
  Proof.
    unfold trie_sound_for_relation.
    intros Hdup Hargs IH m' dqt.
    inversion dqt; clear dqt;
      autorewrite with utils in *;
      try tauto; subst.
    specialize (IH _ H3).
    destruct IH as [tuple [? ?]].
    exists tuple; split; auto.
    revert H.
    clear H0.
    revert tuple; induction args;
      destruct tuple;
      basic_goal_prep;
      basic_utils_crush.
    unfold maps_arg_to.
    destruct a0; auto; intros.
    
    assert (a <> x).
    {
      intro; subst.
      apply Hdup.
      apply H0.
    }
    rewrite map.get_put_diff; auto.
  Qed.
  Local Hint Resolve unconstrained_trie_sound : utils.

  (*TODO: move to Utils.v*)
  Lemma invert_NoDup_cons {A} x (a:A)
    : NoDup (a::x) <-> ~ In a x /\ NoDup x.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite @invert_NoDup_cons : utils.
  
  Lemma build_trie'_sound R args vars
    : NoDup vars ->
      all (arg_from_vars vars) args ->
      trie_sound_for_relation R vars args (build_trie' R vars args).
  Proof.
    revert args; induction vars;
      basic_goal_prep.
    {
      eapply all_args_from_empty_is_const in H0;
        destruct H0.
      case_match.
      {
        symmetry in HeqH1.
        apply args_in_rel_sound in HeqH1.
        unfold trie_sound_for_relation.
        intros m dqt.
        unfold const_args_in_rel in *.
        unfold arg_map_sound_for_relation.
        destruct HeqH1 as [? [? ?]].
        exists x0; split; auto.
      }
      {
        eapply empty_trie_sound.
      }
    }
    case_match.
    {
      eapply tree_trie_sound.
      intros.
      enough (t=(build_trie' R vars (map (arg_subst v a) args)));[subst|].
      {
        autorewrite with utils in H; destruct H.
        eapply IHvars; eauto.
        eapply all_arg_from_vars_subst.
        auto.
      }
      {     
        revert H1.
        clear.
        set map.empty.
        assert (map.get r0 v = None).
        {
          unfold r0.
          erewrite map.get_empty; auto.
        }
        revert H.
        eapply map.fold_spec.
        { basic_goal_prep; congruence. }
        {
          basic_goal_prep.
          intuition subst.
          my_case Heqk (eqb k v).
          { rewrite eqb_eq in Heqk; subst.
            erewrite map.get_put_same in H2.
            congruence.
          }
          {
            rewrite eqb_neq in Heqk.
            apply not_eq_sym in Heqk.
            erewrite map.get_put_diff in H2;
              tauto.
          }
        }
      }
    }
    {
      eapply unconstrained_trie_sound;
        autorewrite with utils in *; try now intuition.
      {
        admit (*TODO: strengthen since a notin args*).
      }
      eapply IHvars; eauto; try now intuition.
      {
        admit (*TODO: strengthen since a notin args*).
      }
  Admitted.

  (*TODO: move to utils*)
  Lemma all_map {A B} P (f : A -> B) l
    : all P (map f l) = all (fun x => P (f x)) l.
  Proof.
    induction l;
      basic_goal_prep; basic_utils_crush.
  Qed.
      
  
  Definition trie_sound_for_atom (d : db) vars '(i,t) '(i',args) :=
    i = i' /\
      let R := unwrap_with_default map.empty (map.get d i) in
      trie_sound_for_relation R vars (map var_arg args) t.
  
  Lemma build_trie_sound d vars a
    : NoDup vars ->
      all (fun x => In x vars) (snd a) ->
      trie_sound_for_atom d vars (build_trie d vars a) a.
  Proof.
    unfold build_trie, atom in *.
    basic_goal_prep.
    case_match;
      unfold trie_sound_for_atom;
      split; auto;
      unfold unwrap_with_default;
      rewrite <- HeqH1.
    {
      apply build_trie'_sound; auto.
      rewrite all_map.
      assumption.
    }
    {
      unfold unwrap_with_default.
      apply empty_trie_sound.
    }
  Qed.
  Local Hint Resolve build_trie_sound : utils.

  
  Lemma build_tries_sound d vars clauses
    : NoDup vars ->
      all (fun a => all (fun x => In x vars) (snd a)) clauses ->
      Forall2 (trie_sound_for_atom d vars) (build_tries d vars clauses) clauses.
  Proof.
    induction clauses;
      basic_goal_prep;
      try now basic_utils_crush.
    destruct H0.
    constructor; eauto with utils.
  Qed.
      

  Definition well_scoped_query q :=
    NoDup q.(free_vars) /\
    all (fun a => all (fun x => In x q.(free_vars)) (snd a)) q.(clauses).
                                     
  
  Theorem generic_join'_sound d m tries vars clauses am
    : Forall2 (trie_sound_for_atom d vars) tries clauses ->
      (*TODO: what do I need to know about am? *)
      In m (generic_join' tries vars am) ->
      (*TODO: use single q for query*)
      satisfies_query d (Build_query vars clauses) m.
  Proof.
    unfold satisfies_query.
    simpl.
    revert tries am clauses.
    induction vars;
      basic_goal_prep;
      basic_utils_crush.
    {
      revert dependent clauses0.
      revert tries.
      induction clauses0;
        destruct tries;
      basic_goal_prep;
        basic_utils_crush.
      {
        destruct H2 as [? [? [? ?]]]; subst.
        assert (x = x0) by congruence; subst.
        exists x0; split; auto.
        inversion H2; subst.
        {
          destruct H as [? [? ?]].
          exists x; split; auto.
          destruct x; destruct args; simpl in *;
            now basic_utils_crush.
        }
        {
          
        }
                                               
        exists 
        TODO: forall vs exists; predicates don't agree
    }
    simpl.
    generalize (clauses q), (free_vars q).
    clear q.
    intros.
    
    
  Theorem generic_join_sound d q m
    : well_scoped_query q ->
      In m (generic_join d q) ->
      satisfies_query d q m.
  Proof.
    unfold generic_join, well_scoped_query.
    intro Hwsq.
    match goal with
    | [|- context[build_tries ?d ?vars ?a]] =>
        pose proof (build_tries_sound d vars a Hwsq)
    end.
    clear Hwsq (*TODO: is this needed anymore?*).
    revert H.
    generalize (build_tries d (free_vars q) (clauses q)).
    unfold satisfies_query.
    generalize (clauses q), (free_vars q).
    clear q.
    intros.
    TODO: reason about generic_join'

      forall i t,

        
        In (i,t) (build_tries d fv cls) ->
        exists R,
          mag.get d i = Some R
          /\ (forall args, (i,args
            sound_trie_for_relation R (map ? t ?


        
      
    
    (*needs to reason about arguments*)
    Inductive sound_trie_for_atom (d : db) i
      : query_trie -> list idx -> list argument -> Prop :=
    | trie_for_atom_nil args : trie_for_atom d t i qt_nil [] args
    | trie_for_atom_unconstrained 
      : trie_for_atom d t i TODO
    | trie_for_atom_tree m
      : (forall e t', map.get m e = Some t' ->
                      
      trie_for_atom d t i qt_nil [] args
    | 
                                             
      
      
      
    
    Lemma build_tries_sound
      : forall i t,
        In (i,t) (build_tries d fv cls) ->
        
        
    
    TODO: build_trie lemma

                     

End __.

Module PositiveInstantiation.
  
Fixpoint list_compare l1 l2 :=
  match l1, l2 with
  | [],[] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | x1::l1, x2::l2 =>
      match BinPosDef.Pos.compare x1 x2 with
      | Eq => list_compare l1 l2
      | c => c
      end
  end.

Axiom TODO: forall {A},A.

Definition list_ltb l1 l2 :=
  match list_compare l1 l2 with
  | Lt => true
  | _ => false
  end.

(* Make this an instance so we can use single-curly-braces so we don't need to qualify field-names with [SortedList.parameters.] *)
Local Instance list_strict_order: @SortedList.parameters.strict_order _ list_ltb
  := { ltb_antirefl := TODO
     ; ltb_trans := TODO
     ; ltb_total := TODO }.


Definition relation_map : map.map (list positive) unit :=
  SortedList.map (SortedList.parameters.Build_parameters (list positive) unit list_ltb)
                 list_strict_order.


Definition relation : set (list positive) := set_from_map relation_map.


Definition db : map.map positive relation := TrieMap.map _.

Definition arg_map : map.map positive positive := TrieMap.map _.

Export PositiveQueryTrie.

Definition generic_join (d : db) (q : query _) : subst_set _ _ arg_map :=
  generic_join positive positive
               trie_set query_trie qt_unconstrained _ qt_tree
               values_of_next_var choose_next_val relation db arg_map d q.

#[global] Notation atom := (atom positive).
#[global] Notation query := (query positive).
#[global] Notation Build_query := (Build_query positive).

End PositiveInstantiation.

  
Module Examples.
  Open Scope positive.
  Import PositiveInstantiation.

  Definition r1 : relation :=
    Sets.add_elt
      (Sets.add_elt
         map.empty
         [10; 20; 20])
      [6; 4; 5].


  
  Definition r2 : relation :=
    Sets.add_elt
      (Sets.add_elt
         (Sets.add_elt
            map.empty
            [4; 56])
         [4; 52])
      [7; 65].

  
  Definition r3 : relation :=
    Sets.add_elt
      (Sets.add_elt
         map.empty
         [10; 20; 30])
      [4; 4; 5].
  
  Definition db_ex : db :=
    Eval compute in (map.put
                       (map.put
                          (map.put
                             map.empty
                             1 r1)
                          2 r2)
                       3 r3).

  Definition q1 : query :=
    Build_query [1;2;3]
                [(1,[1;2;3]);(3,[2;2;3])].
  
End Examples.
