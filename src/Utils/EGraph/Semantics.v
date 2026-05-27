(* TODO: separate semantics and theorems
 *)
From Stdlib Require Import Equalities Orders Lists.List.
Import ListNotations.
From Stdlib Require Import Logic.PropExtensionality
  Logic.FunctionalExtensionality.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.

From Utils Require Import Utils Monad ExtraMaps Relations Maps UnionFind VC.
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
  
  Lemma insert_nth_at n val acc acc'
    : @insert idx Eqb_idx acc n val = Some acc'
      -> nth_error acc' n = Some (Some val).
  Proof.
    revert val acc acc'.
    induction n; intros val acc acc' H.
    - destruct acc; cbn [insert nth_error] in *.
      + injection H; intro; subst; reflexivity.
      + destruct o; [ | injection H; intro; subst; reflexivity].
        destruct (eqb val i) eqn:Heqb; [ | discriminate].
        pose proof (Eqb_idx_ok val i) as Hbs.
        rewrite Heqb in Hbs.
        injection H; intro; subst; congruence.
    - destruct acc; cbn [insert nth_error] in *.
      + destruct (insert idx Eqb_idx [] n val) eqn:Hi.
        * cbn [option_map] in H. injection H; intro; subst.
          apply IHn in Hi. exact Hi.
        * cbn [option_map] in H. discriminate.
      + destruct (insert idx Eqb_idx acc n val) eqn:Hi.
        * cbn [option_map] in H. injection H; intro; subst.
          apply IHn in Hi. exact Hi.
        * cbn [option_map] in H. discriminate.
  Qed.

  Lemma insert_preserves_some n x acc m y acc'
    : nth_error acc n = Some (Some x) ->
      @insert idx Eqb_idx acc m y = Some acc' ->
      nth_error acc' n = Some (Some x).
  Proof.
    revert n acc acc'.
    induction m; intros n acc acc' Hn Hi.
    - destruct acc; cbn [insert] in Hi.
      + destruct n; cbn [nth_error] in Hn; discriminate.
      + destruct o.
        * destruct (eqb y i) eqn:Heqb; [ | discriminate].
          injection Hi; intro; subst. exact Hn.
        * injection Hi; intro; subst.
          destruct n; cbn [nth_error] in Hn.
          -- discriminate.
          -- exact Hn.
    - destruct acc; cbn [insert] in Hi.
      + destruct n; cbn [nth_error] in Hn; discriminate.
      + destruct (insert idx Eqb_idx acc m y) eqn:Hin.
        * cbn [option_map] in Hi. injection Hi; intro; subst.
          destruct n; cbn [nth_error] in *.
          -- exact Hn.
          -- apply (IHm n acc l Hn Hin).
        * cbn [option_map] in Hi. discriminate.
  Qed.

  Lemma match_clause'_preserves_some cargs cv args v acc pa n x
    : match_clause' cargs cv args v acc = Some pa ->
      nth_error acc n = Some (Some x) ->
      nth_error pa n = Some (Some x).
  Proof.
    revert args acc pa.
    induction cargs; intros args acc pa Hmc Hn.
    - destruct args; cbn [match_clause'] in Hmc.
      + apply (insert_preserves_some n x acc cv v pa Hn Hmc).
      + discriminate.
    - destruct args as [ | w args']; cbn [match_clause'] in Hmc.
      + discriminate.
      + destruct (insert idx Eqb_idx acc a w) eqn:Hins; [ | discriminate].
        apply (IHcargs args' l pa Hmc).
        apply (insert_preserves_some n x acc a w l Hn Hins).
  Qed.

  Lemma match_clause'_same_length cargs cv args v acc pa
    : match_clause' cargs cv args v acc = Some pa ->
      length cargs = length args.
  Proof.
    revert args acc pa.
    induction cargs; intros args acc pa Hmc.
    - destruct args; cbn [match_clause'] in Hmc.
      + reflexivity.
      + discriminate.
    - destruct args as [ | w args']; cbn [match_clause'] in Hmc.
      + discriminate.
      + destruct (insert idx Eqb_idx acc a w) eqn:Hins; [ | discriminate].
        cbn [length]. f_equal. apply (IHcargs args' l pa Hmc).
  Qed.

  Lemma match_clause'_nth_error cargs cv args v acc pa
    : length cargs = length args ->
      match_clause' cargs cv args v acc = Some pa ->
      nth_error pa cv = Some (Some v) /\
      forall i n w, nth_error cargs i = Some n -> nth_error args i = Some w ->
                    nth_error pa n = Some (Some w).
  Proof.
    revert args acc pa.
    induction cargs; intros args acc pa Hlen Hmc.
    - destruct args; cbn [length] in Hlen; [ | Lia.lia].
      cbn [match_clause'] in Hmc.
      split.
      + apply insert_nth_at in Hmc. exact Hmc.
      + intros. destruct i; cbn [nth_error] in *; discriminate.
    - destruct args as [ | w args']; cbn [length] in Hlen; [ Lia.lia | ].
      injection Hlen; intro Hlen'.
      cbn [match_clause'] in Hmc.
      destruct (insert idx Eqb_idx acc a w) eqn:Hins; [ | discriminate].
      destruct (IHcargs args' l pa Hlen' Hmc) as [IH1 IH2].
      split.
      + exact IH1.
      + intros i n' wi Hn Hwi.
        destruct i; cbn [nth_error] in Hn, Hwi.
        * injection Hn; injection Hwi; intros; subst.
          apply match_clause'_preserves_some with (acc := l) (1 := Hmc).
          apply insert_nth_at in Hins. exact Hins.
        * exact (IH2 i n' wi Hn Hwi).
  Qed.

  Lemma nth_error_option_all_rev {A} (l1 : list (option A)) (l2 : list A) i x
    : option_all l1 = Some l2 ->
      nth_error l1 i = Some (Some x) ->
      nth_error l2 i = Some x.
  Proof.
    revert i. revert l2.
    induction l1; intros l2 i Hoa He.
    - destruct i; cbn [nth_error] in He; discriminate.
    - cbn [option_all] in Hoa.
      destruct a as [ a' | ]; [ | discriminate].
      destruct (option_all l1) as [ rest | ] eqn:Hoa'; [ | discriminate].
      injection Hoa; intro; subst.
      destruct i; cbn [nth_error] in *.
      + injection He; intro; subst. reflexivity.
      + exact (IHl1 rest i (eq_refl) He).
  Qed.

  Lemma named_list_lookup_combine_seq_nth_error
    {A : Type} (default : A) (start len : nat) (l : list A) (n : nat)
    : n < len ->
      length l = len ->
      named_list_lookup default (combine (seq start len) l) (start + n) =
      match nth_error l n with
      | Some v => v
      | None => default
      end.
  Proof.
    revert start n l.
    induction len; intros start n l Hlt Hlen.
    - Lia.lia.
    - destruct l as [ | a l']; cbn [length] in Hlen; [ Lia.lia | ].
      injection Hlen; intro Hlen'.
      destruct n as [ | n']; cbn [seq combine named_list_lookup nth_error].
      + rewrite PeanoNat.Nat.add_0_r.
        rewrite eqb_refl_true; [ | exact nat_eqb_ok]. reflexivity.
      + pose proof (nat_eqb_ok (start + S n') start) as Hbs.
        destruct (eqb (start + S n') start) eqn:Heqb.
        * Lia.lia.
        * replace (start + S n') with (S start + n') by Lia.lia.
          apply IHlen; [ Lia.lia | exact Hlen'].
  Qed.

  Lemma named_list_lookup_assign_sub default n assignment
    : n < length assignment ->
      named_list_lookup default (assign_sub assignment) n =
      match nth_error assignment n with
      | Some v => v
      | None => default
      end.
  Proof.
    unfold assign_sub. intro Hlt.
    rewrite <- (PeanoNat.Nat.add_0_l n).
    apply named_list_lookup_combine_seq_nth_error; [ exact Hlt | reflexivity].
  Qed.

  Lemma match_clause_correct default cargs cv args v assignment
    : let sub := assign_sub assignment in
      match_clause (cargs, cv) args v = Some assignment
      -> map (fun x => named_list_lookup default sub x) (cv::cargs)
         = v::args.
  Proof.
    cbn [match_clause]. unfold Mbind.
    destruct (match_clause' cargs cv args v []) as [ pa | ] eqn:Hmc; [ | discriminate].
    intro Hoa.
    pose proof (match_clause'_same_length cargs cv args v [] pa Hmc) as Hlen.
    pose proof (match_clause'_nth_error cargs cv args v [] pa Hlen Hmc) as [Hcv Hca].
    cbn [map]. f_equal.
    - pose proof (nth_error_option_all_rev _ _ _ _ Hoa Hcv) as Hcv2.
      pose proof (nth_error_Some_bound_index _ _ _ Hcv2) as Hlt.
      rewrite named_list_lookup_assign_sub; [ | exact Hlt].
      rewrite Hcv2. reflexivity.
    - apply nth_error_ext_samelength; [ rewrite length_map; exact Hlen | ].
      intros i Hi.
      rewrite nth_error_map.
      destruct (nth_error cargs i) as [ n | ] eqn:Hn.
      + cbn [option_map].
        destruct (nth_error args i) as [ w | ] eqn:Hw.
        * pose proof (Hca i n w Hn Hw) as Hpa.
          pose proof (nth_error_option_all_rev _ _ _ _ Hoa Hpa) as Hw2.
          pose proof (nth_error_Some_bound_index _ _ _ Hw2) as Hlt.
          rewrite named_list_lookup_assign_sub; [ | exact Hlt].
          rewrite Hw2. reflexivity.
        * exfalso.
          rewrite nth_error_None in Hw. rewrite <- Hlen in Hw.
          apply PeanoNat.Nat.le_ngt in Hw. apply Hw.
          rewrite length_map in Hi. exact Hi.
      + exfalso.
        rewrite nth_error_None in Hn.
        apply PeanoNat.Nat.le_ngt in Hn. apply Hn.
        rewrite length_map in Hi. exact Hi.
  Qed.


  
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

  (* ------------------------------------------------------------------ *)
  (* build_tries soundness: no false positives in matching               *)
  (* ------------------------------------------------------------------ *)

  Context (idx_map_plus_ok : @map_plus_ok _ _ idx_map_plus).

  (* Helper: get_put on idx_trie with the get-key first, put-key second *)
  Lemma get_put_diff_trie (A : Type) (m : idx_trie A) (k k' : list idx) (v : A)
    : k <> k' ->
      map.get (map.put m k' v) k = map.get m k.
  Proof.
    intro Hne.
    apply (@map.get_put_diff _ _ _ (idx_trie_ok A) m k v k').
    exact Hne.
  Qed.

  Lemma build_tries_for_symbol_sound
    (current_epoch : idx)
    (q_clauses : idx_map (list nat * nat))
    (tbl : idx_trie (db_entry idx analysis_result))
    (n : idx) (clause : list nat * nat) (trie_pair : idx_trie unit * idx_trie unit)
    (assignment : list idx) :
    map.get q_clauses n = Some clause ->
    map.get (build_tries_for_symbol idx Eqb_idx idx_map idx_map_plus idx_trie
               analysis_result current_epoch q_clauses tbl) n = Some trie_pair ->
    map.get (fst trie_pair) assignment = Some tt ->
    exists args entry,
      map.get tbl args = Some entry
      /\ match_clause clause args (entry.(entry_value idx analysis_result)) = Some assignment.
  Proof.
    unfold build_tries_for_symbol.
    intros Hqn Hget Hfull.
    revert trie_pair Hget Hfull.
    eapply (@map.fold_spec (list idx) (db_entry idx analysis_result) (idx_trie _) (idx_trie_ok _)
      (idx_map (idx_trie unit * idx_trie unit))
      (fun tbl_processed tries =>
        forall trie_pair,
        map.get tries n = Some trie_pair ->
        map.get (fst trie_pair) assignment = Some tt ->
        exists args entry,
          map.get tbl_processed args = Some entry
          /\ match_clause clause args (entry_value idx analysis_result entry) = Some assignment));
      [ | ].
    - (* Base case: accumulator = map_map (fun _ => (empty, empty)) q_clauses *)
      intros tp Htp Hfull.
      rewrite (@map_map_spec _ idx_map _ idx_map_plus_ok) in Htp.
      rewrite Hqn in Htp.
      cbn [option_map] in Htp.
      injection Htp; intro; subst tp.
      cbn [fst] in Hfull.
      rewrite (@map.get_empty _ _ _ (idx_trie_ok unit)) in Hfull.
      discriminate.
    - (* Step case: process entry (k, v) from the trie *)
      intros k v m_partial r Hnotk IH tp Htp Hfull.
      destruct v as [ epoch vv va ].
      rewrite (@intersect_spec _ idx_map _ idx_map_plus_ok) in Htp.
      destruct (map.get r n) as [ tp_old | ] eqn:Htp_old.
      2: { destruct (map.get q_clauses n); discriminate. }
      destruct (map.get q_clauses n) as [ cl | ] eqn:Hcl.
      2: { discriminate. }
      injection Hqn; intro; subst cl.
      injection Htp; intro; subst tp.
      destruct tp_old as [ full_old frontier_old ].
      cbn [fst] in Hfull.
      destruct (match_clause clause k vv) as [ assignment0 | ] eqn:Hmatch.
      { (* Match succeeded: assignment0 was recorded in full *)
        destruct (eqb epoch current_epoch) eqn:Hepoch.
        - cbn [fst] in Hfull.
          destruct (eqb (assignment0 : list idx) assignment) eqn:Heqasg.
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs. subst assignment0.
            exists k. exists (Build_db_entry idx analysis_result epoch vv va).
            split.
            * apply (@map.get_put_same _ _ _ (idx_trie_ok _)).
            * cbn [entry_value]. exact Hmatch.
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs.
            rewrite (get_put_diff_trie unit full_old assignment assignment0 tt
              (fun H => Hbs (eq_sym H))) in Hfull.
            destruct (IH (full_old, frontier_old) eq_refl Hfull)
              as [ args [ entry [ Hargs Hentry ] ] ].
            exists args. exists entry.
            split.
            * rewrite (get_put_diff_trie _ m_partial args k _).
              ** exact Hargs.
              ** intro Heq'. subst args. rewrite Hnotk in Hargs. discriminate.
            * exact Hentry.
        - cbn [fst] in Hfull.
          destruct (eqb (assignment0 : list idx) assignment) eqn:Heqasg.
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs. subst assignment0.
            exists k. exists (Build_db_entry idx analysis_result epoch vv va).
            split.
            * apply (@map.get_put_same _ _ _ (idx_trie_ok _)).
            * cbn [entry_value]. exact Hmatch.
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs.
            rewrite (get_put_diff_trie unit full_old assignment assignment0 tt
              (fun H => Hbs (eq_sym H))) in Hfull.
            destruct (IH (full_old, frontier_old) eq_refl Hfull)
              as [ args [ entry [ Hargs Hentry ] ] ].
            exists args. exists entry.
            split.
            * rewrite (get_put_diff_trie _ m_partial args k _).
              ** exact Hargs.
              ** intro Heq'. subst args. rewrite Hnotk in Hargs. discriminate.
            * exact Hentry. }
      { (* Match failed: (full, frontier) unchanged, use IH directly *)
        cbn [fst] in Hfull.
        destruct (IH (full_old, frontier_old) eq_refl Hfull)
          as [ args [ entry [ Hargs Hentry ] ] ].
        exists args. exists entry.
        split.
        - rewrite (get_put_diff_trie _ m_partial args k _).
          + exact Hargs.
          + intro Heq'. subst args. rewrite Hnotk in Hargs. discriminate.
        - exact Hentry. }
  Qed.

  Lemma build_tries_sound (q : rule_set idx symbol symbol_map idx_map)
    (inst : instance)
    (f : symbol) (n : idx) (clause : list nat * nat)
    (clause_tries : idx_map (idx_trie unit * idx_trie unit))
    (trie_pair : idx_trie unit * idx_trie unit) (assignment : list idx)
    (q_f : idx_map (list nat * nat)) :
    map.get (q.(query_clauses idx symbol symbol_map idx_map)) f = Some q_f ->
    map.get q_f n = Some clause ->
    map.get (fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
      idx_map idx_map_plus idx_trie analysis_result q inst)) f = Some clause_tries ->
    map.get clause_tries n = Some trie_pair ->
    map.get (fst trie_pair) assignment = Some tt ->
    exists args v,
      atom_in_db (Build_atom f args v) inst.(db)
      /\ match_clause clause args v = Some assignment.
  Proof.
    intros Hqf Hclause Hbt_f Hct_n Hfull.
    unfold build_tries in Hbt_f. cbn [fst] in Hbt_f.
    rewrite (@intersect_spec _ symbol_map _ symbol_map_plus_ok) in Hbt_f.
    rewrite Hqf in Hbt_f.
    destruct (map.get inst.(db) f) as [ tbl | ] eqn:Htbl.
    - unfold db_map in Htbl.
      rewrite Htbl in Hbt_f.
      injection Hbt_f; intro; subst clause_tries.
      pose proof (build_tries_for_symbol_sound (inst.(epoch)) q_f tbl n clause trie_pair assignment
        Hclause Hct_n Hfull) as [ args [ entry [ Hargs Hentry ] ] ].
      exists args. exists entry.(entry_value idx analysis_result).
      split.
      + unfold atom_in_db. unfold "<$>".
        cbn [atom_fn atom_args atom_ret].
        unfold Is_Some_satisfying.
        cbn [atom_fn atom_args atom_ret].
        pattern (map.get (db inst) f); rewrite Htbl.
        pattern (map.get tbl args); rewrite Hargs.
        reflexivity.
      + exact Hentry.
    - unfold db_map in Htbl.
      rewrite Htbl in Hbt_f.
      cbn in Hbt_f. discriminate.
  Qed.

  Lemma variable_flags_length (qvs cvs : list idx) :
    List.length (variable_flags idx Eqb_idx qvs cvs) = List.length qvs.
  Proof.
    revert cvs.
    induction qvs as [|q qvs' IH]; intros cvs; cbn [variable_flags].
    - reflexivity.
    - destruct cvs as [|c cvs'].
      + cbn. rewrite IH. reflexivity.
      + destruct (eqb q c).
        * cbn. rewrite IH. reflexivity.
        * cbn. rewrite IH. reflexivity.
  Qed.

  Lemma build_tries_for_symbol_frontier_subset
    (current_epoch : idx) (q_clauses : idx_map (list nat * nat))
    (tbl : idx_trie (db_entry idx analysis_result))
    (n : idx) (trie_pair : idx_trie unit * idx_trie unit) (assignment : list idx) :
    map.get (build_tries_for_symbol idx Eqb_idx idx_map idx_map_plus idx_trie
               analysis_result current_epoch q_clauses tbl) n = Some trie_pair ->
    map.get (snd trie_pair) assignment = Some tt ->
    map.get (fst trie_pair) assignment = Some tt.
  Proof.
    intros Hget Hfrontier.
    revert trie_pair Hget Hfrontier.
    unfold build_tries_for_symbol.
    eapply (@map.fold_spec (list idx) (db_entry idx analysis_result) (idx_trie _) (idx_trie_ok _)
      (idx_map (idx_trie unit * idx_trie unit))
      (fun _tbl_processed tries =>
        forall tp,
        map.get tries n = Some tp ->
        map.get (snd tp) assignment = Some tt ->
        map.get (fst tp) assignment = Some tt));
      [ | ].
    - (* Base case *)
      intros tp Htp Hfront.
      rewrite (@map_map_spec _ idx_map _ idx_map_plus_ok) in Htp.
      destruct (map.get q_clauses n) as [ cl | ] eqn:Hcl.
      + cbn [option_map] in Htp.
        injection Htp; intro; subst tp.
        cbn [snd] in Hfront.
        rewrite (@map.get_empty _ _ _ (idx_trie_ok unit)) in Hfront.
        discriminate.
      + cbn [option_map] in Htp. discriminate.
    - (* Step case *)
      intros k v m_partial r Hnotk IH tp Htp Hfront.
      destruct v as [ epoch vv va ].
      rewrite (@intersect_spec _ idx_map _ idx_map_plus_ok) in Htp.
      destruct (map.get r n) as [ tp_old | ] eqn:Htp_old.
      2: { destruct (map.get q_clauses n); discriminate. }
      destruct (map.get q_clauses n) as [ cl | ] eqn:Hcl.
      2: { discriminate. }
      injection Htp; intro; subst tp.
      destruct tp_old as [ full_old frontier_old ].
      destruct (match_clause cl k vv) as [ assignment0 | ] eqn:Hmatch.
      { destruct (eqb epoch current_epoch) eqn:Hepoch.
        - (* epoch matches: frontier' = put frontier_old assignment0 tt *)
          cbn [fst snd] in *.
          destruct (eqb (assignment0 : list idx) assignment) eqn:Heqasg.
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs. subst assignment0.
            apply (@map.get_put_same _ _ _ (idx_trie_ok unit)).
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs.
            rewrite (get_put_diff_trie unit frontier_old assignment assignment0 tt
              (fun H => Hbs (eq_sym H))) in Hfront.
            pose proof (IH (full_old, frontier_old) eq_refl) as HIH.
            cbn [fst snd] in HIH.
            pose proof (HIH Hfront) as Hfull_old.
            rewrite (get_put_diff_trie unit full_old assignment assignment0 tt
              (fun H => Hbs (eq_sym H))).
            exact Hfull_old.
        - (* epoch doesn't match: frontier' = frontier_old unchanged *)
          cbn [fst snd] in *.
          pose proof (IH (full_old, frontier_old) eq_refl) as HIH.
          cbn [fst snd] in HIH.
          pose proof (HIH Hfront) as Hfull_old.
          destruct (eqb (assignment0 : list idx) assignment) eqn:Heqasg.
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs. subst assignment0.
            apply (@map.get_put_same _ _ _ (idx_trie_ok unit)).
          + pose proof (@eqb_spec (list idx) (list_eqb (A:=idx))
              (@list_eqb_ok idx Eqb_idx Eqb_idx_ok) assignment0 assignment) as Hbs.
            rewrite Heqasg in Hbs.
            rewrite (get_put_diff_trie unit full_old assignment assignment0 tt
              (fun H => Hbs (eq_sym H))).
            exact Hfull_old. }
      { (* Match failed: pair unchanged *)
        cbn [fst snd] in *.
        exact (IH (full_old, frontier_old) eq_refl Hfront). }
  Qed.

  Lemma build_tries_frontier_subset (q : rule_set idx symbol symbol_map idx_map)
    (inst : instance)
    (f : symbol) (n : idx)
    (clause_tries : idx_map (idx_trie unit * idx_trie unit))
    (trie_pair : idx_trie unit * idx_trie unit) (assignment : list idx) :
    map.get (fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
      idx_map idx_map_plus idx_trie analysis_result q inst)) f = Some clause_tries ->
    map.get clause_tries n = Some trie_pair ->
    map.get (snd trie_pair) assignment = Some tt ->
    map.get (fst trie_pair) assignment = Some tt.
  Proof.
    intros Hbt_f Hct_n Hfront.
    unfold build_tries in Hbt_f. cbn [fst] in Hbt_f.
    rewrite (@intersect_spec _ symbol_map _ symbol_map_plus_ok) in Hbt_f.
    destruct (map.get (query_clauses idx symbol symbol_map idx_map q) f) as [ q_f | ] eqn:Hqf.
    - destruct (map.get inst.(db) f) as [ tbl | ] eqn:Htbl.
      + unfold db_map in Htbl.
        rewrite Htbl in Hbt_f.
        injection Hbt_f; intro; subst clause_tries.
        apply (build_tries_for_symbol_frontier_subset (inst.(epoch)) q_f tbl n trie_pair assignment
          Hct_n Hfront).
      + unfold db_map in Htbl.
        rewrite Htbl in Hbt_f.
        cbn in Hbt_f. discriminate.
    - cbn in Hbt_f. discriminate.
  Qed.

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
      (* Every idx appearing in the db (as an [atom_arg] or [atom_ret])
         is a key in the union-find. Needed by [update_entry] to call
         [union_sound] with values returned by [db_lookup]: without this,
         [Sep.has_key] for the looked-up [atom_ret] cannot be recovered
         from [atom_in_db] alone. *)
      db_idxs_in_equiv : forall a, atom_in_db a e.(db) ->
                                   all (fun i => Sep.has_key i e.(equiv).(parent))
                                       a.(atom_args)
                                   /\ Sep.has_key a.(atom_ret) e.(equiv).(parent);
    }.

  Section ForModel.

    Context m (idx_interpretation : idx_map m.(domain)).

    Local Notation atom_sound_for_model :=
      (atom_sound_for_model m idx_interpretation).

    (*TODO: move to defining file*)
    Arguments parent {idx}%_type_scope {idx_map rank_map} u.
    
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
      - intros; basic_utils_crush.
      - intros a Hin.
        unfold atom_in_db in Hin.
        rewrite map.get_empty in Hin. cbn in Hin. tauto. }
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
  #[local] Set Warnings "-cannot-define-projection".
  Record forall_nonempty {A} P Q : Prop :=
    {
      fne_elt : A;
      fne_elt_in : P fne_elt;
      fne_all : forall x, P x -> Q x;
    }.
  #[local] Set Warnings "cannot-define-projection".

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
      destruct He_ok as [Hg_eq Hg_wl Hg_par Hg_db];
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
      + intros a Ha.
        rewrite <- Hdb in Ha.
        destruct (Hg_db _ Ha) as [Hargs Hret].
        split; [|apply Hkey; exact Hret].
        eapply all_wkn; [|exact Hargs]; intros; apply Hkey; assumption.
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
      + intros a Ha.
        rewrite Hdb in Ha.
        destruct (Hg_db _ Ha) as [Hargs Hret].
        split; [|apply Hkey; exact Hret].
        eapply all_wkn; [|exact Hargs]; intros; apply Hkey; assumption.
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
  Arguments pull_parents {idx symbol}%_type_scope
  {symbol_map idx_map idx_trie}%_function_scope
  {analysis_result}%_type_scope x _.
  (*TODO: move to Defs.v*)
  Arguments remove_parents {idx symbol}%_type_scope
  {symbol_map idx_map idx_trie}%_function_scope
  {analysis_result}%_type_scope x _.


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
  Arguments db_remove {idx symbol}%_type_scope
  {symbol_map idx_map idx_trie}%_function_scope
  {analysis_result}%_type_scope a _.

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

  
  Arguments db_lookup {idx symbol}%_type_scope {symbol_map idx_map idx_trie}%_function_scope
    {analysis_result}%_type_scope f args%_list_scope _.

  Arguments db_set {idx}%_type_scope {Eqb_idx} {symbol}%_type_scope
    {symbol_map idx_map idx_trie}%_function_scope
    {analysis_result}%_type_scope {H} a _.


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

  (* Monotonic growth of [equiv]'s PER. Used to propagate
     [worklist_entry_ok]-derived facts ([uf_rel_PER e.equiv x_old
     x_canonical] for an unprocessed [union_repair] entry) across
     repair iterations: each repair step may union new pairs but
     never removes existing PER pairs. *)
  Definition equiv_extends (e e' : instance) : Prop :=
    forall x y, uf_rel_PER _ _ _ e.(equiv) x y ->
                uf_rel_PER _ _ _ e'.(equiv) x y.

  Lemma equiv_extends_refl e : equiv_extends e e.
  Proof. unfold equiv_extends; auto. Qed.

  Lemma equiv_extends_trans e1 e2 e3 :
    equiv_extends e1 e2 -> equiv_extends e2 e3 -> equiv_extends e1 e3.
  Proof. unfold equiv_extends; auto. Qed.

  Lemma equiv_extends_worklist_entry_ok e e' ent :
    equiv_extends e e' ->
    worklist_entry_ok e.(equiv) ent ->
    worklist_entry_ok e'.(equiv) ent.
  Proof. destruct ent; cbn; auto. Qed.

  Lemma fields_preserved_equiv_extends e e' :
    fields_preserved e e' -> equiv_extends e e'.
  Proof.
    unfold fields_preserved, equiv_extends.
    intros (_ & _ & _ & _ & _ & _ & Huf_iff) x y. apply Huf_iff.
  Qed.

  (* fields_preserved propagates egraph_ok provided the new equiv is
     itself well-formed (which the find-family lemmas already prove
     separately). The only field of egraph_ok that depends on equiv
     beyond the union-find shape is via uf_rel_PER (in worklist_ok
     and parents_ok), and that is preserved by the iff2 conjunct.
     db_idxs_in_equiv uses has_key, also preserved (iff conjunct). *)
  Lemma fields_preserved_egraph_ok e e' :
    egraph_ok e ->
    fields_preserved e e' ->
    (exists l, union_find_ok lt e'.(equiv) l) ->
    egraph_ok e'.
  Proof.
    intros [Heqok Hwlok Hparok Hdbkok] Hfp Hex'.
    destruct Hfp as (Hdb & Hpa & Hep & Hwl & Han & Hkey & Huf_iff).
    constructor.
    - exact Hex'.
    - rewrite Hwl.
      eapply all_wkn; [|exact Hwlok].
      intros ent _. destruct ent as [old new improved|x]; cbn; auto.
      intros Hper. apply Huf_iff. exact Hper.
    - rewrite Hpa. intros x s Hgs. specialize (Hparok _ _ Hgs).
      eapply all_wkn; [|exact Hparok].
      intros b _ Hbup.
      destruct Hbup as [bb Hbb]. destruct Hbb as [Hca Hbain].
      destruct Hca as [Hfn Hargs_ret]. destruct Hargs_ret as [Hargs Hret].
      exists bb. split.
      + unfold atom_canonical_equiv. split; [exact Hfn|]. split.
        * clear -Hargs Huf_iff.
          revert Hargs. generalize (atom_args b), (atom_args bb).
          intros l1 l2. revert l2.
          induction l1 as [|y ys IH]; destruct l2 as [|z zs];
            cbn; auto; try tauto.
          intros [Hy Hys]. split.
          { apply Huf_iff. exact Hy. }
          { apply IH. exact Hys. }
        * apply Huf_iff. exact Hret.
      + unfold atom_in_egraph. rewrite Hdb. exact Hbain.
    - rewrite Hdb. intros b Hbain. specialize (Hdbkok _ Hbain).
      destruct Hdbkok as [Hka Hkr]. split.
      + eapply all_wkn; [|exact Hka].
        intros j _ Hj. apply Hkey. exact Hj.
      + apply Hkey. exact Hkr.
  Qed.

  (* Soundness for the interpretation is propagated by fields_preserved
     in the same way (db unchanged → atom_interpretation unchanged;
     uf_rel_PER iff → rel_interpretation unchanged; has_key iff →
     interpretation_exact lifts). *)
  Lemma fields_preserved_sound_for_interpretation i e e' :
    egraph_sound_for_interpretation m i e ->
    fields_preserved e e' ->
    egraph_sound_for_interpretation m i e'.
  Proof.
    intros [Hi_wf Hi_exact Hi_atom Hi_rel] Hfp.
    destruct Hfp as (Hdb & _ & _ & _ & _ & Hkey & Huf_iff).
    constructor.
    - exact Hi_wf.
    - intros y Hy. specialize (Hi_exact _ Hy). apply Hkey. exact Hi_exact.
    - intros b Hbain. apply Hi_atom.
      unfold atom_in_egraph in *. rewrite Hdb in Hbain. exact Hbain.
    - intros i1 i2 Hper. apply Hi_rel. apply Huf_iff. exact Hper.
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
     inputs (pointwise via [all2]) in the post-state's [equiv]. A
     clean application of [vc_list_Mmap_outputs]: the invariant [P]
     bundles the union-find ok-witness with [all has_key], the step
     relation [R] is [fields_preserved], and the per-element relation
     [Q] is [uf_rel_PER] in the current state's [equiv]. The transport
     of [Q] across [R] is the [iff2] conjunct of [fields_preserved]. *)
  Lemma list_Mmap_find_preserves_fields_strong (xs : list idx)
    : vc (list_Mmap find xs)
        (fun (e : instance) (res : (list idx * instance)%type) =>
           (exists l, union_find_ok lt e.(equiv) l) ->
           all (fun i => Sep.has_key i e.(equiv).(parent)) xs ->
           (exists l, union_find_ok lt (snd res).(equiv) l)
           /\ fields_preserved e (snd res)
           /\ all2 (uf_rel_PER _ _ _ (snd res).(equiv)) (fst res) xs).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_outputs find
                  (fun l e => (exists rs, union_find_ok lt e.(equiv) rs)
                              /\ all (fun i => Sep.has_key i e.(equiv).(parent)) l)
                  fields_preserved
                  (fun (e : instance) y x => uf_rel_PER _ _ _ e.(equiv) y x))].
    - cbn beta.
      intros e res Hgen Hex Hkeys.
      destruct (Hgen (conj Hex Hkeys)) as ((Hex' & _) & Hf01 & Hall).
      split; [exact Hex'|]. split; [exact Hf01|]. exact Hall.
    - intros s _; apply fields_preserved_refl.
    - intros; eapply fields_preserved_trans; eauto.
    - intros e e' y x Hf01 Huf.
      destruct Hf01 as (_ & _ & _ & _ & _ & _ & Huf_iff).
      apply Huf_iff. exact Huf.
    - intros x l_rest. unfold vc. intros e [Hex Hkeys].
      cbn [all] in Hkeys. destruct Hkeys as [Hkey_x Hkeys'].
      pose proof (find_preserves_fields_strong x e Hex Hkey_x) as Hf.
      cbn beta in Hf.
      destruct (find x e) as [y e1] eqn:Hfind_x.
      cbn [fst snd] in Hf |- *.
      destruct Hf as (Hex1 & Hf01 & Huf_yx).
      split.
      + split; [exact Hex1|].
        destruct Hf01 as (_ & _ & _ & _ & _ & Hkey_iff & _).
        eapply all_wkn; [| exact Hkeys'].
        intros z _ Hz. apply Hkey_iff. exact Hz.
      + split; [exact Hf01 | exact Huf_yx].
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

  (* ============================================================== *)
  (* Soundness of the egraph-population primitives                  *)
  (* (add_open_term, add_open_sort, add_ctx in Pyrosome).            *)
  (*                                                                 *)
  (* These statements are admitted here; they form Layer A of the    *)
  (* re-proof of `add_open_term_sound` / `add_ctx_sound` in          *)
  (* Pyrosome/Tools/EGraph/Theorems.v.  See                          *)
  (* /root/.claude/plans/a-number-of-theorems-functional-trinket.md  *)
  (* for the design.                                                 *)
  (*                                                                 *)
  (* All three lemmas use `vc` (Utils/VC.v) for their conclusions    *)
  (* and `egraph_ok` + `egraph_sound_for_interpretation` as          *)
  (* invariants, matching the style of [rebuild_sound] above.        *)
  (* ============================================================== *)

  (* alloc_opaque: returns a fresh id, leaves db/parents/worklist
     unchanged, adds [fst res] as a key in the union-find, writes
     a default analysis for it.  Preserves both [egraph_ok] and
     [egraph_sound_for_interpretation]: the new id is not in [i]'s
     domain, so atom soundness, eq soundness, and the
     [interpretation_exact] field all carry over unchanged. *)
  (* Forest extension: adding a fresh self-loop as a new root tree. *)
  Lemma forest_extend (l : list idx) (r : idx_map idx) (x : idx)
    : map.get r x = None ->
      forest idx (idx_map idx) l r ->
      forest idx (idx_map idx) (x :: l) (map.put r x x).
  Proof.
    intros Hnone Hf.
    unfold forest in *. cbn [map].
    change (Sep.seps (?h :: ?t)) with (Sep.sep h (Sep.seps t)).
    exists (map.singleton x x), r.
    assert (Hdj : map.disjoint (map.singleton x x) r).
    { intros k v1 v2 Hk1 Hk2.
      eqb_case k x.
      - rewrite Hnone in Hk2; discriminate.
      - rewrite get_singleton_diff in Hk1; auto; discriminate. }
    repeat split.
    3:{ apply (tree_singleton _ Eqb_idx Eqb_idx_ok (idx_map idx) (idx_map_ok _)). }
    3:{ exact Hf. }
    2:{ exact Hdj. }
    rewrite <- (@Sep.putmany_singleton _ Eqb_idx Eqb_idx_ok (idx_map idx) (idx_map_ok _)).
    symmetry.
    pose proof (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) as Hbs.
    apply (@Properties.map.putmany_comm _ _ _ (idx_map_ok _) _ Hbs _ _ Hdj).
  Qed.

  (* PER monotonicity for the new union-find after alloc_opaque:
     The new parent map is (map.put pa nx nx) where nx is fresh in pa.
     Any old PER fact carries over since the underlying [parent_rel]
     fact must reference a [map.get pa i = Some j] with i in pa, so
     i ≠ nx, so the [map.put] doesn't shadow it. *)
  (* Reflection: the new PER after alloc_opaque is the old PER plus the
     isolated self-loop at [nx].  Needs forest-closedness to rule out
     edges that "land on" nx in the old map (impossible since
     map.get pa nx = None plus the forest closure says map.get pa x =
     Some y implies y is also a key). *)
  Lemma uf_rel_PER_alloc_reflect (uf : union_find) (nx : idx) (roots : list idx)
    : union_find_ok lt uf roots ->
      map.get uf.(parent) nx = None ->
      forall i1 i2,
        PER_closure (fun x y => map.get (map.put uf.(parent) nx nx) x = Some y) i1 i2 ->
        (i1 = nx /\ i2 = nx) \/ uf_rel_PER uf i1 i2.
  Proof.
    intros Huok Hnone i1 i2 HP.
    pose proof (uf_forest _ _ _ _ _ _ Huok) as Hforest.
    pose proof (forest_closed _ _ Eqb_idx_ok _ (idx_map_ok _) _ _ Hforest) as Hcl.
    induction HP.
    - (* base *)
      pose proof (Eqb_idx_ok a nx) as Heqa.
      destruct (eqb a nx).
      + subst. rewrite map.get_put_same in H1. inversion H1; subst.
        left; split; reflexivity.
      + rewrite map.get_put_diff in H1 by congruence.
        right. apply PER_clo_base. exact H1.
    - (* trans *)
      destruct IHHP1 as [Hc1 | Hold1]; destruct IHHP2 as [Hc2 | Hold2].
      + destruct Hc1 as [Ha Hb]. destruct Hc2 as [Hb' Hc].
        left; split; congruence.
      + destruct Hc1 as [Ha Hb]. subst.
        exfalso.
        edestruct uf_rel_PER_has_key as [Hkb _]; [exact Huok | exact Hold2 |].
        unfold Sep.has_key in Hkb. rewrite Hnone in Hkb. tauto.
      + destruct Hc2 as [Hb Hc]. subst.
        exfalso.
        edestruct uf_rel_PER_has_key as [_ Hkb]; [exact Huok | exact Hold1 |].
        unfold Sep.has_key in Hkb. rewrite Hnone in Hkb. tauto.
      + right. eapply PER_clo_trans; eauto.
    - (* sym *)
      destruct IHHP as [Hc | Hold].
      + destruct Hc as [Ha Hb]; subst. left; auto.
      + right. apply PER_clo_sym; exact Hold.
  Qed.

  Lemma uf_rel_PER_alloc_monotone (uf : union_find) (nx : idx)
    : map.get uf.(parent) nx = None ->
      forall i1 j,
        uf_rel_PER uf i1 j ->
        PER_closure
          (fun x y => map.get (map.put uf.(parent) nx nx) x = Some y)
          i1 j.
  Proof.
    intros Hnone i1 j HP.
    induction HP.
    - apply PER_clo_base.
      assert (a <> nx).
      { intro; subst. rewrite Hnone in H1. discriminate. }
      rewrite map.get_put_diff by congruence. exact H1.
    - eapply PER_clo_trans; eauto.
    - apply PER_clo_sym; auto.
  Qed.

  (* The caller supplies a domain value [d] (with [domain_wf] and a
     reflexivity witness [domain_eq d d]) to interpret the fresh id.
     The postcondition extends the interpretation accordingly. *)
  Lemma alloc_opaque_sound (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x))
        (Hltt : Transitive lt) (i : idx_map m.(domain))
        (d : m.(domain)) (Hwfd : m.(domain_wf) d) (Hdd : m.(domain_eq) d d)
    : vc (alloc_opaque idx idx_succ symbol symbol_map idx_map idx_trie
                       analysis_result)
        (fun e_in res =>
           egraph_ok e_in ->
           egraph_sound_for_interpretation m i e_in ->
           egraph_ok (snd res)
           /\ egraph_sound_for_interpretation m
                (map.put i (fst res) d) (snd res)
           /\ map.get i (fst res) = None
           /\ ~ Sep.has_key (fst res) e_in.(equiv).(parent)
           /\ Sep.has_key (fst res) (snd res).(equiv).(parent)
           /\ (forall x, Sep.has_key x e_in.(equiv).(parent) ->
                         Sep.has_key x (snd res).(equiv).(parent))
           /\ e_in.(db) = (snd res).(db)
           /\ e_in.(parents) = (snd res).(parents)
           /\ e_in.(worklist) = (snd res).(worklist)).
  Proof.
    unfold vc, alloc_opaque.
    intros [db_in equiv_in parents_in epoch_in worklist_in analyses_in log_in].
    destruct equiv_in as [rk_in pa_in mr_in nx_in] eqn:Heq_in.
    cbn -[map.get map.put].
    intros Hok Hsnd.
    destruct Hok as [Heqok Hwlok Hparok Hdbkok].
    destruct Heqok as [roots Heqok].
    pose proof Heqok as Heqok'.
    destruct Heqok as [Hforest Hrcd Hri Hmax Hnub].
    cbn [parent rank max_rank next equiv] in *.
    assert (Hnxfresh : ~ Sep.has_key nx_in pa_in).
    { intro Hk. specialize (Hnub _ Hk). eapply Hlti; exact Hnub. }
    assert (Hnxnone : map.get i nx_in = None).
    { destruct Hsnd as [_ Hinterp_exact _ _].
      destruct (map.get i nx_in) eqn:Hgi; auto.
      exfalso. apply Hnxfresh.
      apply Hinterp_exact. cbn. rewrite Hgi. constructor. }
    assert (Hgetnone_pa : map.get pa_in nx_in = None).
    { unfold Sep.has_key in Hnxfresh. destruct (map.get pa_in nx_in); tauto. }
    (* Build new union_find_ok with roots' = nx_in :: roots *)
    assert (Hnewok : union_find_ok lt
                      {| rank := map.put rk_in nx_in 0;
                         parent := map.put pa_in nx_in nx_in;
                         max_rank := mr_in;
                         next := idx_succ nx_in |}
                      (nx_in :: roots)).
    { constructor; cbn [parent rank max_rank next].
      - apply forest_extend; auto.
      - intros k v Hget.
        eqb_case k nx_in.
        + exists 0. rewrite map.get_put_same. reflexivity.
        + rewrite map.get_put_diff in Hget by congruence.
          specialize (Hrcd _ _ Hget). destruct Hrcd as [r0 Hr0].
          exists r0. rewrite map.get_put_diff by congruence. exact Hr0.
      - intros ki kj Hget Hneq.
        eqb_case ki nx_in.
        + rewrite map.get_put_same in Hget. inversion Hget. congruence.
        + rewrite map.get_put_diff in Hget by congruence.
          eqb_case kj nx_in.
          * exfalso. apply Hnxfresh.
            apply (forest_closed _ _ Eqb_idx_ok _ (idx_map_ok _) _ _ Hforest _ _ Hget).
          * specialize (Hri _ _ Hget Hneq).
            rewrite ! map.get_put_diff by congruence. exact Hri.
      - intros j r Hget.
        eqb_case j nx_in.
        + rewrite map.get_put_same in Hget. inversion Hget; subst. Lia.lia.
        + rewrite map.get_put_diff in Hget by congruence.
          eauto.
      - intros k Hk.
        unfold Sep.has_key in Hk.
        eqb_case k nx_in.
        + apply Hlts.
        + rewrite map.get_put_diff in Hk by congruence.
          assert (Sep.has_key k pa_in) as Hkpa.
          { unfold Sep.has_key. destruct (map.get pa_in k); auto. }
          specialize (Hnub _ Hkpa).
          (* lt k nx_in -> lt k (succ nx_in) by transitivity *)
          eapply Hltt; [exact Hnub | apply Hlts]. }
    (* Assemble proofs of each conjunct as separate hypotheses *)
    (* Pre-extract sound fields *)
    destruct Hsnd as [Hint_wf Hint_exact Hatom_int Hrel_int].
    assert (Hnewok' : egraph_ok
                       {| db := db_in;
                          equiv := {| rank := map.put rk_in nx_in 0;
                                      parent := map.put pa_in nx_in nx_in;
                                      max_rank := mr_in;
                                      next := idx_succ nx_in |};
                          parents := parents_in;
                          epoch := epoch_in;
                          worklist := worklist_in;
                          analyses := map.put analyses_in nx_in default;
                          log := log_in |}).
    { constructor.
      - exists (nx_in :: roots). exact Hnewok.
      - cbn [worklist].
        eapply all_wkn; [|exact Hwlok].
        intros [old new improved | xa]; cbn; auto.
        intros Hin_wl Hper.
        apply (uf_rel_PER_alloc_monotone
                 {| rank := rk_in; parent := pa_in;
                    max_rank := mr_in; next := nx_in |}
                 nx_in Hgetnone_pa _ _ Hper).
      - cbn [parents db equiv].
        intros xp s Hgetps. specialize (Hparok _ _ Hgetps).
        eapply all_wkn; [|exact Hparok].
        intros at0 Hin_s Hain.
        destruct Hain as [a' Ha']. destruct Ha' as [Hca Hin].
        exists a'. split; [|exact Hin].
        destruct Hca as [Hfn Hrest]. destruct Hrest as [Hargs Hret].
        split; [exact Hfn|split].
        + (* PER monotonicity for args *)
          eapply all2_impl; [|exact Hargs].
          intros i1 j Hp. cbn [parent equiv].
          apply (uf_rel_PER_alloc_monotone
                   {| rank := rk_in; parent := pa_in;
                      max_rank := mr_in; next := nx_in |}
                   nx_in Hgetnone_pa _ _ Hp).
        + (* PER monotonicity for ret *)
          cbn [parent equiv].
          apply (uf_rel_PER_alloc_monotone
                   {| rank := rk_in; parent := pa_in;
                      max_rank := mr_in; next := nx_in |}
                   nx_in Hgetnone_pa _ _ Hret).
      - cbn [db].
        intros at0 Hat. specialize (Hdbkok _ Hat).
        destruct Hdbkok as [Hargk Hretk]. split.
        + eapply all_wkn; [|exact Hargk].
          intros i' Hin_args Hi'. unfold Sep.has_key in *.
          cbn [parent equiv].
          pose proof (Eqb_idx_ok i' nx_in) as Heq.
          destruct (eqb i' nx_in).
          * subst. rewrite map.get_put_same. constructor.
          * rewrite map.get_put_diff by congruence. exact Hi'.
        + unfold Sep.has_key in *.
          cbn [parent equiv].
          pose proof (Eqb_idx_ok (atom_ret at0) nx_in) as Heq.
          destruct (eqb (atom_ret at0) nx_in).
          * rewrite Heq. rewrite map.get_put_same. constructor.
          * rewrite map.get_put_diff by congruence. exact Hretk. }
    assert (Hnewsnd : egraph_sound_for_interpretation m (map.put i nx_in d)
                       {| db := db_in;
                          equiv := {| rank := map.put rk_in nx_in 0;
                                      parent := map.put pa_in nx_in nx_in;
                                      max_rank := mr_in;
                                      next := idx_succ nx_in |};
                          parents := parents_in;
                          epoch := epoch_in;
                          worklist := worklist_in;
                          analyses := map.put analyses_in nx_in default;
                          log := log_in |}).
    { constructor.
      - intros y dy Hgy.
        pose proof (Eqb_idx_ok y nx_in) as Heq.
        destruct (eqb y nx_in).
        + subst. rewrite map.get_put_same in Hgy. inversion Hgy; subst. exact Hwfd.
        + rewrite map.get_put_diff in Hgy by congruence. eauto.
      - intros y Hy. cbn [parent equiv].
        unfold Sep.has_key in *.
        pose proof (Eqb_idx_ok y nx_in) as Heq.
        destruct (eqb y nx_in).
        + subst. rewrite map.get_put_same. constructor.
        + (* y <> nx_in: get i' y = get i y. Use Hint_exact. *)
          rewrite map.get_put_diff in Hy by congruence.
          specialize (Hint_exact _ Hy).
          cbn [parent equiv] in Hint_exact.
          rewrite map.get_put_diff by congruence. exact Hint_exact.
      - cbn [db] in *. intros a Ha. specialize (Hatom_int _ Ha).
        specialize (Hdbkok _ Ha). destruct Hdbkok as [Hargk Hretk].
        (* Key lemma: get with (put i nx_in d) agrees with get i on non-nx_in keys *)
        assert (Hext_ret : map.get (map.put i nx_in d) a.(atom_ret) = map.get i a.(atom_ret)).
        { unfold Sep.has_key in Hretk.
          destruct (map.get pa_in (atom_ret a)) eqn:Hr; [|tauto].
          rewrite map.get_put_diff; auto.
          intro Hex. subst.
          apply Hnxfresh. unfold Sep.has_key. rewrite Hr. constructor. }
        assert (Hext_args : list_Mmap (map.get (map.put i nx_in d)) a.(atom_args)
                          = list_Mmap (map.get i) a.(atom_args)).
        { revert Hargk. generalize (atom_args a). intro xs.
          induction xs as [|x xs IH]; auto.
          intros [Hxk Hxsk]. cbn.
          rewrite (IH Hxsk).
          unfold Sep.has_key in Hxk.
          destruct (map.get pa_in x) eqn:Hgx; [|tauto].
          rewrite map.get_put_diff; auto.
          intro Hex. subst.
          apply Hnxfresh. unfold Sep.has_key. rewrite Hgx. constructor. }
        unfold atom_sound_for_model in *.
        rewrite Hext_args, Hext_ret. exact Hatom_int.
      - intros i1 i2 Hper. cbn [equiv parent] in Hper.
        (* Reflect the new PER edge back to either (nx_in, nx_in) or an
           old PER edge. *)
        unfold uf_rel_PER in Hper.
        eapply (uf_rel_PER_alloc_reflect
                  {| rank := rk_in; parent := pa_in;
                     max_rank := mr_in; next := nx_in |}
                  nx_in roots Heqok' Hgetnone_pa) in Hper.
        destruct Hper as [Hconj | Hold].
        + destruct Hconj as [Hi1 Hi2]; subst. unfold eq_sound_for_model.
          rewrite !map.get_put_same. cbn. exact Hdd.
        + specialize (Hrel_int _ _ Hold).
          unfold eq_sound_for_model in *.
          (* Both i1, i2 in old equiv (has_key), so neither is nx_in. *)
          edestruct uf_rel_PER_has_key as [Hki1 Hki2]; [exact Heqok' | exact Hold |].
          cbn [parent] in Hki1, Hki2.
          assert (Hi1ne : i1 <> nx_in).
          { intro; subst. unfold Sep.has_key in Hki1.
            rewrite Hgetnone_pa in Hki1. tauto. }
          assert (Hi2ne : i2 <> nx_in).
          { intro; subst. unfold Sep.has_key in Hki2.
            rewrite Hgetnone_pa in Hki2. tauto. }
          rewrite !map.get_put_diff by congruence. exact Hrel_int. }
    split; [exact Hnewok'|].
    split; [exact Hnewsnd|].
    split; [exact Hnxnone|].
    split; [exact Hnxfresh|].
    split; [unfold Sep.has_key; rewrite map.get_put_same; constructor|].
    split.
    { intros xa Hxa. unfold Sep.has_key in *.
      cbn [parent equiv].
      pose proof (Eqb_idx_ok xa nx_in) as Heq.
      destruct (eqb xa nx_in).
      + subst. rewrite map.get_put_same. constructor.
      + rewrite map.get_put_diff by congruence. exact Hxa. }
    split; [reflexivity|].
    split; reflexivity.
  Qed.

  (* [alloc] (no analyses update) variant of [alloc_opaque_sound].
     Same shape; the analyses field is irrelevant to egraph_ok and
     egraph_sound_for_interpretation, so the proof structure is
     identical to alloc_opaque_sound modulo not writing to analyses. *)
  Lemma alloc_sound (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x))
        (Hltt : Transitive lt) (i : idx_map m.(domain))
        (d : m.(domain)) (Hwfd : m.(domain_wf) d) (Hdd : m.(domain_eq) d d)
    : vc (alloc idx idx_succ symbol symbol_map idx_map idx_trie
                analysis_result)
        (fun e_in res =>
           egraph_ok e_in ->
           egraph_sound_for_interpretation m i e_in ->
           egraph_ok (snd res)
           /\ egraph_sound_for_interpretation m
                (map.put i (fst res) d) (snd res)
           /\ map.get i (fst res) = None
           /\ ~ Sep.has_key (fst res) e_in.(equiv).(parent)
           /\ Sep.has_key (fst res) (snd res).(equiv).(parent)
           /\ (forall x, Sep.has_key x e_in.(equiv).(parent) ->
                         Sep.has_key x (snd res).(equiv).(parent))
           /\ e_in.(db) = (snd res).(db)
           /\ e_in.(parents) = (snd res).(parents)
           /\ e_in.(worklist) = (snd res).(worklist)).
  Proof.
    unfold vc, alloc.
    intros [db_in equiv_in parents_in epoch_in worklist_in analyses_in log_in].
    destruct equiv_in as [rk_in pa_in mr_in nx_in] eqn:Heq_in.
    cbn -[map.get map.put].
    intros Hok Hsnd.
    destruct Hok as [Heqok Hwlok Hparok Hdbkok].
    destruct Heqok as [roots Heqok].
    pose proof Heqok as Heqok'.
    destruct Heqok as [Hforest Hrcd Hri Hmax Hnub].
    cbn [parent rank max_rank next equiv] in *.
    assert (Hnxfresh : ~ Sep.has_key nx_in pa_in).
    { intro Hk. specialize (Hnub _ Hk). eapply Hlti; exact Hnub. }
    assert (Hnxnone : map.get i nx_in = None).
    { destruct Hsnd as [_ Hinterp_exact _ _].
      destruct (map.get i nx_in) eqn:Hgi; auto.
      exfalso. apply Hnxfresh.
      apply Hinterp_exact. cbn. rewrite Hgi. constructor. }
    assert (Hgetnone_pa : map.get pa_in nx_in = None).
    { unfold Sep.has_key in Hnxfresh. destruct (map.get pa_in nx_in); tauto. }
    assert (Hnewok : union_find_ok lt
                      {| rank := map.put rk_in nx_in 0;
                         parent := map.put pa_in nx_in nx_in;
                         max_rank := mr_in;
                         next := idx_succ nx_in |}
                      (nx_in :: roots)).
    { constructor; cbn [parent rank max_rank next].
      - apply forest_extend; auto.
      - intros k v Hget.
        eqb_case k nx_in.
        + exists 0. rewrite map.get_put_same. reflexivity.
        + rewrite map.get_put_diff in Hget by congruence.
          specialize (Hrcd _ _ Hget). destruct Hrcd as [r0 Hr0].
          exists r0. rewrite map.get_put_diff by congruence. exact Hr0.
      - intros ki kj Hget Hneq.
        eqb_case ki nx_in.
        + rewrite map.get_put_same in Hget. inversion Hget. congruence.
        + rewrite map.get_put_diff in Hget by congruence.
          eqb_case kj nx_in.
          * exfalso. apply Hnxfresh.
            apply (forest_closed _ _ Eqb_idx_ok _ (idx_map_ok _) _ _ Hforest _ _ Hget).
          * specialize (Hri _ _ Hget Hneq).
            rewrite ! map.get_put_diff by congruence. exact Hri.
      - intros j r Hget.
        eqb_case j nx_in.
        + rewrite map.get_put_same in Hget. inversion Hget; subst. Lia.lia.
        + rewrite map.get_put_diff in Hget by congruence.
          eauto.
      - intros k Hk.
        unfold Sep.has_key in Hk.
        eqb_case k nx_in.
        + apply Hlts.
        + rewrite map.get_put_diff in Hk by congruence.
          assert (Sep.has_key k pa_in) as Hkpa.
          { unfold Sep.has_key. destruct (map.get pa_in k); auto. }
          specialize (Hnub _ Hkpa).
          eapply Hltt; [exact Hnub | apply Hlts]. }
    destruct Hsnd as [Hint_wf Hint_exact Hatom_int Hrel_int].
    assert (Hnewok' : egraph_ok
                       {| db := db_in;
                          equiv := {| rank := map.put rk_in nx_in 0;
                                      parent := map.put pa_in nx_in nx_in;
                                      max_rank := mr_in;
                                      next := idx_succ nx_in |};
                          parents := parents_in;
                          epoch := epoch_in;
                          worklist := worklist_in;
                          analyses := analyses_in;
                          log := log_in |}).
    { constructor.
      - exists (nx_in :: roots). exact Hnewok.
      - cbn [worklist].
        eapply all_wkn; [|exact Hwlok].
        intros [old new improved | xa]; cbn; auto.
        intros Hin_wl Hper.
        apply (uf_rel_PER_alloc_monotone
                 {| rank := rk_in; parent := pa_in;
                    max_rank := mr_in; next := nx_in |}
                 nx_in Hgetnone_pa _ _ Hper).
      - cbn [parents db equiv].
        intros xp s Hgetps. specialize (Hparok _ _ Hgetps).
        eapply all_wkn; [|exact Hparok].
        intros at0 Hin_s Hain.
        destruct Hain as [a' Ha']. destruct Ha' as [Hca Hin].
        exists a'. split; [|exact Hin].
        destruct Hca as [Hfn Hrest]. destruct Hrest as [Hargs Hret].
        split; [exact Hfn|split].
        + eapply all2_impl; [|exact Hargs].
          intros i1 j Hp. cbn [parent equiv].
          apply (uf_rel_PER_alloc_monotone
                   {| rank := rk_in; parent := pa_in;
                      max_rank := mr_in; next := nx_in |}
                   nx_in Hgetnone_pa _ _ Hp).
        + cbn [parent equiv].
          apply (uf_rel_PER_alloc_monotone
                   {| rank := rk_in; parent := pa_in;
                      max_rank := mr_in; next := nx_in |}
                   nx_in Hgetnone_pa _ _ Hret).
      - cbn [db].
        intros at0 Hat. specialize (Hdbkok _ Hat).
        destruct Hdbkok as [Hargk Hretk]. split.
        + eapply all_wkn; [|exact Hargk].
          intros i' Hin_args Hi'. unfold Sep.has_key in *.
          cbn [parent equiv].
          pose proof (Eqb_idx_ok i' nx_in) as Heq.
          destruct (eqb i' nx_in).
          * subst. rewrite map.get_put_same. constructor.
          * rewrite map.get_put_diff by congruence. exact Hi'.
        + unfold Sep.has_key in *.
          cbn [parent equiv].
          pose proof (Eqb_idx_ok (atom_ret at0) nx_in) as Heq.
          destruct (eqb (atom_ret at0) nx_in).
          * rewrite Heq. rewrite map.get_put_same. constructor.
          * rewrite map.get_put_diff by congruence. exact Hretk. }
    assert (Hnewsnd : egraph_sound_for_interpretation m (map.put i nx_in d)
                       {| db := db_in;
                          equiv := {| rank := map.put rk_in nx_in 0;
                                      parent := map.put pa_in nx_in nx_in;
                                      max_rank := mr_in;
                                      next := idx_succ nx_in |};
                          parents := parents_in;
                          epoch := epoch_in;
                          worklist := worklist_in;
                          analyses := analyses_in;
                          log := log_in |}).
    { constructor.
      - intros y dy Hgy.
        pose proof (Eqb_idx_ok y nx_in) as Heq.
        destruct (eqb y nx_in).
        + subst. rewrite map.get_put_same in Hgy. inversion Hgy; subst. exact Hwfd.
        + rewrite map.get_put_diff in Hgy by congruence. eauto.
      - intros y Hy. cbn [parent equiv].
        unfold Sep.has_key in *.
        pose proof (Eqb_idx_ok y nx_in) as Heq.
        destruct (eqb y nx_in).
        + subst. rewrite map.get_put_same. constructor.
        + rewrite map.get_put_diff in Hy by congruence.
          specialize (Hint_exact _ Hy).
          cbn [parent equiv] in Hint_exact.
          rewrite map.get_put_diff by congruence. exact Hint_exact.
      - cbn [db] in *. intros a Ha. specialize (Hatom_int _ Ha).
        specialize (Hdbkok _ Ha). destruct Hdbkok as [Hargk Hretk].
        assert (Hext_ret : map.get (map.put i nx_in d) a.(atom_ret) = map.get i a.(atom_ret)).
        { unfold Sep.has_key in Hretk.
          destruct (map.get pa_in (atom_ret a)) eqn:Hr; [|tauto].
          rewrite map.get_put_diff; auto.
          intro Hex. subst.
          apply Hnxfresh. unfold Sep.has_key. rewrite Hr. constructor. }
        assert (Hext_args : list_Mmap (map.get (map.put i nx_in d)) a.(atom_args)
                          = list_Mmap (map.get i) a.(atom_args)).
        { revert Hargk. generalize (atom_args a). intro xs.
          induction xs as [|x xs IH]; auto.
          intros [Hxk Hxsk]. cbn.
          rewrite (IH Hxsk).
          unfold Sep.has_key in Hxk.
          destruct (map.get pa_in x) eqn:Hgx; [|tauto].
          rewrite map.get_put_diff; auto.
          intro Hex. subst.
          apply Hnxfresh. unfold Sep.has_key. rewrite Hgx. constructor. }
        unfold atom_sound_for_model in *.
        rewrite Hext_args, Hext_ret. exact Hatom_int.
      - intros i1 i2 Hper. cbn [equiv parent] in Hper.
        unfold uf_rel_PER in Hper.
        eapply (uf_rel_PER_alloc_reflect
                  {| rank := rk_in; parent := pa_in;
                     max_rank := mr_in; next := nx_in |}
                  nx_in roots Heqok' Hgetnone_pa) in Hper.
        destruct Hper as [Hconj | Hold].
        + destruct Hconj as [Hi1 Hi2]; subst. unfold eq_sound_for_model.
          rewrite !map.get_put_same. cbn. exact Hdd.
        + specialize (Hrel_int _ _ Hold).
          unfold eq_sound_for_model in *.
          edestruct uf_rel_PER_has_key as [Hki1 Hki2]; [exact Heqok' | exact Hold |].
          cbn [parent] in Hki1, Hki2.
          assert (Hi1ne : i1 <> nx_in).
          { intro; subst. unfold Sep.has_key in Hki1.
            rewrite Hgetnone_pa in Hki1. tauto. }
          assert (Hi2ne : i2 <> nx_in).
          { intro; subst. unfold Sep.has_key in Hki2.
            rewrite Hgetnone_pa in Hki2. tauto. }
          rewrite !map.get_put_diff by congruence. exact Hrel_int. }
    split; [exact Hnewok'|].
    split; [exact Hnewsnd|].
    split; [exact Hnxnone|].
    split; [exact Hnxfresh|].
    split; [unfold Sep.has_key; rewrite map.get_put_same; constructor|].
    split.
    { intros xa Hxa. unfold Sep.has_key in *.
      cbn [parent equiv].
      pose proof (Eqb_idx_ok xa nx_in) as Heq.
      destruct (eqb xa nx_in).
      + subst. rewrite map.get_put_same. constructor.
      + rewrite map.get_put_diff by congruence. exact Hxa. }
    split; [reflexivity|].
    split; reflexivity.
  Qed.

  (* Atom-level equality (under the interpretation) preserves
     soundness: if [a3] is sound and [a1] is i-equivalent to [a3]
     (same fn, args eq_sound pointwise, ret eq_sound), then [a1]
     is also sound. *)
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


  
  Arguments repair_parent_analysis {idx symbol}%_type_scope
  {symbol_map idx_map idx_trie}%_function_scope {analysis_result}%_type_scope
  {H} a _.

  Arguments repair_union {idx}%_type_scope {Eqb_idx} {symbol}%_type_scope
  {symbol_map idx_map idx_trie}%_function_scope {analysis_result}%_type_scope
  {H} _ _ _ _.

  (* Lift a per-element vc lemma with post
       [egraph_ok e -> egraph_ok (snd res) /\ denote_iff e (snd res)]
     to a [list_Mmap]/[list_Miter] of the same shape, using
     [vc_list_Mmap_inv]/[vc_list_Miter_inv] with [P l s := egraph_ok s]
     and [R s s' := forall i, denote s i <-> denote s' i]. *)
  Ltac vc_list_Mmap_egraph_iff per_step :=
    eapply vc_consequence;
      [| apply (vc_list_Mmap_inv _
                  (fun _ s => egraph_ok s)
                  (fun s s' => forall i, denote s i <-> denote s' i))];
      [ cbn beta; intros ? ? Hinv Hok; apply (Hinv Hok)
      | intros ? _ i; reflexivity
      | intros ? ? ? H1 H2 i; rewrite H1; auto
      | intros a l_rest;
        eapply vc_consequence; [| apply (per_step a)];
        cbn beta; intros ? ? Hone Hok; apply (Hone Hok) ].

  Ltac vc_list_Miter_egraph_iff per_step :=
    eapply vc_consequence;
      [| apply (vc_list_Miter_inv _
                  (fun _ s => egraph_ok s)
                  (fun s s' => forall i, denote s i <-> denote s' i))];
      [ cbn beta; intros ? ? Hinv Hok; apply (Hinv Hok)
      | intros ? _ i; reflexivity
      | intros ? ? ? H1 H2 i; rewrite H1; auto
      | intros a l_rest;
        eapply vc_consequence; [| apply (per_step a)];
        cbn beta; intros ? ? Hone Hok; apply (Hone Hok) ].

  (* [pull_worklist] only swaps the worklist field of the instance for
     [[]]; denote/egraph_ok don't read the worklist outside of
     [worklist_ok], which trivially holds for [[]]. *)
  Lemma pull_worklist_denote_iff
    : vc (pull_worklist idx symbol symbol_map idx_map idx_trie analysis_result)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ (snd res).(equiv) = e.(equiv)
           /\ all (worklist_entry_ok e.(equiv)) (fst res)).
  Proof.
    unfold vc, pull_worklist; intros e Hok; cbn [fst snd].
    destruct e as [db_e equiv_e parents_e epoch_e wl_e analyses_e log_e]; cbn.
    destruct Hok as [Heq Hwl Hpa Hdb]; cbn in *.
    split.
    { constructor; cbn; auto. }
    split; [intros j; split; intros [Hwf Hex Ha Hr]; constructor; cbn in *; auto|].
    split; [reflexivity | exact Hwl].
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
    destruct Hok as [Heq Hwl Hpa Hdb].
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
                                      e'.(equiv).(parent)))
                     /\ (forall y, Sep.has_key y e.(equiv).(parent)
                                   <-> Sep.has_key y e'.(equiv).(parent))).
    { destruct (map.get e.(equiv).(parent) x) as [px|] eqn:Hgx.
      - assert (Hkx : Sep.has_key x e.(equiv).(parent)).
        { unfold Sep.has_key. rewrite Hgx. exact I. }
        pose proof (@find_spec _ _ _ _ _ _ _ default lt_trans_nat
                      _ _ _ _ _ Huf_l Hkx Hfind) as Hspec.
        destruct Hspec as (Huf'_l & _ & _ & _ & Hlim_iff & Hkey_iff).
        subst e'; cbn.
        split; [exact Huf'_l|]. split; [exact Hlim_iff|exact Hkey_iff].
      - rewrite (find_no_key_identity e x Hgx) in Hfind.
        injection Hfind; intros; subst uf' v'.
        subst e'; cbn.
        split; [exact Huf_l|].
        split; [intros i j; reflexivity | intros y; reflexivity]. }
    destruct Hcommon as (Huf'_l & Hlim_iff & Hkey_iff).
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
        + unfold atom_in_egraph in *; cbn in *. exact Ha_aa.
      - subst e'; cbn.
        intros a Ha.
        destruct (Hdb _ Ha) as [Hargs Hret].
        split; [|apply Hkey_iff; exact Hret].
        eapply all_wkn; [|exact Hargs]; intros; apply Hkey_iff; assumption. }
    split; [exact Hok_e'|].
    intros j; split; intros Hd.
    - apply (Hiff j). split; [|exact Hd]. constructor; auto.
      exists roots; exact Huf_l.
    - destruct (proj2 (Hiff j) (conj Hok_e' Hd)) as [_ Hde]. exact Hde.
  Qed.

  (* [canonicalize_worklist_entry] on a [union_repair] entry calls
     [find] on its [new_idx]; the [analysis_repair] case is a [Mret].
     Both preserve [egraph_ok] and [denote], and a [worklist_entry_ok]
     input remains [worklist_entry_ok] in the post-state's equiv (the
     output entry is [union_repair old new' _] where [new ~ new'] in
     the post equiv, transitively giving [old ~ new']). *)
  Lemma canonicalize_worklist_entry_denote_iff a
    : vc (canonicalize_worklist_entry idx Eqb_idx symbol
            symbol_map idx_map idx_trie analysis_result a)
        (fun e res =>
           egraph_ok e ->
           worklist_entry_ok e.(equiv) a ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ equiv_extends e (snd res)
           /\ worklist_entry_ok (snd res).(equiv) (fst res)).
  Proof.
    unfold canonicalize_worklist_entry.
    destruct a as [old new improved | i_repair]; cbn beta iota.
    - eapply vc_bind;
        [ apply (vc_and _ _ _ (find_denote_iff new) (find_preserves_fields_strong new)) |].
      cbn beta. cbn [fst snd].
      intros e v_e.
      unfold vc, Mret, StateMonad.state_monad.
      intros e1 [Hde Hpf] Hok Hwl_pre.
      cbn beta iota. cbn [fst snd] in *.
      destruct (Hde Hok) as [Hok_e1 Hde_e1].
      pose proof Hok as Hok_orig.
      destruct Hok as [Hex_e _ _].
      specialize (Hpf Hex_e).
      cbn in Hwl_pre.
      assert (Hkey_new : Sep.has_key new e.(equiv).(parent)).
      { destruct Hex_e as [roots Huf]; pose proof Huf as Huf_l.
        destruct (uf_rel_PER_has_key _ _ _ _ Huf_l Hwl_pre) as [_ Hk].
        exact Hk. }
      specialize (Hpf Hkey_new).
      destruct Hpf as (Hex_e1 & Hf01 & Huf_v_new).
      destruct Hf01 as (_ & _ & _ & _ & _ & Hkey_iff & Hper_iff).
      split; [exact Hok_e1|].
      split; [exact Hde_e1|].
      split; [intros x y Hxy; apply Hper_iff; exact Hxy|].
      cbn.
      assert (Holdnew_e1 : uf_rel_PER e1.(equiv) old new)
        by (apply Hper_iff; exact Hwl_pre).
      unfold uf_rel_PER in *.
      eapply PER_clo_trans; [exact Holdnew_e1|].
      apply PER_clo_sym; exact Huf_v_new.
    - unfold vc, Mret, StateMonad.state_monad; cbn [fst snd].
      intros e Hok _; split; [exact Hok|].
      split; [intros i; reflexivity|].
      split; [apply equiv_extends_refl | cbn; exact I].
  Qed.

  (* Convert an [all2] with constant left predicate to [all]. *)
  Lemma all2_const_to_all_l A B (P : A -> Prop) (l1 : list A) (l2 : list B) :
    all2 (fun a _ => P a) l1 l2 -> all P l1.
  Proof.
    revert l2; induction l1 as [|h t IH]; destruct l2 as [|x xs]; cbn;
      try contradiction; auto.
    intros [Hh Ht]; split; [exact Hh | apply (IH _ Ht)].
  Qed.

  (* [worklist_dedup] returns a subset of its input, so any [all]
     predicate transports to the dedup. *)
  Lemma worklist_dedup_preserves_all (P : worklist_entry idx -> Prop) l :
    all P l -> all P (worklist_dedup _ _ l).
  Proof.
    induction l as [|h t IH]; cbn; auto.
    intros [Hh Ht].
    destruct (List.existsb (entry_subsumed_by idx Eqb_idx h)
                (worklist_dedup _ _ t)).
    - apply IH; exact Ht.
    - cbn; split; [exact Hh | apply IH; exact Ht].
  Qed.

  (* List-iterated [canonicalize_worklist_entry] preserves [egraph_ok]
     and [denote] pointwise, AND if every input entry was
     [worklist_entry_ok] in the pre-state's equiv, every output entry
     is [worklist_entry_ok] in the post-state's equiv. *)
  Lemma list_Mmap_canonicalize_worklist_entry_denote_iff l
    : vc (list_Mmap
            (canonicalize_worklist_entry idx Eqb_idx symbol
               symbol_map idx_map idx_trie analysis_result) l)
        (fun e res =>
           egraph_ok e ->
           all (worklist_entry_ok e.(equiv)) l ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ equiv_extends e (snd res)
           /\ all (worklist_entry_ok (snd res).(equiv)) (fst res)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_outputs _
                  (fun l s => egraph_ok s
                              /\ all (worklist_entry_ok s.(equiv)) l)
                  (fun s s' => (forall i, denote s i <-> denote s' i)
                               /\ equiv_extends s s')
                  (fun s b _ => worklist_entry_ok s.(equiv) b))].
    - cbn beta. intros e res Hinv Hok Hwl.
      destruct (Hinv (conj Hok Hwl)) as ((Hok_p & _) & (Hiff & Hext) & Hall_out).
      split; [exact Hok_p|].
      split; [exact Hiff|].
      split; [exact Hext|].
      eapply all2_const_to_all_l; exact Hall_out.
    - intros s _; split; [intros i; reflexivity | apply equiv_extends_refl].
    - intros ? ? ? [H1 He1] [H2 He2]; split;
        [intros i; rewrite H1; auto | eapply equiv_extends_trans; eauto].
    - intros s s' b _a [_ Hext] Hwl.
      destruct b as [old new improved | i_repair]; cbn in *; auto.
    - intros a l_rest.
      eapply vc_consequence;
        [| apply (canonicalize_worklist_entry_denote_iff a)].
      cbn beta. intros s p Hone (Hok & Hwl).
      cbn [all] in Hwl. destruct Hwl as [Hwl_a Hwl_rest].
      destruct (Hone Hok Hwl_a) as (Hok_p & Hde_p & Hext_p & Hwlok_p).
      split; [split; [exact Hok_p|]|].
      + eapply all_wkn; [|exact Hwl_rest].
        intros ent _ Hent.
        eapply equiv_extends_worklist_entry_ok; [exact Hext_p | exact Hent].
      + split; [split; [exact Hde_p | exact Hext_p] | exact Hwlok_p].
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
    - destruct Hok as [_ _ Hpa _]. eapply Hpa; exact Hg.
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
    destruct Hok as [Heq Hwl Hpa Hdb].
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
           /\ (snd res).(equiv) = e.(equiv)
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
    split; [exact Hequiv_eq|].
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
    destruct Hok as [Heq Hwl Hpa Hdb].
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

  Lemma union_after_canonicalize_denote_iff
    a a' side_l (e_ref e0 : instance) (r : idx)
    : egraph_ok e_ref ->
      atom_in_egraph_up_to_equiv a e_ref ->
      all (fun a' => atom_in_egraph_up_to_equiv a' e_ref) side_l ->
      post_db_remove e_ref a e0 ->
      (* New: every entry literally at the removed key has a ret
         PER-related to [atom_ret a].  Established by the prepended
         [repair_each] union step. *)
      (forall r0, atom_in_db (Build_atom (atom_fn a) (atom_args a) r0)
                             e_ref.(db) ->
                  uf_rel_PER e_ref.(equiv) r0 (atom_ret a)) ->
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
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) side_l
           /\ equiv_extends e_ref (snd res)).
  Proof.
    intros Hok_ref Hatom_ref Hatoms_ref Hpost_dbr Hper_lk.
    unfold Mseq. vc_bind union_sound.
    rename s0 into e1, a0 into u_val.
    unfold vc; cbn [Mret StateMonad.state_monad fst snd].
    intros e_post Hu_lazy
           Hex_e1 Hf01 Hfn_eq Hret_eq Hargs_eq Hain_can.
    (* has_key facts for the union *)
    pose proof Hok_ref as [Heq_ref Hwl_ref Hpa_ref Hdb_ref_init].
    destruct Hpost_dbr as (Hequiv_eq_post & Hpar_eq_post & Hep_eq_post
                           & Hwl_eq_post & Han_eq_post & Hdb_iff_post).
    destruct Hf01 as (Hdb_eq01 & Hpar_eq01 & Hep_eq01 & Hwl_eq01 & Han_eq01
                      & Hkey_iff01 & Hper_iff01).
    (* Hkey_lift_01: e0's has_key lifts to e1 (path compression). *)
    assert (Hain_db_e1 : atom_in_db
                          (Build_atom (atom_fn a') (atom_args a') r) e1.(db))
      by exact Hain_can.
    assert (Hain_db_e0 : atom_in_db
                          (Build_atom (atom_fn a') (atom_args a') r) e0.(db))
      by (rewrite Hdb_eq01 in Hain_db_e1; exact Hain_db_e1).
    apply Hdb_iff_post in Hain_db_e0.
    destruct Hain_db_e0 as [Hain_db_ref _].
    assert (Hkr_e1 : Sep.has_key r e1.(equiv).(parent)).
    { destruct (Hdb_ref_init _ Hain_db_ref) as [_ Hkret].
      cbn in Hkret. apply Hkey_iff01. rewrite Hequiv_eq_post in *. exact Hkret. }
    assert (Hkaret_e1 : Sep.has_key (atom_ret a') e1.(equiv).(parent)).
    { destruct Hex_e1 as [rs1 Huf_e1].
      exact (proj1 (uf_rel_PER_has_key e1.(equiv) rs1 _ _ Huf_e1 Hret_eq)). }
    specialize (Hu_lazy Hex_e1 Hkr_e1 Hkaret_e1).
    destruct Hu_lazy as (Hdb_eqe & Hex_post & Hper_iff_union & Hpar_eqe
                        & Hwl_rel & Hu_ret).
    (* [Hext_e1]: lift e1's PER into post-union PER. *)
    assert (Hext_e1 : forall x1 y1, uf_rel_PER e1.(equiv) x1 y1 ->
                                    uf_rel_PER e_post.(equiv) x1 y1).
    { intros x1 y1 Hxy. apply Hper_iff_union.
      apply PER_clo_base. left. exact Hxy. }
    assert (Hr_aret_post : uf_rel_PER e_post.(equiv) r (atom_ret a')).
    { apply Hper_iff_union. apply PER_clo_base. right.
      split; reflexivity. }
    (* [Hext_ref]: e_ref's PER lifts into post-union PER, through e1's
       PER (which is e0's = e_ref's by [Hequiv_eq_post] and [Hper_iff01]
       which is iff). *)
    assert (Hext_ref : forall x1 y1, uf_rel_PER e_ref.(equiv) x1 y1 ->
                                     uf_rel_PER e_post.(equiv) x1 y1).
    { intros x1 y1 Hxy. apply Hext_e1.
      apply Hper_iff01. rewrite Hequiv_eq_post. exact Hxy. }
    (* [Hkey_lift_e1]: keys in e1 lift to post-union. *)
    assert (Hkey_lift_post : forall j, Sep.has_key j e1.(equiv).(parent) ->
                                       Sep.has_key j e_post.(equiv).(parent)).
    { intros j Hj.
      destruct Hex_post as [rs_post Huf_post].
      assert (Hjj_e1 : uf_rel_PER e1.(equiv) j j).
      { unfold Sep.has_key in Hj.
        destruct (map.get e1.(equiv).(parent) j) as [vj|] eqn:Hgj;
          [|tauto].
        unfold uf_rel_PER.
        eapply PER_clo_trans;
          [apply PER_clo_base; exact Hgj
          |apply PER_clo_sym; apply PER_clo_base; exact Hgj]. }
      exact (proj1 (uf_rel_PER_has_key e_post.(equiv) rs_post j j
                     Huf_post (Hext_e1 _ _ Hjj_e1))). }
    (* [Hkey_back_post]: keys in post-union lift back to e1.  The PER
       closure base elements come from e1's PER or the new singleton;
       [r] and [a'.atom_ret] are both has_key in e1. *)
    assert (Hkey_back_post : forall j,
              Sep.has_key j e_post.(equiv).(parent) ->
              Sep.has_key j e1.(equiv).(parent)).
    { intros j Hj.
      destruct Hex_post as [rs_post Huf_post].
      destruct Hex_e1 as [rs_e1 Huf_e1].
      assert (Hjj_post : uf_rel_PER e_post.(equiv) j j).
      { unfold Sep.has_key in Hj.
        destruct (map.get e_post.(equiv).(parent) j) as [vj|] eqn:Hgj;
          [|tauto].
        unfold uf_rel_PER.
        eapply PER_clo_trans;
          [apply PER_clo_base; exact Hgj
          |apply PER_clo_sym; apply PER_clo_base; exact Hgj]. }
      apply Hper_iff_union in Hjj_post.
      assert (Hclo_key : forall p q,
                union_closure_PER (uf_rel_PER e1.(equiv))
                  (singleton_rel r (atom_ret a')) p q ->
                Sep.has_key p e1.(equiv).(parent)
                /\ Sep.has_key q e1.(equiv).(parent)).
      { intros p q Hpq.
        induction Hpq as [p q Hbase | p q rr _ IH1 _ IH2 | p q _ IH].
        - destruct Hbase as [Hbase | Hsing].
          + apply (uf_rel_PER_has_key _ _ _ _ Huf_e1 Hbase).
          + destruct Hsing as [Heq1 Heq2]; subst.
            split; [exact Hkr_e1 | exact Hkaret_e1].
        - split; [apply IH1 | apply IH2].
        - destruct IH; split; assumption. }
      exact (proj1 (Hclo_key _ _ Hjj_post)). }
    (* [e_post]'s db = e1's db = e0's db; parents unchanged. *)
    assert (Hdb_post_eq_e1 : e1.(db) = e_post.(db)) by exact Hdb_eqe.
    assert (Hpar_post_eq_e1 : e1.(parents) = e_post.(parents))
      by exact Hpar_eqe.
    (* Helper: lift [atom_in_egraph_up_to_equiv b e_ref] to [e_post] by
       case-splitting on whether the witness is at the removed literal
       key.  Used in [parents_ok], the side-list conjunct, and the
       backward direction of [denote_iff]. *)
    assert (Hargs_eq_post : all2 (uf_rel_PER e_post.(equiv))
                                 (atom_args a) (atom_args a')).
    { clear -Hargs_eq Hext_e1.
      revert Hargs_eq. generalize (atom_args a'), (atom_args a).
      intros l1 l2. revert l2.
      induction l1 as [|y ys IH]; destruct l2 as [|z zs];
        cbn; auto; try tauto.
      intros [Hyz Hys]. split.
      - apply Hext_e1. unfold uf_rel_PER in *. apply PER_clo_sym. exact Hyz.
      - apply (IH zs Hys). }
    assert (Hain_can_post : atom_in_db
                              (Build_atom (atom_fn a') (atom_args a') r)
                              e_post.(db)).
    { rewrite <- Hdb_post_eq_e1. exact Hain_can. }
    assert (Hlift : forall b, atom_in_egraph_up_to_equiv b e_ref ->
                              atom_in_egraph_up_to_equiv b e_post).
    { intros b Hbref.
      destruct Hbref as (bb & (Hfn & Hargs & Hret) & Hbb_in).
      destruct bb as [fn_bb args_bb ret_bb]; cbn in *.
      subst fn_bb.
      pose proof (eqb_spec (atom_fn b, args_bb) (atom_fn a, atom_args a))
        as Hkey_eq.
      destruct (eqb (atom_fn b, args_bb) (atom_fn a, atom_args a)).
      { assert (H_fn : atom_fn b = atom_fn a)
          by (apply (f_equal fst) in Hkey_eq; cbn in Hkey_eq; exact Hkey_eq).
        assert (H_args : args_bb = atom_args a)
          by (apply (f_equal snd) in Hkey_eq; cbn in Hkey_eq; exact Hkey_eq).
        clear Hkey_eq. subst args_bb.
        assert (Hain_bb_db : atom_in_db
                              (Build_atom (atom_fn a) (atom_args a) ret_bb)
                              e_ref.(db)).
        { revert Hbb_in. unfold atom_in_egraph, atom_in_db; cbn.
          rewrite H_fn. tauto. }
        pose proof (Hper_lk _ Hain_bb_db) as Hret_bb_aret.
        exists (Build_atom (atom_fn a') (atom_args a') r).
        split; cbn.
        - unfold atom_canonical_equiv; cbn. split; [congruence|]. split.
          + clear -Hargs Hargs_eq_post Hext_ref.
            revert Hargs Hargs_eq_post.
            generalize (atom_args b), (atom_args a), (atom_args a').
            intros l1 l2 l3. revert l2 l3.
            induction l1 as [|y ys IH]; destruct l2 as [|z zs];
              destruct l3 as [|w ws]; cbn; auto; try tauto.
            intros [Hyz Hys] [Hzw Hzs]. split.
            * unfold uf_rel_PER in *.
              eapply PER_clo_trans;
                [apply Hext_ref; exact Hyz | exact Hzw].
            * apply (IH zs ws Hys Hzs).
          + unfold uf_rel_PER in *.
            eapply PER_clo_trans;
              [apply Hext_ref; exact Hret |].
            eapply PER_clo_trans;
              [apply Hext_ref; exact Hret_bb_aret|].
            eapply PER_clo_trans;
              [apply Hext_e1; apply PER_clo_sym; exact Hret_eq |].
            apply PER_clo_sym; exact Hr_aret_post.
        - exact Hain_can_post. }
      { exists (Build_atom (atom_fn b) args_bb ret_bb).
        split; cbn.
        - unfold atom_canonical_equiv; cbn. split; [reflexivity|]. split.
          + clear -Hargs Hext_ref.
            revert Hargs. generalize (atom_args b), args_bb.
            intros l1 l2. revert l2.
            induction l1 as [|y ys IH]; destruct l2 as [|z zs];
              cbn; auto; try tauto.
            intros [Hyz Hys]. split;
              [apply Hext_ref; exact Hyz | apply IH; exact Hys].
          + apply Hext_ref; exact Hret.
        - assert (Hbb_in_e0 : atom_in_db
                                (Build_atom (atom_fn b) args_bb ret_bb)
                                e0.(db)).
          { apply Hdb_iff_post.
            split; [exact Hbb_in|].
            cbn. intros Heq. apply Hkey_eq. exact Heq. }
          unfold atom_in_egraph.
          rewrite <- Hdb_post_eq_e1, Hdb_eq01. exact Hbb_in_e0. } }
    (* The proof's main split: egraph_ok, denote_iff, side-list,
       equiv_extends. *)
    split.
    { (* egraph_ok e_post *)
      constructor.
      - (* equiv_ok *) exact Hex_post.
      - (* worklist_ok *)
        destruct Hwl_rel as [Hwl_unchanged
                            | (v_old & v' & ar & Hwl_new & Hv_old & Hv')].
        + rewrite Hwl_unchanged, Hwl_eq01, Hwl_eq_post.
          eapply all_wkn; [|exact Hwl_ref].
          intros [old new improved | k] _ Hent; cbn in *.
          * apply Hext_ref. exact Hent.
          * exact I.
        + rewrite Hwl_new, Hwl_eq01, Hwl_eq_post.
          cbn. split.
          * unfold uf_rel_PER in *.
            eapply PER_clo_trans; [exact Hv_old |].
            eapply PER_clo_trans; [exact Hr_aret_post|].
            apply PER_clo_sym; exact Hv'.
          * eapply all_wkn; [|exact Hwl_ref].
            intros [old new improved | k] _ Hent; cbn in *.
            -- apply Hext_ref. exact Hent.
            -- exact I.
      - (* parents_ok: parents unchanged via Hpar_eq01 + Hpar_eq_post
           + Hpar_eqe; lift atom_in_egraph_up_to_equiv via PER + db
           preservation. *)
        intros x s Hgs.
        rewrite <- Hpar_post_eq_e1 in Hgs.
        rewrite Hpar_eq01 in Hgs.
        rewrite Hpar_eq_post in Hgs.
        eapply all_wkn; [|apply (Hpa_ref _ _ Hgs)].
        intros b _ Hbain. apply Hlift. exact Hbain.
      - (* db_idxs_in_equiv *)
        intros b Hbain.
        rewrite <- Hdb_post_eq_e1 in Hbain.
        rewrite Hdb_eq01 in Hbain.
        apply Hdb_iff_post in Hbain. destruct Hbain as [Hbain _].
        destruct (Hdb_ref_init _ Hbain) as [Hargs_keys Hret_key].
        split.
        + eapply all_wkn; [|exact Hargs_keys]; intros j _ Hj.
          apply Hkey_lift_post. apply Hkey_iff01.
          rewrite Hequiv_eq_post. exact Hj.
        + apply Hkey_lift_post. apply Hkey_iff01.
          rewrite Hequiv_eq_post. exact Hret_key.
    }
    split.
    { (* denote_iff e_ref e_post *)
      intros i. split.
      { (* Forward: e_ref sound → e_post sound. *)
        intros [Hwf Hexact Hatom_e Hrel_e].
        constructor.
        - exact Hwf.
        - intros x Hx. apply Hkey_lift_post. apply Hkey_iff01.
          rewrite Hequiv_eq_post. apply Hexact. exact Hx.
        - intros b Hbain. apply Hatom_e.
          unfold atom_in_egraph in *.
          rewrite <- Hdb_post_eq_e1, Hdb_eq01 in Hbain.
          apply Hdb_iff_post in Hbain. exact (proj1 Hbain).
        - intros i1 i2 Hi12.
          apply Hper_iff_union in Hi12.
          induction Hi12 as [p q Hbase | p q rr _ IH1 _ IH2 | p q _ IH].
          + destruct Hbase as [Hbase | Hsing].
            * (* PER pair in e1.equiv = e_ref.equiv *)
              apply Hrel_e. apply Hper_iff01 in Hbase.
              rewrite Hequiv_eq_post in Hbase. exact Hbase.
            * destruct Hsing as [Hpr Hqaret]; subst.
              (* Need: eq_sound (i r) (i a'.atom_ret) *)
              destruct Hatom_ref as
                (aa & (Hfn_aa & Hargs_aa & Hret_aa) & Hain_aa).
              destruct aa as [fn_aa args_aa ret_aa]; cbn in *.
              subst fn_aa.
              pose proof (Hatom_e _ Hain_db_ref) as Hsa_can.
              pose proof (Hatom_e _ Hain_aa) as Hsa_aa.
              cbn in Hsa_can, Hsa_aa.
              (* args_aa ~PER~ atom_args a' in e_ref.equiv (chain via a) *)
              assert (Hargs_aa_a' :
                all2 (eq_sound_for_model m i) args_aa (atom_args a')).
              { clear -Hargs_aa Hargs_eq Hper_iff01 Hequiv_eq_post Hrel_e.
                revert Hargs_aa Hargs_eq.
                generalize (atom_args a), args_aa, (atom_args a').
                intros l1 l2 l3. revert l2 l3.
                induction l1 as [|y ys IH]; destruct l2 as [|z zs];
                  destruct l3 as [|w ws]; cbn; auto; try tauto.
                intros [Hyz Hys] [Hwy Hws]. split.
                - apply Hrel_e. unfold uf_rel_PER in *.
                  apply Hper_iff01 in Hwy. rewrite Hequiv_eq_post in Hwy.
                  eapply PER_clo_trans;
                    [apply PER_clo_sym; exact Hyz | apply PER_clo_sym; exact Hwy].
                - apply (IH zs ws Hys Hws). }
              rewrite Hfn_eq in Hsa_can.
              pose proof (atom_sound_eq_ret i (atom_fn a)
                            args_aa (atom_args a')
                            ret_aa r
                            Hsa_aa Hsa_can Hargs_aa_a') as Hret_aa_r.
              (* And ret_aa ~PER~ a.ret ~PER~ a'.ret -> i ret_aa ~_d i a'.ret *)
              assert (Hret_aa_a' :
                eq_sound_for_model m i ret_aa (atom_ret a')).
              { apply Hrel_e. apply Hper_iff01 in Hret_eq.
                rewrite Hequiv_eq_post in Hret_eq.
                unfold uf_rel_PER in *.
                eapply PER_clo_trans;
                  [apply PER_clo_sym; exact Hret_aa
                  | apply PER_clo_sym; exact Hret_eq]. }
              eapply eq_sound_for_model_trans;
                [apply eq_sound_for_model_Symmetric; exact Hret_aa_r |].
              exact Hret_aa_a'.
          + eapply eq_sound_for_model_trans; eauto.
          + apply eq_sound_for_model_Symmetric; exact IH. }
      { (* Backward: e_post sound → e_ref sound. *)
        intros [Hwf Hexact Hatom_e Hrel_e].
        constructor.
        - exact Hwf.
        - intros x Hx.
          (* has_key x e_ref.equiv ← has_key x e_post.equiv via Hkey_back_post *)
          rewrite <- Hequiv_eq_post. apply Hkey_iff01.
          apply Hkey_back_post. apply Hexact. exact Hx.
        - intros b Hbain.
          (* atoms in e_ref.db: if at removed key, use canonical entry's
             soundness + eq_atom_implies_sound_l_active. *)
          pose proof (eqb_spec (atom_fn b, atom_args b)
                              (atom_fn a, atom_args a)) as Hkey_eq.
          destruct (eqb (atom_fn b, atom_args b) (atom_fn a, atom_args a)).
          + (* b at removed key *)
            assert (H_fn : atom_fn b = atom_fn a)
              by (apply (f_equal fst) in Hkey_eq; cbn in Hkey_eq;
                  exact Hkey_eq).
            assert (H_args : atom_args b = atom_args a)
              by (apply (f_equal snd) in Hkey_eq; cbn in Hkey_eq;
                  exact Hkey_eq).
            (* b = (atom_fn a, atom_args a, atom_ret b).  By Hper_lk: atom_ret b
               ~PER~ atom_ret a in e_ref.equiv. *)
            assert (Hain_b_db_ref : atom_in_db
                                      (Build_atom (atom_fn a) (atom_args a)
                                                  (atom_ret b))
                                      e_ref.(db)).
            { revert Hbain. unfold atom_in_egraph, atom_in_db; cbn.
              rewrite H_fn, H_args. tauto. }
            pose proof (Hper_lk _ Hain_b_db_ref) as Hretb_aret.
            (* The canonical entry (a'.fn, a'.args, r) is in e_post.db, sound *)
            pose proof (Hatom_e _ Hain_can_post) as Hsa_can_post.
            cbn in Hsa_can_post.
            (* Use eq_atom_implies_sound_l_active to transport. *)
            apply (eq_atom_implies_sound_l_active i
                     (Build_atom (atom_fn a') (atom_args a') r)).
            * unfold eq_atom_in_interpretation; cbn.
              split; [rewrite Hfn_eq; symmetry; exact H_fn|]. split.
              { (* args eq_sound: atom_args a' ~PER~ atom_args a (= atom_args b)
                   in e_post.equiv → eq_sound via Hrel_e. *)
                rewrite H_args.
                clear -Hargs_eq Hext_e1 Hrel_e.
                revert Hargs_eq.
                generalize (atom_args a'), (atom_args a).
                intros l1 l2. revert l2.
                induction l1 as [|y ys IH]; destruct l2 as [|z zs];
                  cbn; auto; try tauto.
                intros [Hyz Hys]. split.
                - apply Hrel_e. apply Hext_e1. exact Hyz.
                - apply IH; exact Hys. }
              { (* ret eq_sound: r ~PER~ a'.ret in e_post.equiv via union pair;
                   chain through atom_ret a via Hret_eq + Hretb_aret. *)
                apply Hrel_e. unfold uf_rel_PER in *.
                eapply PER_clo_trans;
                  [exact Hr_aret_post|].
                eapply PER_clo_trans;
                  [apply Hext_e1; exact Hret_eq|].
                apply PER_clo_sym. apply Hext_ref. exact Hretb_aret. }
            * exact Hsa_can_post.
          + (* b at different key: still in e_post.db *)
            assert (Hbain_e0 : atom_in_db b e0.(db)).
            { apply Hdb_iff_post. split; [exact Hbain|].
              cbn. intros Heq. apply Hkey_eq. exact Heq. }
            apply Hatom_e.
            unfold atom_in_egraph.
            rewrite <- Hdb_post_eq_e1, Hdb_eq01. exact Hbain_e0.
        - intros i1 i2 Hi12.
          apply Hrel_e. apply Hext_ref. exact Hi12. } }
    split.
    { (* all atom_in_egraph_up_to_equiv e_post side_l *)
      eapply all_wkn; [|exact Hatoms_ref].
      intros b _ Hb. apply Hlift. exact Hb. }
    (* equiv_extends e_ref e_post *)
    unfold equiv_extends. intros x1 y1 Hxy. apply Hext_ref. exact Hxy.
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
    destruct Hok as [Heq Hwl Hpa Hdb]; cbn in *.
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
    destruct Hok as [Heq Hwl Hpa Hdb]; cbn in *.
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
    vc_list_Mmap_egraph_iff get_analysis_denote_iff.
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

  (* Helper: [get_analysis] only ever adds [analysis_repair] entries to
     the worklist; existing entries are preserved.  Used to lift
     worklist_ok across [get_analyses]. *)
  Lemma get_analysis_worklist_extends x
    : vc (get_analysis idx symbol symbol_map idx_map idx_trie analysis_result x)
        (fun e res =>
           exists new_ents,
             (snd res).(worklist) = new_ents ++ e.(worklist)
             /\ all (fun ent => exists i, ent = analysis_repair _ i) new_ents).
  Proof.
    unfold vc, get_analysis; intros e.
    destruct (map.get e.(analyses) x) as [a|] eqn:Hga.
    - cbn [fst snd]. exists []. split; [reflexivity | exact I].
    - cbn [Mseq Mbind StateMonad.state_monad fst snd].
      unfold update_analyses, push_worklist; cbn.
      exists [analysis_repair _ x]. split; [reflexivity |].
      cbn. split; [eexists; reflexivity | exact I].
  Qed.

  (* Characterization of how [fold_left] with [map_update] + [cons a]
     transforms the [parents] map: at every index, the new list is
     either the same as before, or has [a] prepended (possibly multiple
     times). In either case, every entry in the new list is either [a]
     itself or was in the old list. *)
  Lemma all_via_in_local {A} (P : A -> Prop) l
    : (forall x, In x l -> P x) -> all P l.
  Proof.
    induction l as [|a rest IH]; cbn; intros HH.
    - exact I.
    - split.
      + apply HH. left. reflexivity.
      + apply IH. intros x Hx. apply HH. right. exact Hx.
  Qed.

  (* Helper specialized for default = []: the "default" list when no
     entry exists is empty.  We pass the WithDefault instance explicitly
     to avoid typeclass-resolution surprises. *)
  Lemma fold_left_cons_map_update_get
    {V} (l : list idx) (a : V) :
    forall (mp : idx_map (list V)) x s,
      map.get (fold_left
                 (fun m x => @map_update _ _ (@nil V)
                                _ m x (cons a)) l mp) x = Some s ->
      forall v, In v s -> v = a \/ (exists s_old, map.get mp x = Some s_old /\ In v s_old).
  Proof.
    induction l as [|y ys IH]; cbn; intros mp x s Hg v Hin.
    - right. exists s. split; [exact Hg | exact Hin].
    - pose proof (IH _ _ _ Hg v Hin) as IHapplied. clear Hg Hin.
      destruct IHapplied as [Hva | (s_old & Hgs_old & Hvin_old)].
      + left. exact Hva.
      + unfold map_update in Hgs_old.
        destruct (map.get mp y) as [s_y|] eqn:Hg_mpy.
        * eqb_case x y.
          -- rewrite map.get_put_same in Hgs_old. injection Hgs_old as <-.
             cbn in Hvin_old. destruct Hvin_old as [Hva | Hvin'].
             ++ left. symmetry. exact Hva.
             ++ right. exists s_y. split; [exact Hg_mpy | exact Hvin'].
          -- rewrite map.get_put_diff in Hgs_old by auto.
             right. exists s_old. split; [exact Hgs_old | exact Hvin_old].
        * eqb_case x y.
          -- rewrite map.get_put_same in Hgs_old. injection Hgs_old as <-.
             cbn in Hvin_old. destruct Hvin_old as [Hva | Hvin'].
             ++ left. symmetry. exact Hva.
             ++ cbn in Hvin'. contradiction.
          -- rewrite map.get_put_diff in Hgs_old by auto.
             right. exists s_old. split; [exact Hgs_old | exact Hvin_old].
  Qed.

  Lemma get_analyses_worklist_extends args
    : vc (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result args)
        (fun e res =>
           exists new_ents,
             (snd res).(worklist) = new_ents ++ e.(worklist)
             /\ all (fun ent => exists i, ent = analysis_repair _ i) new_ents).
  Proof.
    unfold get_analyses.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_inv _
                  (fun _ _ => True)
                  (fun s s' =>
                     exists new_ents,
                       s'.(worklist) = new_ents ++ s.(worklist)
                       /\ all (fun ent => exists i, ent = analysis_repair _ i) new_ents))].
    - cbn beta. intros s res Hinv. exact (proj2 (Hinv I)).
    - intros s _. exists []. split; [reflexivity | exact I].
    - intros s1 s2 s3 (l1 & H1 & Hp1) (l2 & H2 & Hp2).
      exists (l2 ++ l1). rewrite H2, H1. rewrite app_assoc. split; [reflexivity|].
      clear -Hp1 Hp2. induction l2; cbn; auto. destruct Hp2; split; auto.
    - intros x xs.
      eapply vc_consequence; [| apply (get_analysis_worklist_extends x)].
      cbn beta. intros s p Hone _. split; [exact I | exact Hone].
  Qed.

  Lemma db_set_after_canonicalize_denote_iff
    a a' side_l (e_ref e0 : instance)
    : egraph_ok e_ref ->
      atom_in_egraph_up_to_equiv a e_ref ->
      all (fun a' => atom_in_egraph_up_to_equiv a' e_ref) side_l ->
      post_db_remove e_ref a e0 ->
      (* New: same PER fact as in [union_after_canonicalize_denote_iff]. *)
      (forall r0, atom_in_db (Build_atom (atom_fn a) (atom_args a) r0)
                             e_ref.(db) ->
                  uf_rel_PER e_ref.(equiv) r0 (atom_ret a)) ->
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
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) side_l
           /\ equiv_extends e_ref (snd res)).
  Proof.
    (* Bring the [map_default] instance from Defs.v into typeclass scope
       so [map_update]'s implicit [WithDefault] resolves. *)
    Local Instance WithDefault_map_local {K V} `{m : map.map K V} : WithDefault m
      := map.empty.
    intros Hok_ref Hatom_ref Hatoms_ref Hpost_dbr Hper_lk.
    unfold db_set, vc; cbn [Mbind StateMonad.state_monad fst snd].
    intros e1 Hex_e1 Hf01 Hfn_eq Hret_eq Hargs_eq Hno_can.
    (* Decompose hypotheses. *)
    pose proof Hok_ref as Hok_ref_orig.
    pose proof Hok_ref as [Heq_ref Hwl_ref Hpa_ref Hdb_ref_init].
    destruct Hpost_dbr as (Hequiv_eq_post & Hpar_eq_post & Hep_eq_post
                           & Hwl_eq_post & Han_eq_post & Hdb_iff_post).
    destruct Hf01 as (Hdb_eq01 & Hpar_eq01 & Hep_eq01 & Hwl_eq01 & Han_eq01
                      & Hkey_iff01 & Hper_iff01).
    (* === Step 1: get_analyses preserves db/equiv/parents. === *)
    pose proof (get_analyses_preserves_fields (atom_args a') e1) as Hgaf.
    destruct (get_analyses idx symbol symbol_map idx_map idx_trie
                analysis_result (atom_args a') e1) as [arg_as e_g] eqn:Hge.
    cbn [fst snd] in Hgaf.
    destruct Hgaf as (Hdb_g & Heq_g & Hpa_g).
    set (out_a := analyze idx symbol analysis_result a' arg_as).
    (* === Step 2: update_analyses preserves all fields except analyses.
       Destructure manually. === *)
    destruct (update_analyses idx symbol symbol_map idx_map idx_trie
                analysis_result (atom_ret a') out_a e_g) as [_u e_u] eqn:Hue.
    assert (Hdb_u_g : e_u.(db) = e_g.(db))
      by (unfold update_analyses in Hue; injection Hue as _ Hueq;
          subst e_u; reflexivity).
    assert (Heq_u_g : e_u.(equiv) = e_g.(equiv))
      by (unfold update_analyses in Hue; injection Hue as _ Hueq;
          subst e_u; reflexivity).
    assert (Hpa_u_g : e_u.(parents) = e_g.(parents))
      by (unfold update_analyses in Hue; injection Hue as _ Hueq;
          subst e_u; reflexivity).
    cbn [fst snd] in *.
    (* Combine field equalities back to e1. *)
    assert (Hdb_ue1 : e_u.(db) = e1.(db)) by congruence.
    assert (Heq_ue1 : e_u.(equiv) = e1.(equiv)) by congruence.
    assert (Hpa_ue1 : e_u.(parents) = e1.(parents)) by congruence.
    (* === Step 3: db_set'. Destructure. === *)
    destruct (db_set' idx Eqb_idx symbol symbol_map idx_map idx_trie
                analysis_result a' out_a e_u) as [_v e_post] eqn:Hde.
    cbn [fst snd] in *.
    (* Extract e_post's field equalities from Hde. *)
    assert (Heq_post_u : e_post.(equiv) = e_u.(equiv))
      by (unfold db_set' in Hde; injection Hde as _ Hdeq;
          subst e_post; reflexivity).
    assert (Hep_post_u : e_post.(epoch) = e_u.(epoch))
      by (unfold db_set' in Hde; injection Hde as _ Hdeq;
          subst e_post; reflexivity).
    assert (Hwl_post_u : e_post.(worklist) = e_u.(worklist))
      by (unfold db_set' in Hde; injection Hde as _ Hdeq;
          subst e_post; reflexivity).
    assert (Heq_post_e1 : e_post.(equiv) = e1.(equiv)) by congruence.
    (* Bridge PER and key-set iffs between e_ref and e_post. *)
    assert (Hper_iff_post : forall x y,
              uf_rel_PER e_ref.(equiv) x y <-> uf_rel_PER e_post.(equiv) x y).
    { intros x y. rewrite Heq_post_e1.
      rewrite <- (Hper_iff01 x y). rewrite Hequiv_eq_post. reflexivity. }
    assert (Hkey_iff_post : forall y,
              Sep.has_key y e_ref.(equiv).(parent)
              <-> Sep.has_key y e_post.(equiv).(parent)).
    { intros y. rewrite Heq_post_e1.
      rewrite <- (Hkey_iff01 y). rewrite Hequiv_eq_post. reflexivity. }
    (* has_key facts for the new canonical entry's idxs (a'.args, a'.ret). *)
    assert (Hkargs_a' : all (fun i => Sep.has_key i e_post.(equiv).(parent))
                             a'.(atom_args)).
    { rewrite Heq_post_e1.
      destruct Hex_e1 as [roots Huf]. revert Hargs_eq.
      generalize (atom_args a'), (atom_args a). intros l1 l2. revert l2.
      induction l1 as [|y ys IH]; destruct l2 as [|z zs]; cbn; auto; try tauto.
      intros [Hyz Hys]. split.
      - exact (proj1 (uf_rel_PER_has_key e1.(equiv) roots y z Huf Hyz)).
      - apply (IH zs Hys). }
    assert (Hkret_a' : Sep.has_key a'.(atom_ret) e_post.(equiv).(parent)).
    { rewrite Heq_post_e1. destruct Hex_e1 as [roots Huf].
      exact (proj1 (uf_rel_PER_has_key e1.(equiv) roots _ _ Huf Hret_eq)). }
    (* The new canonical entry is in e_post.db. *)
    assert (Hain_can_post : atom_in_db
                              (Build_atom a'.(atom_fn) a'.(atom_args) a'.(atom_ret))
                              e_post.(db)).
    { unfold db_set' in Hde; injection Hde as _ Hdeq; subst e_post.
      unfold atom_in_db, Is_Some_satisfying, map_update; cbn.
      destruct (map.get e_u.(db) a'.(atom_fn)) as [tbl|] eqn:Htbl;
        rewrite map.get_put_same; cbn; rewrite map.get_put_same; reflexivity. }
    (* Hain_old: any atom in e_u.db whose key isn't the canonical key
       survives in e_post.db. *)
    assert (Hain_old : forall b, atom_in_db b e_u.(db) ->
                                 (atom_fn b, atom_args b)
                                 <> (atom_fn a', atom_args a') ->
                                 atom_in_db b e_post.(db)).
    { intros b Hbu Hneq.
      unfold db_set' in Hde; injection Hde as _ Hdeq; subst e_post.
      unfold atom_in_db, Is_Some_satisfying, map_update; cbn.
      destruct b as [bfn bargs bret]; cbn in *.
      destruct (map.get e_u.(db) a'.(atom_fn)) as [tbl|] eqn:Htbl;
        eqb_case bfn a'.(atom_fn).
      - rewrite map.get_put_same.
        unfold atom_in_db, Is_Some_satisfying in Hbu; cbn in Hbu.
        rewrite Htbl in Hbu. cbn in Hbu.
        eqb_case bargs a'.(atom_args); cbn.
        + exfalso. apply Hneq. reflexivity.
        + rewrite map.get_put_diff by auto. exact Hbu.
      - rewrite map.get_put_diff by auto.
        unfold atom_in_db, Is_Some_satisfying in Hbu; cbn in Hbu. exact Hbu.
      - rewrite map.get_put_same.
        unfold atom_in_db, Is_Some_satisfying in Hbu; cbn in Hbu.
        rewrite Htbl in Hbu. cbn in Hbu. destruct Hbu.
      - rewrite map.get_put_diff by auto.
        unfold atom_in_db, Is_Some_satisfying in Hbu; cbn in Hbu. exact Hbu. }
    (* Hain_post_split: any atom in e_post.db is either the new canonical
       entry, or was in e_u.db with a different key. *)
    assert (Hain_post_split : forall b, atom_in_db b e_post.(db) ->
              b = Build_atom a'.(atom_fn) a'.(atom_args) a'.(atom_ret)
              \/ (atom_in_db b e_u.(db)
                  /\ (atom_fn b, atom_args b)
                     <> (atom_fn a', atom_args a'))).
    { intros b Hb.
      unfold db_set' in Hde; injection Hde as _ Hdeq; subst e_post.
      unfold atom_in_db, Is_Some_satisfying, map_update in Hb; cbn in Hb.
      destruct b as [bfn bargs bret]; cbn in Hb.
      destruct (map.get e_u.(db) a'.(atom_fn)) as [tbl|] eqn:Htbl;
        eqb_case bfn a'.(atom_fn).
      - rewrite map.get_put_same in Hb; cbn in Hb.
        eqb_case bargs a'.(atom_args).
        + rewrite map.get_put_same in Hb; cbn in Hb. left. subst. reflexivity.
        + rewrite map.get_put_diff in Hb by auto.
          right. split.
          * unfold atom_in_db, Is_Some_satisfying; cbn.
            rewrite Htbl. cbn. exact Hb.
          * cbn. intros Habs; inversion Habs; contradiction.
      - rewrite map.get_put_diff in Hb by auto.
        right. split.
        + unfold atom_in_db, Is_Some_satisfying; cbn. exact Hb.
        + cbn. intros Habs; inversion Habs; contradiction.
      - rewrite map.get_put_same in Hb; cbn in Hb.
        eqb_case bargs a'.(atom_args).
        + rewrite map.get_put_same in Hb; cbn in Hb. left. subst. reflexivity.
        + rewrite map.get_put_diff in Hb by auto.
          unfold default in Hb.
          rewrite map.get_empty in Hb. cbn in Hb. destruct Hb.
      - rewrite map.get_put_diff in Hb by auto.
        right. split.
        + unfold atom_in_db, Is_Some_satisfying; cbn. exact Hb.
        + cbn. intros Habs; inversion Habs; contradiction. }
    (* Extract the witness aa for atom_in_egraph_up_to_equiv a e_ref. *)
    pose proof Hatom_ref as Hatom_ref_orig.
    destruct Hatom_ref as (aa & Hcan_aa & Hain_aa).
    unfold atom_canonical_equiv in Hcan_aa.
    destruct Hcan_aa as (Hfn_aa & Hargs_aa & Hret_aa).
    destruct aa as [fn_aa args_aa ret_aa]; cbn in *.
    subst fn_aa.
    (* Args lift e_ref → e_post via Hper_iff_post. *)
    assert (Hargs_eq_post : all2 (uf_rel_PER e_post.(equiv))
                                 (atom_args a) (atom_args a')).
    { revert Hargs_eq. generalize (atom_args a'), (atom_args a).
      intros l1 l2. revert l2.
      induction l1 as [|y ys IH]; destruct l2 as [|z zs];
        cbn; auto; try tauto.
      intros [Hyz Hys]. split.
      - rewrite Heq_post_e1. unfold uf_rel_PER in *.
        apply PER_clo_sym. exact Hyz.
      - apply (IH zs Hys). }
    (* Hlift: lift atom_in_egraph_up_to_equiv from e_ref to e_post. *)
    assert (Hlift : forall b, atom_in_egraph_up_to_equiv b e_ref ->
                              atom_in_egraph_up_to_equiv b e_post).
    { intros b Hbref.
      destruct Hbref as (bb & (Hfn_bb & Hargs_bb & Hret_bb) & Hain_bb).
      destruct bb as [fn_bb args_bb ret_bb]; cbn in Hfn_bb, Hargs_bb, Hret_bb.
      subst fn_bb.
      pose proof (eqb_spec (atom_fn b, args_bb) (atom_fn a, atom_args a))
        as Hkey_eq.
      destruct (eqb (atom_fn b, args_bb) (atom_fn a, atom_args a)).
      - (* bb at removed key — substitute with new canonical entry. *)
        assert (H_fn : atom_fn b = atom_fn a)
          by (apply (f_equal fst) in Hkey_eq; cbn in Hkey_eq; exact Hkey_eq).
        assert (H_args : args_bb = atom_args a)
          by (apply (f_equal snd) in Hkey_eq; cbn in Hkey_eq; exact Hkey_eq).
        clear Hkey_eq. subst args_bb.
        assert (Hain_bb_db_ref : atom_in_db
                                  (Build_atom (atom_fn a) (atom_args a) ret_bb)
                                  e_ref.(db)).
        { revert Hain_bb. unfold atom_in_egraph, atom_in_db; cbn.
          rewrite H_fn. tauto. }
        pose proof (Hper_lk _ Hain_bb_db_ref) as Hretbb_aret.
        exists (Build_atom a'.(atom_fn) a'.(atom_args) a'.(atom_ret)).
        split; cbn.
        + unfold atom_canonical_equiv; cbn. split; [congruence|]. split.
          * (* b.args ~ a'.args in e_post.equiv *)
            clear -Hargs_bb Hargs_eq_post Hper_iff_post.
            revert Hargs_bb Hargs_eq_post.
            generalize (atom_args b), (atom_args a), (atom_args a').
            intros l1 l2 l3. revert l2 l3.
            induction l1 as [|y ys IH]; destruct l2 as [|z zs];
              destruct l3 as [|w ws]; cbn; auto; try tauto.
            intros [Hyz Hys] [Hzw Hzs]. split.
            -- unfold uf_rel_PER in *.
               apply Hper_iff_post in Hyz.
               eapply PER_clo_trans; [exact Hyz | exact Hzw].
            -- apply (IH zs ws Hys Hzs).
          * (* b.ret ~ a'.ret in e_post.equiv *)
            unfold uf_rel_PER in *.
            apply Hper_iff_post in Hret_bb.
            apply Hper_iff_post in Hretbb_aret.
            eapply PER_clo_trans; [exact Hret_bb |].
            eapply PER_clo_trans; [exact Hretbb_aret |].
            rewrite Heq_post_e1.
            apply PER_clo_sym. exact Hret_eq.
        + unfold atom_in_egraph; cbn. exact Hain_can_post.
      - (* bb at different key — survives in e_post.db. *)
        exists (Build_atom (atom_fn b) args_bb ret_bb).
        split; cbn.
        + unfold atom_canonical_equiv; cbn. split; [reflexivity|]. split.
          * clear -Hargs_bb Hper_iff_post.
            revert Hargs_bb. generalize (atom_args b), args_bb.
            intros l1 l2. revert l2.
            induction l1 as [|y ys IH]; destruct l2 as [|z zs];
              cbn; auto; try tauto.
            intros [Hyz Hys]. split.
            -- apply Hper_iff_post in Hyz. exact Hyz.
            -- apply (IH zs Hys).
          * apply Hper_iff_post in Hret_bb. exact Hret_bb.
        + unfold atom_in_egraph; cbn.
          apply Hain_old.
          * (* bb in e_u.db: bb in e_ref.db at non-removed key → in e0.db → in e1.db = e_u.db. *)
            rewrite Hdb_ue1, Hdb_eq01. apply Hdb_iff_post.
            split.
            -- unfold atom_in_egraph, atom_in_db in Hain_bb. cbn in Hain_bb. exact Hain_bb.
            -- cbn. intros Heq. apply Hkey_eq. exact Heq.
          * (* bb's key isn't the canonical key.  Suppose it were:
               (atom_fn b, args_bb) = (a'.fn, a'.args).
               Then Hno_can applied to bb's ret would give contradiction. *)
            cbn. intros Habs. injection Habs as He1 He2.
            exfalso. apply (Hno_can ret_bb).
            change (atom_in_egraph (Build_atom (atom_fn a') (atom_args a') ret_bb) e1).
            unfold atom_in_egraph at 1. rewrite Hdb_eq01.
            change (atom_in_egraph (Build_atom (atom_fn a') (atom_args a') ret_bb) e0).
            apply Hdb_iff_post.
            split;
              [rewrite <- He1, <- He2; exact Hain_bb |
               cbn; rewrite He1, He2 in Hkey_eq; exact Hkey_eq]. }
    (* === Now prove the four conjuncts: egraph_ok, denote_iff, side_l, equiv_extends. === *)
    split. 2: split. 3: split.
    { (* (1) egraph_ok e_post *)
      constructor.
      - (* equiv_ok *) rewrite Heq_post_e1. exact Hex_e1.
      - (* worklist_ok: e_post.worklist = e_u.worklist = e_g.worklist.
           e_g.worklist = (analysis_repair entries) ++ e1.worklist (via
           [get_analyses_worklist_extends]).  Each prefix entry is trivially
           ok.  Each e1.worklist entry was ok in e_ref.equiv (Hwl_ref),
           lifts to e_post.equiv via Hper_iff_post. *)
        rewrite Hwl_post_u.
        assert (Hwl_u_g : e_u.(worklist) = e_g.(worklist))
          by (unfold update_analyses in Hue; injection Hue as _ Hueq;
              subst e_u; reflexivity).
        rewrite Hwl_u_g.
        pose proof (get_analyses_worklist_extends (atom_args a') e1) as Hwe.
        rewrite Hge in Hwe. cbn [fst snd] in Hwe.
        destruct Hwe as (new_ents & Hwl_split & Hpre).
        rewrite Hwl_split.
        assert (Hwl_e1 : e1.(worklist) = e_ref.(worklist)) by congruence.
        rewrite Hwl_e1.
        (* Show: all (worklist_entry_ok e_post.equiv) (new_ents ++ e_ref.worklist). *)
        clear -Hpre Hwl_ref Hper_iff_post.
        induction new_ents as [|ent rest IH]; cbn.
        + (* No new entries: lift e_ref.worklist via Hper_iff_post. *)
          eapply all_wkn; [|exact Hwl_ref].
          intros ent _ Hent.
          destruct ent as [old new improved | k_an]; cbn in *; auto.
          apply Hper_iff_post. exact Hent.
        + (* New entry ent: analysis_repair, trivially ok. Then recurse. *)
          destruct Hpre as (Hpre_ent & Hpre_rest).
          destruct Hpre_ent as (i_repair & Heq_ent).
          subst ent. cbn. split; [exact I | exact (IH Hpre_rest)].
      - (* parents_ok: e_post.parents = fold_left over dedup of
           (a'.ret :: a'.args) adding [cons a'] to e_u.parents.
           For each (x, s) in e_post.parents: every entry in s is either
           a' (witnessed by Hain_can_post + reflexive canonical_equiv)
           or an entry from e_u.parents (= e_ref.parents, witnessed via
           Hpa_ref + Hlift). *)
        intros x s Hgs.
        unfold db_set' in Hde; injection Hde as _ Hdeq; subst e_post; cbn in *.
        apply all_via_in_local. intros v Hv_in.
        pose proof (fold_left_cons_map_update_get
                      (dedup (eqb (A:=_)) (a'.(atom_ret) :: a'.(atom_args)))
                      a' e_u.(parents) x s Hgs v Hv_in)
          as [Hva | (s_old & Hs_old & Hvs_old)].
        + (* v = a' — use canonical entry in e_post.db. *)
          subst v.
          exists (Build_atom a'.(atom_fn) a'.(atom_args) a'.(atom_ret)).
          unfold atom_canonical_equiv. cbn.
          (* PER-reflexivity for a'.args and a'.ret in e_post.equiv: use
             Hkargs_a' and Hkret_a'. *)
          repeat split.
          * (* all2 PER (atom_args a') (atom_args a') *)
            clear -Hkargs_a'. revert Hkargs_a'.
            generalize (atom_args a'). intros l. induction l as [|y ys IH]; cbn; auto.
            intros [Hy Hys]. split.
            -- unfold uf_rel_PER, Sep.has_key in *.
               destruct (map.get (parent (equiv e_u)) y) as [vy|] eqn:Hgy;
                 [|tauto].
               eapply PER_clo_trans;
                 [apply PER_clo_base; exact Hgy
                 | apply PER_clo_sym; apply PER_clo_base; exact Hgy].
            -- apply (IH Hys).
          * (* PER a'.ret a'.ret *)
            unfold uf_rel_PER, Sep.has_key in *.
            destruct (map.get (parent (equiv e_u)) a'.(atom_ret)) as [vr|] eqn:Hgr;
              [|tauto].
            eapply PER_clo_trans;
              [apply PER_clo_base; exact Hgr
              | apply PER_clo_sym; apply PER_clo_base; exact Hgr].
          * cbn. exact Hain_can_post.
        + (* v in old parents s_old — apply Hpa_ref + Hlift. *)
          rewrite Hpa_ue1 in Hs_old. rewrite Hpar_eq01 in Hs_old.
          rewrite Hpar_eq_post in Hs_old.
          pose proof (Hpa_ref _ _ Hs_old) as Hall_ref.
          eapply in_all in Hvs_old; [|exact Hall_ref].
          apply Hlift. exact Hvs_old.
      - (* db_idxs_in_equiv *)
        intros b Hbain.
        apply Hain_post_split in Hbain. destruct Hbain as [Heq | (Hbu & Hneq)].
        + (* new canonical entry *)
          subst b. cbn. split; [exact Hkargs_a' | exact Hkret_a'].
        + (* old atom from e_u.db *)
          rewrite Hdb_ue1, Hdb_eq01 in Hbu.
          apply Hdb_iff_post in Hbu. destruct Hbu as [Hbref _].
          destruct (Hdb_ref_init _ Hbref) as [Hka Hkr].
          split.
          * eapply all_wkn; [|exact Hka]; intros j _ Hj.
            apply Hkey_iff_post. exact Hj.
          * apply Hkey_iff_post. exact Hkr.
    }
    { (* (2) denote_iff e_ref e_post *)
      intros i. split.
      - (* Forward: e_ref sound → e_post sound. *)
        intros [Hwf Hexact Hatom_e Hrel_e].
        constructor.
        + exact Hwf.
        + intros x Hx. apply Hkey_iff_post. apply Hexact. exact Hx.
        + intros b Hbain. apply Hain_post_split in Hbain.
          destruct Hbain as [Heq | (Hbu & Hneq)].
          * (* new canonical entry sound via aa *)
            subst b. cbn.
            pose proof (Hatom_e _ Hain_aa) as Hsa_aa. cbn in Hsa_aa.
            (* aa = (atom_fn a, args_aa, ret_aa), sound in e_ref.
               Build_atom a'.fn a'.args a'.ret should be sound.
               Use atom_sound_eq_ret to convert aa to canonical entry. *)
            apply (eq_atom_implies_sound_l_active i
                     (Build_atom (atom_fn a) args_aa ret_aa)).
            -- unfold eq_atom_in_interpretation; cbn.
               split; [symmetry; exact Hfn_eq |]. split.
               ** (* args_aa eq_sound a'.args via Hargs_aa + Hargs_eq lifted *)
                  clear -Hargs_aa Hargs_eq Hper_iff01 Hequiv_eq_post Hrel_e Hper_iff_post Heq_post_e1.
                  revert Hargs_aa Hargs_eq.
                  generalize (atom_args a), args_aa, (atom_args a').
                  intros l1 l2 l3. revert l2 l3.
                  induction l1 as [|y ys IH]; destruct l2 as [|z zs];
                    destruct l3 as [|w ws]; cbn; auto; try tauto.
                  intros [Hyz Hys] [Hwy Hws]. split.
                  --- apply Hrel_e. unfold uf_rel_PER in *.
                      (* Need: z ~PER~ w in e_ref.equiv (for Hrel_e to apply).
                         Hyz : y ~PER~ z in e_ref.equiv (no lift needed).
                         Hwy : w ~PER~ y in e1.equiv (lift to e_ref). *)
                      apply Hper_iff01 in Hwy. rewrite Hequiv_eq_post in Hwy.
                      eapply PER_clo_trans;
                        [apply PER_clo_sym; exact Hyz | apply PER_clo_sym; exact Hwy].
                  --- apply (IH zs ws Hys Hws).
               ** (* ret_aa eq_sound a'.ret via Hret_aa + Hret_eq *)
                  apply Hrel_e. unfold uf_rel_PER in *.
                  (* Hret_aa : atom_ret a ~PER~ ret_aa in e_ref.
                     Hret_eq : atom_ret a' ~PER~ atom_ret a in e1.
                     Goal: PER_closure e_ref.equiv ret_aa (atom_ret a'). *)
                  apply Hper_iff01 in Hret_eq. rewrite Hequiv_eq_post in Hret_eq.
                  eapply PER_clo_trans;
                    [apply PER_clo_sym; exact Hret_aa | apply PER_clo_sym; exact Hret_eq].
            -- exact Hsa_aa.
          * (* old atom from e_u.db; in e_ref.db via reverse chain. *)
            rewrite Hdb_ue1, Hdb_eq01 in Hbu.
            apply Hdb_iff_post in Hbu. destruct Hbu as [Hbref _].
            apply Hatom_e. unfold atom_in_egraph. exact Hbref.
        + intros i1 i2 Hi12. apply Hrel_e. apply Hper_iff_post. exact Hi12.
      - (* Backward: e_post sound → e_ref sound. *)
        intros [Hwf Hexact Hatom_e Hrel_e].
        constructor.
        + exact Hwf.
        + intros x Hx. apply Hkey_iff_post. apply Hexact. exact Hx.
        + intros b Hbain.
          (* b is in e_ref.db.  Either at removed key (use Hper_lk + canonical
             entry) or at non-removed key (use Hain_old to find in e_post.db). *)
          pose proof (eqb_spec (atom_fn b, atom_args b)
                              (atom_fn a, atom_args a)) as Hkey_eq.
          destruct (eqb (atom_fn b, atom_args b) (atom_fn a, atom_args a)).
          * (* b at removed key *)
            assert (H_fn : atom_fn b = atom_fn a)
              by (apply (f_equal fst) in Hkey_eq; cbn in Hkey_eq; exact Hkey_eq).
            assert (H_args : atom_args b = atom_args a)
              by (apply (f_equal snd) in Hkey_eq; cbn in Hkey_eq; exact Hkey_eq).
            assert (Hain_b_db_ref : atom_in_db
                                     (Build_atom (atom_fn a) (atom_args a)
                                                 (atom_ret b))
                                     e_ref.(db)).
            { revert Hbain. unfold atom_in_egraph, atom_in_db; cbn.
              rewrite H_fn, H_args. tauto. }
            pose proof (Hper_lk _ Hain_b_db_ref) as Hretb_aret.
            pose proof (Hatom_e _ Hain_can_post) as Hsa_can_post.
            cbn in Hsa_can_post.
            apply (eq_atom_implies_sound_l_active i
                     (Build_atom a'.(atom_fn) a'.(atom_args) a'.(atom_ret))).
            -- unfold eq_atom_in_interpretation; cbn.
               split; [rewrite Hfn_eq; symmetry; exact H_fn |]. split.
               ** (* atom_args a' eq_sound atom_args b (= atom_args a) *)
                  rewrite H_args.
                  clear -Hargs_eq Hrel_e Hper_iff_post Heq_post_e1.
                  revert Hargs_eq. generalize (atom_args a'), (atom_args a).
                  intros l1 l2. revert l2.
                  induction l1 as [|y ys IH]; destruct l2 as [|z zs];
                    cbn; auto; try tauto.
                  intros [Hyz Hys]. split.
                  --- apply Hrel_e. rewrite Heq_post_e1. exact Hyz.
                  --- apply (IH zs Hys).
               ** (* atom_ret a' eq_sound atom_ret b *)
                  apply Hrel_e.
                  unfold uf_rel_PER in *.
                  rewrite Heq_post_e1.
                  eapply PER_clo_trans; [exact Hret_eq |].
                  apply Hper_iff01. rewrite Hequiv_eq_post.
                  apply PER_clo_sym. exact Hretb_aret.
            -- exact Hsa_can_post.
          * (* b at different key: in e_post.db via Hain_old *)
            assert (Hbain_e_u : atom_in_db b e_u.(db)).
            { rewrite Hdb_ue1, Hdb_eq01. apply Hdb_iff_post.
              split.
              - unfold atom_in_egraph, atom_in_db in Hbain. cbn in Hbain. exact Hbain.
              - cbn. intros Heq. apply Hkey_eq. exact Heq. }
            assert (Hbain_e_post : atom_in_db b e_post.(db)).
            { apply Hain_old; [exact Hbain_e_u |].
              (* (atom_fn b, atom_args b) <> (atom_fn a', atom_args a'). *)
              cbn. intros Habs. injection Habs as He1 He2.
              apply (Hno_can (atom_ret b)).
              unfold atom_in_egraph, atom_in_db; cbn.
              rewrite <- Hdb_ue1.
              unfold atom_in_db, Is_Some_satisfying in Hbain_e_u; cbn in Hbain_e_u.
              rewrite <- He1, <- He2. exact Hbain_e_u. }
            apply Hatom_e. exact Hbain_e_post.
        + intros i1 i2 Hi12.
          apply Hrel_e. apply Hper_iff_post. exact Hi12.
    }
    { (* (3) side_l preservation *)
      eapply all_wkn; [|exact Hatoms_ref].
      intros b _ Hb. apply Hlift. exact Hb. }
    { (* (4) equiv_extends *)
      unfold equiv_extends. intros x y Hxy. apply Hper_iff_post. exact Hxy. }
  Qed.

  (* ============================================================== *)
  (* db_set_sound: fresh-insertion variant of                        *)
  (* db_set_after_canonicalize_denote_iff.                            *)
  (* Inserts an atom [a] whose key (a.fn, a.args) doesn't yet appear  *)
  (* in the db, and whose contents are sound under the model under i. *)
  (* Preserves egraph_ok, egraph_sound_for_interpretation, has_key.   *)
  (* ============================================================== *)
  Lemma db_set_sound (i : idx_map m.(domain)) a
    : vc (db_set a)
        (fun e_in res =>
           egraph_ok e_in ->
           egraph_sound_for_interpretation m i e_in ->
           (forall x, In x a.(atom_args) -> Sep.has_key x e_in.(equiv).(parent)) ->
           Sep.has_key a.(atom_ret) e_in.(equiv).(parent) ->
           atom_sound_for_model m i a ->
           (forall r, ~ atom_in_egraph (Build_atom a.(atom_fn) a.(atom_args) r) e_in) ->
           egraph_ok (snd res)
           /\ egraph_sound_for_interpretation m i (snd res)
           /\ (forall x, Sep.has_key x e_in.(equiv).(parent) ->
                         Sep.has_key x (snd res).(equiv).(parent))).
  Proof.
    unfold db_set, vc; cbn [Mbind StateMonad.state_monad fst snd].
    intros e_in.
    intros Hok Hsound Hargs Hret Hatom_sound Hno_can.
    pose proof (get_analyses_preserves_fields a.(atom_args) e_in) as Hgaf.
    destruct (get_analyses idx symbol symbol_map idx_map idx_trie
                analysis_result a.(atom_args) e_in) as [arg_as e_g] eqn:Hge.
    cbn [fst snd] in Hgaf.
    destruct Hgaf as (Hdb_g & Heq_g & Hpa_g).
    set (out_a := analyze idx symbol analysis_result a arg_as).
    destruct (update_analyses idx symbol symbol_map idx_map idx_trie
                analysis_result a.(atom_ret) out_a e_g) as [_u e_u] eqn:Hue.
    assert (Hdb_u_g : e_u.(db) = e_g.(db))
      by (unfold update_analyses in Hue; injection Hue as _ Hueq;
          subst e_u; reflexivity).
    assert (Heq_u_g : e_u.(equiv) = e_g.(equiv))
      by (unfold update_analyses in Hue; injection Hue as _ Hueq;
          subst e_u; reflexivity).
    assert (Hpa_u_g : e_u.(parents) = e_g.(parents))
      by (unfold update_analyses in Hue; injection Hue as _ Hueq;
          subst e_u; reflexivity).
    assert (Hdb_u_e_in : e_u.(db) = e_in.(db)) by congruence.
    assert (Heq_u_e_in : e_u.(equiv) = e_in.(equiv)) by congruence.
    assert (Hpa_u_e_in : e_u.(parents) = e_in.(parents)) by congruence.
    destruct (db_set' idx Eqb_idx symbol symbol_map idx_map idx_trie
                analysis_result a out_a e_u) as [_v e_post] eqn:Hde.
    cbn [fst snd] in *.
    assert (Heq_post_u : e_post.(equiv) = e_u.(equiv))
      by (unfold db_set' in Hde; injection Hde as _ Hdeq;
          subst e_post; reflexivity).
    assert (Hep_post_u : e_post.(epoch) = e_u.(epoch))
      by (unfold db_set' in Hde; injection Hde as _ Hdeq;
          subst e_post; reflexivity).
    assert (Hwl_post_u : e_post.(worklist) = e_u.(worklist))
      by (unfold db_set' in Hde; injection Hde as _ Hdeq;
          subst e_post; reflexivity).
    assert (Heq_post_e_in : e_post.(equiv) = e_in.(equiv)) by congruence.
    (* Conjunct 3 (has_key preservation): trivial from Heq_post_e_in. *)
    assert (Hkeys : forall x, Sep.has_key x e_in.(equiv).(parent) ->
                              Sep.has_key x e_post.(equiv).(parent)).
    { intros x Hx. rewrite Heq_post_e_in. exact Hx. }
    (* has_key facts for args/ret in e_post *)
    assert (Hkargs_post : forall x, In x (atom_args a) ->
                                    Sep.has_key x e_post.(equiv).(parent)).
    { intros x Hx. apply Hkeys. apply Hargs. exact Hx. }
    assert (Hkret_post : Sep.has_key (atom_ret a) e_post.(equiv).(parent))
      by (apply Hkeys; exact Hret).
    (* e_post.db = map_update e_u.db a.fn (put tbl a.args ...);
       extract structural facts. *)
    pose proof Hde as Hde_orig.
    unfold db_set' in Hde. injection Hde as _ Hdeq.
    (* The new atom is in e_post.db: *)
    assert (Hain_a_post : atom_in_db
                            (Build_atom (atom_fn a) (atom_args a) (atom_ret a))
                            e_post.(db)).
    { subst e_post. unfold atom_in_db, Is_Some_satisfying, map_update; cbn.
      destruct (map.get (db e_u) (atom_fn a)) as [tbl|] eqn:Htbl;
        rewrite map.get_put_same; cbn; rewrite map.get_put_same; reflexivity. }
    (* Every atom in e_post.db is either the new atom or was in e_u.db
       at a different key. *)
    assert (Hain_post_split : forall b, atom_in_db b e_post.(db) ->
              b = Build_atom (atom_fn a) (atom_args a) (atom_ret a)
              \/ (atom_in_db b e_u.(db)
                  /\ (atom_fn b, atom_args b)
                     <> (atom_fn a, atom_args a))).
    { intros b Hb.
      subst e_post.
      unfold atom_in_db, Is_Some_satisfying, map_update in Hb; cbn in Hb.
      destruct b as [bfn bargs bret]; cbn in Hb.
      destruct (map.get (db e_u) (atom_fn a)) as [tbl|] eqn:Htbl;
        eqb_case bfn (atom_fn a).
      - rewrite map.get_put_same in Hb; cbn in Hb.
        eqb_case bargs (atom_args a).
        + rewrite map.get_put_same in Hb; cbn in Hb. left. subst. reflexivity.
        + rewrite map.get_put_diff in Hb by auto.
          right. split.
          * unfold atom_in_db, Is_Some_satisfying; cbn.
            rewrite Htbl. cbn. exact Hb.
          * cbn. intros Habs; inversion Habs; contradiction.
      - rewrite map.get_put_diff in Hb by auto.
        right. split.
        + unfold atom_in_db, Is_Some_satisfying; cbn. exact Hb.
        + cbn. intros Habs; inversion Habs; contradiction.
      - rewrite map.get_put_same in Hb; cbn in Hb.
        eqb_case bargs (atom_args a).
        + rewrite map.get_put_same in Hb; cbn in Hb. left. subst. reflexivity.
        + rewrite map.get_put_diff in Hb by auto.
          unfold default in Hb. rewrite map.get_empty in Hb. cbn in Hb. destruct Hb.
      - rewrite map.get_put_diff in Hb by auto.
        right. split.
        + unfold atom_in_db, Is_Some_satisfying; cbn. exact Hb.
        + cbn. intros Habs; inversion Habs; contradiction. }
    (* atom_in_egraph_up_to_equiv a e_post — witness is a itself. *)
    assert (Hain_a_uptopost : atom_in_egraph_up_to_equiv a e_post).
    { exists (Build_atom (atom_fn a) (atom_args a) (atom_ret a)). split.
      - unfold atom_canonical_equiv. cbn. split; [reflexivity|]. split.
        + (* PER reflexivity on args using has_key *)
          clear -Hkargs_post.
          generalize (atom_args a) Hkargs_post; intros l Hl.
          induction l as [|y ys IH]; cbn; auto.
          assert (Hky : Sep.has_key y (parent (equiv e_post))) by (apply Hl; cbn; auto).
          assert (Hkys : forall x, In x ys -> Sep.has_key x (parent (equiv e_post)))
            by (intros x Hx; apply Hl; cbn; auto).
          split.
          * unfold uf_rel_PER, Sep.has_key in *.
            destruct (map.get (parent (equiv e_post)) y) as [vy|] eqn:Hgy;
              [|tauto].
            eapply PER_clo_trans;
              [apply PER_clo_base; exact Hgy
              | apply PER_clo_sym; apply PER_clo_base; exact Hgy].
          * apply IH. exact Hkys.
        + (* PER reflexivity on ret *)
          unfold uf_rel_PER, Sep.has_key in *.
          destruct (map.get (parent (equiv e_post)) (atom_ret a)) as [vr|] eqn:Hgr;
            [|tauto].
          eapply PER_clo_trans;
            [apply PER_clo_base; exact Hgr
            | apply PER_clo_sym; apply PER_clo_base; exact Hgr].
      - unfold atom_in_egraph. exact Hain_a_post. }
    (* atom_in_egraph_up_to_equiv lifts from e_in to e_post for any old atom *)
    assert (Hlift : forall b, atom_in_egraph_up_to_equiv b e_in ->
                              atom_in_egraph_up_to_equiv b e_post).
    { intros b Hbref.
      destruct Hbref as [bb Hcan_ain].
      destruct Hcan_ain as [Hcan Hbain].
      destruct Hcan as [Hfn_bb Hargs_ret].
      destruct Hargs_ret as [Hargs_bb Hret_bb].
      exists bb. split.
      - unfold atom_canonical_equiv.
        split; [exact Hfn_bb|]. split.
        + (* args PER lift via Heq_post_e_in *)
          clear -Hargs_bb Heq_post_e_in.
          revert Hargs_bb. generalize (atom_args b), (atom_args bb).
          intros l1 l2. revert l2. induction l1; destruct l2; cbn; auto; try tauto.
          intros [Hy Hys]. split.
          * unfold uf_rel_PER in *. rewrite Heq_post_e_in. exact Hy.
          * apply IHl1. exact Hys.
        + unfold uf_rel_PER in *. rewrite Heq_post_e_in. exact Hret_bb.
      - (* old atom bb in e_in.db; show atom_in_db bb e_post.db.
           e_post.db = put e_u.db a.fn (put tbl a.args new_entry).
           Cases:
           - bb.key = (a.fn, a.args): would contradict Hno_can (which says
             no atom with this key is in e_in.db, hence not in e_u.db).
           - bb.key != (a.fn, a.args): bb survives the map.put. *)
        unfold atom_in_egraph in Hbain. rewrite <- Hdb_u_e_in in Hbain.
        unfold atom_in_egraph. cbn.
        destruct bb as [bfn bargs bret].
        unfold atom_in_db, Is_Some_satisfying in Hbain; cbn in Hbain.
        unfold atom_in_db, Is_Some_satisfying; cbn.
        rewrite <- Hdeq; cbn. unfold map_update; cbn.
        destruct (map.get (db e_u) (atom_fn a)) as [tbl|] eqn:Htbl.
        { eqb_case bfn (atom_fn a).
          { subst. rewrite Htbl in Hbain.
            rewrite map.get_put_same.
            eqb_case bargs (atom_args a).
            { subst. exfalso. apply (Hno_can bret).
              unfold atom_in_egraph, atom_in_db; cbn.
              rewrite <- Hdb_u_e_in. unfold Is_Some_satisfying. rewrite Htbl. exact Hbain. }
            { rewrite map.get_put_diff by auto. exact Hbain. } }
          { rewrite map.get_put_diff by auto. exact Hbain. } }
        { eqb_case bfn (atom_fn a).
          { subst. rewrite Htbl in Hbain. cbn in Hbain. destruct Hbain. }
          { rewrite map.get_put_diff by auto. exact Hbain. } } }
    (* Hdeq : Build_instance ... = e_post. Use Heq_post_u, Hep_post_u, Hwl_post_u
       to characterize the e_post fields. *)
    split; [|split].
    - (* egraph_ok e_post. *)
      destruct Hok as [Heqok Hwlok Hparok Hdbkok].
      constructor.
      + (* equiv_ok: rewrite via Heq_post_e_in. *)
        destruct Heqok as [roots Hufok].
        exists roots. rewrite Heq_post_e_in. exact Hufok.
      + (* worklist_ok: e_post.worklist = e_u.worklist = e_g.worklist;
           e_g.worklist = (analysis_repair entries) ++ e_in.worklist;
           each prefix entry trivially ok; old entries lift via Heq_post_e_in. *)
        rewrite Hwl_post_u.
        assert (Hwl_u_g : e_u.(worklist) = e_g.(worklist))
          by (unfold update_analyses in Hue; injection Hue as _ Hueq;
              subst e_u; reflexivity).
        rewrite Hwl_u_g.
        pose proof (get_analyses_worklist_extends a.(atom_args) e_in) as Hgwe.
        rewrite Hge in Hgwe. cbn [snd] in Hgwe.
        destruct Hgwe as [new_ents Hg2]; destruct Hg2 as [Hwl_g_eq Hpref_anr].
        rewrite Hwl_g_eq.
        apply all_app. split.
        * (* analysis_repair entries are ok *)
          clear -Hpref_anr.
          induction new_ents as [|ent ents IH]; cbn in *; auto.
          destruct Hpref_anr as [Hent_ex Hrest].
          destruct Hent_ex as [ix Hent]; subst ent.
          split; [cbn; exact I | apply IH; exact Hrest].
        * (* old entries lift via Heq_post_e_in *)
          eapply all_wkn; [|exact Hwlok].
          intros ent Hin_ent Hent_ok.
          destruct ent as [ix1 ix2 ibool|ix]; cbn in *; auto.
          unfold uf_rel_PER in *. rewrite Heq_post_e_in. exact Hent_ok.
      + (* parents_ok: db_set' prepends [a] to parents at dedup(a.ret :: a.args).
           Each v in any updated parents list is either = a (use Hain_a_uptopost)
           or was in old parents (use Hparok + Hlift). *)
        intros x s Hgs. subst e_post. cbn in Hgs.
        apply all_via_in_local. intros v Hv_in.
        pose proof (fold_left_cons_map_update_get
                      (dedup (eqb (A:=_)) (atom_ret a :: atom_args a))
                      a e_u.(parents) x s Hgs v Hv_in)
          as [Hva | Hold].
        * subst v. exact Hain_a_uptopost.
        * destruct Hold as [s_old Hsold_in].
          destruct Hsold_in as [Hgs_old Hvin_old].
          rewrite Hpa_u_e_in in Hgs_old.
          pose proof (Hparok _ _ Hgs_old) as Hall_old.
          eapply in_all in Hvin_old; [|exact Hall_old].
          apply Hlift. exact Hvin_old.
      + (* db_idxs_in_equiv: every atom in e_post.db has args/ret as keys.
           Either the new atom (use Hkargs_post / Hkret_post) or an old
           atom (use Hdbkok + Heq_post_e_in). *)
        intros b Hbain.
        apply Hain_post_split in Hbain.
        destruct Hbain as [Heq_b | Hb_old_split].
        * subst b. cbn. split.
          -- (* all has_key on atom_args a *)
             clear -Hkargs_post.
             generalize (atom_args a) Hkargs_post; intros l Hl.
             induction l as [|y ys IH]; cbn; auto.
             split; [apply Hl; cbn; auto|].
             apply IH. intros x Hx. apply Hl. cbn. auto.
          -- exact Hkret_post.
        * destruct Hb_old_split as [Hbu _].
          rewrite Hdb_u_e_in in Hbu.
          specialize (Hdbkok _ Hbu).
          destruct Hdbkok as [Hka Hkr].
          split.
          -- eapply all_wkn; [|exact Hka].
             intros j _ Hj. apply Hkeys. exact Hj.
          -- apply Hkeys. exact Hkr.
    - (* egraph_sound_for_interpretation m i e_post. *)
      destruct Hsound as [Hi_wf Hi_exact Hi_atom Hi_rel].
      constructor.
      + (* idx_interpretation_wf: i unchanged *)
        exact Hi_wf.
      + (* interpretation_exact: equiv unchanged via Heq_post_e_in *)
        intros y Hy. specialize (Hi_exact _ Hy).
        rewrite Heq_post_e_in. exact Hi_exact.
      + (* atom_interpretation: every atom in e_post.db is sound for the model.
           Either the new atom (Hatom_sound) or an old atom (Hi_atom). *)
        intros b Hbain. unfold atom_in_egraph in Hbain.
        apply Hain_post_split in Hbain.
        destruct Hbain as [Heq_b | Hb_old_split].
        * subst b. exact Hatom_sound.
        * destruct Hb_old_split as [Hbu _].
          rewrite Hdb_u_e_in in Hbu.
          apply Hi_atom. unfold atom_in_egraph. exact Hbu.
      + (* rel_interpretation: PER unchanged via Heq_post_e_in *)
        intros i1 i2 Hper. rewrite Heq_post_e_in in Hper.
        apply Hi_rel. exact Hper.
    - exact Hkeys.
  Qed.

  (* ============================================================== *)
  (* hash_entry_sound and update_entry_sound (relocated from earlier *)
  (* in the file so that they can use db_set_sound).                  *)
  (* ============================================================== *)

  (* hash_entry: canonicalizes args, looks up (f, args') in the db;
     if present, returns the existing id, otherwise allocates a
     fresh id and writes (f, args', new_id) into the db.

     Precondition: every arg is a key in the union-find, the
     interpretation [i] is sound for the input egraph, all args
     map under [i] to a list of domain values [arg_doms], and the
     model has [interprets_to f arg_doms out_d] for some [out_d].

     Postcondition: result id is mapped (under an extended [i']) to
     a domain value [domain_eq]-related to [out_d]; both invariants
     are preserved. *)
  Lemma hash_entry_sound (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x))
        (Hltt : Transitive lt) (i : idx_map m.(domain)) f args (out_d : m.(domain))
    : vc (hash_entry idx_succ f args)
        (fun e_in res =>
           egraph_ok e_in ->
           egraph_sound_for_interpretation m i e_in ->
           (forall x, In x args -> Sep.has_key x e_in.(equiv).(parent)) ->
           (exists arg_doms,
              list_Mmap (map.get i) args = Some arg_doms
              /\ m.(interprets_to) f arg_doms out_d) ->
           egraph_ok (snd res)
           /\ exists i',
                map.extends i' i
                /\ egraph_sound_for_interpretation m i' (snd res)
                /\ (forall x, Sep.has_key x e_in.(equiv).(parent) ->
                              Sep.has_key x (snd res).(equiv).(parent))
                /\ Sep.has_key (fst res) (snd res).(equiv).(parent)
                /\ option_relation m.(domain_eq)
                     (map.get i' (fst res)) (Some out_d)).
  Proof.
    unfold hash_entry.
    vc_bind list_Mmap_find_preserves_fields_strong.
    rename s0 into e1, a into args'.
    vc_bind db_lookup_pure.
    rename s0 into e2, a into mout.
    destruct mout as [r|]; cbn beta iota; cbn [fst snd].
    - (* Some r *)
      unfold vc, Mret. cbn [StateMonad.state_monad fst snd].
      intros e_post Hpost_lookup Hpost_find.
      intros Hok Hsound Hkeys_args Hex.
      destruct Hpost_lookup as [He2_eq Hin]; subst e2.
      (* Apply find's postcondition with the egraph_ok witness *)
      destruct Hok as [Heqok Hwlok Hparok Hdbkok].
      destruct Heqok as [roots Hroots].
      assert (Hargk_e1 : all (fun i => Sep.has_key i e1.(equiv).(parent)) args).
      { clear -Hkeys_args.
        induction args as [|x xs IH]; cbn; auto.
        split; [apply Hkeys_args; left; reflexivity|].
        apply IH. intros y Hy. apply Hkeys_args. right; exact Hy. }
      specialize (Hpost_find (ex_intro _ roots Hroots) Hargk_e1).
      destruct Hpost_find as (Hex_post & Hfp & Hper_args).
      (* egraph_ok e_post from fields_preserved + e1's ok *)
      assert (Hok_e1 : egraph_ok e1) by (constructor; eauto; exists roots; exact Hroots).
      assert (Hok_post : egraph_ok e_post)
        by (eapply fields_preserved_egraph_ok; eauto).
      (* sound_for_interpretation e_post from fields_preserved *)
      assert (Hsnd_post : egraph_sound_for_interpretation m i e_post)
        by (eapply fields_preserved_sound_for_interpretation; eauto).
      (* atom (f, args', r) is sound under i (from atom_interpretation) *)
      pose proof Hsnd_post as Hsnd_post'.
      destruct Hsnd_post' as [Hi_wf Hi_exact Hi_atom Hi_rel].
      pose proof (Hi_atom _ Hin) as Hatom_r.
      (* Extract atom_sound_for_model destructively *)
      unfold atom_sound_for_model in Hatom_r; cbn in Hatom_r.
      destruct (list_Mmap (map.get i) args') as [args'_doms|] eqn:Hargs'_doms;
        cbn in Hatom_r; [|tauto].
      destruct (map.get i r) as [r_d|] eqn:Hir; cbn in Hatom_r; [|tauto].
      (* Use args_rel_interpretation to relate args'_doms and arg_doms *)
      destruct Hex as [arg_doms Hex_pair]. destruct Hex_pair as [Harg_doms Hint_arg].
      assert (Hrel : option_relation (all2 m.(domain_eq))
                       (list_Mmap (map.get i) args')
                       (list_Mmap (map.get i) args)).
      { eapply args_rel_interpretation;
          [split; [exact Hok_post | exact Hsnd_post] | exact Hper_args]. }
      rewrite Hargs'_doms, Harg_doms in Hrel; cbn in Hrel.
      (* Hrel : all2 domain_eq args'_doms arg_doms *)
      (* Use interprets_to_preserved to get interprets_to f args'_doms out_d *)
      assert (Hwf_outd : m.(domain_wf) out_d)
        by (eapply interprets_to_implies_wf_conclusion; eauto).
      assert (Hrel_sym : all2 m.(domain_eq) arg_doms args'_doms)
        by (apply all2_Symmetric; [typeclasses eauto | exact Hrel]).
      pose proof (interprets_to_preserved _ _ _ _ _ Hint_arg
                    Hrel_sym Hwf_outd) as Hint_args'_outd.
      (* By interprets_to_functional: domain_eq r_d out_d *)
      assert (Hreq : m.(domain_eq) r_d out_d).
      { eapply interprets_to_functional with (args1 := args'_doms) (args2 := args'_doms);
          [exact Hatom_r | exact Hint_args'_outd |].
        eapply interprets_to_implies_wf_args in Hatom_r.
        clear -Hatom_r.
        induction args'_doms; cbn in *; auto.
        intuition. }
      (* Has_key for r in e_post *)
      assert (Hkr_post : Sep.has_key r e_post.(equiv).(parent)).
      { destruct Hok_post as [_ _ _ Hdbkok_post].
        apply Hdbkok_post in Hin. apply Hin. }
      split; [exact Hok_post|].
      exists i.
      split; [intros x v Hv; exact Hv|].
      split; [exact Hsnd_post|].
      destruct Hfp as (_ & _ & _ & _ & _ & Hkey_iff & _).
      split.
      { intros x Hx. apply Hkey_iff. exact Hx. }
      split; [exact Hkr_post|].
      rewrite Hir; cbn. exact Hreq.
    - (* None: alloc + db_set *)
      (* In this branch the body is [alloc; db_set (Build_atom f args' r); Mret r].
         We work directly with the state-monad unfolding rather than vc_bind
         since we've already crossed two vc_binds and the postcondition is
         pinned to the outer state. *)
      cbn [Mbind StateMonad.state_monad].
      intros e_post Hpost_lookup Hpost_find.
      intros Hok Hsound Hkeys_args Hex.
      destruct Hpost_lookup as [He2_eq Hnone]; subst e2.
      destruct Hex as [arg_doms Hex_pair]. destruct Hex_pair as [Harg_doms Hint_arg].
      assert (Hwf_outd : m.(domain_wf) out_d)
        by (eapply interprets_to_implies_wf_conclusion; eauto).
      (* Derive egraph_ok and sound for e_post (the state after find) *)
      destruct Hok as [Heqok Hwlok Hparok Hdbkok].
      destruct Heqok as [roots Hroots].
      assert (Hargk_e1 : all (fun i => Sep.has_key i e1.(equiv).(parent)) args).
      { clear -Hkeys_args.
        induction args as [|x xs IH]; cbn; auto.
        split; [apply Hkeys_args; left; reflexivity|].
        apply IH. intros y Hy. apply Hkeys_args. right; exact Hy. }
      specialize (Hpost_find (ex_intro _ roots Hroots) Hargk_e1).
      destruct Hpost_find as (Hex_post & Hfp & Hper_args).
      assert (Hok_e1 : egraph_ok e1) by (constructor; eauto; exists roots; exact Hroots).
      assert (Hok_post : egraph_ok e_post)
        by (eapply fields_preserved_egraph_ok; eauto).
      assert (Hsnd_post : egraph_sound_for_interpretation m i e_post)
        by (eapply fields_preserved_sound_for_interpretation; eauto).
      (* Apply alloc_sound *)
      pose proof (alloc_sound Hlti Hlts Hltt i out_d Hwf_outd Hwf_outd) as Halloc_sound.
      unfold vc in Halloc_sound. specialize (Halloc_sound e_post).
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e_post)
        as [r e_alloc] eqn:Halloc_eq.
      cbn [fst snd] in Halloc_sound.
      specialize (Halloc_sound Hok_post Hsnd_post).
      destruct Halloc_sound as (Hok_alloc & Hsnd_alloc & Hinone_r & Hr_fresh_pre &
                                Hr_key_alloc & Hkeys_alloc & Hdb_alloc & Hpar_alloc & Hwl_alloc).
      (* Args are still keys in e_alloc (alloc preserves keys) *)
      assert (Hargs_keys_alloc :
                forall x, In x args' -> Sep.has_key x e_alloc.(equiv).(parent)).
      { intros x Hx.
        apply Hkeys_alloc.
        (* args' are keys in e_post via per_args + Hkeys_args + fields_preserved *)
        assert (Hkargs'_e_post : all (fun y => Sep.has_key y e_post.(equiv).(parent))
                                  args').
        { destruct Hex_post as [roots_post Hroots_post].
          revert Hper_args. generalize args' as l1, args as l2.
          intros l1 l2. revert l2.
          induction l1 as [|y ys IH]; destruct l2 as [|z zs]; cbn; auto; try tauto.
          intros [Hy Hys]. split.
          - edestruct uf_rel_PER_has_key as [Hky _];
              [exact Hroots_post | exact Hy |]. exact Hky.
          - eapply IH; exact Hys. }
        clear -Hkargs'_e_post Hx.
        induction args' as [|y ys IH]; cbn in Hx, Hkargs'_e_post; try tauto.
        destruct Hx as [-> | Hin]; destruct Hkargs'_e_post as [Hy Hys]; auto. }
      (* Atom_sound_for_model under i' := map.put i r out_d for (f, args', r) *)
      pose proof Hsnd_post as Hsnd_post'.
      destruct Hsnd_post' as [Hi_wf Hi_exact Hi_atom Hi_rel].
      set (i' := map.put i r out_d).
      (* Has_key for args' in e_alloc was just established. *)
      assert (Hint_args'_outd : m.(interprets_to) f
                                  (map (fun _ => out_d) args')   (* placeholder, fixed below *)
                                  out_d -> True). { tauto. }
      clear Hint_args'_outd.
      (* args'_doms := list_Mmap (map.get i) args'. interprets_to f args'_doms out_d. *)
      assert (Hrel : option_relation (all2 m.(domain_eq))
                       (list_Mmap (map.get i) args')
                       (list_Mmap (map.get i) args)).
      { eapply args_rel_interpretation;
          [split; [exact Hok_post | exact Hsnd_post] | exact Hper_args]. }
      rewrite Harg_doms in Hrel.
      destruct (list_Mmap (map.get i) args') as [args'_doms|] eqn:Hargs'_doms;
        cbn in Hrel; [|discriminate].
      assert (Hrel_sym : all2 m.(domain_eq) arg_doms args'_doms)
        by (apply all2_Symmetric; [typeclasses eauto | exact Hrel]).
      pose proof (interprets_to_preserved _ _ _ _ _ Hint_arg
                    Hrel_sym Hwf_outd) as Hint_args'_outd.
      (* Apply db_set_sound to (Build_atom f args' r) with interp = i' *)
      pose proof (db_set_sound i' (Build_atom f args' r)) as Hdss.
      unfold vc in Hdss. specialize (Hdss e_alloc).
      cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in Hdss.
      destruct (db_set (Build_atom f args' r) e_alloc) as [u_db e_db] eqn:Hdb_eq.
      cbn [fst snd] in Hdss.
      (* Build the preconditions for db_set_sound *)
      assert (Hr_key_db : Sep.has_key r e_alloc.(equiv).(parent)) by exact Hr_key_alloc.
      assert (Hatom_sound_i' :
                atom_sound_for_model m i' (Build_atom f args' r)).
      { unfold atom_sound_for_model, i'. cbn.
        (* Show map.get (map.put i r out_d) on args' is preserved
           (r is fresh: not in args' since Hinone_r implies r not in dom(i)
           but args' are keys via Hex_post + Hsnd_post.interpretation_exact?).
           Actually we need: args' don't contain r.
           args' are keys in e_post, and r is fresh w.r.t. e_post.
           Hr_fresh_pre: ~ Sep.has_key r e_post.(equiv).(parent).  So if r ∈ args',
           we'd have has_key r in e_post via the keys_e_post derivation.
           Actually, let me just compute directly. *)
        assert (Hr_not_in_args' : ~ In r args').
        { intro Hin'.
          (* args' are keys in e_post, but r is not. *)
          assert (Hkr_post : Sep.has_key r e_post.(equiv).(parent)).
          { destruct Hex_post as [roots_post Hroots_post].
            revert Hin' Hper_args.
            generalize args' as l1, args as l2.
            intros l1 l2. revert l2.
            induction l1 as [|y ys IH]; destruct l2 as [|z zs]; cbn; auto; try tauto.
            intros [Heq | Hin] [Hy Hys].
            - subst y. edestruct uf_rel_PER_has_key as [Hky _];
                [exact Hroots_post | exact Hy |]. exact Hky.
            - eapply IH; eauto. }
          apply Hr_fresh_pre. exact Hkr_post. }
        (* list_Mmap (map.get (put i r out_d)) args' = list_Mmap (map.get i) args' *)
        assert (Hlmap_put : list_Mmap (map.get (map.put i r out_d)) args'
                          = list_Mmap (map.get i) args').
        { set (zs := args') in Hr_not_in_args' |- *.
          clearbody zs. revert Hr_not_in_args'.
          induction zs as [|y ys IH]; auto.
          intros Hni; cbn. assert (Hyne : y <> r)
            by (intros ->; apply Hni; left; reflexivity).
          assert (Hr_not_in_ys : ~ In r ys)
            by (intros Hin; apply Hni; right; exact Hin).
          rewrite IH by exact Hr_not_in_ys.
          rewrite map.get_put_diff by congruence.
          reflexivity. }
        rewrite Hlmap_put, Hargs'_doms; cbn.
        rewrite map.get_put_same; cbn.
        exact Hint_args'_outd. }
      assert (Hno_existing :
                forall r0, ~ atom_in_egraph
                             (Build_atom f args' r0) e_alloc).
      { intros r0 Hin_egraph.
        unfold atom_in_egraph in Hin_egraph; cbn in Hin_egraph.
        rewrite <- Hdb_alloc in Hin_egraph.
        eapply Hnone. unfold atom_in_egraph. exact Hin_egraph. }
      cbn [atom_args atom_ret atom_fn] in Hdss.
      specialize (Hdss Hok_alloc Hsnd_alloc Hargs_keys_alloc Hr_key_alloc
                       Hatom_sound_i' Hno_existing).
      destruct Hdss as (Hok_db & Hsnd_db & Hkeys_db).
      unfold Mret. cbn [StateMonad.state_monad fst snd].
      split; [exact Hok_db|].
      exists i'.
      split.
      { unfold i'. intros x v Hgv.
        eqb_case x r.
        - subst. (* If get i r = Some v, then ... but get i r = None. *)
          rewrite Hinone_r in Hgv. discriminate.
        - rewrite map.get_put_diff by congruence. exact Hgv. }
      split; [exact Hsnd_db|].
      split.
      { intros x Hx.
        apply Hkeys_db.
        apply Hkeys_alloc.
        destruct Hfp as (_ & _ & _ & _ & _ & Hkey_iff & _).
        apply Hkey_iff. exact Hx. }
      split.
      { apply Hkeys_db. exact Hr_key_alloc. }
      unfold i'.
      rewrite map.get_put_same; cbn. exact Hwf_outd.
  Qed.

  (* update_entry: ensures atom [a] is recorded.  If a previous
     entry exists for [(a.fn, a.args)], it unions [a.ret] with that
     value; otherwise it inserts [a].

     Precondition: args and ret are keys, the atom is sound under
     [i].  Postcondition: invariants preserved (no extension to [i]
     needed because the ret value is supplied by the caller). *)
  Lemma update_entry_sound (i : idx_map m.(domain)) a
    : vc (update_entry a)
        (fun e_in res =>
           egraph_ok e_in ->
           egraph_sound_for_interpretation m i e_in ->
           (forall x, In x a.(atom_args) -> Sep.has_key x e_in.(equiv).(parent)) ->
           Sep.has_key a.(atom_ret) e_in.(equiv).(parent) ->
           atom_sound_for_model m i a ->
           egraph_ok (snd res)
           /\ egraph_sound_for_interpretation m i (snd res)
           /\ (forall x, Sep.has_key x e_in.(equiv).(parent) ->
                         Sep.has_key x (snd res).(equiv).(parent))).
  Proof.
    unfold update_entry.
    vc_bind db_lookup_pure.
    rename s0 into e_in, a0 into mout.
    destruct mout as [r|]; cbn beta iota; cbn [fst snd].
    - (* Some r: union r (atom_ret a) *)
      intros s_pre HpreL. destruct HpreL as [Heq Hin]; subst s_pre.
      unfold Mseq.
      intros Hok Hsound Hargs Hret Hatom_sound.
      destruct Hok as [Heqok Hwlok Hparok Hdbkok].
      assert (Hkey_r : Sep.has_key r e_in.(equiv).(parent))
        by (apply Hdbkok in Hin; apply Hin).
      pose proof (union_sound r (atom_ret a) e_in) as Hus.
      cbn [fst snd] in Hus.
      destruct Heqok as [roots_e Hroots_e].
      destruct (Defs.union r (atom_ret a) e_in) as [v_u e_u'] eqn:Heu.
      cbn [fst snd] in Hus.
      specialize (Hus ltac:(exists roots_e; exact Hroots_e) Hkey_r Hret).
      destruct Hus as [Hdb_eq Hus2].
      destruct Hus2 as [Hroots Hus3].
      destruct Hus3 as [Hper Hus4].
      destruct Hus4 as [Hpar_eq Hus5].
      destruct Hus5 as [Hwl_rel Hper_xr].
      cbn [Mbind Mret StateMonad.state_monad fst snd].
      rewrite Heu. cbn [fst snd].
      assert (Hkey_pres : forall x, Sep.has_key x e_in.(equiv).(parent) ->
                                    Sep.has_key x e_u'.(equiv).(parent)).
      { intros x Hx.
        destruct Hroots as [roots' Hroots'].
        unfold Sep.has_key in *.
        destruct (map.get (parent (equiv e_u')) x) eqn:Hgx; [constructor|].
        exfalso.
        destruct (map.get (parent (equiv e_in)) x) eqn:Hgx_in; [|tauto].
        assert (Hxx : uf_rel_PER (equiv e_in) x x).
        { unfold uf_rel_PER.
          eapply PER_clo_trans;
            [apply PER_clo_base; exact Hgx_in
            |apply PER_clo_sym; apply PER_clo_base; exact Hgx_in]. }
        assert (Hxx' : uf_rel_PER (equiv e_u') x x).
        { apply Hper. unfold union_closure_PER.
          apply PER_clo_base. left. exact Hxx. }
        edestruct uf_rel_PER_has_key as [Hkx _];
          [exact Hroots' | exact Hxx' |].
        unfold Sep.has_key in Hkx. rewrite Hgx in Hkx. tauto. }
      (* Establish the soundness of the new PER edge (r, atom_ret a).
         From Hin we have atom_in_egraph (a.fn, a.args, r) e_in, hence
         (by atom_interpretation) atom_sound_for_model i (a.fn, a.args, r).
         Combined with Hatom_sound and interprets_to_functional, the two
         return ids are domain_eq, i.e. eq_sound_for_model i r (atom_ret a). *)
      destruct Hsound as [Hi_wf Hi_exact Hi_atom Hi_rel].
      assert (Hr_eq : eq_sound_for_model m i r (atom_ret a)).
      { pose proof (Hi_atom _ Hin) as Hatom_r.
        eapply atom_sound_eq_ret with (args1 := atom_args a) (args2 := atom_args a).
        - exact Hatom_r.
        - (* Hatom_sound has type atom_sound_for_model m i a;
             we need atom_sound_for_model m i (Build_atom (atom_fn a) ...). *)
          revert Hatom_sound. clear.
          destruct a; cbn in *. intros; assumption.
        - (* all2 eq_sound on (atom_args a) with itself *)
          unfold atom_sound_for_model in Hatom_sound; cbn in Hatom_sound.
          destruct (list_Mmap (map.get i) (atom_args a)) as [arg_doms|] eqn:Hargdoms;
            cbn in Hatom_sound; [|tauto].
          destruct (map.get i (atom_ret a)) as [da|] eqn:Hia;
            cbn in Hatom_sound; [|tauto].
          pose proof (interprets_to_implies_wf_args _ _ _ Hatom_sound) as Hwf.
          clear -Hwf Hargdoms.
          revert arg_doms Hargdoms Hwf.
          induction (atom_args a) as [|x xs IH]; cbn; intros arg_doms Hmap Hwf.
          + auto.
          + destruct (map.get i x) as [vx|] eqn:Hgx; cbn in Hmap; [|discriminate].
            destruct (list_Mmap (map.get i) xs) as [ls|] eqn:Hmxs; cbn in Hmap;
              [|discriminate].
            inversion Hmap; subst arg_doms.
            destruct Hwf as [Hwfx Hwfls]. split.
            * unfold eq_sound_for_model. rewrite Hgx. cbn.
              exact Hwfx.  (* domain_wf vx = domain_eq vx vx *)
            * eapply IH; eauto. }
      (* rel_interpretation: new PER edges are either in old PER or
         the closure with (r, atom_ret a). *)
      assert (Hrel_new : forall i1 i2,
                          uf_rel_PER (equiv e_u') i1 i2 ->
                          eq_sound_for_model m i i1 i2).
      { intros i1 i2 Hi12. apply Hper in Hi12.
        induction Hi12.
        - destruct H1 as [Hold | Hnew].
          + apply Hi_rel. exact Hold.
          + destruct Hnew as [Hpa Hpb]. subst.
            exact Hr_eq.
        - eapply eq_sound_for_model_trans; eauto.
        - eapply eq_sound_for_model_Symmetric; eauto. }
      (* Old PER edges still hold in new equiv (one direction of Hper). *)
      assert (Hper_lift : forall i1 i2,
                          uf_rel_PER (equiv e_in) i1 i2 ->
                          uf_rel_PER (equiv e_u') i1 i2).
      { intros i1 i2 Hi12. apply Hper.
        unfold union_closure_PER. apply PER_clo_base. left. exact Hi12. }
      split; [|split].
      + (* egraph_ok e_u' *)
        constructor.
        * exact Hroots.
        * (* worklist_ok: either same or new union_repair entry *)
          assert (Hwl_lift : forall ent, worklist_entry_ok (equiv e_in) ent ->
                                         worklist_entry_ok (equiv e_u') ent).
          { intros ent. destruct ent as [old new improved|x]; cbn.
            - intros Hper_old. unfold uf_rel_PER in *.
              apply Hper_lift. exact Hper_old.
            - intros; exact I. }
          destruct Hwl_rel as [Hwl_same | Hwl_new].
          { rewrite Hwl_same.
            eapply all_wkn; [|exact Hwlok].
            intros ent _. apply Hwl_lift. }
          { destruct Hwl_new as [v_old Hwl_new'].
            destruct Hwl_new' as [v_new Hwl_new''].
            destruct Hwl_new'' as [improved Hwl_new3].
            destruct Hwl_new3 as [Hwl_eq Hpers].
            destruct Hpers as [Hper_old Hper_new].
            rewrite Hwl_eq. cbn. split.
            - (* v_old ~ v_new via v_old ~ r ~ atom_ret a ~ v_new *)
              assert (Hr_ar : uf_rel_PER (equiv e_u') r (atom_ret a)).
              { apply Hper. apply PER_clo_base. right. unfold singleton_rel.
                split; reflexivity. }
              unfold uf_rel_PER in *.
              eapply PER_clo_trans; [exact Hper_old|].
              eapply PER_clo_trans; [exact Hr_ar|].
              apply PER_clo_sym. exact Hper_new.
            - eapply all_wkn; [|exact Hwlok].
              intros ent _. apply Hwl_lift. }
        * (* parents_ok: parents same, PER monotone *)
          rewrite <- Hpar_eq. intros x s Hgs. specialize (Hparok _ _ Hgs).
          eapply all_wkn; [|exact Hparok].
          intros b _ Hbup.
          destruct Hbup as [bb Hcan_ain].
          destruct Hcan_ain as [Hcan Hbain].
          destruct Hcan as [Hfn_bb Hargs_ret].
          destruct Hargs_ret as [Hargs_bb Hret_bb].
          exists bb. split.
          { unfold atom_canonical_equiv. split; [exact Hfn_bb|]. split.
            + clear -Hargs_bb Hper_lift.
              revert Hargs_bb. generalize (atom_args b), (atom_args bb).
              intros l1 l2. revert l2.
              induction l1 as [|y ys IH]; destruct l2 as [|z zs];
                cbn; auto; try tauto.
              intros [Hy Hys]. split.
              * apply Hper_lift. exact Hy.
              * apply IH. exact Hys.
            + apply Hper_lift. exact Hret_bb. }
          { unfold atom_in_egraph. rewrite <- Hdb_eq. exact Hbain. }
        * (* db_idxs_in_equiv: db same, has_key preserved via Hkey_pres *)
          rewrite <- Hdb_eq. intros b Hbain. specialize (Hdbkok _ Hbain).
          destruct Hdbkok as [Hka Hkr]. split.
          { eapply all_wkn; [|exact Hka].
            intros j _ Hj. apply Hkey_pres. exact Hj. }
          { apply Hkey_pres. exact Hkr. }
      + (* egraph_sound_for_interpretation *)
        constructor.
        * exact Hi_wf.
        * intros y Hy. apply Hkey_pres. apply Hi_exact. exact Hy.
        * (* atom_interpretation: db same *)
          unfold atom_in_egraph. rewrite <- Hdb_eq. exact Hi_atom.
        * exact Hrel_new.
      + exact Hkey_pres.
    - (* None: db_set a — apply db_set_sound *)
      intros s_pre HpreL. destruct HpreL as [Heq Hnone]; subst s_pre.
      pose proof (db_set_sound i a) as Hdss.
      unfold vc in Hdss. specialize (Hdss e_in).
      intros Hok Hsound Hargs Hret Hatom_sound.
      apply Hdss; auto.
  Qed.

  (* Dispatcher: [update_entry a'] case-splits on [db_lookup a'.fn
     a'.args]; the [Some r] case uses
     [union_after_canonicalize_denote_iff] and the [None] case uses
     [db_set_after_canonicalize_denote_iff]. *)
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
           (* New: PER fact for the literal removed key, provided by the
              prepended [repair_each] union step. *)
           (forall r0, atom_in_db (Build_atom (atom_fn a) (atom_args a) r0)
                                  e_ref.(db) ->
                       uf_rel_PER e_ref.(equiv) r0 (atom_ret a)) ->
           egraph_ok (snd res)
           /\ (forall i, denote e_ref i <-> denote (snd res) i)
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) side_l
           /\ equiv_extends e_ref (snd res)).
  Proof.
    unfold update_entry.
    vc_bind db_lookup_pure.
    rename s0 into e1, a0 into mr.
    destruct mr as [r|]; cbn beta iota; cbn [fst snd];
      intros s_pre [Hs_eq Hatom_case]; subst s_pre;
      intros Hok_ref Hatom_ref Hatoms_ref Hpost
             Hex_e1 Hf01 Hfn_eq Hret_eq Hargs_eq Hper_lk.
    - (* Some r: invoke union branch *)
      pose proof (union_after_canonicalize_denote_iff
                    a a' side_l e_ref e0 r
                    Hok_ref Hatom_ref Hatoms_ref Hpost Hper_lk) as Hu.
      specialize (Hu e1).
      apply Hu; auto.
    - (* None: invoke db_set branch *)
      pose proof (db_set_after_canonicalize_denote_iff
                    a a' side_l e_ref e0
                    Hok_ref Hatom_ref Hatoms_ref Hpost Hper_lk) as Hd.
      specialize (Hd e1).
      apply Hd; auto.
  Qed.

  (* The conditional-union prefix of the new [repair_each]: looks up
     the entry literally at [(atom_fn a, atom_args a)] and, if found,
     unions its [entry_value] with [atom_ret a].  Behavior is identical
     to a no-op whenever [entry_value = atom_ret a] (the only case that
     actually arises in egglog execution, since [parents] only stores
     atoms that were inserted via [db_set'] with their own [atom_ret]).
     The point of this step is to materialize the PER link
     [v ~ atom_ret a] in [equiv] so that downstream the up-to-equiv
     witness for [a] at the removed key links to [atom_ret a]. *)
  Lemma repair_each_prefix_denote_iff a l (x_old x_canonical : idx)
    : vc (@! let mv <- db_lookup a.(atom_fn) a.(atom_args) in
             match mv with
             | Some v => Defs.union v a.(atom_ret)
             | None => Mret a.(atom_ret)
             end)
        (fun e res =>
           egraph_ok e ->
           atom_in_egraph_up_to_equiv a e ->
           all (fun a' => atom_in_egraph_up_to_equiv a' e) l ->
           uf_rel_PER e.(equiv) x_old x_canonical ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ atom_in_egraph_up_to_equiv a (snd res)
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) l
           /\ equiv_extends e (snd res)
           /\ uf_rel_PER (snd res).(equiv) x_old x_canonical
           /\ e.(db) = (snd res).(db)
           /\ (forall r, atom_in_db
                           (Build_atom a.(atom_fn) a.(atom_args) r) e.(db)
                         -> uf_rel_PER (snd res).(equiv) r a.(atom_ret))).
  Proof.
    vc_bind db_lookup_pure.
    rename s0 into e_init, a0 into mv.
    destruct mv as [v | ]; cbn beta iota; cbn [fst snd];
      intros e_lkup [He_eq Hlk]; subst e_lkup.
    - (* Some v: union v with a.(atom_ret) *)
      intros Hok_init Hatom_init Hatoms_init Hper_init.
      pose proof Hlk as Hain_v.
      (* has_key facts for the union's preconditions *)
      pose proof Hok_init as Hok_init'.
      destruct Hok_init' as [Heq_init _ _ Hdb_init].
      assert (Hkv : Sep.has_key v e_init.(equiv).(parent)).
      { destruct (Hdb_init _ Hain_v) as [_ Hret_key]. exact Hret_key. }
      pose proof (atom_in_egraph_up_to_equiv_has_key e_init a Hok_init Hatom_init)
        as [_Hkargs Hkaret].
      pose proof (union_sound v a.(atom_ret) e_init Heq_init Hkv Hkaret) as Hu.
      destruct (Defs.union v a.(atom_ret) e_init) as [u_v e_post] eqn:Eunion.
      cbn [fst snd] in Hu |- *.
      destruct Hu as (Hdb_eq & Hex_post & Hper_iff & Hpar_eq
                      & Hwl_rel & Hu_v_aret).
      (* [Hext] lifts e_init's PER into e_post's PER. *)
      assert (Hext : forall x1 y1, uf_rel_PER e_init.(equiv) x1 y1 ->
                                   uf_rel_PER e_post.(equiv) x1 y1).
      { intros x1 y1 Hxy. apply Hper_iff. apply PER_clo_base. left. exact Hxy. }
      assert (Hv_aret_post : uf_rel_PER e_post.(equiv) v a.(atom_ret)).
      { apply Hper_iff. apply PER_clo_base. right. split; reflexivity. }
      (* [Hkey_lift]: union preserves has_key — any j in e_init.equiv's
         key set has [uf_rel_PER e_init.equiv j j] (from get-then-get-back),
         lifts via [Hext] to e_post's PER, then [uf_rel_PER_has_key]. *)
      assert (Hkey_lift : forall j, Sep.has_key j e_init.(equiv).(parent) ->
                                    Sep.has_key j e_post.(equiv).(parent)).
      { intros j Hj.
        destruct Hex_post as [roots_post Huf_post].
        assert (Hjj_init : uf_rel_PER e_init.(equiv) j j).
        { unfold Sep.has_key in Hj.
          destruct (map.get e_init.(equiv).(parent) j) as [v_j|] eqn:Hgj;
            [|tauto].
          unfold uf_rel_PER.
          eapply PER_clo_trans;
            [apply PER_clo_base; exact Hgj
            |apply PER_clo_sym; apply PER_clo_base; exact Hgj]. }
        exact (proj1 (uf_rel_PER_has_key e_post.(equiv) roots_post j j
                       Huf_post (Hext _ _ Hjj_init))). }
      split.
      { (* egraph_ok e_post *)
        pose proof Hok_init as [_ Hwl_init Hpa_init _].
        constructor.
        - (* egraph_equiv_ok *) exact Hex_post.
        - (* worklist_ok: case on [Hwl_rel] *)
          destruct Hwl_rel as [Hwl_unchanged
                              | (v_old & v' & ar & Hwl_new & Hv_old & Hv')].
          + rewrite Hwl_unchanged.
            eapply all_wkn; [|exact Hwl_init].
            intros [old new improved | k] _ Hent; cbn in *; auto.
          + rewrite Hwl_new. cbn. split.
            * (* uf_rel_PER e_post.equiv v_old v':
                 v_old ~ v ~ a.ret ~ v' via transitivity *)
              unfold uf_rel_PER in *.
              eapply PER_clo_trans; [exact Hv_old|].
              eapply PER_clo_trans; [exact Hv_aret_post|].
              apply PER_clo_sym. exact Hv'.
            * eapply all_wkn; [|exact Hwl_init].
              intros [old new improved | k] _ Hent; cbn in *; auto.
        - (* parents_ok: parents unchanged; lift via PER monotonicity *)
          intros x s Hgs. rewrite <- Hpar_eq in Hgs.
          eapply all_wkn; [|apply (Hpa_init _ _ Hgs)].
          intros b _ Hbain.
          destruct Hbain as (aa & (Hfn & Hargs & Hret) & Hain).
          exists aa. split.
          + unfold atom_canonical_equiv. split; [exact Hfn|]. split.
            * clear -Hargs Hext.
              revert Hargs. generalize (atom_args b), (atom_args aa).
              intros l1 l2. revert l2.
              induction l1 as [|y ys IH]; destruct l2 as [|z zs];
                cbn; auto; try tauto.
              intros [Hyz Hys]. split;
                [apply Hext; exact Hyz | apply IH; exact Hys].
            * apply Hext; exact Hret.
          + unfold atom_in_egraph in *. rewrite <- Hdb_eq. exact Hain.
        - (* db_idxs_in_equiv: db unchanged, lift has_key *)
          intros b Hbain. rewrite <- Hdb_eq in Hbain.
          destruct (Hdb_init _ Hbain) as [Hargs_keys Hret_key].
          split.
          + eapply all_wkn; [|exact Hargs_keys]; intros; apply Hkey_lift; auto.
          + apply Hkey_lift; exact Hret_key.
      }
      (* Reverse key-lift: the union's PER closure base cases live
         in e_init's PER + {(v, a.ret)}; both v and a.ret are
         already has_key in e_init (Hkv / Hkaret), and induction on
         the closure transports has_key back. *)
      assert (Hkey_back : forall j, Sep.has_key j e_post.(equiv).(parent) ->
                                    Sep.has_key j e_init.(equiv).(parent)).
      { intros j Hj.
        destruct Hex_post as [roots_post Huf_post].
        destruct Heq_init as [roots_init Huf_init].
        assert (Hjj_post : uf_rel_PER e_post.(equiv) j j).
        { unfold Sep.has_key in Hj.
          destruct (map.get e_post.(equiv).(parent) j) as [v_j|] eqn:Hgj;
            [|tauto].
          unfold uf_rel_PER.
          eapply PER_clo_trans;
            [apply PER_clo_base; exact Hgj
            |apply PER_clo_sym; apply PER_clo_base; exact Hgj]. }
        apply Hper_iff in Hjj_post.
        assert (Hclo_key : forall p q,
                  union_closure_PER (uf_rel_PER e_init.(equiv))
                    (singleton_rel v a.(atom_ret)) p q ->
                  Sep.has_key p e_init.(equiv).(parent)
                  /\ Sep.has_key q e_init.(equiv).(parent)).
        { intros p q Hpq.
          induction Hpq as [p q Hbase | p q r _ IH1 _ IH2 | p q _ IH].
          - destruct Hbase as [Hbase | Hsing].
            + apply (uf_rel_PER_has_key _ _ _ _ Huf_init Hbase).
            + destruct Hsing as [Heq1 Heq2]; subst.
              split; [exact Hkv | exact Hkaret].
          - split; [apply IH1 | apply IH2].
          - destruct IH; split; assumption. }
        exact (proj1 (Hclo_key _ _ Hjj_post)). }
      split.
      { intros i. split.
        { (* Forward: e_init sound → e_post sound. *)
          intros [Hwf Hexact Hatom_e Hrel_e].
          constructor.
          - exact Hwf.
          - intros x Hx. apply Hkey_lift. apply Hexact. exact Hx.
          - intros b Hbain. apply Hatom_e.
            unfold atom_in_egraph in *. rewrite Hdb_eq. exact Hbain.
          - intros i1 i2 Hi12.
            apply Hper_iff in Hi12.
            induction Hi12 as [p q Hbase | p q r _ IH1 _ IH2 | p q _ IH].
            + destruct Hbase as [Hbase | Hsing].
              * apply Hrel_e; exact Hbase.
              * destruct Hsing as [Hpv Hqaret]; subst.
                (* eq_sound (i v) (i a.ret) via interprets_to_functional *)
                destruct Hatom_init as
                  (aa & (Hfn_aa & Hargs_aa & Hret_aa) & Hain_aa).
                destruct aa as [fn_aa args_aa ret_aa]; cbn in *.
                subst fn_aa.
                pose proof (Hatom_e _ Hain_v) as Hsa_v.
                pose proof (Hatom_e _ Hain_aa) as Hsa_aa.
                cbn in Hsa_v, Hsa_aa.
                (* args_aa ~PER~ atom_args a lifted to eq_sound *)
                assert (Hargs_eq :
                  all2 (eq_sound_for_model m i) args_aa (atom_args a)).
                { clear -Hargs_aa Hrel_e.
                  revert Hargs_aa. generalize (atom_args a), args_aa.
                  intros l1 l2. revert l1.
                  induction l2 as [|y ys IH]; destruct l1 as [|z zs];
                    cbn; auto; try tauto.
                  intros [Hyz Hys]. split.
                  - apply Hrel_e. unfold uf_rel_PER in *.
                    apply PER_clo_sym. exact Hyz.
                  - apply IH; exact Hys. }
                (* atom_sound_eq_ret: aa and (a.fn, a.args, v) sound,
                   args eq_sound → ret_aa eq_sound v *)
                pose proof (atom_sound_eq_ret i (atom_fn a)
                              args_aa (atom_args a)
                              ret_aa v
                              Hsa_aa Hsa_v Hargs_eq) as Hret_eq.
                (* combine with ret_aa ~PER~ a.ret lifted via Hrel_e *)
                eapply eq_sound_for_model_trans;
                  [apply eq_sound_for_model_Symmetric; exact Hret_eq |].
                apply Hrel_e.
                unfold uf_rel_PER in *.
                apply PER_clo_sym. exact Hret_aa.
            + eapply eq_sound_for_model_trans; eauto.
            + apply eq_sound_for_model_Symmetric; exact IH. }
        { (* Backward: e_post sound → e_init sound. *)
          intros [Hwf Hexact Hatom_e Hrel_e].
          constructor.
          - exact Hwf.
          - intros x Hx. apply Hkey_back. apply Hexact. exact Hx.
          - intros b Hbain. apply Hatom_e.
            unfold atom_in_egraph in *. rewrite <- Hdb_eq. exact Hbain.
          - intros i1 i2 Hi12.
            apply Hrel_e. apply Hext. exact Hi12. } }
      split.
      { (* atom_in_egraph_up_to_equiv a e_post: same witness, PER widened *)
        destruct Hatom_init as (aa & (Hfn_aa & Hargs_aa & Hret_aa) & Hain_aa).
        exists aa. split.
        - unfold atom_canonical_equiv. split; [exact Hfn_aa|]. split.
          + clear -Hargs_aa Hext.
            revert Hargs_aa. generalize (atom_args a), (atom_args aa).
            intros l1 l2. revert l2.
            induction l1 as [|y ys IH]; destruct l2 as [|z zs];
              cbn; auto; try tauto.
            intros [Hyz Hys]. split; [apply Hext; exact Hyz | apply IH; exact Hys].
          + apply Hext; exact Hret_aa.
        - unfold atom_in_egraph in *. rewrite <- Hdb_eq. exact Hain_aa. }
      split.
      { (* all (atom_in_egraph_up_to_equiv ... e_post) l: same lift *)
        clear -Hatoms_init Hext Hdb_eq.
        induction l as [|b bs IH]; cbn in *; auto.
        destruct Hatoms_init as [Hb Hbs]. split.
        - destruct Hb as (aa & (Hfn & Hargs & Hret) & Hain).
          exists aa. split.
          + unfold atom_canonical_equiv. split; [exact Hfn|]. split.
            * clear -Hargs Hext.
              revert Hargs. generalize (atom_args b), (atom_args aa).
              intros l1 l2. revert l2.
              induction l1 as [|y ys IH]; destruct l2 as [|z zs];
                cbn; auto; try tauto.
              intros [Hyz Hys]. split; [apply Hext; exact Hyz | apply IH; exact Hys].
            * apply Hext; exact Hret.
          + unfold atom_in_egraph in *. rewrite <- Hdb_eq. exact Hain.
        - apply IH; exact Hbs. }
      split.
      { (* equiv_extends e_init e_post *)
        unfold equiv_extends. intros x1 y1 Hxy. apply Hext; exact Hxy. }
      split.
      { (* uf_rel_PER e_post.equiv x_old x_canonical *)
        apply Hext; exact Hper_init. }
      split; [exact Hdb_eq|].
      (* (forall r, atom_in_db (Build_atom a.fn a.args r) e_init.db ->
                    uf_rel_PER e_post.equiv r a.ret).
         The atom-in-db at key (a.fn, a.args) forces r = v (single entry
         per key), and union puts v ~ a.ret in e_post.equiv. *)
      intros r Hain_r.
      assert (Hr_eq : r = v).
      { clear -Hain_r Hain_v.
        unfold atom_in_egraph, atom_in_db, Is_Some_satisfying in *;
          cbn in *.
        destruct (map.get e_init.(db) a.(atom_fn)) as [tbl|]; cbn in *;
          try tauto.
        destruct (map.get tbl a.(atom_args)) as [entry|]; cbn in *;
          try tauto.
        congruence. }
      subst r. exact Hv_aret_post.
    - (* None: Mret a.(atom_ret); state unchanged *)
      intros Hok_init Hatom_init Hatoms_init Hper_init.
      split; [exact Hok_init|].
      split; [intros j; reflexivity|].
      split; [exact Hatom_init|].
      split; [exact Hatoms_init|].
      split; [apply equiv_extends_refl|].
      split; [exact Hper_init|].
      split; [reflexivity|].
      (* (forall r, atom_in_db (Build_atom a.fn a.args r) e_init.db ->
         uf_rel_PER e_init.equiv r a.ret): vacuous since [Hlk] says
         no such r exists. *)
      intros r Hr.
      exfalso. eapply Hlk; exact Hr.
  Qed.

  (* Composes the three pieces: [db_remove a] gives [post_db_remove],
     [canonicalize a] uses the has-key facts derived from
     [atom_in_egraph_up_to_equiv a e_ref] to produce a canonically-
     equivalent atom [a'] in a state with [equiv]-only changes, and
     [update_entry_canonicalized_denote_iff] finishes by restoring
     egraph_ok and denote w.r.t. the original [e_ref].  The new outer
     [db_lookup]/conditional-[union] prefix is handled by
     [repair_each_prefix_denote_iff], which both preserves all the
     pre-existing properties and yields the new PER fact that
     [update_entry_canonicalized_denote_iff] needs to discharge its
     sub-case B obligation. *)
  Lemma repair_each_denote_iff a l (x_old x_canonical : idx)
    : vc (@! let _ <- (@! let mv <- db_lookup a.(atom_fn) a.(atom_args) in
                          match mv with
                          | Some v => Defs.union v a.(atom_ret)
                          | None => Mret a.(atom_ret)
                          end) in
             let _ <- db_remove a in
             let a' <- canonicalize a in
             (update_entry a'))
        (fun e res =>
           egraph_ok e ->
           atom_in_egraph_up_to_equiv a e ->
           all (fun a' => atom_in_egraph_up_to_equiv a' e) l ->
           uf_rel_PER e.(equiv) x_old x_canonical ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ all (fun a' => atom_in_egraph_up_to_equiv a' (snd res)) l
           /\ equiv_extends e (snd res)).
  Proof.
    vc_bind (repair_each_prefix_denote_iff a l x_old x_canonical).
    rename s0 into e_orig, a0 into _u_pref.
    vc_bind db_remove_sound.
    rename s0 into e_ref, a0 into u_dbr.
    vc_bind canonicalize_preserves_fields_strong.
    rename s0 into e0, a0 into a'.
    eapply vc_consequence;
      [| apply (update_entry_canonicalized_denote_iff a a' l e_ref e0)].
    cbn beta. cbn [fst snd].
    intros e1 res Hupd Hcan Hdbr Hpref Hok_orig Hatom_orig Hatoms_orig
                  Hper_orig.
    destruct (Hpref Hok_orig Hatom_orig Hatoms_orig Hper_orig)
      as (Hok_ref & Hde_ref & Hatom_ref & Hatoms_ref & Hext_ref
          & Hper_old_can & Hdb_pref_eq & Hper_lookup_ret).
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
    (* Transport the prefix's PER fact from [e_orig.db] to [e_ref.db]
       (both equal since the prefix step doesn't touch the db). *)
    assert (Hper_lk_ref : forall r0,
              atom_in_db (Build_atom (atom_fn a) (atom_args a) r0)
                         e_ref.(db) ->
              uf_rel_PER e_ref.(equiv) r0 (atom_ret a)).
    { intros r0 Hain. apply Hper_lookup_ret. rewrite Hdb_pref_eq. exact Hain. }
    specialize (Hupd Hok_ref_orig Hatom_ref Hatoms_ref Hpost_full
                  Hex_e1 Hfp01 Hfn_a' Hret_a' Hargs_a' Hper_lk_ref).
    destruct Hupd as (Hok_res & Hde_res & Hatoms_res & Hext_res).
    split; [exact Hok_res|].
    split; [intros i; rewrite Hde_ref; exact (Hde_res i)|].
    split; [exact Hatoms_res|].
    eapply equiv_extends_trans; [exact Hext_ref | exact Hext_res].
  Qed.

  (* Iterating [repair_each] over a list of atoms-in-egraph preserves
     egraph_ok and denote, by induction with [repair_each_denote_iff]
     threading the side-list invariant. The [uf_rel_PER e.equiv x_old
     x_canonical] precondition (the [worklist_entry_ok]-derived fact
     for the [union_repair x_old x_canonical _] entry being processed)
     is preserved across iterations via [equiv_extends]. *)
  Lemma list_Mmap_repair_each_denote_iff old_ps (x_old x_canonical : idx)
    : vc (list_Mmap (fun a : atom =>
                       @! let _ <- (@! let mv <- db_lookup a.(atom_fn) a.(atom_args) in
                                       match mv with
                                       | Some v => Defs.union v a.(atom_ret)
                                       | None => Mret a.(atom_ret)
                                       end) in
                          let _ <- db_remove a in
                          let a' <- canonicalize a in
                          (update_entry a'))
                    old_ps)
        (fun e res =>
           egraph_ok e ->
           all (fun a => atom_in_egraph_up_to_equiv a e) old_ps ->
           uf_rel_PER e.(equiv) x_old x_canonical ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ equiv_extends e (snd res)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Mmap_inv _
                  (fun l s =>
                     egraph_ok s
                     /\ all (fun a => atom_in_egraph_up_to_equiv a s) l
                     /\ uf_rel_PER s.(equiv) x_old x_canonical)
                  (fun s s' => (forall i, denote s i <-> denote s' i)
                               /\ equiv_extends s s'))].
    - cbn beta. intros s res Hinv Hok Hall Hper.
      specialize (Hinv (conj Hok (conj Hall Hper))).
      destruct Hinv as ([Hok_p _] & Hiff & Hext). auto.
    - intros s _; split; [intros i; reflexivity | apply equiv_extends_refl].
    - intros ? ? ? [H1 He1] [H2 He2]; split;
        [intros i; rewrite H1; auto | eapply equiv_extends_trans; eauto].
    - intros a l_rest.
      eapply vc_consequence;
        [| apply (repair_each_denote_iff a l_rest x_old x_canonical)].
      cbn beta. intros s p Hone (Hok & Hall & Hper).
      cbn [all] in Hall. destruct Hall as [Ha Hl_rest].
      destruct (Hone Hok Ha Hl_rest Hper) as (Hok_p & Hde_p & Hl_p & Hext_p).
      split; [split; [exact Hok_p|]; split; [exact Hl_p|]; apply Hext_p; exact Hper |].
      split; [exact Hde_p | exact Hext_p].
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
    destruct Hok as [Heq Hwl Hpa Hdb]; cbn in *.
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
      + intros y s Hg. specialize (Hpa _ _ Hg).
        eapply all_wkn; [|exact Hpa].
        intros aa _ Hex.
        unfold atom_in_egraph_up_to_equiv, atom_canonical_equiv,
          atom_in_egraph in *.
        destruct Hex as (a'' & Hcanon & Hain'').
        exists a''; cbn in *. split.
        * exact Hcanon.
        * apply Hdb_iff. exact Hain''.
      + intros a' Ha'. apply Hdb. apply Hdb_iff. exact Ha'.
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
    vc_list_Miter_egraph_iff repair_parent_analysis_denote_iff.
  Qed.

  (* [repair_parent_analysis] only writes to db / analyses / worklist;
     equiv is unchanged. *)
  Lemma repair_parent_analysis_preserves_equiv a
    : vc (repair_parent_analysis a)
        (fun e res => (snd res).(equiv) = e.(equiv)).
  Proof.
    unfold repair_parent_analysis, vc.
    intros e. cbn [Mbind Mseq StateMonad.state_monad fst snd].
    destruct (db_lookup_entry idx symbol symbol_map idx_map idx_trie
                analysis_result (atom_fn a) (atom_args a) e)
      as [me e_l] eqn:Hlk; cbn [fst snd].
    assert (Hlk_eq : e_l = e).
    { unfold db_lookup_entry, Mret, StateMonad.state_monad in Hlk.
      repeat (match type of Hlk with
              | context [match ?x with _ => _ end] => destruct x; cbn in Hlk
              end); inversion Hlk; reflexivity. }
    subst e_l.
    destruct me as [entry|]; [|cbn; reflexivity].
    destruct entry as [v_epoch v old_a].
    pose proof (get_analyses_preserves_fields (atom_args a) e) as Hga.
    destruct (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result
                (atom_args a) e) as [arg_as e_g] eqn:Hge.
    cbn [fst snd] in Hga. destruct Hga as (_ & Heq_g & _).
    destruct (eqb (analyze idx symbol analysis_result a arg_as) old_a) eqn:Hcmp.
    - cbn [Mret StateMonad.state_monad fst snd]. exact Heq_g.
    - cbn [Mseq Mbind StateMonad.state_monad fst snd
           update_analyses push_worklist db_set_entry].
      destruct e_g as [db_g equiv_g parents_g epoch_g wl_g analyses_g log_g];
        cbn in *.
      unfold map_update.
      destruct (map.get db_g (atom_fn a)) as [tbl|] eqn:Htbl;
        cbn; exact Heq_g.
  Qed.

  (* [list_Miter repair_parent_analysis] iterates a no-equiv-change op,
     so equiv is unchanged across the whole iter. *)
  Lemma list_Miter_repair_parent_analysis_preserves_equiv ps
    : vc (list_Miter repair_parent_analysis ps)
        (fun e res => (snd res).(equiv) = e.(equiv)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Miter_inv _
                  (fun _ _ => True)
                  (fun s s' => s'.(equiv) = s.(equiv)))].
    - cbn beta. intros s res Hinv. apply (Hinv I).
    - intros s _; reflexivity.
    - intros ? ? ? H1 H2; congruence.
    - intros a l_rest.
      eapply vc_consequence; [| apply (repair_parent_analysis_preserves_equiv a)].
      cbn beta. intros s p Hone _. split; [exact I | exact Hone].
  Qed.

  (* The optional analysis pass after the parent-canonicalization mmap.
     Both branches (run-analyses or skip) preserve egraph_ok and denote.
     Equiv is preserved literally (the analysis pass only writes
     analyses/worklist/db); the [equiv_extends] conjunct is for callers
     that thread a [worklist_entry_ok]-derived PER fact through. *)
  Lemma repair_after_mmap_denote_iff x_canonical (improved : bool)
    : vc (if improved
          then (@! let canon_ps <- get_parents x_canonical in
                   (list_Miter repair_parent_analysis canon_ps))
          else Mret tt)
        (fun e res =>
           egraph_ok e ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ equiv_extends e (snd res)).
  Proof.
    destruct improved.
    - vc_bind get_parents_denote_iff.
      eapply vc_consequence;
        [| apply (vc_and _ _ _
                    (list_Miter_repair_parent_analysis_denote_iff a)
                    (list_Miter_repair_parent_analysis_preserves_equiv a))].
      cbn beta. intros s1 res [HIH Heq_res_s1] Hgp Hok_s0.
      cbn [fst snd] in Hgp.
      destruct (Hgp Hok_s0) as (Hok_s1 & Hde_s1 & Hs1_eq & _).
      destruct (HIH Hok_s1) as [Hok_res Hde_res].
      split; [exact Hok_res|].
      split; [intros i; rewrite Hde_s1; exact (Hde_res i)|].
      intros x y Hxy. rewrite Heq_res_s1, Hs1_eq; exact Hxy.
    - unfold vc, Mret, StateMonad.state_monad; cbn [fst snd].
      intros e Hok; split; [exact Hok|].
      split; [intros i; reflexivity | apply equiv_extends_refl].
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
           uf_rel_PER e.(equiv) x_old x_canonical ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ equiv_extends e (snd res)).
  Proof.
    unfold repair_union.
    vc_bind pull_parents_denote_iff.
    rename s0 into e_init, a into ps.
    vc_bind (list_Mmap_repair_each_denote_iff ps x_old x_canonical).
    rename s0 into s1, a into _u.
    eapply vc_consequence;
      [|apply (repair_after_mmap_denote_iff x_canonical improved)].
    cbn beta. cbn [fst snd]. intros s2 res HIH Hmap Hpull Hok_init Hper_init.
    destruct (Hpull Hok_init) as (Hok_s1 & Hde_s1 & Hequiv_s1 & Hains_s1).
    assert (Hper_s1 : uf_rel_PER s1.(equiv) x_old x_canonical)
      by (rewrite Hequiv_s1; exact Hper_init).
    destruct (Hmap Hok_s1 Hains_s1 Hper_s1) as (Hok_s2 & Hde_s2 & Hext_s2).
    destruct (HIH Hok_s2) as (Hok_res & Hde_res & Hext_res).
    split; [exact Hok_res|].
    split; [intros i; rewrite Hde_s1, Hde_s2; exact (Hde_res i)|].
    intros x y Hxy.
    apply Hext_res, Hext_s2.
    rewrite Hequiv_s1; exact Hxy.
  Qed.

  (* Top-level [repair] dispatches by worklist-entry shape. Union
     repairs delegate to [repair_union_denote_iff]; analysis repairs
     run [list_Miter_repair_parent_analysis] over the parents of the
     analyzed index. *)
  Lemma repair_denote_iff a
    : vc (repair a)
        (fun e res =>
           egraph_ok e ->
           worklist_entry_ok e.(equiv) a ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ equiv_extends e (snd res)).
  Proof.
    destruct a as [old new improved | i_repair]; cbn [repair].
    - unfold vc; intros e Hok Hwl.
      cbn in Hwl.
      apply (repair_union_denote_iff old new improved e); auto.
    - vc_bind get_parents_denote_iff.
      eapply vc_consequence;
        [| apply (vc_and _ _ _
                    (list_Miter_repair_parent_analysis_denote_iff a)
                    (list_Miter_repair_parent_analysis_preserves_equiv a))].
      cbn beta. cbn [fst snd]. intros s1 res [HIH Heq_res_s1] Hgp Hok_s0 _Hwl.
      destruct (Hgp Hok_s0) as (Hok_s1 & Hde_s1 & Hs1_eq & _).
      destruct (HIH Hok_s1) as [Hok_res Hde_res].
      split; [exact Hok_res|].
      split; [intros i; rewrite Hde_s1; exact (Hde_res i)|].
      intros x y Hxy. rewrite Heq_res_s1, Hs1_eq; exact Hxy.
  Qed.

  (* Iterate [repair] over a list of worklist entries. Used by
     [rebuild_sound]'s inner loop. *)
  Lemma list_Miter_repair_denote_iff l
    : vc (list_Miter repair l)
        (fun e res =>
           egraph_ok e ->
           all (worklist_entry_ok e.(equiv)) l ->
           egraph_ok (snd res)
           /\ (forall i, denote e i <-> denote (snd res) i)
           /\ equiv_extends e (snd res)).
  Proof.
    eapply vc_consequence;
      [| apply (vc_list_Miter_inv _
                  (fun l s => egraph_ok s /\ all (worklist_entry_ok s.(equiv)) l)
                  (fun s s' => (forall i, denote s i <-> denote s' i)
                               /\ equiv_extends s s'))].
    - cbn beta. intros e res Hinv Hok Hl.
      destruct (Hinv (conj Hok Hl)) as ((Hok_p & _) & Hiff & Hext); auto.
    - intros s _; split; [intros i; reflexivity | apply equiv_extends_refl].
    - intros ? ? ? [H1 He1] [H2 He2]; split;
        [intros i; rewrite H1; auto | eapply equiv_extends_trans; eauto].
    - intros a l_rest.
      eapply vc_consequence; [| apply (repair_denote_iff a)].
      cbn beta. intros s p Hone (Hok & Hwl).
      cbn [all] in Hwl. destruct Hwl as [Hwl_a Hwl_rest].
      destruct (Hone Hok Hwl_a) as (Hok_p & Hde_p & Hext_p).
      split; [split; [exact Hok_p|]|].
      + (* preserve all worklist_entry_ok across PER growth *)
        eapply all_wkn; [| exact Hwl_rest].
        intros ent _ Hent.
        eapply equiv_extends_worklist_entry_ok; [exact Hext_p | exact Hent].
      + split; [exact Hde_p | exact Hext_p].
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
    rename s0 into e_init, a into wl_pulled.
    destruct wl_pulled as [|w wl'].
    { unfold vc; cbn [Mret StateMonad.state_monad fst snd].
      intros s1 HPpull Hok_s0.
      destruct (HPpull Hok_s0) as (Hok_s1 & Hde_s1 & _).
      split; [exact Hok_s1 | exact Hde_s1]. }
    cbn [Mbind StateMonad.state_monad Mseq].
    vc_bind list_Mmap_canonicalize_worklist_entry_denote_iff.
    rename s0 into s1, a into wl_canon.
    vc_bind list_Miter_repair_denote_iff.
    rename s0 into s2, a into u_miter.
    eapply vc_consequence; [|apply IHn].
    cbn beta. cbn [fst snd]. intros s3 res HIH Hmiter Hmap Hpull Hok_init.
    destruct (Hpull Hok_init) as (Hok_s1 & Hde_s1 & Hequiv_s1 & Hwl_pulled).
    assert (Hwl_s1 : all (worklist_entry_ok s1.(equiv)) (w :: wl')).
    { rewrite Hequiv_s1; exact Hwl_pulled. }
    destruct (Hmap Hok_s1 Hwl_s1) as (Hok_s2 & Hde_s2 & _Hext_s2 & Hwl_canon_s2).
    pose proof (worklist_dedup_preserves_all
                  (worklist_entry_ok s2.(equiv)) wl_canon Hwl_canon_s2)
      as Hwl_dedup_s2.
    destruct (Hmiter Hok_s2 Hwl_dedup_s2) as (Hok_s3 & Hde_s3 & _Hext_s3).
    destruct (HIH Hok_s3) as [Hok_res Hde_res].
    split; [exact Hok_res|].
    intros i. rewrite Hde_s1, Hde_s2, Hde_s3, Hde_res. reflexivity.
  Qed.

  (* ============================================================== *)
  (* Soundness of exec_write                                         *)
  (* ============================================================== *)

  (* [allocate_existential_vars wvars env0] iterates [alloc] over
     [wvars], giving each write var a fresh egraph idx and accumulating
     the idx into the environment.  The domain values for the fresh idxs
     come from [a_src] (the source-assignment map).

     Soundness: given distinct [wvars] absent from [env0] and with
     domain values in [a_src], running [allocate_existential_vars] from
     an ok + sound egraph produces an ok + sound egraph (under an
     extended interpretation [i']), and every env0 entry and write-var
     entry survives into the result environment. *)
  Lemma allocate_existential_vars_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (a_src : idx_map m.(domain))
    (wvars : list idx)
    : forall (i : idx_map m.(domain)) (env0 : idx_map idx),
      List.NoDup wvars ->
      (forall w, In w wvars -> map.get env0 w = None) ->
      (forall w, In w wvars ->
                 exists d, map.get a_src w = Some d /\ m.(domain_wf) d) ->
      vc (allocate_existential_vars idx idx_succ symbol symbol_map idx_map idx_trie analysis_result wvars env0)
        (fun e_in res =>
           egraph_ok e_in ->
           egraph_sound_for_interpretation m i e_in ->
           egraph_ok (snd res) /\
           exists i',
             map.extends i' i /\
             egraph_sound_for_interpretation m i' (snd res) /\
             (forall x v, map.get env0 x = Some v -> map.get (fst res) x = Some v) /\
             (forall x, In x wvars ->
                        exists v d,
                          map.get (fst res) x = Some v /\
                          map.get a_src x = Some d /\
                          map.get i' v = Some d /\
                          Sep.has_key v (snd res).(equiv).(parent)) /\
             (forall x, Sep.has_key x e_in.(equiv).(parent) ->
                        Sep.has_key x (snd res).(equiv).(parent))).
  Proof.
    induction wvars as [|x wvars' IH]; intros i0 env0 Hnodup Hfresh Hdom.
    - (* base case: wvars = [] *)
      unfold allocate_existential_vars, list_Mfoldl.
      unfold vc; intros e_in; cbn [Mret StateMonad.state_monad fst snd].
      intros Hok Hsnd.
      split; [exact Hok|].
      exists i0. split; [intros k v0 Hg; exact Hg|].
      split; [exact Hsnd|].
      split; [intros x0 v0 Hg; exact Hg|].
      split; [intros x0 Hin; contradiction|].
      intros x0 Hx0; exact Hx0.
    - (* inductive case: x :: wvars' *)
      inversion Hnodup as [|?? Hnotin Hnodup']; subst.
      assert (Hfresh_x : map.get env0 x = None)
        by (apply Hfresh; left; reflexivity).
      assert (Hfresh' : forall w, In w wvars' -> map.get env0 w = None)
        by (intros w Hw; apply Hfresh; right; exact Hw).
      assert (Hdom' : forall w, In w wvars' ->
                                exists d, map.get a_src w = Some d /\ m.(domain_wf) d)
        by (intros w Hw; apply Hdom; right; exact Hw).
      assert (Hdx : exists d, map.get a_src x = Some d /\ m.(domain_wf) d)
        by (apply Hdom; left; reflexivity).
      destruct Hdx as (d_x & Ha_src_x & Hwf_dx).
      unfold allocate_existential_vars, list_Mfoldl.
      fold (list_Mfoldl (M:=state instance) (A:=idx) (B:=idx_map idx)).
      unfold vc; intros e_in.
      cbn [Mbind StateMonad.state_monad Mret].
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e_in)
        as [v_x e1] eqn:Halloc_eq.
      cbn [fst snd].
      intros Hok Hsnd.
      (* Apply alloc_sound for v_x: gives i1 = map.put i0 v_x d_x *)
      pose proof (alloc_sound Hlti Hlts Hltt i0 d_x Hwf_dx Hwf_dx) as Hals.
      unfold vc in Hals. specialize (Hals e_in).
      rewrite Halloc_eq in Hals. cbn [fst snd] in Hals.
      destruct Hals as (Hok1 & Hsnd1 & _Hi_vx_none & _Hk_vx_none & Hkv_x &
                        Hpres1 & _Hdb1 & _Hpar1 & _Hwl1); auto.
      (* i1 = map.put i0 v_x d_x *)
      set (i1 := map.put i0 v_x d_x).
      (* Derive preconditions for IH: write vars in wvars' not in (put env0 x v_x) *)
      assert (Hfresh_put : forall w, In w wvars' -> map.get (map.put env0 x v_x) w = None).
      { intros w Hw.
        rewrite map.get_put_diff.
        - apply Hfresh'. exact Hw.
        - intro Heq. subst w. exact (Hnotin Hw). }
      (* Apply IH for (wvars', i1, map.put env0 x v_x, e1) *)
      pose proof (IH i1 (map.put env0 x v_x) Hnodup' Hfresh_put Hdom') as IH1.
      unfold allocate_existential_vars, list_Mfoldl in IH1.
      fold (list_Mfoldl (M:=state instance) (A:=idx) (B:=idx_map idx)) in IH1.
      unfold vc in IH1. specialize (IH1 e1).
      destruct IH1 as (Hok2 & i2 & Hi2ext1 & Hsnd2 & Henv2 & Hwvars2 & Hpres2); auto.
      split; [exact Hok2|].
      (* i' = i2 extends i1 = map.put i0 v_x d_x extends i0 *)
      exists i2.
      assert (Hi2ext0 : map.extends i2 i0).
      { intros k vk Hg.
        apply Hi2ext1.
        unfold i1. rewrite map.get_put_diff.
        - exact Hg.
        - intro Heq. subst k.
          (* v_x is NOT in i0 (from alloc_sound) but map.get i0 k = Some vk — contradiction *)
          rewrite _Hi_vx_none in Hg. discriminate. }
      split; [exact Hi2ext0|].
      split; [exact Hsnd2|].
      split.
      { (* env0 entries preserved *)
        intros x0 v0 Hg0.
        apply Henv2.
        rewrite map.get_put_diff.
        - exact Hg0.
        - intro Heq. subst x0. rewrite Hfresh_x in Hg0. discriminate. }
      split.
      { (* each write var in (x :: wvars') has its fresh idx in result env *)
        intros x0 Hin0.
        destruct Hin0 as [Heq | Hin'].
        - (* x0 = x: use alloc for v_x *)
          subst x0.
          (* IH env preservation: put env0 x v_x maps x to v_x, result preserves it *)
          assert (Hxv : map.get (map.put env0 x v_x) x = Some v_x)
            by apply map.get_put_same.
          apply Henv2 in Hxv.
          (* map.get i2 v_x = Some d_x because i2 extends i1 and i1 v_x = Some d_x *)
          assert (Hi1_vx : map.get i1 v_x = Some d_x).
          { unfold i1. apply map.get_put_same. }
          apply Hi2ext1 in Hi1_vx.
          exists v_x, d_x.
          split; [exact Hxv|].
          split; [exact Ha_src_x|].
          split; [exact Hi1_vx|].
          apply Hpres2. exact Hkv_x.
        - (* In x0 wvars': from IH *)
          destruct (Hwvars2 x0 Hin') as (v0 & d0 & Hgv0 & Hasrc0 & Hi2_v0 & Hkey0).
          exists v0, d0.
          exact (conj Hgv0 (conj Hasrc0 (conj Hi2_v0 Hkey0))). }
      { (* parent keys monotone *)
        intros x0 Hx0. apply Hpres2. apply Hpres1. exact Hx0. }
  Qed.

  Lemma list_Mmap_env_i'
    (env0 : idx_map idx) (i0 : idx_map (m.(domain)))
    (a_src0 : idx_map (m.(domain))) (args0 : list idx) :
    (forall j, In j args0 ->
       exists v, map.get env0 j = Some v /\ map.get i0 v = map.get a_src0 j) ->
    list_Mmap (map.get i0)
      (map (fun x => unwrap_with_default (map.get env0 x)) args0) =
    list_Mmap (map.get a_src0) args0.
  Proof.
    intros Henv0.
    induction args0 as [|j js IH]; cbn; [ reflexivity | ].
    destruct (Henv0 j (or_introl eq_refl)) as (v & Hg & Hi).
    rewrite Hg. cbn. rewrite Hi.
    rewrite IH; [ reflexivity | ].
    intros k Hk. apply Henv0. right. exact Hk.
  Qed.

  Lemma all2_uf_rel_has_key
    (uf : union_find) (l xs ys : list idx) :
    union_find_ok lt uf l ->
    all2 (uf_rel_PER uf) xs ys ->
    all (fun v => Sep.has_key v (parent uf)) ys ->
    all (fun v => Sep.has_key v (parent uf)) xs.
  Proof.
    intros Hok.
    revert ys.
    induction xs as [|x xs' IH]; intros ys Hall2 Hky.
    - cbn. tauto.
    - destruct ys as [|y ys']; cbn in Hall2; [ tauto | ].
      destruct Hall2 as [Hrel Hall2'].
      cbn in Hky. destruct Hky as [Hky_y Hky_ys].
      cbn. split.
      + edestruct uf_rel_PER_has_key as [Hk _]; [ exact Hok | exact Hrel | ]. exact Hk.
      + eapply IH; [ exact Hall2' | exact Hky_ys ].
  Qed.

  Lemma exec_clause_sound
    (i : idx_map (m.(domain)))
    (env : idx_map idx) (c : atom) (a_src : idx_map (m.(domain))) (e : instance) :
    egraph_ok e ->
    egraph_sound_for_interpretation m i e ->
    (forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
       exists v, map.get env x = Some v
                 /\ Sep.has_key v (parent (equiv e))
                 /\ map.get i v = map.get a_src x) ->
    atom_sound_for_model m a_src c ->
    match exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env c e with
    | (_, e') =>
        egraph_ok e'
        /\ egraph_sound_for_interpretation m i e'
        /\ (forall z, Sep.has_key z (parent (equiv e)) -> Sep.has_key z (parent (equiv e')))
    end.
  Proof.
    intros Hok Hsound Henv Hatom_src.
    unfold exec_clause.
    cbn [Mbind Mret StateMonad.state_monad].
    set (args_vals := map (fun x => unwrap_with_default (map.get env x)) (atom_args c)).
    set (out_val := unwrap_with_default (map.get env (atom_ret c))).
    assert (Henv_args : forall j, In j (atom_args c) ->
      exists v, map.get env j = Some v /\ Sep.has_key v (parent (equiv e)) /\ map.get i v = map.get a_src j).
    { intros j Hj. apply Henv. right. exact Hj. }
    destruct (Henv (atom_ret c) (or_introl eq_refl)) as (vr & Hgvr & Hkr & Hivr).
    assert (Hkey_args : all (fun v => Sep.has_key v (parent (equiv e))) args_vals).
    { unfold args_vals.
      assert (H_ka : forall (xs : list idx),
        (forall j, In j xs -> exists v, map.get env j = Some v /\ Sep.has_key v (parent (equiv e))) ->
        all (fun v => Sep.has_key v (parent (equiv e))) (map (fun x => unwrap_with_default (map.get env x)) xs)).
      { induction xs as [|x xs' IH]; cbn; [ tauto | ].
        intros Hxs. split.
        { destruct (Hxs x (or_introl eq_refl)) as (v & Hg & Hk). rewrite Hg. exact Hk. }
        { apply IH. intros y Hy. apply Hxs. right. exact Hy. } }
      apply H_ka. intros j Hj. destruct (Henv_args j Hj) as (v & Hg & Hk & _).
      exact (ex_intro _ v (conj Hg Hk)). }
    assert (Hkey_out : Sep.has_key out_val (parent (equiv e))).
    { unfold out_val. rewrite Hgvr. exact Hkr. }
    unfold atom_sound_for_model in Hatom_src.
    cbn [atom_args atom_ret atom_fn] in Hatom_src.
    destruct (list_Mmap (map.get a_src) (atom_args c)) as [doms|] eqn:Hdoms;
      cbn [Is_Some_satisfying] in Hatom_src; [ | tauto ].
    destruct (map.get a_src (atom_ret c)) as [out_dom|] eqn:Hout_dom;
      cbn [Is_Some_satisfying] in Hatom_src; [ | tauto ].
    assert (Hi_args_vals : list_Mmap (map.get i) args_vals = Some doms).
    { rewrite <- Hdoms. unfold args_vals.
      apply list_Mmap_env_i'.
      intros j Hj. destruct (Henv_args j Hj) as (v & Hg & _ & Hiv).
      exact (ex_intro _ v (conj Hg Hiv)). }
    assert (Hi_out_val : map.get i out_val = Some out_dom).
    { unfold out_val. rewrite Hgvr. cbn. exact Hivr. }
    destruct Hok as [Heqok Hwlok Hparok Hdbkok].
    destruct Heqok as [roots Hroots].
    assert (Hok_e : egraph_ok e).
    { constructor; [ exact (ex_intro _ roots Hroots) | exact Hwlok | exact Hparok | exact Hdbkok ]. }
    pose proof (list_Mmap_find_preserves_fields_strong args_vals) as Hlm.
    unfold vc in Hlm. specialize (Hlm e).
    destruct (list_Mmap find args_vals e) as [args_vals' e1] eqn:Hlma.
    cbn [fst snd] in Hlm.
    destruct (Hlm (ex_intro _ roots Hroots) Hkey_args) as (Hex1 & Hfp01 & Hall_args').
    assert (Hkey_out_e1 : Sep.has_key out_val (parent (equiv e1))).
    { destruct Hfp01 as (_ & _ & _ & _ & _ & Hkey_iff & _). apply Hkey_iff. exact Hkey_out. }
    pose proof (find_preserves_fields_strong out_val) as Hfind_out.
    unfold vc in Hfind_out. specialize (Hfind_out e1).
    destruct (find out_val e1) as [out_val' e2] eqn:Hfinoa.
    cbn [fst snd] in Hfind_out.
    destruct (Hfind_out Hex1 Hkey_out_e1) as (Hex2 & Hfp12 & Huf_out).
    cbn [fst snd atom_fn].
    assert (Hfp02 : fields_preserved e e2).
    { eapply fields_preserved_trans; [ exact Hfp01 | exact Hfp12 ]. }
    assert (Hok2 : egraph_ok e2).
    { exact (fields_preserved_egraph_ok e e2 Hok_e Hfp02 Hex2). }
    assert (Hsound2 : egraph_sound_for_interpretation m i e2).
    { eapply fields_preserved_sound_for_interpretation; eassumption. }
    assert (Hall2 : all2 (uf_rel_PER (equiv e2)) args_vals' args_vals).
    { destruct Hfp12 as (_ & _ & _ & _ & _ & _ & Huf_iff).
      eapply all2_impl; [ | exact Hall_args' ].
      intros x y Hxy. apply Huf_iff. exact Hxy. }
    pose proof (args_rel_interpretation m i e2 (conj Hok2 Hsound2) args_vals' args_vals Hall2) as Hrel_args.
    rewrite Hi_args_vals in Hrel_args.
    destruct (list_Mmap (map.get i) args_vals') as [doms'|] eqn:Hdoms'.
    2: { cbn in Hrel_args. discriminate. }
    cbn [option_relation] in Hrel_args.
    assert (Hrel_out : eq_sound_for_model m i out_val' out_val).
    { apply (rel_interpretation _ i _ Hsound2). exact Huf_out. }
    unfold eq_sound_for_model in Hrel_out.
    rewrite Hi_out_val in Hrel_out.
    destruct (map.get i out_val') as [out_dom'|] eqn:Hout_val';
      cbn [Is_Some_satisfying] in Hrel_out; [ | tauto ].
    assert (Hatom_i : atom_sound_for_model m i
      {| atom_fn := atom_fn c; atom_args := args_vals'; atom_ret := out_val' |}).
    { unfold atom_sound_for_model. cbn [atom_args atom_ret atom_fn].
      rewrite Hdoms'. cbn [Is_Some_satisfying].
      rewrite Hout_val'. cbn [Is_Some_satisfying].
      eapply interprets_to_preserved; [ exact Hatom_src | | ].
      - eapply all2_Symmetric; [ | exact Hrel_args ].
        apply domain_eq_PER.
      - apply domain_eq_PER. exact Hrel_out. }
    destruct Hex2 as [roots2 Hroots2].
    assert (Hkey_all2 : all (fun v => Sep.has_key v (parent (equiv e2))) args_vals).
    { destruct Hfp02 as (_ & _ & _ & _ & _ & Hkey_iff & _).
      eapply all_wkn; [ | exact Hkey_args ].
      intros v _. apply Hkey_iff. }
    assert (Hkey_args2 : all (fun v => Sep.has_key v (parent (equiv e2))) args_vals').
    { exact (all2_uf_rel_has_key _ _ _ _ Hroots2 Hall2 Hkey_all2). }
    assert (Hkey_out2 : Sep.has_key out_val' (parent (equiv e2))).
    { edestruct uf_rel_PER_has_key as [Hk _]; [ exact Hroots2 | exact Huf_out | ]. exact Hk. }
    pose proof (update_entry_sound i {| atom_fn := atom_fn c; atom_args := args_vals'; atom_ret := out_val' |}) as Hue.
    unfold vc in Hue. specialize (Hue e2).
    destruct (update_entry {| atom_fn := atom_fn c; atom_args := args_vals'; atom_ret := out_val' |} e2)
      as [u e'] eqn:Hue_eq.
    cbn [snd] in Hue |- *.
    specialize (Hue Hok2).
    specialize (Hue Hsound2).
    specialize (Hue ltac:(intros x Hx; cbn [atom_args] in Hx; exact (in_all _ _ _ Hkey_args2 Hx))).
    specialize (Hue Hkey_out2).
    specialize (Hue Hatom_i).
    destruct Hue as (Hok' & Hsound' & Hkeys').
    split; [ exact Hok' | ].
    split; [ exact Hsound' | ].
    intros z Hz. apply Hkeys'.
    destruct Hfp02 as (_ & _ & _ & _ & _ & Hkey_iff & _).
    apply Hkey_iff. exact Hz.
  Qed.

  (* Helper: union extends the key-set of the union-find.
     Derived purely from union_sound + uf_rel_PER_has_key. *)
  Lemma union_extends_keys_sem (x y : idx) (e_in : instance)
    (Hroots_in : exists roots, union_find_ok lt (equiv e_in) roots)
    (Hkx : Sep.has_key x (parent (equiv e_in)))
    (Hky : Sep.has_key y (parent (equiv e_in)))
    (z : idx)
    (Hz : Sep.has_key z (parent (equiv e_in)))
    : Sep.has_key z (parent (equiv (snd (Defs.union x y e_in)))).
  Proof.
    destruct Hroots_in as [roots Hroots].
    pose proof (union_sound x y) as Hus.
    unfold vc in Hus. specialize (Hus e_in).
    destruct (Defs.union x y e_in) as [v_u e_u] eqn:Hu.
    cbn [snd] in Hus |- *.
    destruct (Hus (ex_intro _ roots Hroots) Hkx Hky) as
      (_ & Hroots' & Hper & _).
    destruct Hroots' as [roots' Hroots'].
    (* Build uf_rel_PER (equiv e_in) z z from has_key *)
    unfold Sep.has_key in Hz.
    destruct (map.get (parent (equiv e_in)) z) as [vr|] eqn:Hgz; [ | tauto ].
    assert (Hzz_in : uf_rel_PER (equiv e_in) z z).
    { unfold uf_rel_PER.
      eapply PER_clo_trans;
        [ apply PER_clo_base; exact Hgz
        | apply PER_clo_sym; apply PER_clo_base; exact Hgz ]. }
    (* Lift to union_closure_PER *)
    assert (Hzz_clo : union_closure_PER (uf_rel_PER (equiv e_in)) (singleton_rel x y) z z).
    { unfold union_closure_PER. apply PER_clo_base. left. exact Hzz_in. }
    (* Cross the iff2 to get uf_rel_PER in e_u *)
    assert (Hzz_u : uf_rel_PER (equiv e_u) z z) by (apply Hper; exact Hzz_clo).
    (* Use uf_rel_PER_has_key to recover has_key *)
    exact (proj1 (uf_rel_PER_has_key _ roots' _ _ Hroots' Hzz_u)).
  Qed.

  (* Helper: union preserves egraph_ok when has_key for both arguments *)
  Lemma union_preserves_egraph_ok_sem (x y : idx) (e_in : instance)
    (Hok_in : egraph_ok e_in)
    (Hkx : Sep.has_key x (parent (equiv e_in)))
    (Hky : Sep.has_key y (parent (equiv e_in)))
    : egraph_ok (snd (Defs.union x y e_in)).
  Proof.
    pose proof (union_sound x y) as Hus.
    unfold vc in Hus. specialize (Hus e_in).
    destruct (Defs.union x y e_in) as [v_u e_u] eqn:Hu.
    cbn [snd] in Hus |- *.
    destruct Hok_in as [Heqok Hwlok Hparok Hdbkok].
    destruct Heqok as [roots Hroots].
    destruct (Hus (ex_intro _ roots Hroots) Hkx Hky) as
      (Hdb_u & Hroots' & Hper & Hpar_u & Hwl_u & _).
    destruct Hroots' as [roots' Hroots'].
    (* Key monotonicity helper *)
    assert (Hkm : forall z, Sep.has_key z (parent (equiv e_in)) ->
                             Sep.has_key z (parent (equiv e_u)))
      by (intros z Hz;
          unfold Sep.has_key in Hz;
          destruct (map.get (parent (equiv e_in)) z) as [vr|] eqn:Hgz; [|tauto];
          assert (Hzz_u : uf_rel_PER (equiv e_u) z z)
            by (apply (proj1 (Hper z z));
                unfold union_closure_PER; apply PER_clo_base; left;
                unfold uf_rel_PER; eapply PER_clo_trans;
                  [apply PER_clo_base; exact Hgz | apply PER_clo_sym; apply PER_clo_base; exact Hgz]);
          exact (proj1 (uf_rel_PER_has_key _ roots' _ _ Hroots' Hzz_u))).
    (* Hper_lift: old PER implies new PER *)
    assert (Hper_lift : forall i1 i2,
      uf_rel_PER (equiv e_in) i1 i2 -> uf_rel_PER (equiv e_u) i1 i2)
      by (intros i1 i2 Hi12; apply Hper;
          unfold union_closure_PER; apply PER_clo_base; left; exact Hi12).
    constructor.
    - (* egraph_equiv_ok *)
      exact (ex_intro _ roots' Hroots').
    - (* worklist_ok *)
      destruct Hwl_u as [Hwl_same | Hwl_new].
      + rewrite Hwl_same. eapply all_wkn; [ | exact Hwlok ].
        intros ent _ Hp. destruct ent as [old new improved | xa];
          cbn in *; [ apply Hper_lift; exact Hp | exact I ].
      + destruct Hwl_new as (v_old & v_new & improved & Hwl_eq & Hper_old & Hper_new).
        rewrite Hwl_eq. cbn. split.
        * assert (Hr_xy : uf_rel_PER (equiv e_u) x y)
            by (apply Hper; apply PER_clo_base; right; unfold singleton_rel; split; reflexivity).
          unfold uf_rel_PER in *.
          eapply PER_clo_trans; [ exact Hper_old | ].
          eapply PER_clo_trans; [ exact Hr_xy | ].
          apply PER_clo_sym. exact Hper_new.
        * eapply all_wkn; [ | exact Hwlok ].
          intros ent2 _ Hp2. destruct ent2 as [old2 new2 improved2 | xa2];
            cbn in *; [ apply Hper_lift; exact Hp2 | exact I ].
    - (* parents_ok *)
      rewrite <- Hpar_u.
      intros x_p s_p Hgs.
      specialize (Hparok _ _ Hgs).
      eapply all_wkn; [ | exact Hparok ].
      intros b _ Hbup.
      destruct Hbup as (bb & Hca & Hbain).
      destruct Hca as (Hfn & Hargs & Hret).
      exists bb. split.
      + unfold atom_canonical_equiv. split; [ exact Hfn | ]. split.
        * revert Hargs. generalize (atom_args b), (atom_args bb).
          intros l1 l2. revert l2.
          induction l1 as [| w ws IH]; destruct l2 as [| z zs];
            cbn; auto; try tauto.
          intros [Hw Hws]. split; [apply Hper_lift; exact Hw | apply IH; exact Hws].
        * apply Hper_lift. exact Hret.
      + unfold atom_in_egraph. rewrite <- Hdb_u. exact Hbain.
    - (* db_idxs_in_equiv *)
      rewrite <- Hdb_u. intros b Hb.
      specialize (Hdbkok _ Hb).
      destruct Hdbkok as [Hka Hkr]. split.
      + eapply all_wkn; [ | exact Hka ].
        intros j _ Hj. apply Hkm. exact Hj.
      + apply Hkm. exact Hkr.
  Qed.

  (* Helper: union preserves egraph_sound_for_interpretation when
     the two merged ids are equal in the interpretation *)
  Lemma union_preserves_sound_sem (x y : idx)
    (i0 : idx_map m.(domain)) (e_in : instance)
    (Hok_in : egraph_ok e_in)
    (Hsnd_in : egraph_sound_for_interpretation m i0 e_in)
    (Hkx : Sep.has_key x (parent (equiv e_in)))
    (Hky : Sep.has_key y (parent (equiv e_in)))
    (Heq_xy : eq_sound_for_model m i0 x y)
    : egraph_sound_for_interpretation m i0 (snd (Defs.union x y e_in)).
  Proof.
    pose proof (union_sound x y) as Hus.
    unfold vc in Hus. specialize (Hus e_in).
    destruct (Defs.union x y e_in) as [v_u e_u] eqn:Hu.
    cbn [snd] in Hus |- *.
    destruct Hok_in as [Heqok Hwlok Hparok Hdbkok].
    destruct Heqok as [roots Hroots].
    destruct (Hus (ex_intro _ roots Hroots) Hkx Hky) as
      (Hdb_u & Hroots' & Hper & _ & _ & _).
    destruct Hroots' as [roots' Hroots'].
    destruct Hsnd_in as [Hi_wf Hi_exact Hi_atom Hi_rel].
    (* Key monotonicity helper *)
    assert (Hkm : forall z, Sep.has_key z (parent (equiv e_in)) ->
                             Sep.has_key z (parent (equiv e_u)))
      by (intros z Hz;
          unfold Sep.has_key in Hz;
          destruct (map.get (parent (equiv e_in)) z) as [vr|] eqn:Hgz; [|tauto];
          assert (Hzz_u : uf_rel_PER (equiv e_u) z z)
            by (apply (proj1 (Hper z z));
                unfold union_closure_PER; apply PER_clo_base; left;
                unfold uf_rel_PER; eapply PER_clo_trans;
                  [apply PER_clo_base; exact Hgz | apply PER_clo_sym; apply PER_clo_base; exact Hgz]);
          exact (proj1 (uf_rel_PER_has_key _ roots' _ _ Hroots' Hzz_u))).
    constructor.
    - (* idx_interpretation_wf: unchanged interpretation *)
      exact Hi_wf.
    - (* interpretation_exact: keys extended via Hkm *)
      intros z Hz. apply Hkm. apply Hi_exact. exact Hz.
    - (* atom_interpretation: db preserved *)
      intros a Ha. apply Hi_atom.
      unfold atom_in_egraph. rewrite Hdb_u. exact Ha.
    - (* rel_interpretation: lift the closure *)
      intros i1 i2 Hi12.
      apply Hper in Hi12.
      induction Hi12 as [a b H1 | a b c IHab Hab IHbc Hbc | a b IHab Hab].
      + destruct H1 as [Hold | Hnew].
        * apply Hi_rel. exact Hold.
        * destruct Hnew as [Hax Hby]; subst. exact Heq_xy.
      + eapply eq_sound_for_model_trans; eauto.
      + eapply eq_sound_for_model_Symmetric; eauto.
  Qed.

  (* Helper: a key in a sound egraph has a domain value in the interpretation *)
  Lemma has_key_to_domain
    (m0 : model) (i0 : idx_map m0.(domain)) (e0 : instance)
    (Hsnd0 : egraph_sound_for_interpretation m0 i0 e0)
    (v : idx)
    (Hkv : Sep.has_key v (parent (equiv e0)))
    : exists d, map.get i0 v = Some d.
  Proof.
    unfold Sep.has_key in Hkv.
    destruct (map.get (parent (equiv e0)) v) as [vr|] eqn:Hgv; [ | tauto ].
    assert (Hperv : uf_rel_PER (equiv e0) v v).
    { unfold uf_rel_PER.
      eapply PER_clo_trans;
        [ apply PER_clo_base; exact Hgv
        | apply PER_clo_sym; apply PER_clo_base; exact Hgv ]. }
    pose proof (rel_interpretation m0 i0 e0 Hsnd0 v v Hperv) as Heqv.
    unfold eq_sound_for_model in Heqv.
    destruct (map.get i0 v) as [d|] eqn:Hgiv.
    - exact (ex_intro _ d eq_refl).
    - exact (False_rect _ Heqv).
  Qed.

  Lemma exec_write_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (Hm : model_ok m)
    (i : idx_map m.(domain))
    (r : erule idx symbol) (assignment : list idx) (e : instance)
    (a_src : idx_map m.(domain)) :
    let env0 := map.of_list (combine (query_vars idx symbol r) assignment) in
    List.NoDup (write_vars idx symbol r) ->
    (forall x, In x (write_vars idx symbol r) -> map.get env0 x = None) ->
    (forall x, In x (write_vars idx symbol r) ->
        exists d, map.get a_src x = Some d /\ m.(domain_wf) d) ->
    (forall x v, map.get env0 x = Some v ->
        map.get i v = map.get a_src x /\ Sep.has_key v (parent (equiv e))) ->
    (forall c, In c (write_clauses idx symbol r) ->
        forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
        (exists v, map.get env0 x = Some v) \/ In x (write_vars idx symbol r)) ->
    (forall p, In p (write_unifications idx symbol r) ->
        ((exists v, map.get env0 (fst p) = Some v) \/ In (fst p) (write_vars idx symbol r))
        /\ ((exists v, map.get env0 (snd p) = Some v) \/ In (snd p) (write_vars idx symbol r))) ->
    all (atom_sound_for_model m a_src) (write_clauses idx symbol r) ->
    all (fun p => eq_sound_for_model m a_src (fst p) (snd p)) (write_unifications idx symbol r) ->
    egraph_ok e ->
    egraph_sound_for_interpretation m i e ->
    match exec_write idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result r assignment e with
    | (_, e') =>
        egraph_ok e'
        /\ exists i', map.extends i' i
                      /\ egraph_sound_for_interpretation m i' e'
    end.
  Proof.
    intros env0 Hnodup Hfresh Hwf_wv Hcons Hcov_c Hcov_u Hsnd_c Hsnd_u Hok Hsnd.
    unfold exec_write.
    pose proof (allocate_existential_vars_sound Hlti Hlts Hltt a_src (write_vars idx symbol r) i env0) as Halloc.
    unfold vc in Halloc.
    specialize (Halloc Hnodup Hfresh Hwf_wv e Hok Hsnd).
    destruct (allocate_existential_vars idx idx_succ symbol symbol_map idx_map idx_trie analysis_result (write_vars idx symbol r) env0 e) as [env e1] eqn:Halloc_eq.
    cbn [fst snd] in Halloc.
    destruct Halloc as (Hok1 & i1 & Hext1 & Hsnd1 & Henv0_pres & Hwv_cov & Hmono1).
    fold env0.
    cbn [Mbind Mret StateMonad.state_monad].
    rewrite Halloc_eq.
    cbn [fst snd].
    assert (Hcons1 : forall x,
      ((exists v0, map.get env0 x = Some v0) \/ In x (write_vars idx symbol r)) ->
      exists v, map.get env x = Some v
                /\ Sep.has_key v (parent (equiv e1))
                /\ (forall d, map.get a_src x = Some d -> map.get i1 v = Some d)).
    { intros x [ [v0 Hv0] | Hxw ].
      - exists v0.
        pose proof (Hcons x v0 Hv0) as [Hiv0 Hkv0].
        split; [exact (Henv0_pres x v0 Hv0)|].
        split; [exact (Hmono1 v0 Hkv0)|].
        intros d Hd. apply Hext1. rewrite Hiv0. exact Hd.
      - destruct (Hwv_cov x Hxw) as (v & d' & Henvx & Hasrc & Hi1v & Hkv).
        exists v.
        split; [exact Henvx|].
        split; [exact Hkv|].
        intros d Hd. rewrite Hasrc in Hd. inversion Hd; subst d'. exact Hi1v. }
    assert (Hmmap_in : forall (B:Type) (f : idx -> option B) l l',
      list_Mmap f l = Some l' -> forall x, In x l -> exists b, f x = Some b)
      by (intros B f l; induction l as [|a l IHl]; cbn [list_Mmap]; intros l' Hl x Hx;
          [ contradiction
          | destruct (f a) as [b0|] eqn:Hfa; cbn [Mbind option_monad] in Hl; [|discriminate];
            destruct (list_Mmap f l) as [bl|] eqn:Hfl; cbn [Mbind option_monad] in Hl; [|discriminate];
            destruct Hx as [->|Hx]; [exists b0; exact Hfa | exact (IHl _ eq_refl x Hx)] ]).
    assert (Hcl_cons : forall c, In c (write_clauses idx symbol r) ->
      atom_sound_for_model m a_src c ->
      forall x, In x (atom_ret c :: atom_args c) ->
      exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e1))
                /\ map.get i1 v = map.get a_src x)
      by (intros c Hc Hsndc x Hx;
          destruct (Hcons1 x (Hcov_c c Hc x Hx)) as (v & Henvx & Hkv & Hi1cond);
          exists v; split; [exact Henvx|]; split; [exact Hkv|];
          assert (Hasx : exists d, map.get a_src x = Some d) by
            (unfold atom_sound_for_model in Hsndc;
             destruct (list_Mmap (map.get a_src) (atom_args c)) as [argd|] eqn:Hargd;
               cbn [Is_Some_satisfying] in Hsndc; [|tauto];
             destruct (map.get a_src (atom_ret c)) as [outd|] eqn:Houtd;
               cbn [Is_Some_satisfying] in Hsndc; [|tauto];
             destruct Hx as [Heq|Hxa];
               [ rewrite <- Heq; exists outd; exact Houtd
               | exact (Hmmap_in _ _ _ _ Hargd x Hxa) ]);
          destruct Hasx as [d Hd]; rewrite Hd; apply Hi1cond; exact Hd).
    assert (Hphase2 : forall cs,
      (forall c, In c cs -> atom_sound_for_model m a_src c) ->
      (forall c, In c cs -> forall x, In x (atom_ret c :: atom_args c) ->
         exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e1))
                   /\ map.get i1 v = map.get a_src x) ->
      forall e_cur, egraph_ok e_cur -> egraph_sound_for_interpretation m i1 e_cur ->
      (forall z, Sep.has_key z (parent (equiv e1)) -> Sep.has_key z (parent (equiv e_cur))) ->
      match list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) cs e_cur with
      | (_, e2) => egraph_ok e2 /\ egraph_sound_for_interpretation m i1 e2
                   /\ (forall z, Sep.has_key z (parent (equiv e_cur)) -> Sep.has_key z (parent (equiv e2)))
      end).
    { induction cs as [|c cs' IHcs]; intros Hsnd_cs Hcons_cs e_cur Hok_cur Hsnd_cur Hmono_cur.
      - cbn [list_Miter]. split; [exact Hok_cur|]. split; [exact Hsnd_cur|]. intros z Hz; exact Hz.
      - cbn [list_Miter].
        assert (Hcc : forall x, In x (atom_ret c :: atom_args c) ->
           exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e_cur))
                     /\ map.get i1 v = map.get a_src x).
        { intros x Hx. destruct (Hcons_cs c (or_introl eq_refl) x Hx) as (v & Hev & Hkv & Hiv).
          exists v. split; [exact Hev|]. split; [exact (Hmono_cur v Hkv)|]. exact Hiv. }
        pose proof (exec_clause_sound i1 env c a_src e_cur Hok_cur Hsnd_cur Hcc
                      (Hsnd_cs c (or_introl eq_refl))) as Hec.
        destruct (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env c e_cur) as [u e_mid] eqn:Hec_eq.
        destruct Hec as (Hok_mid & Hsnd_mid & Hkeys_mid).
        pose proof (IHcs (fun c0 Hc0 => Hsnd_cs c0 (or_intror Hc0))
                         (fun c0 Hc0 => Hcons_cs c0 (or_intror Hc0))
                         e_mid Hok_mid Hsnd_mid
                         (fun z Hz => Hkeys_mid z (Hmono_cur z Hz))) as HIH.
        destruct (list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) cs' e_mid) as [u2 e2] eqn:Hlm2.
        destruct HIH as (Hok2 & Hsnd2 & Hkeys2).
        cbn [Mseq Mbind Mret StateMonad.state_monad].
        rewrite Hec_eq. rewrite Hlm2.
        split; [exact Hok2|]. split; [exact Hsnd2|].
        intros z Hz. apply Hkeys2. apply Hkeys_mid. exact Hz. }
    pose proof (Hphase2 (write_clauses idx symbol r)
      (fun c0 Hc0 => in_all _ _ _ Hsnd_c Hc0)
      (fun c0 Hc0 x0 Hx0 => Hcl_cons c0 Hc0 (in_all _ _ _ Hsnd_c Hc0) x0 Hx0)
      e1 Hok1 Hsnd1 (fun z Hz => Hz)) as Hp2.
    destruct (list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) (write_clauses idx symbol r) e1) as [u2 e2] eqn:Hlm_c.
    destruct Hp2 as (Hok2 & Hsnd2 & Hkeys2).
    cbn [fst snd].
    assert (Hun_cons : forall p, In p (write_unifications idx symbol r) ->
      exists vx vy, map.get env (fst p) = Some vx /\ map.get env (snd p) = Some vy
                    /\ Sep.has_key vx (parent (equiv e1)) /\ Sep.has_key vy (parent (equiv e1))
                    /\ eq_sound_for_model m i1 vx vy).
    { intros p Hp.
      destruct (Hcov_u p Hp) as [Hcx Hcy].
      destruct (Hcons1 (fst p) Hcx) as (vx & Hevx & Hkvx & Hivx).
      destruct (Hcons1 (snd p) Hcy) as (vy & Hevy & Hkvy & Hivy).
      pose proof (in_all _ _ _ Hsnd_u Hp) as Hequ.
      exists vx, vy.
      split; [exact Hevx|]. split; [exact Hevy|]. split; [exact Hkvx|]. split; [exact Hkvy|].
      unfold eq_sound_for_model in Hequ |- *.
      destruct (map.get a_src (fst p)) as [dx|] eqn:Hax; cbn [Is_Some_satisfying] in Hequ; [|tauto].
      destruct (map.get a_src (snd p)) as [dy|] eqn:Hay; cbn [Is_Some_satisfying] in Hequ; [|tauto].
      rewrite (Hivx dx eq_refl). cbn [Is_Some_satisfying].
      rewrite (Hivy dy eq_refl). cbn [Is_Some_satisfying]. exact Hequ. }
    assert (Hphase3 : forall ps,
      (forall p, In p ps -> exists vx vy, map.get env (fst p) = Some vx /\ map.get env (snd p) = Some vy
                    /\ Sep.has_key vx (parent (equiv e1)) /\ Sep.has_key vy (parent (equiv e1))
                    /\ eq_sound_for_model m i1 vx vy) ->
      forall e_cur, egraph_ok e_cur -> egraph_sound_for_interpretation m i1 e_cur ->
      (forall z, Sep.has_key z (parent (equiv e1)) -> Sep.has_key z (parent (equiv e_cur))) ->
      match list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) ps e_cur with
      | (_, e3) => egraph_ok e3 /\ egraph_sound_for_interpretation m i1 e3
                   /\ (forall z, Sep.has_key z (parent (equiv e_cur)) -> Sep.has_key z (parent (equiv e3)))
      end).
    { induction ps as [|p ps' IHps]; intros Hcons_ps e_cur Hok_cur Hsnd_cur Hmono_cur.
      - cbn [list_Miter]. split; [exact Hok_cur|]. split; [exact Hsnd_cur|]. intros z Hz; exact Hz.
      - cbn [list_Miter]. destruct p as [px py].
        destruct (Hcons_ps (px,py) (or_introl eq_refl)) as (vx & vy & Hevx & Hevy & Hkvx & Hkvy & Hequ).
        cbn [fst snd] in Hevx, Hevy.
        cbn [Mseq Mbind Mret StateMonad.state_monad].
        rewrite Hevx, Hevy. cbn [unwrap_with_default].
        pose proof Hok_cur as Hok_cur2. destruct Hok_cur2 as [Hroots_cur _ _ _].
        pose proof (union_preserves_egraph_ok_sem vx vy e_cur Hok_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy)) as Hok_mid.
        pose proof (union_preserves_sound_sem vx vy i1 e_cur Hok_cur Hsnd_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy) Hequ) as Hsnd_mid.
        pose proof (fun z Hz => union_extends_keys_sem vx vy e_cur Hroots_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy) z Hz) as Hkeys_mid.
        destruct (Defs.union vx vy e_cur) as [vu e_mid] eqn:Hu_eq.
        cbn [snd] in Hok_mid, Hsnd_mid, Hkeys_mid.
        pose proof (IHps (fun p0 Hp0 => Hcons_ps p0 (or_intror Hp0)) e_mid Hok_mid Hsnd_mid
                     (fun z Hz => Hkeys_mid z (Hmono_cur z Hz))) as HIH.
        destruct (list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) ps' e_mid) as [vu2 e3] eqn:Hlm3.
        destruct HIH as (Hok3 & Hsnd3 & Hkeys3).
        split; [exact Hok3|]. split; [exact Hsnd3|].
        intros z Hz. apply Hkeys3. apply Hkeys_mid. exact Hz. }
    pose proof (Hphase3 (write_unifications idx symbol r) Hun_cons e2 Hok2 Hsnd2 Hkeys2) as Hp3.
    destruct (list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) (write_unifications idx symbol r) e2) as [u3 e3] eqn:Hlm_u.
    destruct Hp3 as (Hok3 & Hsnd3 & _).
    split; [exact Hok3|]. exists i1. split; [exact Hext1|exact Hsnd3].
  Qed.

End WithMap.

Arguments atom_in_egraph {idx symbol}%_type_scope {symbol_map idx_map idx_trie}%_function_scope
  {analysis_result}%_type_scope
  a i.

Arguments seq_assumptions {idx symbol}%_type_scope s.
Arguments seq_conclusions {idx symbol}%_type_scope s.

Arguments forall_vars {idx symbol}%_type_scope s.
Arguments exists_vars {idx}%_type_scope {Eqb_idx} {symbol}%_type_scope s.
Arguments sequent_vars {idx symbol}%_type_scope s.

Arguments eq_clause {idx symbol}%_type_scope x y.
Arguments atom_clause {idx symbol}%_type_scope a.


Arguments clauses_to_instance {idx}%_type_scope {Eqb_idx}
  idx_succ%_function_scope
  {symbol}%_type_scope {symbol_map idx_map idx_trie}%_function_scope
  {analysis_result}%_type_scope
  {H}
  l%_list_scope _ _.


Arguments instance_to_clauses {idx symbol}%_type_scope
  {symbol_map idx_map idx_trie}%_function_scope
  {analysis_result}%_type_scope i.


Arguments db_to_atoms {idx symbol}%_type_scope
  {symbol_map idx_trie}%_function_scope 
  {analysis_result}%_type_scope
  d.


Arguments uf_to_clauses {idx symbol}%_type_scope {idx_map}%_function_scope u.


