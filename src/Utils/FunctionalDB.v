(* An implementation of the core of egglog
 *)
Require Import Equalities Orders ZArith Lists.List Uint63.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

Require Std.Sorting.Mergesort.
Module Merge := Std.Sorting.Mergesort.Sectioned.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind SpacedMapTreeN.
From Utils Require TrieMap TrieMapInt63.
(*From Pyrosome.Theory Require Import Core.*)
Import Sets.
  

Section WithMap.
  Context
    (* these first 3 types may all be the same *)
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)
      (*TODO: any reason to have separate from idx?*)
    (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
    (* the type of values in the table. TODO: generalize to a symbol-dependent signature.
    (elt : Type)
    We use idx as the sole output type for now since it behaves specially wrt matching
     *).
  (*(term_args_map : map.map (list idx) elt).*)

  Definition table := (named_list (list idx) idx).
  
 Context (symbol_map : forall A, map.map symbol A).

  Context 
      (idx_map : forall A, map.map idx A)
      (idx_map_ok : forall A, map.ok (idx_map A)).

  (* we need constants for residual queries in generic_join *)
  Variant argument := const_arg (c : idx) | var_arg (x : idx).

  (* assumption a = const_arg x *)
  Definition resolve_arg a :=
    match a with const_arg x => Some x | var_arg _ => None end.

  
  (* args_locs represents the indices of the arguments we want to match.
     for functions of the form f(x0..xn) |-> x_n+1, the index i refers to xi.
     For simplicity, we assume that any index >= n+1 refers to out.
     (Alternately, this function should only be called w/ indices up to n+1)

     Returns `Some i` if this row has i at indices l0::args_locs,
     and None if those locations do not all have the same value.
   *)
  Definition match_args (args : list idx) (out : idx) '(l0,args_locs) : option _ :=
    let v := nth l0 args out in
    if forallb (fun i => eqb v (nth i args out)) args_locs then Some v else None. 
  
  (*
  Require Import Coq.Sorting.Mergesort.
  Import NatSort. *)
  
  (*
    `split_by` sorts the table into subtables where all key indices in 'is' have the same value
    Split up into a call to mergesort and a second filter/split pass.
    This increases runtime (but not complexity), but lets us use the library mergesort.
   *)
  (*Fail Context (sort : ((list idx) * idx -> (list idx) * idx -> bool) -> table -> table).*)

  Fixpoint filter_split_sorted' (args_locs : nat * list nat) (tab : table)
    out current current_idx
    : named_list idx (named_list (list idx) idx) :=
    match tab with
    | [] => (current_idx,current)::out
    | (args,e)::tab' =>
        match match_args args e args_locs with
        | Some i =>
            if eqb i current_idx
            then filter_split_sorted' args_locs tab' out ((args,e)::current) current_idx
            else filter_split_sorted' args_locs tab' ((current_idx, current)::out) [(args,e)] i
        | None => filter_split_sorted' args_locs tab' out current current_idx
        end
    end.

  Definition filter_split_sorted args_locs tab :=
    match tab with
    | [] => []
    | (args,e)::tab' =>
        match match_args args e args_locs with
        | Some i => filter_split_sorted' args_locs tab' [] [(args,e)] i
        (* TODO: Silences errors. Consider proper error propagation *)
        | None => []
        end
    end.

  (*TODO: move to Booloeans/WithDefault*)
  Instance default_bool : WithDefault bool := false.

  Context (idx_leb : idx -> idx -> bool).
  
  Definition args_order loc0 : list idx * idx -> list idx * idx -> bool :=
    fun l1 l2 =>
      let v1 := nth loc0 (fst l1) (snd l1) in 
      let v2 := nth loc0 (fst l2) (snd l2) in 
      idx_leb v1 v2.

  Definition split_by (args_locs : nat * list nat) (tab : table)
    : named_list idx table :=
    let table' := Merge.sort (args_order (fst args_locs)) tab in
    filter_split_sorted args_locs table'.

  (*TODO: move to list utils?*)
  Fixpoint indices_of' {A} `{Eqb A} (a : A) offset l : list nat :=
    match l with
    | [] => []
    | b::l' => if eqb a b then offset::(indices_of' a (S offset) l')
               else indices_of' a (S offset) l'
    end.

  Definition indices_of {A} `{Eqb A} (a : A) l : list nat :=
     indices_of' a 0 l.

  Definition ne_table : Type := ((list idx) * idx) * table.

  Definition ne_as_table (n : ne_table) := cons (fst n) (snd n).
  
  Coercion ne_as_table : ne_table >-> list.

  Instance eqb_argument : Eqb argument :=
    fun a b =>
      match a,b with
      | var_arg ax, var_arg bx => eqb ax bx
      | const_arg ac, const_arg bc => eqb ac bc
      | _,_ => false
      end.


  
  Instance eqb_argument_ok : Eqb_ok eqb_argument.
  Proof using Eqb_idx_ok.
    unfold Eqb_ok, eqb, eqb_argument.
    intros a b;
      my_case Ha a;
      my_case Hb b;
      basic_goal_prep;
      try congruence.
    { eqb_case c c0; congruence. }
    { eqb_case x x0; congruence. }
  Qed.

  Definition var_indices (vars : list idx) (args : list argument) :=
    map (fun x => indices_of (var_arg x) args) vars.
  
  Definition c_is_of_vars : list (list nat) -> _ :=
  map (fun x : list nat => if x then false else true).
  
  Fixpoint build_trie' (tab : ne_table) (v_is : list (list nat))
    : MapTreeN.ntree idx unit
        (List.length (filter id (c_is_of_vars v_is))) :=
    match v_is as v_is with
    | [] =>
        (* Assumes that all arguments must be constant here.
           Implied by fvs(args) <= vars.

           Further assumes that the table is functional,
           i.e. that each key (arg list) appears at most once.
           TODO: figure out whether we need to relax this assumption,
           e.g. for semi-naive evaluation.
         *)
        tt
    (* unconstrained *)
    | []::v_is => build_trie' tab v_is
    | (loc0::arg_locs)::v_is =>
        let split_tab := split_by (loc0,arg_locs) tab in                
        fold_left
          (fun trie_map '(i, tab) =>
             match tab with
             (* Short-circuit if there are no more entries.
                      TODO: check whether this can happen.
                      If so, it means that map.get can return None on the output
                      in normal operation
              *)
             | [] => trie_map
             | r1::tab' => map.put trie_map i (build_trie' (r1,tab') v_is)
             end)
          split_tab
          map.empty
    end.

  (*
    clauses have the form R(x1,...xn) (|-> xn+1)?
    where xn+1, if provided, binds the output.
    atom_args should be of length either arity(R) or arity(R)+1
   *)
  Record atom :Type :=
    {
      atom_fn : symbol;
      atom_args : list idx;
      atom_ret : idx;
    }.

  Definition node_map := symbol_map table.
  
  (* Returns None only if the clause doesn't match any rows.
     Note: may still return Some in such cases.
   *)
  Definition build_trie (nodes:node_map) (vars : list idx) (clause : atom) : option _ :=
    @!let (r1::tab) <?- map.get nodes clause.(atom_fn) in
      (*TODO: find a better way to pass ret & trace it back to simplify deps,
        since they can assume a ret exists.
       *)
      let v_is := var_indices vars
                    (map var_arg (clause.(atom_args)
                                           ++[clause.(atom_ret)])) in
      let t := build_trie' (r1,tab) v_is in
      ret Build_ntree _ _ t.

  
  Record query :=
    {
      free_vars : list idx;
      clauses : list atom;
    }.
  
  
  (* Returns None only if some clause doesn't match any rows.
     Note: may still return Some in such cases.
   *)
  Definition build_tries (nodes : node_map) (q: query)
    : option (list _) :=
    list_Mmap (build_trie nodes q.(free_vars)) q.(clauses).

(*
TODO: what is best wrt intersection?

Seems like the sorted-list-style map might be the best here.
- arrays (when available) are best when the keys are dense
- Sorted list is better than ptree when you have to iterate over the whole map
- ptree is better than sorted list when you need to get or to set possibly exisitng keys

Issue: building trie performs unordered insertions
Question: what dominates: unordered insertions or iteration? probably insertion
Alternately: should I build a tree then convert to a list?
2nd alt: can I define an intersection that directly builds sorted lists?
 *)

  (*TODO: move tp SpacedMapTreeN*)
  Lemma top_tree_cast {A} var_count
    : A = MapTreeN.ntree idx A (Datatypes.length (filter id (repeat false var_count))).
  Proof.
    replace (filter id (repeat false var_count)) with (@nil bool);
      [ reflexivity |].
    induction var_count;
      cbn;
      try reflexivity.
    assumption.
  Defined.

  (*TODO: move to a better place*)
  Definition cast {A B} (eq : A = B) : A -> B :=
    match eq with eq_refl => id end.
  
  Definition top_tree {A} `{WithDefault A} var_count : ntree A :=
    Build_ntree _ (m:=idx_map) (repeat false var_count)
      (cast (top_tree_cast var_count) default).

  Context `{map_plus_ok idx (m:=idx_map)}.
  
  (* We implement a simplified generic join by just iteratively intersecting the tries.
     Note: the running time here is proportional to the second-largest trie in the worst case,
     whereas it should be proportional to the smallest.
     Potential solutions: lazy tries &/or special nary-intersect (second seems easier than first)

     TODO: how to handle var_count being the same across trees?
     Can't take advantage of it as easily here.
     TODO: intersect_checked returning Some is inconvenient as speculated; return default?
     alternately, to avoid checking length a bunch of times, could have a forest package
   *)                                                              
  Definition generic_join' (t1: ntree unit) (tries : list (ntree unit)) : list _ :=
    ntree_fold _ (fun acc k _ => cons k acc)
      (List.fold_right (ntree_intersect_unchecked (fun _ _ => tt)) t1 tries) [].
  

  (* Returns a list of all possible outputs of the query's clauses
     such that the query matches.
     Note: duplicates are possible.
   *)
  Definition generic_join (nodes : node_map) q : list (list idx) :=
    match build_tries nodes q with
    | None => [] (* short-circuit: includes an empty trie *)
    | Some [] => [] (* NOTE: no clauses, invalid result in this case *)
    | Some (t1::tries) => generic_join' t1 tries
    end.

  (* Properties *)

  
  Lemma ntree_intersect_length A B (merge : A -> B -> B) `{WithDefault B} t1 (t2: ntree B)
    : ntree_len_eq t1 t2 ->
      ntree_len_eq t1 (ntree_intersect_unchecked merge t1 t2).
  Proof.
    intro Hlen.
    unfold ntree_intersect_unchecked.
    unshelve erewrite compute_unchecked_eq; eauto.
    unfold ntree_intersect, ntree_len_eq, zip in *.
    basic_goal_prep;
      basic_utils_crush.
    rewrite combine_length.
    Lia.lia.
  Qed.

  Lemma ntree_len_eq_trans A B C (t1 : ntree A) (t12 : ntree (m:=idx_map) B) (t2 : ntree C)
    : ntree_len_eq t1 t12 ->
      ntree_len_eq t12 t2 ->
      ntree_len_eq t1 t2.
  Proof.
    unfold ntree_len_eq; basic_utils_crush.
    congruence.
  Qed.
  
  Lemma fold_ntree_intersect_length A B (merge : A -> B -> B) `{WithDefault B} l (t : ntree B)
    : all (fun t' : ntree A => ntree_len_eq t t') l ->
      ntree_len_eq t (fold_right (ntree_intersect_unchecked merge) t l).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    1: unfold ntree_len_eq; basic_utils_crush.
    eapply ntree_len_eq_trans.
    2:eapply ntree_intersect_length.
    all: eauto.
    unfold ntree_len_eq in *; basic_utils_crush.
    congruence.
  Qed.
    

  Lemma fold_ntree_intersect A B (merge : A -> B -> B) `{WithDefault B} l (t : ntree B) k
    : all (fun t' => ntree_len_eq t t') l ->
      let merge' (ma : option A) (mb : option B) :=
        @! let a <- ma in
          let b <- mb in
          ret merge a b
      in
      ntree_get (fold_right (ntree_intersect_unchecked merge) t l) k
      = fold_right merge' (ntree_get t k) (map (fun t => ntree_get t k) l).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite ntree_intersect_unchecked_spec; eauto.
    2:{
      revert H3 H4; clear.
      intros.
      eapply ntree_len_eq_trans.
      2: eapply fold_ntree_intersect_length; eauto.
      unfold ntree_len_eq in *;
        basic_utils_crush;
        congruence.
    }
    case_match; eauto.
    rewrite H2.
    reflexivity.
  Qed.

  Definition fully_constrained {A} (t : ntree (m:=idx_map) A) : Prop :=
    Is_true (forallb id t.(constrained_indices)).

  (*TODO: move to coqutil maybe?*)
  Lemma fold_right_flatmap X Y f (acc : list Y) (l : list X)
    : (forall x acc, f x acc = f x [] ++ acc) ->
      let f' x := f x [] in
      fold_right f acc l = flat_map f' l ++ acc.
  Proof.
    intro Hf.
    intro f'; subst f'.
    revert acc; induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite Hf.
    rewrite IHl.
    rewrite app_assoc.
    reflexivity.
  Qed.


  (*TODO: move to MapTreeN.v?*)
  Lemma ntree_fold'_monotone A len acc0 keystack n
    : MapTreeN.ntree_fold' A
    (fun (acc1 : list (list idx)) (k0 : list idx) (_ : A) => k0 :: acc1) len acc0
    keystack n =
        MapTreeN.ntree_fold' A
    (fun (acc1 : list (list idx)) (k0 : list idx) (_ : A) => k0 :: acc1) len []
    keystack n ++ acc0.
  Proof.
    revert acc0 keystack n.
    induction len;
      basic_goal_prep;
      basic_utils_crush.
    cbn.
    rewrite !Properties.map.fold_to_tuples_fold.
    
    unfold MapTreeN.ntree in *.
    generalize (map.tuples n) as l.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite IHlen.
    rewrite IHl.
    rewrite app_assoc.
    rewrite <- IHlen.
    reflexivity.
  Qed.
  
(* *)
  Lemma ntree_fold'_keys A (k:list idx) len t acc keystack
    : In k (MapTreeN.ntree_fold' A (fun acc k _ => k::acc) len acc keystack t)
      <-> (exists k_suff, k = rev keystack ++ k_suff
                          /\ Is_Some (MapTreeN.ntree_get t k_suff)
                          /\ List.length k_suff = len)
          \/ In k acc.
  Proof.
    revert t acc keystack.
    induction len;
      basic_goal_prep.
    {
      split;
      basic_goal_prep;
        basic_utils_crush.
      {
        left; exists [];
          basic_goal_prep;
          basic_utils_crush.
      }
      {
        destruct x;
          basic_goal_prep;
          basic_utils_crush.
      }
    }
    {
      match goal with
        |- context [(map.fold ?f ?acc ?m)] =>
          pose proof (Properties.map.fold_to_list f acc m)
      end.
      break.
      (*assert (all_fresh x) as Hxfr by admit.*)
      unfold MapTreeN.ntree in *.
      rewrite H1.
      clear H1.
      rewrite fold_right_flatmap.
      2:{
        basic_goal_prep.
        eapply ntree_fold'_monotone.
      }
      split;
        basic_goal_prep;
        basic_utils_crush.
      {
        rewrite in_flat_map in *.
        basic_goal_prep;
          basic_utils_crush.
        eapply IHlen in H3.
        basic_goal_prep;
          basic_utils_crush.
        left.
        exists (i::x0).
        basic_goal_prep;
          basic_utils_crush.
        { rewrite <- app_assoc; eauto. }
        {
          rewrite H2 in H1.
          rewrite H1.
          eauto.
        }
      }
      {
        rewrite in_flat_map in *.
        revert H3; case_match;
        basic_goal_prep;
          basic_utils_crush.
        revert H3; case_match;
          basic_goal_prep;
          basic_utils_crush.
        left.
        exists (i,n).
        basic_goal_prep;
          basic_utils_crush.
        {
          rewrite H2.
          congruence.
        }
        {
          eapply IHlen.
          basic_goal_prep;
            basic_utils_crush.
          exists H1.
          basic_goal_prep;
            basic_utils_crush.
          rewrite <- app_assoc; eauto.
        }
      }
    }
  Qed.

  Lemma MapTreeN_ntree_fold_keys A (k:list idx) len (t : MapTreeN.ntree idx A len)
    : In k (MapTreeN.ntree_fold A (fun acc k _ => k::acc) len t [])
      <-> Is_Some (MapTreeN.ntree_get t k) /\ List.length k = len.
  Proof.
    rewrite (ntree_fold'_keys _ k len t [] []).
    intuition (basic_goal_prep;
               basic_utils_crush).
  Qed.

  (*TODO: move to lists*)
  Lemma all_true_filter (B : Type) (f : B -> bool) (l : list B)
    : all (fun x => Is_true (f x)) l -> filter f l = l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    destruct (f a);
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma all_true_filter_key (B : Type) (k : list B) l
    : List.length k = List.length l ->
      all (fun x => Is_true x) l -> filter_key k l = k.
  Proof.
    revert k;
      induction l;
      destruct k;
      basic_goal_prep;
      basic_utils_crush.
    destruct a;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma ntree_fold_keys A (k:list idx) t
    : fully_constrained t ->
      In k (ntree_fold A (fun acc k _ => k::acc) t [])
      <-> Is_Some (ntree_get t k) /\ List.length k = List.length t.(constrained_indices).
  Proof.
    unfold ntree_get,  fully_constrained, ntree_fold.
    destruct t; cbn [SpacedMapTreeN.inner_tree SpacedMapTreeN.constrained_indices].
    autorewrite with bool utils.
    intro Hall.
    revert inner_tree.
    rewrite all_true_filter with (f:=id) (l:=constrained_indices); eauto.
    intro.
    rewrite MapTreeN_ntree_fold_keys.
    intuition eauto;
      rewrite all_true_filter_key in *; eauto.
  Qed.

  (*TODO: move to Lists*)
  Lemma fold_right_invariant A (P : A -> Prop) f acc l
    : P acc -> all P l -> (forall a b, P a -> P b -> P (f a b)) -> P (fold_right f acc l).
  Proof.
    intros Hacc Hl Hf; revert Hl;
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma all_map A B P (f : A -> B) l
    : all P (map f l) <-> all (fun x => P (f x)) l.
  Proof.
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma all_implies A (P Q : A -> Prop) l
    : (forall x,  P x -> Q x) -> all P l -> all Q l.
  Proof.
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    

  Lemma fold_intersect_indices t1 tries
    : all (fun t' : ntree unit => ntree_len_eq t1 t') tries ->
      constrained_indices (fold_right (ntree_intersect_unchecked (fun _ _ : unit => tt)) t1 tries)
      = fold_right (List.zip orb) (constrained_indices t1) (map constrained_indices tries).
  Proof.    
    unfold ntree_intersect_unchecked, ntree_len_eq.
    induction tries;
      basic_goal_prep;
      eauto.
    
    unshelve erewrite compute_unchecked_eq.
    {
      autorewrite with bool utils in *.
      break.
      rewrite IHtries; eauto.
      clear IHtries.
      eapply fold_right_invariant; eauto.
      2:{
        unfold zip.
        basic_goal_prep;
          basic_utils_crush.
        rewrite combine_length; Lia.lia.
      }
      rewrite all_map.
      eapply all_implies; eauto.
      basic_goal_prep;
        basic_utils_crush.
      congruence.
    }      
    destruct t1, a;
      basic_goal_prep;
    basic_utils_crush.
  Qed.
  
  Lemma generic_join'_sound t1 tries assignment
    : all (fun t' : ntree unit => ntree_len_eq t1 t') tries ->
      all Is_true (fold_right (zip orb) (constrained_indices t1) (map constrained_indices tries)) ->
      In assignment (generic_join' t1 tries) ->
      all (fun t => Is_Some (ntree_get t assignment)) (t1::tries).
  Proof.
    unfold generic_join'.
    intros Hlen Hconstrained.
    rewrite ntree_fold_keys.
    2:{
      unfold fully_constrained.
      basic_utils_crush.
      rewrite fold_intersect_indices; eauto.
    }
    clear Hconstrained.
    rewrite fold_ntree_intersect; eauto.
    intros; break.
    clear H2.
    generalize dependent tries.
    induction tries;
      basic_goal_prep.
    1:basic_utils_crush.
    revert H1; repeat (case_match; cbn); intuition eauto.
  Qed.

  Lemma build_trie_length nodes fvs a t
    : Some t = build_trie nodes fvs a ->
      List.length t.(constrained_indices) = List.length fvs.
  Proof.
    unfold build_trie.
    cbn.
    repeat (case_match; cbn);
      basic_goal_prep;
      basic_utils_crush.
    cbn.
    unfold c_is_of_vars, var_indices.
    basic_utils_crush.
  Qed.

  
  Lemma list_Mmap_invariant A B (f : A -> option B) (P : B -> Prop) l l'
    : (forall x y, Some y = f x -> P y) -> Some l' = list_Mmap f l -> all P l'.
  Proof.
    intro Hf.
    revert l';
      induction l;
      repeat (case_match; cbn);
      basic_goal_prep;
      basic_utils_crush.
    revert H1;
      repeat (case_match; cbn);
      basic_goal_prep;
      basic_utils_crush.
    cbn; intuition eauto.
  Qed.

  Lemma build_tries_length nodes q l t1
    : Some (t1::l) = build_tries nodes q ->
      all (fun t' : ntree unit => ntree_len_eq t1 t') l.
  Proof.
    unfold build_tries; destruct q;
      cbn.
    intro HM.
    eapply list_Mmap_invariant in HM.
    { cbn in *; intuition eauto. }
    {
      unfold ntree_len_eq.
      basic_goal_prep;
        basic_utils_crush.
      destruct clauses0; cbn in HM; try congruence.
      revert HM; repeat case_match;
      basic_goal_prep;
        basic_utils_crush.
      cbn.
      unfold c_is_of_vars, var_indices.
      basic_utils_crush.
      erewrite build_trie_length; eauto.
    }
  Qed.

  Definition in_node_map (n : node_map) a :=
    match map.get n a.(atom_fn) with
    | Some t => In (a.(atom_args),a.(atom_ret)) t
    | None => False
    end.

  
  Context `{WithDefault idx}.

  (* Note: defaults don't protect against out-of-scope idxs *)
  Definition atom_subst (sub : named_list idx idx) (a : atom) : atom :=
    let (f, args, r) := a in
    Build_atom f
      (map (named_list_lookup default sub) args)
      (named_list_lookup default sub r).

  Definition matches_pat mp (x:idx) :=
    match mp with Some x' => x = x' | None => True end.

  Definition table_compatible (t : table) (sub : named_list idx idx) args rv :=
    let args_pat := map (named_list_lookup_err sub) args in
    let r_pat := named_list_lookup_err sub rv in
    all (fun '(k,r) => all2 matches_pat args_pat k /\ matches_pat r_pat r) t.

  (* TODO: move to Lists.v*)
  Lemma named_list_lookup_from_err (i0 : idx) (sub' : named_list idx idx) r
    : Some i0 = named_list_lookup_err sub' r ->
      named_list_lookup default sub' r = i0.
  Proof using Eqb_idx_ok.
    induction sub';
      basic_goal_prep; try congruence.
    eqb_case r i; try congruence; eauto.
  Qed.
  
  Lemma table_compatible_lookup (t : ne_table) sub' args r
    :  table_compatible t sub' args r ->
       In r (map fst sub') ->
       incl args (map fst sub') ->
       In (map (named_list_lookup default sub') args, named_list_lookup default sub' r) t.
  Proof.
    clear idx_leb.
    unfold table_compatible, matches_pat.
    destruct t as [[x i] t].
    induction t;
      basic_goal_prep;
      basic_utils_crush.
    2:{
      revert H7;
      case_match;
      basic_goal_prep;
      subst;
      basic_utils_crush.
      { erewrite named_list_lookup_from_err; eauto. }
      { exfalso.
        eapply pair_fst_in_exists in H3; break.
        eapply named_list_lookup_none in HeqH5; eauto.
      }
    }
    {
      revert x H2 H4.
      clear H7 H6 H3 r.
      induction args;
        destruct x;
        repeat case_match;
        basic_goal_prep;
        subst;
        basic_utils_crush.
      revert H3;
      case_match;
      basic_goal_prep;
      subst;
      basic_utils_crush.
      { erewrite named_list_lookup_from_err; eauto. }
      { exfalso.
        eapply pair_fst_in_exists in H2; break.
        eapply named_list_lookup_none in HeqH3; eauto.
      }
    }
  Qed.


  (* TODO: move to namedlist *)
  Lemma lookup_app_notin {A} (x:idx) (l1 l2 : named_list idx A) 
    : fresh x l2 ->
      named_list_lookup_err (l1++l2) x
      = named_list_lookup_err l1 x.
  Proof.
    clear idx_leb.
    induction l1;
      basic_goal_prep;
      basic_utils_crush.
    {
      symmetry.
      rewrite named_list_lookup_none_iff.
      eauto.
    }
    {
      eqb_case x i; eauto.
    }
  Qed.
  
  Local Lemma map_lookup_app_notin {A} l (l1 l2 : named_list idx A) 
    : all (fun x => fresh x l2) l ->
      map (named_list_lookup_err (l1++l2)) l
      = map (named_list_lookup_err l1) l.
  Proof.
    clear idx_leb.
    induction l;
      cbn; eauto.
    intuition (f_equal; eauto using lookup_app_notin).
  Qed.

  Lemma table_compatible_snoc_unconstrained t sub' a args r i
    : ~ In a args ->
      a <> r ->
      table_compatible t sub' args r ->
      table_compatible t (sub' ++ [(a, i)]) args r.
  Proof.
    unfold table_compatible.
    intros Hargs Hr.
    eapply all_implies.
    basic_goal_prep;
      subst;
      basic_utils_crush.
    2:{
      clear H2.
      unfold matches_pat in *.
      rewrite lookup_app_notin; eauto.
      cbv; intuition eauto.
    }
    {
      clear H3.
      unfold matches_pat in *.
      rewrite map_lookup_app_notin; eauto.
      {
        unfold fresh.
        cbn.
        revert Hargs; clear;
          induction args;
          basic_goal_prep;
          basic_utils_crush.
      }
    }
  Qed.

  
  Lemma empty_indices_of a l
    : [] = indices_of (var_arg a) (map var_arg l) ->
      ~ In a l.
  Proof.
    unfold indices_of.
    generalize 0.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    cbn in *.
    eqb_case a a0;
      try congruence.
    eapply IHl; eauto.
  Qed.
  
  Lemma build_trie'_sound (ne_tab : ne_table) assignment args r fvs sub'
    : List.length fvs = List.length assignment ->
      table_compatible ne_tab sub' args r ->
      let v_is := var_indices fvs (map var_arg (args ++ [r])) in
      Is_Some (MapTreeN.ntree_get (build_trie' ne_tab v_is)
                 (filter_key assignment (c_is_of_vars v_is))) ->
      In r (map fst sub' ++ fvs) ->
      incl args (map fst sub' ++ fvs) ->
      let sub := named_list_lookup default (sub' ++ combine fvs assignment) in
      In (map sub args, sub r) ne_tab.
  Proof.
    revert assignment sub'.
    induction fvs;
      destruct assignment;
      try (basic_goal_prep; congruence).
    {
      intros.
      eapply table_compatible_lookup; 
        basic_goal_prep;
        basic_utils_crush.
    }
    {
      intros.
      subst v_is sub.
      cbn [combine] in *.

      
      revert H4; cbn.
      case_match.
      {
        (*unconstrained case *)
        replace (map fst sub' ++ a :: fvs)
          with (map fst (sub' ++ [(a,i)]) ++ fvs) in *.
        2:{
          clear.
          rewrite map_app.
          basic_goal_prep;
            basic_utils_crush.
          rewrite <- app_assoc.
          eauto.
        }
        replace (sub' ++ (a,i) :: combine fvs assignment)
          with ((sub' ++ [(a,i)]) ++ combine fvs assignment) in *.
        2:{
          rewrite <- app_assoc.
          eauto.
        }
        intro Hsome.
        eapply IHfvs; eauto.
        {
          eapply empty_indices_of in HeqH4.
          eapply table_compatible_snoc_unconstrained; eauto;
            basic_utils_crush.
        }
      }
      {
        (*
        Design questions:
          1. can I assume some sort on the table?
             - needs to be per-query, but does it have to be per recursive branch?
          2. what data structure does the table need to have?                                  - is there something that is more amenable to quick lookup&insertion?
             - related: when/what lookups,insertions do I perform?
               for equalities: no lookups, but batched insertions
                               w/ potentially mergable results
               for type inference: lookups for every metametavariable/hole,
               alternately a recursive whole-term lookup
         *)
        (*
        TODO: properties of split_by;
        fold_left invariant;
        put sound
         *)
  Admitted.

  
  Definition atom_ws fvs (a:atom) :=
    In a.(atom_ret) fvs /\ incl a.(atom_args) fvs.

  (*TODO: move to Lists*)
  Lemma all2_map_l A B C (f : A -> B) (P : B -> C -> Prop) l1 l2
    : all2 P (map f l1) l2 <-> all2 (fun x y => P (f x) y) l1 l2.
  Proof.
    clear.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
    all:apply IHl1; eauto.
  Qed.

  Lemma all2_implies B C (P Q : B -> C -> Prop) l1 l2
    : (forall x y, P x y -> Q x y) -> all2 P l1 l2 -> all2 Q l1 l2.
  Proof.
    clear.
    intro Hpq.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma table_compatible_nil (t : table) args r
    : all (fun row => List.length args = List.length (fst row)) t ->
      table_compatible t [] args r.
  Proof.
    unfold table_compatible, matches_pat.
    cbn.
    eapply all_implies.
    {
      basic_goal_prep.
      intuition eauto.
      rewrite all2_map_l.
      revert args H2;
        induction l;
        destruct args;
        basic_goal_prep;
        basic_utils_crush.
    }
  Qed.    
  
  Lemma build_trie_sound t fvs c nodes assignment
    : atom_ws fvs c ->
      Some t = build_trie nodes fvs c ->
      Is_Some (ntree_get t assignment) ->
      in_node_map nodes (atom_subst (combine fvs assignment) c).
  Proof.
    unfold build_trie, atom_ws.
    destruct c.
    unfold in_node_map, ntree_get.
    cbn in *.    
    repeat case_match;
      try (cbv [default option_default]; congruence).
    intros; basic_utils_crush.
    eapply build_trie'_sound
      with (ne_tab:= (l, i, H2))
           (sub':=[]);
      eauto.
    { admit (*ntree get len lemma*). }
    {
      eapply table_compatible_nil.
      admit (*table arity wfness*). }
  Abort.    
    
  Lemma build_tries_sound l q nodes assignment
    : Some l = build_tries nodes q ->
      all2 (fun t c => Is_Some (ntree_get t assignment) ->
                       in_node_map nodes (atom_subst (combine (free_vars q) assignment) c))
        l q.(clauses).
  Proof.
    unfold build_tries.
    destruct q.
    cbn.

  Abort.
  
  (* Note: We don't need completeness for our purposes, but it should hold. *)
  Theorem generic_join_sound nodes q assignment
    : (*wf_query q -> (probably necessary) *)
    In assignment (generic_join nodes q) ->
      let sub := combine q.(free_vars) assignment in
      forall c, In c q.(clauses) ->
                in_node_map nodes (atom_subst sub c).
  Proof.
    unfold generic_join.
    repeat case_match.
    all: basic_utils_crush.
    eapply generic_join'_sound in H3.
    2:{ eapply build_tries_length; eauto. }
    2:{ admit (*TODO: add wf query assumption *). }
    revert HeqH2 H3.
    generalize (n::H2).
    clear n H2.
    intros.
    repeat case_match.
    (*TODO: use build_tries_sound*)
  Abort.


  Definition db_map := symbol_map {n & (MapTreeN.ntree idx idx n)}.

  Context `{@map_plus symbol symbol_map}.

  Definition flatten_db : db_map -> node_map :=
    map_map (fun p => MapTreeN.ntree_to_tuples _ (projT1 p) (projT2 p)).
    
  
  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).

  
  Record instance := {
      db : db_map;
      (*sort_map : idx_map idx;*)
      equiv : union_find;
      (* TODO: maintain an upper bound on the number of rows in db
         for the purpose of ensuring termination?
       
      size : nat;*)
    }.

  Import StateMonad.

  Definition table_put n (t : MapTreeN.ntree idx idx n) uf ks v :=
     match MapTreeN.ntree_get t ks with
     | Some v1 =>
         (*TODO: union shouldn't ever fail? check this &/or make non-option union *)
         match UnionFind.union _ _ _ _ uf v v1 with
         | Some (uf',v') =>
            (* Note: needs rebuilding*)
             (v', t, uf')
         | None => (*should never happen if v in uf *) (v, t, uf)  
         end
        | None =>
            let t' := MapTreeN.ntree_set _ n t ks v in
            (v, t', uf)            
        end.

  (* TODO: assumes idx merge fn. Generalize.
     TODO: why the option out?
   *)
  Definition db_put s ks v i : idx * instance :=
    match map.get i.(db) s with
    | Some (existT _ n t) =>
        let '(v', t', uf') := table_put _ t i.(equiv) ks v in
        let db' := map.put i.(db) s (existT _ n t') in
        (v,Build_instance db' uf')
    | None =>
        let s_ntree := MapTreeN.ntree_singleton _ (List.length ks) ks v in
        let db' := map.put i.(db) s (existT _ (List.length ks) s_ntree) in
        (v, Build_instance db' i.(equiv))
    end.

  Context (idx_succ : idx -> idx).
  
  Definition db_get s ks : stateT instance option idx :=
    fun i =>
      (* TODO: abstact out the 'mutate value' pattern? *)
      @! let (existT _ n t) <- map.get i.(db) s in
        match MapTreeN.ntree_get t ks with
        | Some v => Some (v, i)
        | None =>
            let (uf',v) := alloc _ _ _ idx_succ i.(equiv) in
            let t' := MapTreeN.ntree_set _ n t ks v in
            let db' := map.put i.(db) s (existT _ n t') in
            Some (v,Build_instance db' uf')            
        end.

  Definition find' (v : idx) : stateT _ option idx :=
    fun uf => @!let p <- UnionFind.find _ _ _ _ uf v in ret (snd p, fst p).
  
  (*TODO: write instead in terms of node_map?*)
  Definition rebuild_ntree' (uf : union_find) n (t : MapTreeN.ntree idx idx (S n))
    : (MapTreeN.ntree idx idx (S n) * union_find * bool) :=
    MapTreeN.ntree_fold (key:=idx) _ (fun '(t,uf, changed) keys v =>
                    unwrap_with_default (H:=(t,uf,changed))
                      (@! let {option} (keys',uf1) <- list_Mmap (M:= stateT _ option) find' keys uf in
                         let {option} (v', uf2) <- find' v uf1 in
                         let (_,t', uf') := table_put _ t uf keys' v' in
                         let changed' := (changed || eqb v v')%bool in
                         ret {option} (t',uf',changed')))
       (S n) t (map.empty : MapTreeN.ntree idx idx (S n),uf,false).
    
  (*TODO: `unwrap_with_default` assumes presence in uf. Is this the best way to handle things? *)
  Definition rebuild_ntree (uf : union_find) n
    : MapTreeN.ntree idx idx n -> (MapTreeN.ntree idx idx n * union_find*bool) :=
    match n with
    (* can always mark changed as false here, since rebuilding a tree0 needs at most one update *)
    | 0 => fun x => unwrap_with_default (H:=(x,uf,false)) (Mfmap (fun x => (x,false)) (find' x uf))
    | S n' => rebuild_ntree' uf n'
    end.
                               
  Definition rebuild_once i : instance * bool :=
      map.fold (fun '(acc, has_changed) k '(existT _ n v) =>
                  let '(v', uf', v_has_changed) := rebuild_ntree acc.(equiv) n v in
                  (Build_instance (map.put acc.(db) k (existT _ n v')) uf',
                    (has_changed || v_has_changed)%bool))
        (Build_instance map.empty i.(equiv),false) i.(db).

  Fixpoint rebuild' limit (i : instance) : instance :=
    match limit with
    | 0 => i
    | S n =>
        let '(i',changed) := rebuild_once i in
        if changed then rebuild' n i' else i'
    end.

  (* Note: partial rebuilding is sound but not complete.
         We use a bound of 100 for now.
         On strange match failures, check this.
   *)
  Definition rebuild (i : instance) : instance := rebuild' 100 i.
  
  (*TODO: rebuilding process requires non-functional dbs at intermediate steps
    once we use non-idx merges
   *)
  
  (*
    TODO: do I want to support let_query? I don't have a use for it right now
    and generally, multiple queries is a bad idea since they should be bundled into one
    instead: log_exp an upd_exp
   *)
  Variant log_upd : Type :=
  | put_row : atom -> idx (* var *) -> log_upd
  | let_row : atom -> idx (* binder *) -> log_upd
  | unify : idx -> idx -> log_upd.

  Record op_state : Type :=
   Mk_state {
      data : instance;
      env : idx_map idx;
      changed : bool;
     }.
  
  Definition do_unify a b : state op_state unit :=
    fun s =>
      (* shortcut when equal so that changed remains false *)
      if eqb a b then (tt,s) else
      match UnionFind.union _ _ _ _ s.(data).(equiv) a b with
      | Some (uf,_) => (tt,Mk_state (Build_instance s.(data).(db) uf) s.(env) true)
      | None => (tt,s) (* shouldn't happen *)
      end.

  Context `{WithDefault idx}.

  (* assumes the input is in the domain *)
  Definition sub (env : idx_map idx) i : idx :=
    unwrap_with_default (map.get env i).

  Definition do_put_row a i : state op_state unit :=
    fun s =>
      let f := a.(atom_fn) in
      let args := map (sub s.(env)) a.(atom_args) in
      let val := sub s.(env) i in
      let (_, d) := db_put f args val s.(data) in
      (tt, Mk_state d s.(env) true).

  (* Assumes that the symbol of a corresponds to a real table *)
  Definition do_let_row a x : state op_state unit :=
    fun s =>
      let f := a.(atom_fn) in
      let args := map (sub s.(env)) a.(atom_args) in
      match db_get f args s.(data) with
      | Some (i, d) =>
          (tt, Mk_state d (map.put s.(env) x i) true)          
      | None => (tt,s) (* shouldn't happen *)
      end.
  
  (* TODO: generate differential instance?
   *)
  Definition apply_upd (l : log_upd) : state op_state unit :=
      match l with
      | unify i1 i2 => do_unify i1 i2
      | put_row a i => do_put_row a i
      | let_row a x => do_let_row a x
      end.

  
  Definition apply_upds : list log_upd -> state op_state unit :=
    list_Miter apply_upd.
  
  (*
    Note: should be able to generate terms (e.g. proofs of internal facts like neq) in addition to equalities!
   *)
  Record log_op : Type :=
    {
      (*
        We generalized the conclusion :- assumption ... pattern from core egglog
        to better support multiple operations being performed on the results of a single match.
        log_ops behave as follows:
        - run `assumptions` query
        - for each substitution in the result, run the update program

       This is useful for things like recording `sort_of` entries at the same time as terms are added to the db

       TODO: w/ advanced enough optimization, it will be worth generalizing further to a program
       made up of an (ordered) sequence of queries and conclusions, to take advantage of subqueries.
       Note: Use the var/const split for this
       *)
      update : list log_upd;
      assumptions : query;
    }.
  
  Definition log_program : Type := list log_op.

  Definition opt_to_list {A} o : list A :=
    match o with Some x => [x] | None => [] end.

  (*
  Definition make_query l :=
    let c_vars := (opt_to_list (snd l.(conclusion)) ++ atom_args (fst l.(conclusion))) in
    let vars := List.dedup (eqb (A:=_))
                  (List.fold_left (app (A:=_))
                     (map atom_args l.(assumptions)) c_vars) in
    Build_query vars l.(assumptions).
   *)

  (*
  (*TODO: how to tell arity of conclusion to differentiate val var and no val var?*)
  Definition apply_join_sub c fvs s : atom * option idx :=
    let '(Build_atom f args,out) := c in
    let args' := atom_args_subst s fvs args in
    (Build_atom f args',Mfmap (named_list_lookup default (combine fvs s)) out).*)

  Definition db_alloc '(Build_instance db equiv) : idx * instance :=
    let '(equiv',v):= alloc _ _ _ idx_succ equiv in
    (v, Build_instance db equiv').

  (* TODO: move to Monad.v *)
  Section __.
    Context {M : Type -> Type} `{Monad M} {A B : Type} (f : A -> M (list B)).
    Fixpoint list_Mflatmap (l : list A) : M (list B) :=
      match l with
      | [] => @! ret []
      | a::al' =>
          @! let b <- f a in
            let bl' <- list_Mflatmap al' in
            ret (b++bl')
      end.
  End __.

  Definition state_upd {S} (f : S -> S) : state S unit := fun s => (tt, f s).

  Fixpoint fold_updates has_changed upd subs : state instance bool :=
    match subs with
    | [] => Mret has_changed
    | s::subs' =>
        @! let s_changed <- fun i =>
                            let (_,op_s) := apply_upds upd (Mk_state i s has_changed) in
                            (op_s.(changed), op_s.(data)) in
          let subs'_changed <- fold_updates has_changed upd subs' in
          ret orb s_changed subs'_changed
    end.

  (* TODO: generate differential instance? *)
  Definition apply_op changed (l : log_op) : state instance bool :=
    fun i =>
      (* TODO: precompute, choose a good var order as part of query optimization *)
      let q := l.(assumptions) in
      let subs := generic_join (flatten_db i.(db)) q in
      let sub_maps := map (fun s => map.of_list (combine q.(free_vars) s)) subs in
      (fold_updates changed l.(update) sub_maps i).
    
  Definition run_once (p : log_program) : state instance bool :=
    list_Mfoldl apply_op p false.    
  
  Fixpoint run (p : log_program) n i : instance :=
    match n with
    | 0 => i
    | S n =>
        let (changed,i') := run_once p i in
        if changed then run p n (rebuild i') else i
    end.


End WithMap.

Module PositiveIdx.

  (*TODO: move to Eqb or sim. locaion *)
  #[export] Instance positive_Eqb : Eqb positive := Pos.eqb.

  Definition generic_join_pos :=
    generic_join positive _ positive (TrieMap.trie_map)
      TrieMap.trie_map Pos.leb (H:=TrieMap.ptree_map_plus).

  Local Open Scope positive.
  Example db1 : TrieMap.trie_map (table _) :=
    map.put
      (map.put map.empty 10 [([7;7;3], 1); ([7;3;3], 9)])
      20 [([8;4], 3); ([3;1], 7)].

  Local Notation query := (query positive positive).

  Example query1 : query :=
    Build_query _ _ [3;1;2;4;5;6]
      [
        Build_atom _ _ 10 [4;5] 6;
        Build_atom _ _ 20 [2] 3;
        Build_atom _ _ 10 [1;1;2] 3
      ].
  Time Compute (generic_join_pos db1 query1).
  
  Example query2 : query :=
    Build_query _ _ [1;2;3]
      [
        Build_atom _ _ 10 [1;2;2] 3
      ].

  Compute (generic_join_pos db1 query2).
End PositiveIdx.

  

 (* (*TODO: Does reachable being reflexive cause a problem?
    Really want a PER since malformed terms shouldn't count? *)

  Axiom lookup : term symbol -> instance -> option idx.
  Axiom sort_of : forall {V}, lang V -> ctx V -> term V -> sort V.

  (* TODO: extend to support existentials *)
  (* Assumes no sort eqns in l (and so does not store sorts in instance) *)
  Definition valid_instance l c (i : instance) :=
    (forall i' t, lookup t i = Some i' -> interp_uf (equiv i) i' i')
    /\ (forall t1 i1 t2 i2, interp_uf (equiv i) i1 i2 ->
                            lookup t1 i = Some i1 ->
                           lookup t2 i = Some i2 ->
                           eq_term l c (sort_of l c t1) t1 t2).
  *)
