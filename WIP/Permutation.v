From coqutil Require Import Map.Interface.
Require Import Lists.List.
Import ListNotations.

Require Import Coq.Sorting.Permutation Coq.PArith.BinPos.

From Utils Require Import Base Booleans Props Eqb Options Lists ExtraMaps.

Section DecidablePermutation.
  Context (A : Type)
    (Eqb_A : Eqb A)
    (Eqb_A_ok : Eqb_ok Eqb_A)
    (*
      We use positives so that we have a unique representation for a -> 0
     *)
    (multiset : map.map A positive)
    (multiset_ok : map.ok multiset)
    (Eqb_multiset : Eqb multiset)
    (Eqb_multiset_ok : Eqb_ok Eqb_multiset).

  
  #[local] Open Scope positive_scope.
  
  Definition add_elt (s : multiset) a :=
    match map.get s a with
    | None => map.put s a 1
    | Some p => map.put s a (Pos.succ p)
    end.
  
  Definition sub_elt (s : multiset) a :=
    match map.get s a with
    | None => None
    | Some 1 => Some (map.remove s a)
    | Some p => Some (map.put s a (Pos.pred p))
    end.
  
  Fixpoint list_contents (l : list A) : multiset :=
    match l with
    | [] => map.empty
    | a::l' => add_elt (list_contents l') a
    end.
  
  Definition permutationb l1 l2 : bool :=
    eqb (list_contents l1) (list_contents l2).

  (* TODO: move to ExtraMaps or similar *)
  
  Hint Rewrite map.get_empty : utils.
  #[local] Hint Rewrite map.get_put_same : utils.
  #[local] Hint Rewrite map.get_put_diff using congruence : utils.
  Lemma map_empty_put_inv (m : multiset) k v
    : map.empty = map.put m k v <-> False.
  Proof.
    intuition.
    assert (map.get map.empty k = map.get (map.put m k v) k) by congruence.
    basic_utils_crush.
  Qed.
  #[local] Hint Rewrite map_empty_put_inv : utils.

  
  Definition has_key i (t : multiset) :=
    if map.get t i then True else False.
  Hint Unfold has_key : utils.
  
  (* TODO: handle = symmetry before automating *)
  Lemma empty_list_contents l
    : map.empty = list_contents l -> l = [].
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    unfold add_elt in *.
    revert H; case_match; 
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma match_p_neq_1 {B} p (a b : B)
    : p <> 1 ->
      match p with 1 => a | _ => b end = b.
  Proof.
    destruct p; tauto.
  Qed.
  
  Lemma contains_add_sub s a
    : match sub_elt s a with
      | Some s' => s = add_elt s' a
      | None => ~ has_key a s
      end.
  Proof.
    unfold sub_elt.
    my_case Hg (map.get s a); auto.
    {
      replace match p with
              | 1 => Some (map.remove s a)
              | _ => Some (map.put s a (Pos.pred p))
              end
        with (Some match p with
                | 1 => (map.remove s a)
                | _ => (map.put s a (Pos.pred p))
                end) by (destruct p; eauto).
      unfold add_elt.

      destruct (Pos.eq_dec p 1); subst.
      {
        rewrite map.get_remove_same.
        rewrite Properties.map.put_remove_same.
        maps_equal.
      }
      {
        rewrite !match_p_neq_1; eauto.
        basic_utils_crush.
        replace (Pos.succ (Pos.pred p)) with p by Lia.lia.
        maps_equal.
      }
    }
    {
      unfold has_key; rewrite Hg; eauto.
    }
  Qed.
  
  Lemma sub_add_elt s a
    : sub_elt (add_elt s a) a = Some s.
  Proof.
    unfold add_elt, sub_elt.
    my_case Hg (map.get s a);
      basic_utils_crush.
    2: maps_equal.
    assert (Pos.succ p <> 1) by Lia.lia.
    rewrite match_p_neq_1; eauto.
    f_equal; maps_equal.
    rewrite Hg; f_equal; Lia.lia.
  Qed.
  
  Fixpoint remove_one (a:A) l :=
    match l with
    | [] => None
    | a'::l' =>
        if eqb a a' then Some l' else option_map (cons a') (remove_one a l')
    end.

  
  Lemma get_add_elt_same s a
    : map.get (add_elt s a) a = match map.get s a with
                                | Some p => Some (Pos.succ p)
                                | None => Some 1
                                end.
  Proof.
    unfold add_elt.
    case_match;
      basic_utils_crush.
  Qed.

  
  Lemma get_add_elt_diff s a a'
    :a <> a' ->
     map.get (add_elt s a) a' = map.get s a'.
  Proof.
    unfold add_elt.
    case_match;
      basic_utils_crush.
  Qed.

  
  Lemma put_add_elt_same s a n
    : map.put (add_elt s a) a n = map.put s a n.
  Proof.
    unfold add_elt.
    case_match;
      basic_utils_crush.
    all: maps_equal.
  Qed.

  (*TODO: move to ExtraMaps.v*)
  
  Lemma remove_add_elt_same s a
    : map.remove (add_elt s a) a = map.remove s a.
  Proof.
    unfold add_elt.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
    all: maps_equal.
  Qed.
  #[local] Hint Rewrite remove_add_elt_same : utils.
  
  Lemma remove_add_elt_diff s a a'
    : a <> a' -> map.remove (add_elt s a) a' = add_elt (map.remove s a') a.
  Proof.
    unfold add_elt.
    basic_goal_prep;
      rewrite map.get_remove_diff by eauto.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
    all: maps_equal.
  Qed.
  #[local] Hint Rewrite remove_add_elt_diff using solve[auto] : utils.
  
  Lemma put_add_elt_diff s a a' v
    : a <> a' -> map.put (add_elt s a) a' v = add_elt (map.put s a' v) a.
  Proof.
    unfold add_elt.
    basic_goal_prep;
      rewrite map.get_put_diff by eauto.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
    all: maps_equal.
  Qed.
  #[local] Hint Rewrite put_add_elt_diff using solve[auto] : utils.

  Lemma sub_elt_remove_one l a
    : option_map list_contents (remove_one a l)
      = sub_elt (list_contents l) a.
  Proof.
    unfold sub_elt.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_utils_crush.
    {
      rewrite get_add_elt_same.
      revert IHl; case_match;
        basic_goal_prep;
        basic_utils_crush.
      2: maps_equal.
      rewrite match_p_neq_1 by Lia.lia.
      f_equal.
      rewrite put_add_elt_same.
      maps_equal.
      rewrite <- HeqH; f_equal; Lia.lia.
    }
    {
      rewrite get_add_elt_diff; eauto.
      case_match;
        basic_utils_crush.
      2:{
        unfold option_map;
        cbn.
        my_case Hr (remove_one a l);
          basic_goal_prep;
          basic_utils_crush.
      }
      {
        destruct (Pos.eq_dec p 1);
          subst;
          rewrite ?match_p_neq_1 in * by eauto.
        all: my_case Hr (remove_one a l);
          basic_goal_prep;
          basic_utils_crush.
      }
    }
  Qed.

  
  Lemma map_put_inj_v (s1 : multiset) a v1 s2 v2
    : map.put s1 a v1 = map.put s2 a v2 ->
      v1 = v2.
  Proof.
    intros.
    enough (map.get (map.put s1 a v1) a
            = map.get (map.put s2 a v2) a)
      by basic_utils_crush.
    rewrite H.
    basic_utils_crush.
  Qed.
  
  Lemma add_elt_inj s1 s2 a
    : add_elt s1 a = add_elt s2 a -> s1 = s2.
  Proof.
    unfold add_elt.
    case_match; case_match;
      basic_goal_prep;
      basic_utils_crush.
    all:apply map_put_inj_v in H; try Lia.lia.
    {
      apply Pos.succ_inj in H; subst.
      TODO: strange case
      maps_equal.
      
  (* sound but not complete *)
  Lemma use_permutationb l1 l2
    : Is_true (permutationb l1 l2) -> Permutation l1 l2.
  Proof.
    unfold permutationb.
    basic_utils_crush.
    revert l2 H.
    induction l1;
      basic_goal_prep;
      basic_utils_crush.
    {
      apply empty_list_contents in H;
        basic_utils_crush.
    }
    {
      
      assert (match sub_elt (list_contents l2) a with
              | Some s' => add_elt s' a = list_contents l2
              | None => False
              end).
      {
        rewrite <- H.
        rewrite sub_add_elt.
        f_equal.
      }
      {
        revert H0; case_match; [intro| tauto].
        rewrite <- H0 in H.
        rewrite <- sub_elt_remove_one in HeqH0.
        my_case Hr (remove_one a l2); cbn in *; [|congruence].
        safe_invert HeqH0.
        TODO: r doesn't correspond to an l2
      pose proof (contains_add_sub (list_contents l2) a).
      replace (sub_elt (list_contents l2) a)
        with (sub_elt (add_elt (list_contents l1) a) a)
        in H0
          by congruence.
      rewrite sub_add_elt in H0.
      Lemma add_elt_in
      Lemma add_elt_contains s a
        : has_key a (add_elt s a).

        Lemma contains_add_sub
          : has_key a s ->
            match sub_elt s a with
            | Some s' => s = add_elt s' a
            | None => False
            end.
      sub_elt
    Lemma Permutation_nil_l
      : 
  
End DecidablePermutation.
