From coqutil Require Import Map.Interface.
Require Import Lists.List.
Import ListNotations.

From Coq.Sorting Require Import Permutation Mergesort.
Import NatSort.

From Utils Require Import Base Booleans Props Eqb Lists.

Definition nat_permutationb (l1 l2 : list nat) : bool :=
  eqb (sort l1) (sort l2).

(* The other direction should be true too *)
Lemma use_nat_permutationb l1 l2
  : Is_true (nat_permutationb l1 l2) -> Permutation l1 l2.
Proof.
  unfold nat_permutationb;
    basic_goal_prep;
    basic_utils_crush.
  rewrite Permuted_sort with (l:=l1).
  rewrite Permuted_sort with (l:=l2).
  rewrite H.
  reflexivity.
Qed.


 Fixpoint remove_all' {A} perm (l : list A) idx :=
    match l with
    | [] => []
    | a::l' => if inb idx perm
               then remove_all' perm l' (S idx)
               else a::remove_all' perm l' (S idx)
    end.
  Definition remove_all {A} (l : list A) perm :=
    remove_all' perm l 0.

Section __.
  Context (A : Type).

  Fixpoint select_all (l : list A) perm:=
    match perm with
    | [] => []
    | n::perm' =>
        match nth_error l n with
        | Some a => a::select_all l perm'
        | None => select_all l perm'
        end
    end.
  
  (*TODO: if slow, write a version that computes in (near) linear time *)
  Definition permute (l : list A) (perm : list nat) :=
    (select_all l perm) ++ (remove_all l perm).

  Definition extend_perm (perm : list nat) n :=
    filter (fun x => Nat.ltb x n) perm ++ remove_all (seq 0 n) perm.

  
  Lemma permute_map (default : A) l perm
    : permute l perm = map (fun n => nth n l default) (extend_perm perm (length l)).
  Proof.
    unfold permute, extend_perm.
    rewrite map_app.
    f_equal.
    {
      induction perm;
        basic_goal_prep;
        basic_utils_crush.
      case_match;
        destruct (PeanoNat.Nat.ltb_spec a (length l)); eauto.
      3:{
        symmetry in HeqH.
        rewrite nth_error_None in HeqH.
        Lia.lia.
      }
      2:{
        rewrite <- nth_error_None in H.
        congruence.
      }
      {
        basic_goal_prep.
        f_equal;
          basic_utils_crush.
        erewrite nth_error_nth; eauto.
      }
    }
    {
      unfold remove_all.      
      change (fun n : nat => nth n l default)
        with  (fun n : nat => nth n ([]++l) default).
      change 0 with (@length A []).
      generalize (@nil A).
      
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      {

        case_match;
          basic_goal_prep;
          basic_utils_crush.
        {
          replace (S (length l0)) with (length (l0++[a])).
          2:rewrite app_length; simpl; Lia.lia.
          change (l0 ++ a :: l)
            with (l0 ++ [a] ++ l).
          rewrite app_assoc.
          apply IHl with (l:=l0 ++[a]).
        }
        {
          symmetry; apply nth_middle.
        }
        {
          
          replace (S (length l0)) with (length (l0++[a])).
          2:rewrite app_length; simpl; Lia.lia.
          change (l0 ++ a :: l)
            with (l0 ++ [a] ++ l).
          rewrite app_assoc.
          apply IHl with (l:=l0 ++[a]).
        }
      }
    }
  Qed.

  Lemma map_seq_nth l (a:A)
    : (map (fun n : nat => nth n l a) (seq 0 (length l)))
      = l.
  Proof.
    change (fun n : nat => nth n l a)
      with  (fun n : nat => nth n ([]++l) a).
    change 0 with (@length A []).
    generalize (@nil A).
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    { apply nth_middle. }
    {
      replace (S (length l0)) with (length (l0++[a0])).
      2:rewrite app_length; simpl; Lia.lia.
      change (fun n : nat => nth n (l0 ++ a0 :: l) a)
        with  (fun n : nat => nth n (l0 ++ [a0] ++ l) a).
      rewrite app_assoc.
      apply IHl with (l:=l0 ++[a0]).
    }
  Qed.

  
  Lemma permute_nil perm : permute [] perm = [].
  Proof.
    unfold permute, remove_all.
    basic_goal_prep; basic_utils_crush.
    induction perm;
      basic_goal_prep; basic_utils_crush.
    rewrite IHperm.
    destruct a; eauto.
  Qed.

  
  
  Lemma permute_is_Permutation l perm
    : let ex := (extend_perm perm (length l)) in
      (* (NoDup perm) is sufficient, but that's harder to prove *)
      Is_true (nat_permutationb ex (seq 0 (length l))) ->
      Permutation (permute l perm) l.
  Proof.
    intros.
    apply use_nat_permutationb in H.
    destruct l.
    {
      rewrite permute_nil; reflexivity.
    }
    revert dependent l.
    intro l; generalize (a::l); clear l.
    intros.
    apply Permutation_map
      with (f:= (fun n => nth n l a))
      in H.
    subst ex.
    rewrite <- permute_map in H.
    rewrite H; clear H.
    rewrite map_seq_nth.
    reflexivity.
  Qed.
    
End __.
