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
    : Permutation (extend_perm perm (length l)) (seq 0 (length l)) ->
      Permutation (permute l perm) l.
  Proof.
    intros.
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
    rewrite <- permute_map in H.
    rewrite H; clear H.
    rewrite map_seq_nth.
    reflexivity.
  Qed.

  
  (*TODO: move to Lists*)
  Lemma In_seq m n1 n2
    : In m (seq n1 n2) <-> n1 <= m < n1 + n2.
  Proof.
    revert n1 m.
    induction n2;
      basic_goal_prep;
      basic_utils_crush.
    all: try Lia.lia.
    {
      rewrite IHn2 in H0; Lia.lia.
    }
    {
      rewrite IHn2 in H0; Lia.lia.
    }
    {
      pose proof (eqb_spec n1 m);
        destruct (eqb n1 m);
        basic_goal_prep;
        basic_utils_crush.
      right.
      eapply IHn2.
      Lia.lia.
    }
  Qed.
  #[local] Hint Rewrite In_seq : utils.

  (*TODO: move to Lists*)
  #[local] Hint Rewrite filter_In : utils.

  (* TODO: move to Nats *)
  Lemma is_true_ltb (n m : nat)
    : Is_true (Nat.ltb n m) <-> (n < m)%nat.
  Proof.
    rewrite <- PeanoNat.Nat.ltb_lt.
    basic_utils_crush.
  Qed.
  #[local] Hint Rewrite is_true_ltb : utils.

  
  Lemma In_remove_all B (a : B) perm l
    : In a (remove_all l perm) -> In a l.
  Proof.
    unfold remove_all.
    generalize 0.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    revert H; case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma extend_perm_incl perm n
    : incl (extend_perm perm n) (seq 0 n).
  Proof.
    unfold extend_perm.
    apply incl_app.
    {
      unfold incl.
      intros.
      basic_utils_crush.
      Lia.lia.
    }      
    {
      unfold incl.
      intros.
      basic_utils_crush.
      all: try Lia.lia.
      apply In_remove_all in H.
      basic_utils_crush.
    }
  Qed.

  Lemma filter_false B f (l : list B)
    : (forall x, f x = false) ->
      filter f l = [].
  Proof.
    induction l;
      basic_goal_prep; basic_utils_crush.
    case_match;
      basic_goal_prep; basic_utils_crush.
    rewrite H in HeqH1; eauto.
  Qed.

  Lemma all_false B P (l : list B)
    : (forall x, ~ P x) -> all P l -> l = [].
  Proof.
    destruct l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma remove_all_filter n perm
    : (remove_all (seq 0 n) perm)
    = remove_all (seq 0 n) (filter (fun x : nat => Nat.ltb x n) perm).
  Proof.
    unfold remove_all.
    replace  (filter (fun x : nat => Nat.ltb x n) perm)
      with (filter (fun x : nat => Nat.ltb x (0+ length (seq 0 n))) perm).
    2:{
      apply filter_ext.
      intros.
      rewrite seq_length.
      (*replace (n-0) with n by Lia.lia.*)
      auto.
    }
    generalize (seq 0 n) as l.
    intro l.
    generalize 0.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_utils_crush;
      case_match;
        basic_utils_crush; try Lia.lia;
      replace (n0 + S (length l))
          with (S n0 + (length l)) by Lia.lia;
      apply IHl with (n:= S n0); Lia.lia.
  Qed.

  
  Lemma is_true_nat_leb a b
    : Is_true (Nat.leb a b) <-> (a <= b)%nat.
  Proof.
    destruct (PeanoNat.Nat.leb_spec a b);
      basic_utils_crush.
    Lia.lia.
  Qed.
  Hint Rewrite is_true_nat_leb : utils.
  
  Lemma filter_filter B (f g : B -> bool) l
    : filter f (filter g l) = filter (fun x => andb (f x) (g x)) l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    my_case Hg (g a);
    my_case Hf (f a);
      basic_goal_prep;
      basic_utils_crush.
    {
      rewrite Is_true_implies_eq_true with (b:=f a) by eassumption.
      congruence.
    }
    {
      change (~Is_true (f a)) in Hf.
      rewrite <- eq_false_to_Is_true in Hf.
      rewrite Hf.
      congruence.
    }
  Qed.    

  Lemma remove_all'_filter_leb B (l : list B) perm n
        :  (remove_all' perm l n)
           =  (remove_all' (filter (Nat.leb n) perm) l n).
  Proof.
    revert perm n.
    Local Opaque Nat.leb.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
    {
      case_match;
        basic_goal_prep;
        basic_utils_crush.
      etransitivity.
      2: symmetry; apply IHl.
      rewrite filter_filter.
      rewrite filter_ext with (g:=Nat.leb (S n)); eauto.
      basic_goal_prep;
        unfold andb; case_match;
        basic_utils_crush.
      Lia.lia.
    }
    {
      case_match;
        basic_goal_prep;
        basic_utils_crush.
      etransitivity.
      2: symmetry; apply IHl.
      rewrite filter_filter.
      rewrite filter_ext with (g:=Nat.leb (S n)); eauto.
      basic_goal_prep;
        unfold andb; case_match;
        basic_utils_crush.
      Lia.lia.
    }
  Qed.

  Lemma length_filter_notin_perm_S n perm
    : NoDup perm ->
      ~In n perm ->
      (length (filter (Nat.leb (S n)) perm)) = length (filter (Nat.leb n) perm).
  Proof.
    revert n.
    induction perm;
      basic_goal_prep;
      basic_utils_crush.
      case_match; basic_utils_crush; try Lia.lia.
      {
        case_match; basic_utils_crush; try Lia.lia.
        cbn.
        f_equal.
        apply IHperm; eauto.
        safe_invert H; eauto.
      }
      {
        case_match; basic_utils_crush; try Lia.lia.
        cbn.
        apply IHperm; eauto.
        safe_invert H; eauto.
      }
  Qed.
    
  Lemma length_filter_perm_S n perm
    : NoDup perm ->
      In n perm ->
      S (length (filter (Nat.leb (S n)) perm)) = length (filter (Nat.leb n) perm).
  Proof.
    induction perm;
      basic_goal_prep;
      basic_utils_crush.
    {
      case_match; basic_utils_crush; try Lia.lia.
      case_match; basic_utils_crush; try Lia.lia.
      cbn.
      safe_invert H.
      f_equal.
      apply length_filter_notin_perm_S; eauto.
    }
    {
      safe_invert H.
      case_match; basic_utils_crush; try Lia.lia;
        case_match; basic_utils_crush; try Lia.lia;
        cbn;
        eauto.
      exfalso.
      apply HeqH.
      pose proof (eqb_spec a n);
        destruct (eqb a n);
        subst; intuition Lia.lia.
    }
  Qed.

  
  Lemma length_filter_bound {B} (f : B -> _) l
    : (length (filter f l) <= length l)%nat.
  Proof.
    induction l;
      basic_goal_prep;
      try case_match;
      basic_goal_prep;
      basic_utils_crush;
      Lia.lia.
  Qed.

  Local Open Scope nat_scope.

  Lemma filter_true_In B (f : B -> bool) l
    : (forall x, In x l -> Is_true (f x)) ->
      filter f l = l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  (*TODO: move*)
  Lemma inv_NoDup_cons B (x:B) l
    : NoDup (x::l) <-> ~ In x l /\ NoDup l.
  Proof.
    solve_invert_constr_eq_lemma.
  Qed.
  Hint Rewrite inv_NoDup_cons : utils.

  Lemma length_filter_elt_NoDup l (a : nat)
    : NoDup l ->
      length l <= S (length (filter (fun x => negb (eqb x a)) l)).
  Proof.
    induction l;     
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_goal_prep.
    2:{
      apply Bool.negb_sym in HeqH2.
      basic_utils_crush.
      rewrite filter_true_In; eauto.
      basic_goal_prep;
      basic_utils_crush.
    }
    {
      basic_goal_prep;
        basic_utils_crush.
      Lia.lia.
    }
  Qed.
  
  Lemma NoDup_filter B f (l : list B)
    : NoDup l ->
      NoDup (filter f l).
  Proof.
    induction l;     
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma all_filter {B} (l : list B) f (P : _ -> Prop)
    : (forall i, In i l -> Is_true (f i) -> P i) ->
      all P (filter f l).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    case_match; 
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma NoDup_max_list_len (P : nat -> Prop) l max_l
    : NoDup l ->
      (forall x, P x -> In x max_l) ->
      all P l ->
      (length l <= length max_l).
  Proof.
    revert P l.
    induction max_l;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct l;
      basic_goal_prep;
        basic_utils_crush.
    }
    {
      set (fun x => negb (eqb x a)) as f.
      pose proof (length_filter_elt_NoDup l a H).
      enough (length (filter (fun x : nat => negb (eqb x a)) l)
              <= length max_l) by Lia.lia.
      apply IHmax_l with (P:=(fun x => P x /\ x <> a)).
      { apply NoDup_filter; eauto. }
      {
        basic_goal_prep;
          basic_utils_crush.
        specialize (H0 x).
        basic_utils_crush.
      }
      {
      firstorder eauto.
        
      specialize (IHmax_l (fun x => P x /\ x <> a)
                    (filter (fun x : nat => negb (eqb x a)) l)
                    (NoDup_filter _ _ _ H)).
      apply all_filter.
      basic_goal_prep;
      basic_utils_crush.
      eapply in_all; eauto.
      }
    }
  Qed.
  
  Lemma length_filter_perm perm n m
    : NoDup perm ->
      all (fun x => x < n + m)%nat perm ->
      m >= length (filter (Nat.leb n) perm).
  Proof.
    intros.
    enough ((length (filter (Nat.leb n) perm)) <= m) by Lia.lia.
    replace m with (length (seq n m)) by (rewrite seq_length; eauto).
    eapply NoDup_max_list_len with (P := (fun x : nat => n <= x < n + m)); eauto.
    1: apply NoDup_filter; eauto.
    2:{
      apply all_filter.
      basic_goal_prep.
      autorewrite with utils in H2.
      split; eauto.
      eapply (in_all _ _ _ H0); eauto.
    }
    {      
      basic_goal_prep;
        basic_utils_crush.
    }
  Qed.

  

  
  Lemma length_remove_all' B (l : list B) perm n
    : NoDup perm ->
      all (fun x => x < n + length l)%nat perm ->
      length (remove_all' (filter (Nat.leb n) perm) l n)
      = length l - length (filter (Nat.leb n) perm).
  Proof.
    revert perm n.
    Local Opaque Nat.sub.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
    {
      rewrite remove_all'_filter_leb.
      rewrite filter_filter.
      rewrite filter_ext with (g:=Nat.leb (S n)); eauto.
      2:basic_goal_prep;
        unfold andb; case_match;
      basic_utils_crush; Lia.lia.
      rewrite IHl; eauto.
      2:{
        replace (S n + length l)
        with (n + S (length l)) by Lia.lia.
        auto.
      }
      
      replace (length (filter (Nat.leb n) perm))
        with (S (length (filter (Nat.leb (S n)) perm)));
        [ reflexivity |].
      apply length_filter_perm_S; eauto.
    }
    rewrite <- length_filter_notin_perm_S with (n:=n);
      eauto.
    rewrite remove_all'_filter_leb.
    rewrite filter_filter.
    rewrite filter_ext with (g:= (Nat.leb (S n))).
      2:basic_goal_prep;
        unfold andb; case_match;
      basic_utils_crush; Lia.lia.
      
      rewrite IHl; eauto; try Lia.lia.
      {
        enough (length l >= length (filter (Nat.leb (S n)) perm))
          by Lia.lia.
        pose proof (length_filter_bound (Nat.leb (S n)) perm).
        eapply length_filter_perm; eauto.
        replace (S n + length l)
          with (n + S (length l)) by Lia.lia.
        auto.
      }
      {
        replace (S n + length l)
          with (n + S (length l)) by Lia.lia.
        auto.
      }
  Qed.

  Hint Resolve List.NoDup_filter : utils.

  Lemma length_filter_perm_upper perm n
    : NoDup perm ->
      n >= length (filter (fun x => Nat.ltb x n) perm).
  Proof.
    assert (all (fun x => x < n) (filter (fun x : nat => Nat.ltb x n) perm)).
    {
      induction perm; basic_goal_prep; basic_utils_crush.
      case_match; basic_goal_prep; basic_utils_crush.
    }
    intro Hnd.
    apply List.NoDup_filter with (f:=  (fun x : nat => Nat.ltb x n)) in Hnd.
    revert H Hnd.
    generalize ((filter (fun x : nat => Nat.ltb x n) perm)).
    induction n;  basic_goal_prep; basic_utils_crush.
    {
      destruct l; basic_goal_prep; basic_utils_crush; Lia.lia.
    }
    {
      pose proof (length_filter_elt_NoDup _ n Hnd).
      enough (n >= length  (filter (fun x : nat => negb (eqb x n)) l)) by Lia.lia.
      eapply IHn; basic_utils_crush.
      revert H; clear.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      case_match;
        basic_goal_prep;
        basic_utils_crush; try Lia.lia.
    }
  Qed.
     
  
  Lemma len_extend_perm perm n
    : NoDup perm ->
      length (extend_perm perm n) = n.
  Proof.
    intros.
    unfold extend_perm.
    rewrite app_length.
    rewrite remove_all_filter.
    unfold remove_all.



    
    assert (all (fun x => x < n)%nat
              (filter (fun x : nat => Nat.ltb x n) perm)).
    {
      induction perm; basic_goal_prep; basic_utils_crush; try Lia.lia.
      case_match;
        basic_goal_prep; basic_utils_crush; try Lia.lia.
    }
    assert (NoDup (filter (fun x : nat => Nat.ltb x n) perm))
      by eauto using NoDup_filter.
    assert (n >= length (filter (fun x : nat => Nat.ltb x n) perm))
      by eauto using length_filter_perm_upper.
     
      

    revert H0 H1 H2.
    generalize (filter (fun x : nat => Nat.ltb x n) perm).
    clear H perm.
    basic_goal_prep.
    rewrite <- filter_true_In
      with (l:=l)
           (f:= Nat.leb 0)
           at 2.
    2:{
      basic_goal_prep;
      basic_utils_crush.
      Lia.lia.
    }
    rewrite length_remove_all'; eauto.
    all: rewrite seq_length; eauto.
    rewrite filter_true_In; try Lia.lia.
    basic_goal_prep; basic_utils_crush.
    Lia.lia.
  Qed.

  Lemma remove_all_seq_filter' perm n m
    : remove_all' perm (seq m n) m
      = filter (fun x => (negb (inb x perm))) (seq m n).
  Proof.
    revert m;
      induction n;
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    
  Lemma remove_all_seq_filter perm n
    : remove_all (seq 0 n) perm
      = filter (fun x => negb (inb x perm)) (seq 0 n).
  Proof.
    unfold remove_all.
    apply remove_all_seq_filter'.
  Qed.
   
  Lemma NoDup_extend_perm perm n
    : NoDup perm ->
      NoDup (extend_perm perm n).
  Proof.
    unfold extend_perm.
    rewrite remove_all_seq_filter.
    rewrite filter_ext
      with (g:= (fun x : nat => (inb x (seq 0 n))))
           at 1.
    2:{
      basic_goal_prep;
      basic_utils_crush.
      my_case Hin (inb a (seq 0 n));
        basic_utils_crush;
        try Lia.lia.
    }
    intros.
    apply List.NoDup_app_iff;
      basic_goal_prep;
      basic_utils_crush.
    apply NoDup_filter.
    apply seq_NoDup.
  Qed.
  
  (* TODO: simplify proof: use the fact that remove_all is equivalent to a filter
       in other side-conditions.
   *)
  Lemma no_dups_extend_perm_permutation perm n
    : NoDup perm ->
      Permutation (extend_perm perm n) (seq 0 n).
  Proof.
    intros.
    apply NoDup_Permutation_bis.
    { apply NoDup_extend_perm; eauto. }
    { rewrite seq_length, len_extend_perm; eauto. }
    { apply extend_perm_incl; eauto. }
  Qed.
      
End __.


Arguments select_all {A}%type_scope (l perm)%list_scope.
