(* A union-find data structure that can be instantiated 
   with either persistent arrays or a functional implementation of the same spec.
   The instantiation with persistent arrays should be performant,
   while the instantiation with a function implementation should be closed
   under the global context.

   based on this paper:
   Sylvain Conchon and Jean-Christophe Filliâtre. A persistent union-find data structure.
   In ACM SIGPLAN Workshop on ML, 37–45. Freiburg, Germany, October 2007. ACM Press.
   URL: https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf.
*)

Require Import ZArith List.
Open Scope positive.

From Tries Require Import Canonical.
Import PTree.

From Utils Require Import Utils Monad.
(*TODO: I think the eq instance is already defined somewhere*)
From Utils Require NatlikePos.
(*From Utils Require TrieMap NatlikePos.*)

Section UnionFind.

  Local Arguments empty {_}%type_scope.
  
  Record union_find :=
    MkUF {
        (* We use nats for rank because we do recursion on them.
           TODO: all ranks or just max rank?
         *)
        rank : tree nat;
        parent : tree positive;
        (* we include an upper bound on the rank for purposes of termination *)
        max_rank : nat;
        length : positive;
      }.
  
  Definition empty : union_find :=
    MkUF empty empty 0 1.

  (*TODO: write w/ state monad for clarity?*)
  
  Definition alloc '(MkUF ra pa mr l) :=
    (MkUF (set l 0%nat ra) (set l l pa), mr, l+1).

  (*TODO: should also decrease ranks for performance*)
  Fixpoint find_aux (mr : nat) f i : option (tree positive * positive) :=
    match mr with
    | O => None
    | S mr =>
          @! let fi <- get i f in
            if eqb fi i then
              ret (f,i)
            else
              let (f, r) <- find_aux mr f fi in
              let f := set i r f in
              ret (f,r)
    end.

                   
  
  Definition find '(MkUF ra pa mr l) x  : option _ :=
    @! let (f,cx) <- find_aux (S mr) pa x in
      ret (MkUF ra f mr l, cx).

  (*TODO: needs to return the root id (check)*)
  (* Note: returns None if either id is not in the map *)
  Definition union h x y : option _ :=
    @! let (h, cx) <- find h x in
      let (h, cy) <- find h y in
      if eqb cx cy then ret (h, cx) else
      (*  let '(ra, pa, mr, l) := h in*)
        let rx <- get cx h.(rank) in
        let ry <- get cy h.(rank) in
        match Nat.compare ry rx with
        | Lt => @!ret (MkUF (h.(rank))
                         (set cy cx h.(parent))
                         (h.(max_rank))
                         h.(length), cx)
        | Gt => @!ret (MkUF (h.(rank))
                         (set cx cy h.(parent)) 
                         (h.(max_rank))
                         (h.(length)), cy)
        | Eq => @!ret (MkUF (set cx (Nat.succ rx) h.(rank))
                         (set cy cx h.(parent))
                         (max h.(max_rank) (Nat.succ rx))
                         h.(length), cx)
        end.

  
  Import ListNotations.
  
  Inductive exact_rank (pa : tree positive) : positive -> nat -> Prop :=
  | rank_0 i : Some i = get i pa -> exact_rank pa i 0
  | rank_S n i j : exact_rank pa j n -> i<>j -> Some j = get i pa -> exact_rank pa i (S n).
  Hint Constructors exact_rank : utils.

(*
  Lemma path_unique pa i l1
    : path_at pa i l1 -> forall l2, path_at pa i l2 -> l1 = l2.
  Proof.
    induction 1;
      destruct 1;
      basic_goal_prep;
      basic_utils_crush;
      try congruence.
    assert (i = i0) by congruence; subst.
    erewrite IHpath_at; eauto.
  Qed.*)

  Definition is_parent u x y : Prop :=
    get y u.(parent) = Some x.

  
  (*TODO: move to Utils.v*)
  Section Closure.
    Context {A : Type}
      (R : A -> A -> Prop).
    Inductive equivalence_closure : A -> A -> Prop :=
    | eq_clo_base a b : R a b -> equivalence_closure a b
    | eq_clo_refl a : equivalence_closure a a
    | eq_clo_trans a b c : equivalence_closure a b -> equivalence_closure b c -> equivalence_closure a c
    | eq_clo_sym a b : equivalence_closure a b -> equivalence_closure b a.
    Hint Constructors equivalence_closure : utils.

    Inductive TR_closure : A -> A -> Prop :=
    | TR_refl a : TR_closure a a
    | trans_clo_succ a b c : R a b -> TR_closure b c -> TR_closure a c.
    Hint Constructors TR_closure : utils.

    Lemma TR_closure_trans a b c
      : TR_closure a b ->
        TR_closure b c ->
        TR_closure a c.
    Proof.
      induction 1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
  Lemma TR_implies_equiv a b
    : TR_closure a b ->
      equivalence_closure a b.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  End Closure.

    Hint Constructors equivalence_closure : utils.
    Hint Constructors TR_closure : utils.
    Hint Resolve TR_closure_trans TR_implies_equiv : utils.

  
  Definition Prop2_equiv {A B} (R1 R2 : A -> B -> Prop) :=
    forall a b, R1 a b <-> R2 a b.


  Hint Rewrite Pos.eqb_refl : utils.
  
  Notation pa_rel pa := (fun x y => Some x = get y pa).

  (* Defined thinking about separation logic *)
  Inductive repr :  tree positive -> (positive -> option positive) -> Prop :=
  | repr_emp  : repr PTree.empty (fun _ => None)
  | repr_alloc pa f i
    : repr pa f ->
      f i = None ->
      repr (set i i pa) (fun x => if x =? i then Some i else f x)
  | repr_compress pa f i j k
    : repr pa f ->
      get i pa = Some j ->
      f j = Some k ->
      repr (set i k pa) f
  | repr_union pa f i k
    : repr pa f ->
      get i pa = Some i ->
      get k pa = Some k ->
      repr (set i k pa)
        (fun x =>
           match f x with
           | Some j => if j =? i then Some k else f x
           | None => None
           end).

  Hint Rewrite gss : utils.
  
  Definition disjoint_sum {A} (t1 t2 t12: tree A) : Prop :=
    forall i,
      match get i t1, get i t2, get i t12 with
      | None, None, None => True
      | Some j, None, Some j' => j = j'
      | None, Some j, Some j' => j = j'
      | _, _, _ => False
      end.
  
  Definition sep {A} (P1 : _ -> Prop) (P2 : _ -> Prop)
    (t12 : tree A) : Prop :=
    exists t1 t2, disjoint_sum t1 t2 t12 /\ (P1 t2) /\ (P2 t2).

  Definition singleton {A} i j : tree A := (set i j PTree.empty).
  
  Inductive parent_tree_at : positive -> tree positive -> Prop :=
  | tree_root i : parent_tree_at i (singleton i i)
  | tree_branch pa1 pa2 i1 i2 pa
    : parent_tree_at i1 pa1 ->
      parent_tree_at i2 pa2 ->
      disjoint_sum pa1 pa2 pa ->
      parent_tree_at i2 (set i1 i2 pa).
  Hint Constructors parent_tree_at : utils.


  Lemma disjoint_sum_right pa1 pa2 pa i2
    : disjoint_sum pa1 pa2 pa ->
      Some i2 = get i2 pa2 ->
      Some i2 = get i2 pa.
  Proof.
    unfold disjoint_sum;
      intros H H';
      specialize (H i2).
    rewrite <- H' in *.
    revert H.
    case_match; try tauto.
    case_match; try tauto.
    congruence.
  Qed.

  

  Lemma disjoint_sum_left pa1 pa2 pa i1
    : disjoint_sum pa1 pa2 pa ->
      Some i1 = get i1 pa1 ->
      Some i1 = get i1 pa.
  Proof.
    unfold disjoint_sum;
      intros H H';
      specialize (H i1).
    rewrite <- H' in *.
    revert H.
    case_match; try tauto.
    case_match; try tauto.
    congruence.
  Qed.
  
  Lemma root_cycle i pa
    : parent_tree_at i pa ->
      Some i = get i pa.
  Proof.
    induction 1; intros;
      unfold singleton.
    {
      rewrite gss; auto.
    }
    {
      destruct (Pos.eq_dec i2 i1);
        subst;
        basic_utils_crush.
      rewrite gso; eauto.
      eauto using disjoint_sum_right.
    }
  Qed.
  
  Lemma roots_disjoint pa1 pa2 i1 i2 pa
    : parent_tree_at i1 pa1 ->
      parent_tree_at i2 pa2 ->
      disjoint_sum pa1 pa2 pa ->
      i1 <> i2.
  Proof.
    intros.
    intro Heq; subst.
    apply root_cycle in H, H0.

    specialize (H1 i2).
    rewrite <- H, <- H0 in H1.
    auto.
  Qed.

  
  Lemma set_set_same {A} a (b : A) p
    : (set a b (set a b p)) = (set a b p).
  Proof.
    eapply extensionality.
    intro i;
      destruct (Pos.eq_dec i a);
      subst;
      basic_utils_crush.
    rewrite !gso; eauto.
  Qed.
  Hint Rewrite @set_set_same : utils.

  
  Lemma set_set_comm {A} a c (b d : A) p
    : a <>c -> (set a b (set c d p)) = (set c d (set a b p)).
  Proof.
    intro Hneq.
    eapply extensionality.
    intro i.
    destruct (Pos.eq_dec i a);
      destruct (Pos.eq_dec i c);
      subst;
      repeat (rewrite ?gss; rewrite ?gso by eauto);
      congruence.
  Qed.
  
  Lemma disjoint_get_some A pa1 pa2 pa (k :A) j
    : disjoint_sum pa1 pa2 pa ->
      Some k = get j pa ->
      Some k = get j pa1 \/ Some k = get j pa2.
  Proof.
    intro H; specialize (H j); revert H;
      repeat (case_match; try tauto);
      intros; subst; (right + left); congruence.
  Qed.

  
  Lemma disjoint_sum_update_left A pa1 pa2 pa j (k : A) i
    : disjoint_sum pa1 pa2 pa ->
      Some k = get j pa1 ->
      disjoint_sum (set j i pa1) pa2 (set j i pa).
  Proof.
    intros H1 H2 j';
      specialize (H1 j');
      revert H1;
      destruct (Pos.eq_dec j j');
      subst;
      [ rewrite <- !H2 |].
    {
      repeat (case_match; intros; subst; try tauto; try congruence).
      all: rewrite !gss in*.
      all: try congruence.
    }
    {
      repeat (case_match; intros; subst; try tauto; try congruence).
      all: rewrite ?gso in* by eauto; try congruence.
      all: revert H1; case_match;intros; subst; try tauto; try congruence.
    }
  Qed.
  
  
  Lemma disjoint_sum_update_right A pa1 pa2 pa j (k : A) i
    : disjoint_sum pa1 pa2 pa ->
      Some k = get j pa2 ->
      disjoint_sum pa1 (set j i pa2) (set j i pa).
  Proof.
    intros H1 H2 j';
      specialize (H1 j');
      revert H1;
      destruct (Pos.eq_dec j j');
      subst;
      [ rewrite <- !H2 |].
    {
      repeat (case_match; intros; subst; try tauto; try congruence).
      all: rewrite !gss in*.
      all: try congruence.
    }
    {
      repeat (case_match; intros; subst; try tauto; try congruence).
      all: rewrite ?gso in* by eauto; try congruence.
      all: revert H1; case_match;intros; subst; try tauto; try congruence.
      all: revert H1; case_match;intros; subst; try tauto; try congruence.
    }
  Qed.

  (*
  (*TODO: should I require a self loop here?*)
  Lemma tree_split pa i
    :  parent_tree_at i pa ->
       forall j k,
         Some k = get j pa ->
         j <> i ->
         sep (parent_tree_at i) (parent_tree_at j) (set j j pa).
  Proof.
    unfold sep.
    induction 1;
      intros;
      unfold singleton in *.
    {
      rewrite ?gso in * by eauto; simpl in*; congruence.
    }
    {
*)
      

  Lemma path_compression' i pa
    : parent_tree_at i pa ->
      forall j k,
        j <> i ->
        Some k = get j pa ->
        parent_tree_at i (set j i pa).
  Proof.
    induction 1;
      intros;
      unfold singleton in *.
    {
      rewrite gso in*; eauto.
      simpl in *; congruence.
    }
    {
      destruct (Pos.eq_dec j i1);
        subst;
        basic_utils_crush.
      {
        rewrite gso in *; eauto.
        rewrite set_set_comm by eauto.
        pose proof (disjoint_get_some _ _ _ _ _ _ H1 H3) as H'.
        destruct H' as [H' | H'].
        2:{
          pose proof H'.
          apply IHparent_tree_at2 in H4; eauto.
          econstructor; eauto.
          eapply disjoint_sum_update_right; eauto.
        }
        {
          pose proof H'.
          apply IHparent_tree_at1 in H4; eauto.
          econstructor; eauto.
          eapply disjoint_sum_update_right; eauto.
          
          
eauto        Lemma set_comm
        
    
  Lemma path_compression i pa
    : parent_tree_at i pa ->
      forall j k,
        Some k = get j pa ->
        parent_tree_at i (set j i pa).
  Proof.
    induction 1;
      intros;
      unfold singleton.
      basic_goal_prep.

  Definition emp {A} (t : tree A) := t = PTree.empty.
  
  Fixpoint forest (l : list positive) : tree positive -> Prop :=
    match l with
    | [] => emp
    | i::l => sep (parent_tree_at i) (forest l)
    end.

  
  
  Lemma repr_no_cycles
    : repr pa f ->
      

  
  Lemma repr_spec pa f
    :  repr pa f ->
       forall i j,
         get i pa = Some j ->
         exists k, f i = Some k
                   /\ f j = Some k
                   /\ (f k = Some k)
                   /\ (i = j -> k = i).
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct (Pos.eq_dec i0 i); subst;
        basic_utils_crush.
      pose proof n.
      apply Pos.eqb_neq in n; rewrite n in*.
      rewrite gso in *; eauto.
      apply IHrepr in H1; break.
      eexists; intuition eauto.
      destruct (Pos.eq_dec j i); subst;
        basic_utils_crush;
        try congruence.
      pose proof n0.
      apply Pos.eqb_neq in n0; rewrite n0 in*.
      eauto.      
    }
    {
      pose proof (IHrepr _ _ H0); break.
      assert (x = k) by congruence; subst.
      destruct (Pos.eq_dec i0 i); subst;
        basic_utils_crush.
      {
        eexists; intuition eauto.
      destruct (Pos.eq_dec i j); subst;
        basic_utils_crush;
        try congruence.
        destru
      }
      pose proof n.
      apply Pos.eqb_neq in n; rewrite n in*.
      rewrite gso in *; eauto.
      apply IHrepr in H1; break.
      eexists; intuition eauto.
      destruct (Pos.eq_dec j i); subst;
        basic_utils_crush;
        try congruence.
      pose proof n0.
      apply Pos.eqb_neq in n0; rewrite n0 in*.
      eauto.  
      
    }
      
  
    Lemma repr_root pa f k
    :  repr pa f ->
       get k pa = Some k ->
       f k = Some k.
    intro H; revert k; induction H;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct (Pos.eq_dec k i); subst;
        basic_utils_crush.
      pose proof n.
      apply Pos.eqb_neq in n; rewrite n in*.
      rewrite gso in *; eauto.
    }
    {
      destruct (Pos.eq_dec k0 i); subst;
        basic_utils_crush.
      
    }
      {
        basic
    
  Lemma repr_parent  pa f
    :  repr pa f ->
       forall i j,
       get i pa = Some j ->
       f i = f j.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct (Pos.eq_dec i0 i); subst;
        basic_utils_crush.
      rewrite gso in *; eauto.
      apply Pos.eqb_neq in n; rewrite n in*.
      apply IHrepr in H1.
      rewrite H1.
      destruct (Pos.eq_dec i0 i); subst;
        basic_utils_crush;
        try congruence.
      destruct (Pos.eq_dec j i); subst;
        basic_utils_crush;
        try congruence.
      
      - cong.

        
  Lemma repr_exists pa f
    :  repr pa f ->
       forall i,
         match f i, get i pa with
         | Some _, Some _
         | None, None => True
         | _, _ => False
         end          
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct (Pos.eq_dec i0 i); subst;
        basic_utils_crush.
      rewrite gso in *; eauto.
      apply Pos.eqb_neq in n; rewrite n in*.
      apply IHrepr.
    }
    {
      destruct (Pos.eq_dec i0 i); subst;
        basic_utils_crush.
      rewrite gso in *; eauto.
      apply Pos.eqb_neq in n; rewrite n in*.
      apply IHrepr.
    }
      
    }
  

      
  Lemma repr_idempotent pa f
    : repr pa f ->
      forall i, option_map f (f i) = f i.
  Proof.
    unfold option_map.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      case_match; auto.
      destruct (Pos.eq_dec i0 i); subst;
        basic_utils_crush.
      apply Pos.eqb_neq in n; rewrite n in*.
      specialize (IHrepr i0).
      rewrite <- HeqH1 in *.
      destruct (Pos.eq_dec p i); subst;
        basic_utils_crush.
      apply Pos.eqb_neq in n0; rewrite n0 in*;
        auto.
    }
    {
      pose proof (IHrepr i0).
      my_case H' (f i0); auto.
      destruct (Pos.eq_dec p i); subst;
        basic_utils_crush.
      {
        assert (f k = Some k).
    }
  
  Definition represents (pa : tree positive) (f : positive -> positive) :=
    (forall i j, Some j = get i pa -> f i = f j)
    /\ (forall i, Some i = get i pa -> f i = i)
    /\ (forall i, None = get i pa -> f i = i).

  Lemma represents_empty : represents PTree.empty id.
  Proof.
    unfold represents.
    firstorder;
      (rewrite gempty in *; congruence).
  Qed.

  Lemma represents_idempotent pa f
    : represents pa f ->
      forall i, f (f i) = f i.
  Proof.
    unfold represents.
    firstorder.
    my_case H' (get i pa).
    2:{
      symmetry in H'; apply H1 in H'; congruence.
    }
    {
      symmetry in H'.
      assert (f i = f p) by eauto.
      
      specialize (H _ _ H').
      specialize (H p).
      [ rewrite H0 | rewrite H1]; eauto.
  
  Lemma represents_compress pa f i
    : represents pa f ->
      represents (set i (f i) pa) f.
  Proof.
    unfold represents.
    firstorder subst.
    {
      destruct (Pos.eq_dec i0 i); subst.
      {
        rewrite gss in *;
          basic_utils_crush.
      pose proof (H i0 j).
      rewrite H.
    }
      (rewrite ?gss in *; try congruence).
  Qed.
  
  

  (* equivalent to exists + and if i,j have ranks*)
  Definition rank_lt pa i j :=
    forall n m,
      exact_rank pa i n ->
      exact_rank pa j m ->
      (n < m)%nat.
  
  (* equivalent to exists + and if i,j have ranks*)
  Definition rank_le pa i j :=
    forall n m,
      exact_rank pa i n ->
      exact_rank pa j m ->
      (n <= m)%nat.


  
  (* Holds when a has values for exactly the positives less than bound *)
  Definition dense {A} (a : tree A) (bound : positive) : Prop :=
    forall i,
      match Pos.compare i bound, PTree.get i a with
      | Lt, Some _
      | Eq, None => True
      | Gt, None => True
      | _, _ => False
      end.

  Definition bounded_paths pa l :=
    forall i, i < l -> exists n, exact_rank pa i n.
  
  Record union_find_ok (u : union_find) :=
    {
      max_rank_ok : forall i j,
        (get i u.(rank)) = Some j ->
        (j <= u.(max_rank))%nat;
      ranks_ok : forall i ir n,
        get i u.(rank) = Some ir ->
        exact_rank u.(parent) i n -> (n <= ir)%nat;
      parents_ok : bounded_paths (parent u) u.(length);
      (*1/2 implied by above*)
      parents_dense : dense u.(parent) u.(length);
      rank_dense : dense u.(rank) u.(length);
    }.


  Lemma exact_rank_implies_parent_in_dom pa i n
    : exact_rank pa i n ->
      forall j,
        get i pa = Some j ->
        if get j pa then True else False.
  Proof.
    inversion 1; subst;
      basic_goal_prep;
      case_match; basic_utils_crush;
      try congruence.
    assert (j0 = j) by congruence; subst.
    inversion H0; congruence.
  Qed.
  
  Lemma bounded_paths_all_lt pa l
    : bounded_paths pa l ->
      dense pa l ->
      forall i j,
        get i pa = Some j ->
        j < l.
  Proof.
    unfold bounded_paths.
    intros.
    enough (if get j pa then True else False).
    {
      revert H2.
      pose proof (H0 j).
      case_match; try tauto.
      intros _.
      destruct (Pos.compare_spec j l); Lia.lia.
    }
    {
      case_match; try tauto.
      assert (i < l).
      {
        pose proof (H0 i).        
        destruct (Pos.compare_spec i l); subst; rewrite H1 in H2; try Lia.lia.
      }
      apply H in H2.
      break.
      inversion H2; subst; clear H2; try congruence.
      assert (j = j0) by congruence; subst.
      inversion H3; subst; clear H3; try congruence.
    }
  Qed.

  Lemma rank_pred pa i n
    : exact_rank pa i n ->
      forall j,
      get i pa = Some j ->
      exact_rank pa j (pred n).
  Proof.
    induction 1;
      basic_goal_prep; basic_utils_crush.
    {
      assert (i = j) by congruence; subst.
      basic_utils_crush.
    }
    {
      assert (j = j0) by congruence; subst.
      inversion H; subst; eauto with utils.
    }
  Qed.
    
     
  Lemma find_aux_preserves_dense l mr pa i pa' i'
    : dense pa l ->
      find_aux mr pa i = Some (pa', i') ->
      dense pa' l.
  Proof.
    unfold dense.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep; basic_utils_crush.
    {
      apply H.
    }
    {
      revert H0.
      case_match; try congruence.
      case_match.
      {
        basic_goal_prep;basic_utils_crush.
        apply H; eauto.
      }
      case_match; try congruence.
      basic_goal_prep; basic_utils_crush.
      
      destruct (Pos.eq_dec i0 i); subst.
      2:{
        rewrite gso; eauto.
        eapply IHmr; eauto.
      }
      rewrite gss.
      specialize (H i).
      rewrite <- HeqH0 in H.
      assumption.
    }
  Qed.
  
  Lemma find_aux_sets mr pa i pa' i'
    : find_aux mr pa i = Some (pa', i') ->
      mr <> 0%nat ->
      get i pa' = Some i'.
  Proof.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep; basic_utils_crush.
    revert H.
    case_match; try congruence.
    case_match.
    {
      basic_goal_prep;basic_utils_crush.
      symmetry in HeqH0; apply Pos.eqb_eq in HeqH0; subst; eauto.
    }
    case_match; try congruence.
    basic_goal_prep; basic_utils_crush.
    rewrite gss.
    reflexivity.
  Qed.

  
  Lemma rank_unique pa i m n
    : exact_rank pa i n -> exact_rank pa i m -> n = m.
    intro H.
    revert m.
    induction H;
      inversion 1;
      basic_goal_prep;
      basic_utils_crush;
      try congruence.
    assert (j = j0) by congruence; subst.
    apply IHexact_rank; eauto.
  Qed.
    
  Lemma rank_le_refl pa i
    : rank_le pa i i.
  Proof.
    intros m n He1 He2.
    enough (m = n) by Lia.lia.
    eauto using rank_unique.
  Qed.
  Hint Resolve rank_le_refl : utils.
  
  
  Lemma rank_le_parent p i pa
    : Some p = get i pa ->
      rank_le pa p i.
  Proof.
    unfold rank_le.
    intros.
    revert dependent p.
    revert n.
    induction H1;
      basic_goal_prep;
      basic_utils_crush.
    {
      assert (p = i) by congruence; subst.
      enough (n = 0)%nat by Lia.lia.
      eapply rank_unique; eauto with utils.      
    }
    {
      assert (j = p) by congruence; subst.
      assert (n = n0) by eauto using rank_unique; subst.
      Lia.lia.
    }
  Qed.

  Lemma rank_le_trans pa l i j k
    : bounded_paths pa l ->
      j < l ->
      rank_le pa i j ->
      rank_le pa j k ->
      rank_le pa i k.
  Proof.
    unfold rank_le;
      intuition.
    specialize (H _ H0).
    break.
    etransitivity.
    - eapply H1; eauto.
    - eapply H2; eauto.
  Qed.

  (*
  Lemma exact_rank_set_same pa i ri
    : exact_rank pa i ri ->
      forall i' ri',
      exact_rank pa i' ri' ->
      (ri' <= ri)%nat ->
      exists n, exact_rank (set i i' pa) i n.
  Proof.
    induction 1.
    {
      intros.
      destruct (Pos.eq_dec i i'); subst.
      {
        exists 0%nat; constructor; rewrite gss; eauto.
      }
      exists (S ri').
        ex
      
  
  Lemma exact_rank_set pa j rj
    (*TODO: what hyps needed?*)
    : (*dense pa l ->
      i < l ->
      i' < l ->*)
    exact_rank pa j rj ->
    forall i i' ri ri',
      exact_rank pa i ri ->
      exact_rank pa i' ri' ->
      (ri' <= ri)%nat ->
      exists n, exact_rank (set i i' pa) j n.
  Proof.
    induction 1.
    {
      intros.
      destruct (Pos.eq_dec i0 i); subst.
      {
        destruct (Pos.eq_dec i i'); subst.
        {
          exists 0%nat; constructor; rewrite gss; eauto.
        }
        exists (S ri').
        econstructor 2; eauto.
        - econstructor; rewrite gso; eauto.
          assert (exact_rank pa i 0)%nat by basic_utils_crush.
          specialize (H2 _ _ H6 H7).
          assert (x = 0)%nat by Lia.lia; subst.
          inversion H6; eauto.
        - rewrite gss; eauto.
      }
      {
        exists 0%nat; constructor; rewrite gso; eauto.
      }
    }
    {
      destruct (Pos.eq_dec i j).
    {
      intros; subst.
    }
   *)

  
  Lemma exact_rank_set_le' pa i i' j n m
    : exact_rank pa j n ->
      exact_rank pa i m ->
      (n <= m)%nat ->
      i <> j ->
      exact_rank (set i i' pa) j n.
  Proof.
    intro H; revert i i' m.
    induction H;
      basic_goal_prep;
      basic_utils_crush.
    {
      econstructor; eauto.
      rewrite gso; eauto.
    }
    {
      econstructor; cycle 2.
      { rewrite gso; eauto. }
      2:{ eauto. }
      eapply IHexact_rank; eauto.
      { Lia.lia. }
      intro; subst.
      pose proof (rank_unique _ _ _ _ H H2).
      Lia.lia.
    }
  Qed.
  
  Lemma exact_rank_set_le pa i i' n m
    : exact_rank pa i' n ->
      exact_rank pa i m ->
      (n <= m)%nat ->
      i <> i' ->
      exact_rank (set i i' pa) i (S n).
  Proof.
    intros H1 H2.
    revert n i' H1.
    induction H2.
    {
      inversion 1; subst; try Lia.lia.
      intros _ H3.
      econstructor; eauto.
      2: now rewrite gss.
      constructor; eauto.
      rewrite gso; eauto.
    }
    {
      intros.
      econstructor; cycle 2.
      { rewrite gss;eauto. }
      2:{ auto. }
      inversion H1; subst; clear H1.
      {
        econstructor; eauto.
        rewrite gso; eauto.
      }
      {
        econstructor; cycle 2.
        { rewrite gso; eauto. }
        2:{ auto. }
        assert (j0 <> i).
        {
          intro; subst.
          pose proof (rank_S _ _ _ _ H2 H H0).
          assert (n1 = S n) by eauto using rank_unique.
          Lia.lia.
        }
        eapply exact_rank_set_le'; [auto | | | auto].
        {
          econstructor 2; cycle 2; eauto.
        }
        Lia.lia.        
      }      
    }
    (*TODO: did I do induction? probably has a simpler proof*)
  Qed.
  
  Lemma bounded_paths_set pa i i' l
    : rank_le pa i' i ->
      bounded_paths pa l ->
      dense pa l ->
      i < l ->
      i' < l ->
      bounded_paths (set i i' pa) l.
  Proof.
    unfold bounded_paths.
    intros.
    revert dependent i.
    revert dependent i'.
    pose proof (H0 _ H4); break.
    induction H; basic_goal_prep; basic_utils_crush.
    {
      
      destruct (Pos.eq_dec i0 i).
      {
        subst.
        pose proof (H0 _ H3); break.
        destruct (Pos.eq_dec i i'); subst.
        {
          exists 0%nat; constructor; rewrite gss; eauto.
        }
        exists 1%nat; econstructor 2; eauto.
        - econstructor; rewrite gso; eauto.
          assert (exact_rank pa i 0)%nat by basic_utils_crush.
          specialize (H2 _ _ H6 H7).
          assert (x = 0)%nat by Lia.lia; subst.
          inversion H6; eauto.
        - rewrite gss; eauto.
      }
      {
        exists 0%nat; constructor; rewrite gso; eauto.
      }
    }
    {
      specialize (IHexact_rank ltac:(eapply bounded_paths_all_lt; eauto)).
      specialize (IHexact_rank _ H5).
      pose proof (IHexact_rank _ H6 H7); break.
      destruct (Pos.eq_dec i0 i).
      2:{        
        exists (S x); econstructor; eauto.
        rewrite gso; eauto.
      }
      subst.
      pose proof (H0 _ H5).
      break.
      destruct (Pos.eq_dec i i'); subst.
      {
        exists 0%nat; constructor; rewrite gss; eauto.
      }
      exists (S x0).
      econstructor; cycle 1; eauto.
      { rewrite gss; auto. }
      eapply exact_rank_set_le'.
      { eauto. }
      { econstructor 2; cycle 2; eauto. }
      {
        assert (exact_rank pa i (S n)); basic_utils_crush.
      }
      { eauto. }
    }
  Qed.

  
  Lemma dense_set_le {A} (a : tree A) l i i'
    : dense a l ->
      i < l ->
      dense (set i i' a) l.
  Proof.
    unfold dense.
    intros Hd Hlt i0.
    specialize (Hd i0).
    revert Hd.
    destruct (Pos.eq_dec i0 i); subst;
      [rewrite !gss | rewrite !gso]; auto.
    destruct (Pos.compare_spec i l); Lia.lia.
  Qed.

  Lemma find_aux_preserves_bounds mr l pa i pa' i'
    : bounded_paths pa l ->
      dense pa l ->
      i < l ->
      find_aux mr pa i = Some (pa', i') ->
      (i' < l /\ dense pa' l /\ bounded_paths pa' l /\ (rank_le pa' i' i) /\ (forall j, j < l -> rank_le pa i j -> i <> j -> get j pa = get j pa')).
  Proof.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep.
    { basic_utils_crush. }
    {
      revert H2.
      case_match; try congruence.
      case_match.
      {
        basic_goal_prep;basic_utils_crush.
      }
      case_match; try congruence.
      basic_goal_prep.
      safe_invert H2.

      symmetry in HeqH1.
      assert (p < l) by eauto using bounded_paths_all_lt.
      specialize (IHmr _ _ _ _ H H0 H2 HeqH1).
      break.
      assert (rank_le t0 i' i).
      {
        eapply rank_le_trans; eauto.
        intros m n Hem Hen.
        pose proof (rank_le_parent _ _ _ HeqH2).
        symmetry in HeqH0.
        apply Pos.eqb_neq in HeqH0.
        specialize (H7 _ H1 H8 HeqH0).
        rewrite H7 in HeqH2.
        symmetry in HeqH2.
        pose proof (rank_pred _ _ _ Hen _ HeqH2).
        assert (m = pred n) by eauto using rank_unique; subst; Lia.lia.
      }
      intuition eauto using dense_set_le, bounded_paths_set.
      2:{ rewrite gso; eauto.
          symmetry in HeqH0.
          rewrite Pos.eqb_neq in HeqH0.
          pose proof (H _ H1).          
          pose proof (H _ H9).
          break.
          inversion H12; subst; try congruence.
          assert (j0 = p) by congruence; subst.
          apply H7; eauto.
          {            
            intros m' n' Hm Hn.
            assert (x = n') by eauto using rank_unique; subst.
            assert (n = m') by eauto using rank_unique; subst.
            specialize (H10 _ _ H12 Hn).
            Lia.lia.
          }
          intro; subst.
          specialize (H10 _ _ H12 H14).
          Lia.lia.
      }
      {
        destruct (Pos.eq_dec i i'); subst; eauto with utils.
        intros m' n' Hm Hn.
        inversion Hn; subst; eauto with utils.
        {
          rewrite gss in *; eauto; congruence.
        }
        {
          rewrite gss in H11; safe_invert H11.
          assert (m' = n0) by eauto using rank_unique.
          Lia.lia.
        }
      }
    }
  Qed.
  

  
  (*TODO: move to Utils*)

  Fixpoint all_unique {A} (l : list A) :=
    match l with
    | [] => True
    | n::l' => ~ In n l' /\ all_unique l'
    end.
  Arguments all_unique {_} !_ /.


  
  Definition represents_sem (pa : tree positive) (f : positive -> positive) :=
    forall a b, equivalence_closure (pa_rel pa) a b <-> f a = f b.

  Inductive represents : tree positive -> (positive -> positive) -> Prop :=
  | repr_empty : represents PTree.empty id
  | repr_set pa f i j
    : represents pa f ->
      represents (set i j pa) (fun x => if x =? i then f j else f x).

  Lemma empty_represents
    : represents_sem PTree.empty id.
  Proof.
    unfold represents_sem, id; intros;
      simpl;
      basic_goal_prep; basic_utils_crush.
    induction H; congruence.
  Qed.

  Lemma find_aux_represents mr pa f i pa' i'
    : represents pa f ->
      Some (pa', i') = find_aux mr pa i ->
      represents pa f.
  
  (*TODO: want sets instead of lists.
    Will it be a problem?
   *)
  Inductive parent_tree_containing (pa : tree positive)
    : positive -> list positive -> Prop :=
  | parent_tree_root i : parent_tree_containing pa i []
  | parent_tree_branch i li j lj
    : parent_tree_containing pa i li ->
      parent_tree_containing pa j lj ->
      Some j = get i pa ->
      parent_tree_containing pa j (i::li++lj).

  Inductive parent_forest pa :=
  | empty_forest : parent_forest pa
  
  Definition parent_forest pa (roots : list positive) l :=
    forall i, i < l ->
              exists r lst, In r roots

  (*TODO: not true w/out cycle conditions*)
  Lemma pa_rel_set pa a b i j
    : equivalence_closure (pa_rel pa) a b ->
      TR_closure (pa_rel pa) j i ->
      equivalence_closure (pa_rel (set i j pa)) a b.
  Proof.
    intro H; revert j i; induction H;
      basic_goal_prep;
      basic_utils_crush.
    destruct (Pos.eq_dec b i);
      subst;
      basic_utils_crush.
    {
      inversion H0; subst.
      erewrite gss.
      econstructor 1.
    
    

  Lemma find_aux_preserves_rel mr pa i pa' i'
    : Some (pa', i') = find_aux mr pa i ->
      (forall a b, TR_closure (pa_rel pa) a b
                   <-> TR_closure (pa_rel pa') a b)
      /\ TR_closure (pa_rel pa) i' i.
  Proof.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep.
    { basic_utils_crush. }
    {
      revert H.
      case_match; try congruence.
      destruct (Pos.eq_dec p i); subst.
      {
        rewrite Pos.eqb_refl.
        basic_utils_crush.
      }
      {
        pose proof n as Hneq;
          apply Pos.eqb_neq in Hneq;
          rewrite Hneq.
        case_match; try congruence.
        break.
        intro H'; safe_invert H'.
        specialize (IHmr _ _ _ _ HeqH0).
        basic_utils_crush.
        {
          assert (TR_closure (pa_rel pa) p0 i) by eauto with utils.
          rewrite H in *.
        (*TODO: only true when i < i' *)
        2:{        
  
  Lemma find_aux_reduces_rank mr l pa i pa' i'
    : bounded_paths pa l ->
      dense pa l ->
      i < l ->
      Some (pa', i') = find_aux mr pa i ->
      forall j m,
        exact_rank pa j m ->
        exists n, exact_rank pa' j n /\ (n <= m)%nat.
  Proof.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep;
      basic_utils_crush.
    revert H2; case_match; try congruence.
    destruct (Pos.eq_dec p i); subst;
      [ rewrite Pos.eqb_refl;intro H'; safe_invert H'; eauto|].
    apply Pos.eqb_neq in n; rewrite n.
    case_match; try congruence; eauto.
    break.
    intro H'; safe_invert H'.
    assert (p < l) by eauto using bounded_paths_all_lt.
    specialize (IHmr _ _ _ _ H H0 H2 HeqH0 _ _ H3).
    break.
    symmetry in HeqH0.
    pose proof (find_aux_preserves_bounds _ _ _ _ _ _ H H0 H2 HeqH0).
    break.
    apply Pos.eqb_neq in n.
    destruct (Pos.eq_dec i j); subst.
    {
      pose proof HeqH2.
      rewrite H10 in H11; eauto; cycle 1.
      {
        intros m' n' Hm Hn.
        inversion Hn; subst; try congruence.
        assert (p = j0) by congruence; subst.
        assert (m' = n0) by eauto using rank_unique; subst.
        Lia.lia.
      }
      pose proof (H8 _ H2); break.
      pose proof (H8 _ H6); break.
      assert (j <> p0).
      {
        intro; subst.
        assert (exact_rank t0 p0 (S x0)) by eauto with utils.
        specialize (H9 _ _ H14 H12); Lia.lia.
      }
      eexists; split.
      {
        eapply exact_rank_set_le.
        1: eauto.
        1: eauto.
        2: eauto.
        eapply H9; eauto.
        2:eauto.
        3:eauto.
        eauto.
        
        apply exact_rank_set_le'.
    eauto.
    {
      
      .
        eexists; split; eauto.
      

  Lemma empty_ok : union_find_ok empty.
  Proof.
    unfold empty; constructor; simpl;
      unfold bounded_paths, dense;
      eauto;
      try congruence;
      try Lia.lia;
      intro i;
      rewrite ?gempty;
      destruct (Pos.compare_spec i 1); subst; eauto;
      Lia.lia.
  Qed.

  Lemma find_ok u u' i j
    : union_find_ok u ->
      (*Note: can relax this if max_rank > 1/sim conditions*)
      i < u.(length) ->
      Some (u', j) = find u i ->
      union_find_ok u'.
  Proof.
    unfold find.
    destruct u; simpl.
    intro H; destruct H; simpl in *.
    case_match; try congruence.
    break.
    intros Hlt H; safe_invert H.
    symmetry in HeqH.
    pose proof (find_aux_preserves_bounds _ _ _ _ _ _ parents_ok0 parents_dense0 Hlt HeqH).
    break.
    constructor; simpl; eauto.
  

Lemma in_split_path pa i l
  : path_at pa i l ->
    forall l1 j l2,
      l = l1 ++ j::l2 ->
      path_at pa j l2.
Proof.
  intros H l1; revert i l H.
  induction l1;
      basic_goal_prep; basic_utils_crush.
  {
    inversion H; eauto.
  }
  {
    safe_invert H.
    eapply IHl1 in H2; eauto.
  }
Qed.

  Lemma path_all_unique pa i l
    : path_at pa i l ->
      all_unique (i::l).
  Proof.
    induction 1;
      basic_goal_prep; basic_utils_crush.
    apply in_split in H5.
    destruct H5 as [l1 [l2 ?]].
    subst.
    eapply in_split_path in H; eauto.
    inversion H; subst; eauto; clear H.
    {
      assert (j = i) by congruence; subst; tauto.
    }
    {
      assert (i0 = i) by congruence; subst.
      apply H2.
      basic_utils_crush.
    }
    Qed.

  Definition rank_filtered ra mr (p1 p2 : tree positive) :=
    forall i,
      match get i ra with
      | Some ir =>
          (ir <= mr /\ get i p1 = get i p2)%nat
          \/ (ir > mr /\ get i p2 = None)%nat
      | None => get i p2 = None
      end.
  
  (*TODO: I want to filter keys, this filters vals;
    use a Prop to encode what I want?
   
  Definition rank_filter ra mr :=
    map_filter (fun i : positive => match get i ra with
                                    | Some r => if Nat.leb r mr then Some i else None
                                    | _ => None
                                    end).*)

  Lemma rank_filtered_0 u pa'
    : union_find_ok u ->
      u.(max_rank) = O ->
      rank_filtered u.(rank) 0 u.(parent) pa' ->
      forall i, get i pa' = Some i \/ get i pa' = None.
  Proof.
    unfold rank_filtered.
    intros.
    destruct u; destruct H;
      simpl in *; subst.
    specialize (H1 i).
    revert H1; case_match; intuition.
    rewrite <- H1.
    specialize (max_rank_ok0 _ _ ltac:(eauto)).
    assert (n = O) by Lia.lia;subst.
    my_case H' (get i parent0); intuition.
    specialize (ranks_ok0 _ _ ltac:(eauto)).
    destruct ranks_ok0;
      intuition; subst; intuition.
    unfold rank_lt in H.
    revert H; case_match; try tauto.
    case_match; try tauto.
    safe_invert HeqH.
    Lia.lia.
  Qed.

  (*
  Lemma rank_filtered_0_eq u pa'
    : union_find_ok u ->
      u.(max_rank) = O ->
      rank_filtered u.(rank) 0 u.(parent) pa' ->
      forall i, get i pa' = get i u.(parent).
  Proof.
    unfold rank_filtered.
    intros.
    destruct u; destruct H;
      simpl in *; subst.
    specialize (H1 i).
    revert H1; case_match; intuition.
    rewrite <- H1.
    specialize (max_rank_ok0 _ _ ltac:(eauto)).
    assert (n = O) by Lia.lia;subst.
    my_case H' (get i parent0); intuition.
    specialize (ranks_ok0 _ _ ltac:(eauto)).
    destruct ranks_ok0;
      intuition; subst; intuition.
    unfold rank_lt in H.
    revert H; case_match; try tauto.
    case_match; try tauto.
    safe_invert HeqH.
    Lia.lia.
  Qed.*)

  Definition value_ordering pa (l : list positive) :=
    forall i j, get i pa = Some j ->
                exists l1 l2, l = l1 ++ i::l2 /\ In j (i::l2).

  Definition record_if_rank ra n i :=
    match get i ra with
    | Some n' => if (n =? n')%nat then [i] else []
    | _ => []
    end.
  
  (* very inefficient, but useful for proofs*)
  Definition terms_of_rank_n ra l (n : nat) :=
    Pos.peano_rect _
      (record_if_rank ra n 1)
      (fun p l => record_if_rank ra n p ++ l)
      l.

  Fixpoint compute_value_ordering' ra l mr :=
    match mr with
    | O => terms_of_rank_n ra l 0
    | S n => terms_of_rank_n ra l mr ++ compute_value_ordering' ra l n
    end.

  Definition compute_value_ordering u :=
    compute_value_ordering' u.(rank) u.(length) u.(max_rank).

  
  Lemma value_order_tail
    : forall mr n ra l, (n <= mr)%nat ->
                        exists l1,
                          compute_value_ordering' ra l mr
                          = l1 ++ compute_value_ordering' ra l n.
  Proof.
    induction mr.
    {
      intros.
      replace n with O by Lia.lia.
      exists []; reflexivity.
    }
    {
      intros.
      destruct (Nat.compare_spec n (S mr)).
      {
        exists []; subst; reflexivity.
      }
      {
        simpl.
        assert (n <= mr)%nat by Lia.lia.
        specialize (IHmr _ ra l H1).
        destruct IHmr.
        rewrite H2.
        eexists; rewrite app_assoc; eauto.
      }
      {
        Lia.lia.
      }
    }
  Qed.

  
      
  Lemma record_if_rank_in'
    : forall n ra i, get i ra = Some n ->
                     In i (record_if_rank ra n i).
  Proof.
    unfold record_if_rank; intros; simpl in *.
    rewrite H.
    rewrite Nat.eqb_refl.
    basic_utils_crush.
  Qed.
  
  Lemma terms_of_rank_in' l
    : forall n ra i, i < l ->
                     get i ra = Some n ->
                     In i (terms_of_rank_n ra l n).
  Proof.
    unfold terms_of_rank_n.
    apply Pos.peano_ind with (p:=l).
    {
      intros; simpl.
      Lia.lia.
    }
    {
      intros; simpl.
      rewrite Pos.peano_rect_succ.
      basic_utils_crush.
      destruct (Pos.compare_spec i p).
      {
        left.
        subst.
        eapply record_if_rank_in'; eauto.
      }
      {
        right.
        apply H; eauto.
      }
      { Lia.lia. }
    }
  Qed.
        

  (*
  Lemma value_order_in
    : forall n ra l i,
      i < l ->
      get i ra = Some n ->
      In i (compute_value_ordering' ra l n).
  Proof.
    *)
  
  Lemma value_ordering_valid u
    : union_find_ok u ->
      value_ordering u.(parent) (compute_value_ordering u).
  Proof.
    unfold compute_value_ordering.
    destruct u; intro H; destruct H; simpl in *.
    unfold value_ordering; intros.
    pose proof (parents_dense0 i) as H0.
    revert H0; case_match; rewrite H; try tauto.
    intros _.
    pose proof (rank_dense0 i) as H0; revert H0.
    rewrite <- HeqH0.
    case_match; try tauto.
    intros _.
    assert (n <= max_rank0)%nat.
    {
      eapply max_rank_ok0; eauto.
    }
    pose proof (value_order_tail _ _ rank0 length0 H0).

    
    symmetry in HeqH1.
    symmetry in HeqH0.
    rewrite Pos.compare_lt_iff in HeqH0.
    pose proof (terms_of_rank_in' length0 n _ i ltac:(Lia.lia) HeqH1).
    apply in_split in H2.
    specialize (ranks_ok0 _ _ H).

    revert dependent i.
    revert dependent j.
    revert dependent n.
    induction n; intros;      
      destruct H1;
      rewrite H1;
      destruct H2 as [? [? ?]].
    {
      simpl in *.
      rewrite H2.
      exists (x++x0); exists x1;
        basic_utils_crush;
        rewrite ?app_assoc; auto.
      left.
      intuition.
      exfalso.
      unfold rank_lt in H3.
      revert H3; case_match; try tauto.
      rewrite HeqH1.
      Lia.lia.
    }
    {
      simpl in *.
      rewrite H2.
      exists (x ++ x0).
      exists (x1 ++ compute_value_ordering' rank0 length0 n).
      split.
      {
        change (?a::?b) with ([a]++b).
        rewrite !app_assoc.
        reflexivity.
      }
      {
        intuition.
        right.
        unfold rank_lt in H3.
        revert H3; case_match; try tauto.
        rewrite HeqH1.
        intro.
        specialize (IHn ltac:(Lia.lia)).
        assert (exists l1 : list positive,
                   compute_value_ordering' rank0 length0 max_rank0 = l1 ++ compute_value_ordering' rank0 length0 n).
        {
          rewrite app_assoc in H1.
          eexists; eauto.
        }
        specialize (IHn  ltac:(assumption)).
        clear H4.
  Admitted.


  
    Lemma find_aux_preserves_out_path mr pa i pa' i'
    : Some (pa', i') = find_aux mr pa i ->
      forall l, path_at pa i' l ->
                path_at pa' i' l.
    Proof.
      revert pa i pa' i'.
      induction mr;
        basic_goal_prep; basic_utils_crush.
       revert H.
    case_match; try congruence.
    case_match.
    {
      basic_goal_prep;basic_utils_crush.
    }
    case_match; try congruence.
    basic_goal_prep; basic_utils_crush.

    pose proof (path_all_unique _ _ _ H0).
    destruct H.
    specialize (IHmr _ _ _ _ HeqH1 _ H0).
    TODO: need i notin l
    inversion H0; subst; clear H0.
    {
      symmetry in HeqH0.
      apply Pos.eqb_neq in HeqH0.
      congruence.
    }
    replace i0 with p in * by congruence; clear i0.
    pose proof (IHmr _ _ _ _ HeqH1 _ H) as H'.
    destruct H' as [l1 [l2 [? ?]]].
    exists (p::l1); exists l2.
    basic_utils_crush.
    constructor; eauto.
    TODO: how to prove out /= in
    eexists; eexists.
    clar
    destruct HeqH1.
  
    Lemma find_aux_preserves_paths mr pa i pa' i'
    : Some (pa', i') = find_aux mr pa i ->
      forall l, path_at pa i l ->
      exists l1 l2,
        (l = l1 ++ l2) /\ path_at pa' i' l1.
  Proof.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep; basic_utils_crush.
    {
      exists l; exists [].
      basic_utils_crush.
    }
    revert H.
    case_match; try congruence.
    case_match.
    {
      basic_goal_prep;basic_utils_crush.
      exists l; exists [].
      basic_utils_crush.
    }
    case_match; try congruence.
    basic_goal_prep; basic_utils_crush.
    inversion H0; subst; clear H0.
    {
      symmetry in HeqH0.
      apply Pos.eqb_neq in HeqH0.
      congruence.
    }
    replace i0 with p in * by congruence; clear i0.
    pose proof (IHmr _ _ _ _ HeqH1 _ H) as H'.
    destruct H' as [l1 [l2 [? ?]]].
    exists (p::l1); exists l2.
    basic_utils_crush.
    constructor; eauto.
    TODO: how to prove out /= in
    eexists; eexists.
    clar
    destruct HeqH1.
    specialize (IHmr _ _ _ _
    pose proof (H p).
    destruct H0 as [l [Hpath [ir [? ?]]]].
    eexists.
    intuition.
    {
      constructor 2.
      destruct (Pos.eq_dec i0 i); subst.
      2:{
        rewrite gso; eauto.
        eapply IHmr; eauto.
      }
      rewrite gss.
      specialize (H i).
      rewrite <- HeqH0 in H.
      assumption.
    }
  Qed.
    
  Qed.

  
  Inductive find_aux_rel f : positive -> tree positive -> positive -> Prop :=
  | find_aux_self i : get i f = Some i -> find_aux_rel f i f i
  | find_aux_step i j
    : get i f = Some j ->
      forall f' k, find_aux_rel f j f' k ->
                   find_aux_rel f i (set i k f) k.


  Definition all_le (r1 r2 : tree nat) : Prop :=
    forall i, match get i r1, get i r2 with
              | Some ir1, Some ir2 => (ir1 <= ir2)%nat
              | None, None => True
              | _, _ => False
              end.

  Definition index_under_rank mr ra i :=
    match get i ra with
    | Some ir => (ir <= mr)%nat
    | None => False
    end.

  Definition some_and_equal {A} (a b : option A) :=
    match a,b with
    | Some a', Some b' => a' = b'
    | _, _ => False
    end.

  Definition read_set {A} (f : tree positive -> A) (l : list positive) :=
    forall p1 p2, (forall i, In i l -> some_and_equal (get i p1) (get i p2)) ->
                  f p1 = f p2.

  
  (*TODO: move to Utils.v?*)
  Inductive transitive_closure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | trans_clo_base a b : R a b -> transitive_closure R a b
  | trans_clo_succ a b c : R a b -> transitive_closure R b c -> transitive_closure R a c.

  Definition is_ancestor pa := transitive_closure (fun x y => get y pa = Some x).


  Lemma path_exists
    : forall u,
      union_find_ok u ->
      forall i, i < length u -> exists p, path_at (parent u) i p.
  Proof.
    destruct u;
      intro H; destruct H; simpl in *.
    
  
  Lemma find_aux_reads_ancestors mr pa i l
    : let f pa := find_aux mr pa i in
      read_set f l <-> (forall j, In j l <-> j = i \/ is_ancestor pa j i).
  Proof.
    revert pa i l.
    

    find_aux mr pa i = Some (pa', i') ->
      mr <> 0%nat ->
      get i pa' = Some i'.
  Proof.

  Lemma rank_ind ra (P : nat -> list positive -> _ -> Prop)
    : (forall pa l, 
          (forall i j : positive, get i pa = Some j -> i = j \/ rank_lt ra j i) ->
          (forall (i : positive) (ir : nat),  -> get i (rank u) = Some ir -> ir = 0%nat) ->
          (*Simplified: (forall i, get i ra = Some 0 -> get i pa = Some i) ->*)
                  P 0 pa) ->
      (forall pa mr pa', 
          (forall i j : positive, get i pa = Some j -> i = j \/ rank_lt ra j i) ->
          (forall i j : positive, get i pa' = Some j -> i = j \/ rank_lt ra j i) ->
          (forall i : positive, get i ra = Some ir ->
                                (ir <= mr)%nat ->
                                get i pa = get i pa') ->





    (forall pa mr,
          (forall i j : positive, get i pa = Some j -> i = j \/ rank_lt ra j i) ->
          (forall mr' pa', mr' < mr ->
                           (forall (i : positive) (j : nat), get i ra = Some j ->
                                                             (j <= mr')%nat ->
                                                             get i pa = get i pa') ->
                           P mr' pa') ->
      forall mr pa,
        (forall i j : positive, get i pa = Some j -> i = j \/ rank_lt ra j i) ->
        P mr pa.
  Proof.
    intros.
    revert ra P H pa H0.
    induction mr;
      basic_goal_prep; basic_utils_crush.
    {
      
      
  
  (*TODO: not very compatible w/ dense/ok
    
   *)
  Lemma uf_rank_ind (P : union_find -> Prop)
    : (forall u u', (u.(max_rank) > u'.(max_rank))%nat ->
                    (*TODO: do I need an iff here?*)
                    (forall i ir,
                        match get i u.(rank), get i u'.(rank) with
                        | Some ir, Some ir' =>
                            (ir <= u'.(max_rank))%nat ->
                            ir = ir' /\ get i u.(parent) = get i u'.(parent))
                        | None, None => True
                        | _, _ => False
                        end


                        get i u.(rank) = Some ir ->
                                  (ir <= u'.(max_rank))%nat ->
                                  (*TODO: = or <=?*)
                                  get i u'.(rank) = Some ir
                                  /\ get i u.(parent) = get i u'.(parent)) ->
                    P u' -> P u) ->
      forall u, P u.
    Admitted.
  
  Lemma find_aux_satisfies_rel u
    : union_find_ok u ->
      forall i pa' i',
        Some (pa', i') = find_aux u.(max_rank) u.(parent) i ->
        find_aux_rel u.(parent) i pa' i'.
  Proof.
    eapply uf_rank_ind with (u := u) (i:=i).
    intros.
    destruct u0; simpl in *.
    
    
    destruct u.

    TODO: how to do induction on rank?
    need a subset of things below a certain raink
    revert
  

  
  
  Lemma find_aux_sets_ancestors mr pa i pa' i'
    : Some (pa', i') = find_aux mr pa i ->
      forall j,
        get j pa = get j pa'
        \/ (is_ancestor pa j i /\ Some i' = get j pa').
  Proof.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep; basic_utils_crush.
    revert H.
    case_match; try congruence.
    case_match.
    {
      basic_goal_prep;basic_utils_crush.
    }
    case_match; try congruence.
    basic_goal_prep; basic_utils_crush.
    specialize (IHmr _ _ _ _ HeqH1).
    destruct (Pos.eq_dec j i); subst.
    {
      rewrite gss.
      specialize (IHmr i).
      intuition.
      TODO: pa not pa'; or p0 not p
      right.
      intuition.
    }
    intuition.
    rewrite gss.
    reflexivity.
  Qed.

  Section DenseIsoList.

    Import ListNotations.

    Definition tree_to_list {A} (t : tree A) : positive -> list A :=
      Pos.iter (fun (l : list A) => match get (Pos.of_succ_nat (List.length l)) t with
                         | Some x => x::l
                         | None => []
                                    end) [].

    Lemma tree_to_list_len {A} (t : tree A) p
      : dense t p -> List.length (tree_to_list t p) = pred (Pos.to_nat p).
    Proof.
      unfold tree_to_list.
      eapply Pos.peano_ind  with (p:=p).
      {
        simpl.
        intro H; specialize (H 1); simpl in *.
        revert H.
        case_match; tauto.
      }
      {
        intros; simpl in *.
        
      }
     intros _.
        compute.
      }      
      induction p; simpl in *.
      
    
    Fixpoint list_to_tree {A}  (l : list A) : positive * tree A :=
      match l with
      | [] => (1, PTree.empty)
      | x::l' =>
          let '(p,t) := list_to_tree l' in
          (Pos.succ p, set p x t)
      end.

    
    Lemma dense_1_empty {A} (t : tree A) : dense t 1 -> t = PTree.empty.
    Proof.
      intros.
      apply extensionality.
      intro i.
      specialize (H i).
      revert H.
      destruct (Pos.compare_spec i 1); subst; simpl in *;
        case_match; simpl; try tauto.
      Lia.lia.
    Qed.
    
    Definition dense_list_iso {A} (t : tree A) l
      : dense t l -> list_to_tree (tree_to_list t l) = (l,t).
    Proof.
      revert t.
      eapply Pos.peano_ind  with (p:=l).
      {
        unfold tree_to_list.
        simpl.
        intros.
        pose proof (H 1); simpl in *.
        revert H0.
        case_match; try tauto.
        intros _.
        simpl.

        f_equal.
        rewrite dense_1_empty; eauto.
      }
      {
        intros.
        unfold tree_to_list.
        rewrite Pos.iter_succ.
        
      }
        apply extensionality.
        intros.
        simpl.
        specialize (H i).
        revert H.
        destruct (Pos.compare_spec i 1); subst; simpl in *.
        {
          rewrite <- HeqH0; auto.
        }
        {
          Lia.lia.
        }
        {
          
        }
      }
    
    Record list_union_find :=
      MkUF {
          (* We use nats for rank because we do recursion on them.
           TODO: all ranks or just max rank?
           *)
          rank : list nat;
          parent : list positive;
          (* we include an upper bound on the rank for purposes of termination *)
          max_rank : nat;
          length : positive;
        }.
   
  Lemma find_aux_out_rank_ok mr u i pa' i'
    :  union_find_ok u ->
       find_aux mr u.(parent) i = Some (pa', i') ->
       (mr > 0)%nat ->
       is_parent u i i \/ rank_lt u.(rank) i' i.
  Proof.
    unfold is_parent.
    revert u i pa' i'.
    induction mr;
      basic_goal_prep; basic_utils_crush.
    { Lia.lia. }
    revert H0.
    case_match; try congruence.
    case_match.
    {
      basic_goal_prep;basic_utils_crush.
      symmetry in HeqH1; rewrite Pos.eqb_eq in HeqH1; subst; auto.     
    }
    case_match; try congruence.
    basic_goal_prep; basic_utils_crush.
    right.
    symmetry in HeqH2.
    symmetry in HeqH1; rewrite Pos.eqb_neq in HeqH1.
    destruct mr.
    {
      simpl in *.
      safe_invert HeqH2.
      destruct H.
      symmetry in HeqH0.
      specialize (ranks_ok0 _ _ HeqH0).
      destruct ranks_ok0; congruence.
    }
    
    specialize (IHmr _ _ _ _ H HeqH2 ltac:(Lia.lia)).
    destruct IHmr.
    {
      simpl in *.
      revert HeqH2.
      rewrite H0.
      rewrite Pos.eqb_refl.
      intro H'; safe_invert H'.
      destruct H.
      symmetry in HeqH0.
      specialize (ranks_ok0 _ _ HeqH0).
      destruct ranks_ok0; congruence.
    }
    unfold rank_lt in *.
    revert H0.
    case_match; auto.
    case_match; try tauto.
    case_match.
    2:{admit (*dense*). }
      {
        destruct H.
        specialuze
      }
    destruct H.
    
    rewrite <- HeqH3.
    intuition; subst.
    { admit(*TODO: need to know no cycles here*). }
    try congruence.
    
    destruct (Pos.eq_dec i0 i); subst.
      2:{
        rewrite gso; eauto.
        eapply IHmr; eauto.
      }
      rewrite gss.
      specialize (H i).
      rewrite <- HeqH0 in H.
      assumption.
    }
  Qed.


    

  Inductive represents : tree' positive -> @named_list positive (list positive) -> Prop :=
  | repr_empty : represents PTree.empty []
  | repr_nodes t' : represents' t' l -> represents (Nodes t') l.
  | 
  | repr001 t l : represents' t l -> tree' A
  | repr010 : A -> tree' A
  | repr011 : A -> tree' A -> tree' A
  | repr100 : tree' A -> tree' A
  | repr101 : tree' A -> tree' A -> tree' A
  | repr110 : tree' A -> A -> tree' A
  | repr111 : tree' A -> A -> tree' A -> tree' A.
  
  Inductive represents : tree positive -> @named_list positive (list positive) -> Prop :=
  | repr_empty : represents PTree.empty []
  | repr_nodes t' : represents' t' l -> represents (Nodes t') l.
    
 
  Definition represents (pa : tree positive) (forest : @named_list positive (list positive)) :=
    {
      indices_are_roots : forall i,
        match named_list_lookup_err forest i with
        | Some l => forall j, In j l <-> 
        | None => True
    }.
    forall n m, get n pa = Some m <->
                exists i l, named_list_lookup_err forest i = Some l
                            /\ List.In n l /\ List.In m l.

  Import ListNotations.
  Lemma empty_represents : represents PTree.empty [].
  Proof.
    split.
    {
      intros Hp; simpl in *.
      congruence.
    }
    {
      firstorder.
      simpl in *.
      congruence.
    }
  Qed.
  
  Lemma find_aux_preserves_represents mr pa i pa' i' l
    : represents pa l ->
      find_aux mr pa i = Some (pa', i') ->
      represents pa' l.
  Proof.
    unfold represents.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep; basic_utils_crush.
    {
      apply H; auto.
    }
    {
      apply H; eauto.
    }
    {
      revert H0.
      case_match; try congruence.
      case_match.
      {
        basic_goal_prep;basic_utils_crush.
        apply H; eauto.
      }
      case_match; try congruence.
      basic_goal_prep; basic_utils_crush.

      
      
      destruct (Pos.eq_dec i0 i); subst.
      2:{
        rewrite gso; eauto.
        eapply IHmr; eauto.
      }
      rewrite gss.
      specialize (H i).
      rewrite <- HeqH0 in H.
      assumption.
    }
  Qed.
    
    
  Lemma empty_represents : represents empty [].
  Proof.
    intros n m Hp;
      unfold is_parent in Hp; simpl in *.
    congruence.
  Qed.

  (*
  Inductive parent_degree (pa : tree positive) : positive -> nat -> Prop :=
  | pdegree_0 i : get i pa = Some i -> parent_degree pa i 0
  | pdegree_S i j n
    : get i pa = Some j ->
      parent_degree pa j n ->
      parent_degree pa i (Nat.succ n).
   *)
  
  Inductive parent_path (pa : tree positive)
    : positive -> positive -> Prop :=
  | ppath_0 i : get i pa = Some i -> parent_path pa i i
  | ppath_S i j k
    : get i pa = Some j ->
      parent_path pa j k ->
      parent_path pa i k.
  Hint Constructors parent_path : utils.

  (*
  Fixpoint path_length {pa i j} (path : parent_path pa i j) : nat :=
    match path with
    | ppath_0 _ _ => 0
    | ppath_S _ _ _ _ _ path' => S (path_length path')
    end.
   *)

  
  Record union_find_ok (u : union_find) :=
    {
      max_rank_ok : forall i j,
        (get i u.(rank)) = Some j ->
        (j <= u.(max_rank))%nat;
      ranks_ok : forall i j ir jr,
        get i u.(parent) = Some j ->
        get i u.(rank) = Some ir ->
        get j u.(rank) = Some jr ->
        i = j \/ (ir > jr)%nat;
      parents_ok : forall i j, get i u.(parent) = Some j -> j < u.(length);
      parents_dense : dense u.(parent) u.(length);
      rank_dense : dense u.(rank) u.(length);
    }.

  (*TODO: move to Utils.v*)
  Inductive equivalence_closure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | eq_clo_base a b : R a b -> equivalence_closure R a b
  | eq_clo_refl a : equivalence_closure R a a
  | eq_clo_trans a b c : equivalence_closure R a b -> equivalence_closure R b c -> equivalence_closure R a c
  | eq_clo_sym a b : equivalence_closure R a b -> equivalence_closure R b a.
  

  Hint Constructors equivalence_closure transitive_closure : utils.

 
  (*
  Lemma parent_path_rank_lt u
    : union_find_ok u ->
      forall j k,
        parent_path u.(parent) j k ->
        forall jr kr,
        get j u.(rank) = Some jr ->
        get k u.(rank) = Some kr ->
        (jr > kr)%nat.
  Proof.
    intro H; destruct H; destruct u; simpl in *.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    specialize (parents_ok0 _ _ H).
    rewrite <- Pos.compare_lt_iff in parents_ok0.
    specialize (rank_dense0 j).
    rewrite parents_ok0 in rank_dense0.
    revert rank_dense0; case_match; [intros _ | tauto].
    symmetry in HeqH3.
    specialize (IHparent_path n).
    assert (n > kr)%nat by (apply IHparent_path; eauto).
    enough (jr > n)%nat by Lia.lia.
    eapply ranks_ok0; eauto.
  Qed.
      
  
  Lemma find_aux_monotonic_path_length mr
    : forall u i pa' i',
      union_find_ok u ->
      Some (pa', i') = find_aux mr u.(parent) i ->
      forall j k jr kr,
        parent_path u.(parent) j k ->
      get j u.(rank) = Some jr ->
      get k u.(rank) = Some kr ->
      (jr > kr)%nat.
        
      (*
      union_find_ok (MkUF u.(rank) pa' u.(max_rank) u.(length)).*)
(*      get j pa' = Some k ->
      get j u.(rank) = Some jr ->
      get k u.(rank) = Some kr ->
parent_path_len 
      (jr > kr)%nat.*)
  Proof.
    induction mr;
      basic_goal_prep;
      basic_utils_crush.
    {
      eapply parent_path_rank_lt; eauto.
    }
    {
    revert H0.
    case_match; [| congruence].
    destruct (Pos.eq_dec p i); subst.
    {
      rewrite Pos.eqb_refl.
      intro H'; safe_invert H'.
      eapply parent_path_rank_lt; eauto.
    }
    {
      apply Pos.eqb_neq in n; rewrite n.
      case_match; [| congruence].
      case_match.
      intro H'; safe_invert H'; eauto.
    }
    }
    (*
      pose H.
      destruct H; constructor; simpl; eauto.
      2:{ admit (*Prior lemma + set lemma + i < len*). }
        {
          intros.
          destruct (Pos.eq_dec i0 i); subst.
          {
            rewrite gss in H.
            safe_invert H.
            eapply IHmr in HeqH1; eauto.
            destruct HeqH1; simpl in *.
            specialize (ranks_ok1 _ _ _ _ ? H0 H1
            eapply ranks_ok1; eauto.
            {}
            speciali
        }
      eapply IHmr in HeqH1; eauto.
      eapply ranks_ok0. [| eauto..].
      rewrite 
      TODO: need inverse of dense; empty above bound
      destruct (Pos.eq_dec j i); subst.
      {
        rewrite gss in H1.
        pose proof (H i p jr).
        TODO: need dense(rank)
        eapply H; eauto.
      eauto.
    }
    }*)
  Qed.
*)


  Lemma ancestor_in_uf u j k
    : union_find_ok u ->
      is_ancestor u k j ->
      if get j u.(parent) then True else False.
  Proof.
    unfold is_parent in *.
    destruct u.
    destruct 1.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    unfold is_parent in H; simpl in *.
    rewrite H; auto.
  Qed.
      
    
  Lemma ancestor_fixed_point u a
    : is_parent u a a ->
      forall b,
        is_ancestor u b a ->
        b = a.
  Proof.
    unfold is_ancestor, is_parent in *;
      destruct u.
    induction 2; try congruence.
    assert (b = c) by eauto.
    congruence.
  Qed.

  Lemma find_auxreturns_ancestor mr u i pa' i'
    : (mr > 0)%nat ->
      Some (pa', i') = find_aux mr u.(parent) i ->
      (is_ancestor u i' i).
  Proof.
    revert u i pa' i'.
    induction mr;
      basic_goal_prep;
      basic_utils_crush.
    { Lia.lia. }
    revert H0.
    case_match; [| congruence].
    destruct (Pos.eq_dec p i); subst.
    {
      rewrite Pos.eqb_refl.
      intro H'; safe_invert H'.
      constructor.
      unfold is_parent; auto.
    }
    {
      apply Pos.eqb_neq in n; rewrite n.
      case_match; [| congruence].
      case_match.
      intro H'; safe_invert H'; eauto.
      econstructor 2.
      {
        unfold is_parent; 
    }
    }
  
  Lemma ancestor_rank_geq'
    : forall u j k,
      union_find_ok u ->
      k <> j ->
      is_ancestor u k j ->
      forall jr kr,
        get j u.(rank) = Some jr ->
        get k u.(rank) = Some kr ->
        (jr > kr)%nat.
  Proof.
    unfold is_parent in *.
    intros u j k H.
    revert j k.
    induction 2;
        basic_goal_prep;
        basic_utils_crush.
    {
      destruct u; destruct H; simpl in *;
      specialize (ranks_ok0 _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption));
        intuition.
    }
    {
      destruct (Pos.eq_dec a b).
      {
        subst.
        pose proof (ancestor_fixed_point _ _ H1 _ H2).
             
      pose proof (ancestor_in_uf u 
    }
    
  Lemma ancestor_rank_geq'
    : forall u j k,
      union_find_ok u ->
      is_ancestor u k j ->
      k = j \/
      forall jr kr,
        get j u.(rank) = Some jr ->
        get k u.(rank) = Some kr ->
        (jr > kr)%nat.
  Proof.
    unfold is_parent in *.
    intros u j k H.
    revert j k.
    induction 1.
    {
      destruct u;
        destruct H;
        basic_goal_prep;
        basic_utils_crush.
      
    right.
    intros.
    pose proof (ancestor_in_uf u 
    pose proof (H1 _ _
    {
      

  (*
  Lemma find_aux_follows_path mr
    : forall u i pa' i',
      union_find_ok u ->
      Some (pa', i') = find_aux mr u.(parent) i ->
      parent_path u.(parent) i i'.
  Proof.
    induction mr;
      basic_goal_prep;
      basic_utils_crush.
    {
      constructor; eauto.
    }
    revert H0.
    case_match; [| congruence].
    destruct (Pos.eq_dec p i); subst.
    {
      rewrite Pos.eqb_refl.
      intro H'; safe_invert H'.
      eauto.
    }
    {
      apply Pos.eqb_neq in n; rewrite n.
      case_match; [| congruence].
      case_match.
      intro H'; safe_invert H'; eauto.
      
    }
   }
*)
    
    
  Lemma find_aux_preserves_longest_path mr
    : forall u i pa' i',
      union_find_ok u ->
      Some (pa', i') = find_aux mr u.(parent) i ->
      forall j k,
        parent_path u.(parent) j k ->
        get k u.(parent) = Some k ->
        parent_path pa' j k.
  Proof.
    induction mr;
      basic_goal_prep;
      basic_utils_crush.
    revert H0.
    case_match; [| congruence].
    destruct (Pos.eq_dec p i); subst.
    {
      rewrite Pos.eqb_refl.
      intro H'; safe_invert H'.
      eauto.
    }
    {
      apply Pos.eqb_neq in n; rewrite n.
      case_match; [| congruence].
      case_match.
      intro H'; safe_invert H'; eauto.
      
    }
    }
     
    
  Lemma find_preserves_ok uf i uf' i'
    : union_find_ok uf ->
      find uf i = Some (uf', i') ->
      union_find_ok uf'.
  Proof.
    destruct uf, uf'.
    intro H. (*; destruct H; simpl in *. *)
    simpl in *.
    case_match;[| congruence].
    case_match.
    intro H'; safe_invert H'.
    constructor; simpl; try solve [ destruct H; simpl in *; eauto].
    {
      intros.
      eapply find_aux_monotonic_path_length; eauto.
      eapply ppath_S; simpl; eauto.
      1:econstructor.
      all: simpl.
      eauto.
      
      admit (*
      TODO: hard case; show path length decreases*).
    }
    {
      symmetry in HeqH.
      eapply find_aux_preserves_dense; eauto.
    }
  Qed.
        
End UnionFind.

  
Module PositiveUnionFind.
  Import ZArith.
  Import TrieMap.TrieArrayList.
  Open Scope positive.

  Notation union_find := (@UnionFind.union_find positive trie_array).

  
  Definition is_parent '(MkUF ra pa mr : union_find) x y : Prop :=
    get pa y = x.

  (* TODO: will there be issues w/ positive overflowing here?
     TODO: if we assume is_top = false, do the issues go away?
   *)
  Inductive parent_degree (pa : trie_array positive) : positive -> positive -> Prop :=
  | pdegree_0 i : get pa i = i -> parent_degree pa i 1
  | pdegree_S i j n : get pa i = j -> parent_degree pa j n -> parent_degree pa i (succ n).
  
  Inductive parent_degree_bound (pa : trie_array positive) : positive -> positive -> Prop :=
  | pdegree_b0_bound i n : get pa i = i -> parent_degree_bound pa i n
  | pdegree_S_bound i j n m
    : get pa i = j ->
      parent_degree_bound pa j n ->
      n < m ->
      parent_degree_bound pa i m.
  
  Record trie_array_ok {A} (a : trie_array A) :=
    {
      len_gt_max_key : forall i e,
        PTree.get i (snd (fst a)) = Some e ->
        fst (fst a) > i
    }.

  Definition dense {A} (a : trie_array A) :=
    forall i, i < fst (fst a) ->
              if PTree.get i (snd (fst a)) then True else False.
  
  Record union_find_ok (u : union_find) :=
    {
      max_rank_ok : forall i, (get u.(rank) i) <= u.(max_rank);
      ranks_ok : forall i, parent_degree_bound u.(parent) i (get u.(rank) i);
      len_same : ArrayList.length u.(parent) = ArrayList.length u.(rank);
      parents_ok : trie_array_ok u.(parent);
      parents_dense : dense u.(parent);
      rank_ok : trie_array_ok u.(rank);
      rank_dense : dense u.(rank);
    }.

  (*TODO: move to Utils.v*)
  Inductive equivalence_closure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | eq_clo_base a b : R a b -> equivalence_closure R a b
  | eq_clo_refl a : equivalence_closure R a a
  | eq_clo_trans a b c : equivalence_closure R a b -> equivalence_closure R b c -> equivalence_closure R a c
  | eq_clo_sym a b : equivalence_closure R a b -> equivalence_closure R b a.

  Hint Constructors equivalence_closure : utils.

  Inductive parent_path (pa : trie_array positive) : positive -> positive -> Prop :=
  | ppath_0 i : parent_path pa i i
  | ppath_S i j k : get pa i = j -> parent_path pa j k -> parent_path pa i k.
  Hint Constructors parent_path : utils.

  Let uf_clo uf := equivalence_closure (is_parent uf).
  
  Lemma find_preserves_len_parents (uf : union_find) i uf' i'
    : find uf i = (uf', i') ->
      i < ArrayList.length uf.(parent) ->
      ArrayList.length uf.(parent) =  ArrayList.length uf'.(parent).
  Proof.    
    destruct uf as [ra pa mr].
    revert ra pa i uf' i'.
    eapply Pos.peano_ind with (p:=mr);
      intros;
      destruct uf' as [ra' pa' mr'];
      unfold trie_array in *; break; simpl in *.
    {
      revert H; case_match.
      repeat (revert HeqH;case_match); simpl in *;
        basic_goal_prep;
          basic_utils_crush;
        try congruence;
        safe_invert H3;
        rewrite Pos.max_l; Lia.lia.
    }
  Abort.

  (*
    
  Lemma find_preserves_ok uf i uf' i'
    : union_find_ok uf ->
      find uf i = (uf', i') ->
      (*TODO: do I want this condition?*)
      i < ArrayList.length uf.(parent) ->
      union_find_ok uf'.
  Proof.
    
    destruct uf as [ra pa mr].
    revert ra pa i uf' i'.
    eapply Pos.peano_ind with (p:=mr);
      intros; unfold trie_array in *; break.
    {
      destruct H;
        revert H0; simpl in *.
      case_match;
      revert HeqH.
      case_match;
        revert HeqH.
      {
        case_match;
          intro H'; symmetry in H'; apply Pos.eqb_eq in H'; subst;
          intro H'; safe_invert H';
          intro H'; safe_invert H';
          constructor; eauto.
      }
      {
        case_match.
        {
          intros _.
          intro H'; safe_invert H';
            intro H'; safe_invert H'.
          assert (Pos.max p1 (i + 1) = p1).
          {
            eapply Pos.max_l.
            destruct parents_ok0.
            simpl in *.
            symmetry in HeqH.
            apply len_gt_max_key0 in HeqH.
            Lia.lia.
          }
          {
            constructor; simpl; eauto.
            
            simpl.
      }
        }
        {
          
        }
          
    
  Lemma find_preserves_relation uf i uf' i'
    : union_find_ok uf ->
      find uf i = (uf', i') ->
      (forall x y, uf_clo uf x y <-> uf_clo uf' x y)
      /\ (uf_clo uf i i').
  Proof.
    destruct uf as [ra pa mr].
    revert ra pa i uf' i'.
    eapply Pos.peano_ind with (p:=mr);
      intros; unfold trie_array in *; break.
    {
      simpl in *.
      revert H.
      my_case Hir (PTree.get i r).
      2:{
      case_match.
      revert HeqH.
      case_match.
    }
  
  (*TODO: not true because arrays are non-canonical due to default elt*)
  Lemma get_set_same_existing (pa : trie_array positive) i
    :  trie_array_ok pa ->
       i < ArrayList.length pa -> set pa i (get pa i) = pa.
  Proof.
    destruct pa as [[? ?] ?]; simpl.
    intros [?] iltp; simpl in *.
    f_equal; f_equal.
    {
      unfold Pos.max.
      destruct (Pos.compare_spec p (i+1)); try Lia.lia.
    }
    case_match.
    2:{
    [|f_equal].
    cbn 
    unfold get, set.
    

  Lemma find_aux_path pa mr
    : forall i i' pa',
      i < ArrayList.length pa ->
        find_aux mr pa i = (pa', i') ->
        parent_path pa i i'.
  Proof.
    cbn [find_aux Natlike.iter NatlikePos.natlike_positive].
    revert pa.
    
    eapply Pos.peano_ind with (p:=mr);
      intros; break.
    {
      cbn -[get set] in H0.
      revert H0; case_match.
      {        
        basic_goal_prep;
          basic_utils_crush.
      }
      {
        destruct 
      }
    rewrite iter_succ in *; eauto.
    2:{
      apply is_top_spec; eauto.
    }
    revert H4; case_match.
    { 
      basic_goal_prep;
        basic_utils_crush.
    }
    remember (iter _ _ _ _ _) as loop.
    destruct loop.
    basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma max_rank_upper_bound u
    : union_find_ok u ->
      forall i, parent_degree_bound u.(parent) i u.(max_rank).
  Proof.
    intro H'; destruct H'.
    intro i.
    specialize (ranks_ok0 i).
    specialize (max_rank_ok0 i).
    clear len_same0.
    revert ranks_ok0 max_rank_ok0.
    generalize (get (rank u) i).
    induction 1.
    {
      constructor; eauto.
    }
    {
      econstructor 2; eauto.
      
    }

  Lemma find_aux_degree pa mr
    : forall i i' pa',
      find_aux mr pa i = (pa', i') ->
      (get pa' i = i' /\
      forall n j,
      parent_degree_bound pa j n ->
      parent_degree_bound pa' j n).
  Proof.
    revert pa.
    unfold find_aux.
    eapply natlike_ind with (n:=mr); auto;
      [ rewrite iter_zero in * |];
      basic_goal_prep;
      basic_utils_crush.
    rewrite iter_succ in *; eauto.
    2:{
      apply is_top_spec; eauto.
    }
    revert H4; case_match.
    { 
      basic_goal_prep;
        basic_utils_crush.
    }
    remember (iter _ _ _ _ _) as loop.
    destruct loop.
    basic_goal_prep;
      basic_utils_crush.
    symmetry in Heqloop.
    eapply H3 in Heqloop; eauto.
    TODO: need to know about i, i'

    Lemma decreasing_parent_degree_bound
      : parent_degree_bound pa j n ->
        parent_degree_bound (set pa i i') j n.
                             

    
  Lemma find_aux_sound pa mr
    : (forall i j, parent_degree pa i j -> leb j mr = true) ->
      forall i i' pa',
        find_aux mr pa i = (pa', i') ->
        equivalence_closure (fun a b => get pa a = b) i i'.
  Proof.
    unfold find_aux.
    revert pa.
    eapply natlike_ind with (n:=mr); auto;
      [ rewrite iter_zero in * |];
      basic_goal_prep;
      basic_utils_crush.
    rewrite iter_succ in *; eauto.
    2:{
      apply is_top_spec; eauto.
    }
    {
      revert H5; case_match.
      { 
        basic_goal_prep;
          basic_utils_crush.
      }
      remember (iter _ _ _ _ _) as loop.
      destruct loop.
      basic_goal_prep;
        basic_utils_crush.
      eapply H3; eauto.
      case_match'.
      eapply eq_clo_trans.
      rewrite iter_zero in H3.
      
      simpl in *.
    }
    auto.
    
    induction mr.
 
  Lemma find_sound u i u' i'
    : union_find_ok u -> find u i = (u', i') -> EqClo u i i'.
  Proof.
    destruct u.
    unfold find.
    unfold find_aux, union_find_ok.
    simpl.
    revert max_rank0 rank0 parent0.
    eapply natlike_ind; eauto.
    intros.
      with (n:=max_rank0).

    induction max_rank0.


  TODO: generalize proofs to any unionfind
*)

End PositiveUnionFind.
