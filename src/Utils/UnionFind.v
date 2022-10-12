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


Hint Rewrite gempty : utils.
Hint Rewrite Pos.eqb_refl : utils.
Hint Rewrite gss : utils.
Hint Rewrite grs : utils.


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


Lemma remove_remove_same A (t : tree A) i
  : remove i (remove i t) = remove i t.
Proof.
  apply extensionality;
    intro j;
    destruct (Pos.eq_dec i j);
    subst;
    rewrite ?grs;
    rewrite ?gro by eauto;
    auto.
Qed.
Hint Rewrite remove_remove_same : utils.


Hint Rewrite grs : utils.

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

  (* allocates a distinct identifier at the end *)
  Definition alloc '(MkUF ra pa mr l) :=
    (MkUF (set l 0%nat ra) (set l l pa) mr (l+1), l).

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
    exists t1 t2, disjoint_sum t1 t2 t12 /\ (P1 t1) /\ (P2 t2).

  Notation singleton i j := (set i j PTree.empty).

  
  Definition has_key {A} i (t : tree A) :=
    if get i t then True else False.
  Hint Unfold has_key : utils.

  
  Definition and1 {A} (P1 P2 : A -> Prop) a : Prop :=
    P1 a /\ P2 a.
  Hint Unfold and1 : utils.
  
  Definition not1 {A} (P : A -> Prop) a : Prop :=
    ~ P a.
  Hint Unfold not1 : utils.

  Definition impl1 {A} (P1 P2 : A -> Prop) a :=
    P1 a -> P2 a.
  Hint Unfold impl1 : utils.
  
  Notation Uimpl1 P1 P2 := (forall a, P1 a -> P2 a) (only parsing).
  
  Lemma sep_impl {A} {P1 P1' P2 P2' : tree A -> Prop}
    : Uimpl1 P1 P1' ->
      Uimpl1 P2 P2' ->
      Uimpl1 (sep P1 P2) (sep P1' P2').
  Proof.
    intros; unfold sep in *;
      break.
    exists x, x0; basic_utils_crush.
  Qed.
  
  Local Lemma sep_impl_def {A} {P1 P1' P2 P2' : tree A -> Prop}
    : Uimpl1 P1 P1' ->
      Uimpl1 P2 P2' ->
      Uimpl1 (sep P1 P2) (sep P1' P2').
  Proof.
    intros; unfold sep in *;
      break.
    exists x, x0; basic_utils_crush.
  Defined.

  Unset Elimination Schemes.
  Inductive tree_pointing_to : positive -> tree positive -> Prop :=
  | empty_points j : tree_pointing_to j PTree.empty
  | successor_points i1 i2 pa
    : i1 <> i2 ->
      sep (and1 (not1 (has_key i2)) (tree_pointing_to i1))
          (eq (singleton i1 i2)) pa ->
      tree_pointing_to i2 pa
  | branch_points i pa
    : sep (tree_pointing_to i) (tree_pointing_to i) pa ->
      tree_pointing_to i pa.
  Set Elimination Schemes.
  Hint Constructors tree_pointing_to : utils.

  Section TreePointingToInd.
    Context  (P : positive -> tree positive -> Prop)
      (Hempty : forall j : positive, P j PTree.empty)
      (Hsucc : forall (i1 i2 : positive) (pa : tree positive),
          i1 <> i2 ->
          sep (and1 (and1 (not1 (has_key i2)) (tree_pointing_to i1)) (P i1))
            (eq (singleton i1 i2)) pa ->
          P i2 pa)
      (Hbranch : forall (i : positive) (pa : tree positive),
          sep (and1 (tree_pointing_to i) (P i))
            (and1 (tree_pointing_to i) (P i)) pa -> P i pa).

    Fixpoint tree_pointing_to_ind (p : positive) (t : tree positive)
      (pf : tree_pointing_to p t) {struct pf} : P p t.
    Proof.
      refine (match pf with
              | empty_points j => Hempty j
              | successor_points i1 i2 pa Hneq pf' =>
                  Hsucc i1 i2 pa Hneq _
              | branch_points i pa pf' => _
              end).
      {
        eapply sep_impl_def.
        3: eauto.
        2: eauto.
        intros.
        split; eauto.
        apply tree_pointing_to_ind.
        destruct H; eauto.
      }
      {
        eapply Hbranch.
        eapply sep_impl_def.
        3: eauto.
        all:
        intros;
        split; eauto;
        apply tree_pointing_to_ind;
        eapply (proj2).
      }
    Qed.
  End TreePointingToInd.
  
  Definition parent_tree_at i : tree _ -> Prop :=
    sep (tree_pointing_to i)
      (eq (singleton i i)).

  Lemma disjoint_sum_right A pa1 pa2 pa i (j : A)
    : disjoint_sum pa1 pa2 pa ->
      Some j = get i pa2 ->
      Some j = get i pa.
  Proof.
    unfold disjoint_sum;
      intros H H';
      specialize (H i).
    rewrite <- H' in *.
    revert H.
    case_match; try tauto.
    case_match; try tauto.
    congruence.
  Qed.

  

  Lemma disjoint_sum_left A pa1 pa2 pa i (j : A)
    : disjoint_sum pa1 pa2 pa ->
      Some j = get i pa1 ->
      Some j = get i pa.
  Proof.
    unfold disjoint_sum;
      intros H H';
      specialize (H i).
    rewrite <- H' in *.
    revert H.
    case_match; try tauto.
    case_match; try tauto.
    congruence.
  Qed.

  
  
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

  
  Lemma disjoint_empty_left A (a : tree A)
    : disjoint_sum PTree.empty a a.
  Proof.
    intro i.
    rewrite gempty.
    case_match; subst; auto.
  Qed.
  Hint Resolve disjoint_empty_left : utils.
  
  Lemma disjoint_empty_right A (a : tree A)
    : disjoint_sum a PTree.empty a.
  Proof.
    intro i.
    rewrite gempty.
    case_match; subst; auto.
  Qed.
  Hint Resolve disjoint_empty_right : utils.

  
  Lemma sep_get_r A P1 P2 t (j:A) i
    : sep P1 P2 t ->
      (forall t', P2 t' -> Some j = get i t') ->
      Some j = get i t.
  Proof.
    unfold sep;
      intros; break.
    specialize (H i);
      specialize (H0 _ H2);
      rewrite <- H0 in H;
      revert H.
    repeat (case_match; autorewrite with utils; try tauto).
  Qed.

  
  Lemma sep_get_l A P1 P2 t (j:A) i
    : sep P1 P2 t ->
      (forall t', P1 t' -> Some j = get i t') ->
      Some j = get i t.
  Proof.
    unfold sep;
      intros; break.
    specialize (H i);
      specialize (H0 _ H1);
      rewrite <- H0 in H;
      revert H.
    repeat (case_match; autorewrite with utils; try tauto).
  Qed.
  
  
  Lemma root_cycle i pa
    : parent_tree_at i pa ->
      Some i = get i pa.
  Proof.
    unfold parent_tree_at.
    intros; eapply sep_get_r; eauto.
    basic_utils_crush.
  Qed.

  (*
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
   *)

  

  
  Lemma disjoint_remove A i1 i2 (pa : tree A)
    : disjoint_sum (remove i1 pa) (singleton i1 i2) (set i1 i2 pa).
  Proof.
    intro i.
    destruct (Pos.eq_dec i i1);
      subst;
      rewrite ?gss, ?grs;
      rewrite ?gso, ?gro by eauto;
      rewrite ?gempty; eauto.
    case_match; try tauto.
  Qed.
                       
  Lemma disjoint_unique_l A (t1 t2 t t1' : tree A)
    : disjoint_sum t1 t2 t ->
      disjoint_sum t1' t2 t ->
      t1 = t1'.
  Proof.
    intros.
    apply extensionality.
    intro i;
      specialize (H i);
      specialize (H0 i);
      revert H H0;
      repeat (case_match; try tauto; try congruence).
  Qed.
                   
  Lemma disjoint_unique_r A (t1 t2 t t2' : tree A)
    : disjoint_sum t1 t2 t ->
      disjoint_sum t1 t2' t ->
      t2 = t2'.
  Proof.
    intros.
    apply extensionality.
    intro i;
      specialize (H i);
      specialize (H0 i);
      revert H H0;
      repeat (case_match; try tauto; try congruence).
  Qed.
                 
  Lemma disjoint_unique_out A (t1 t2 t t' : tree A)
    : disjoint_sum t1 t2 t ->
      disjoint_sum t1 t2 t' ->
      t = t'.
  Proof.
    intros.
    apply extensionality.
    intro i;
      specialize (H i);
      specialize (H0 i);
      revert H H0;
      repeat (case_match; try tauto; try congruence).
  Qed.

  
  Lemma disjoint_sum_comm A (pa1 pa2 pa : tree A)
    : disjoint_sum pa1 pa2 pa ->
      disjoint_sum pa2 pa1 pa.
  Proof.
    intros H i;
      specialize (H i);
      revert H;
      repeat (case_match;
              subst;
              autorewrite with utils;
              try tauto;
              try congruence).
  Qed.
  

  Lemma sep_empty_left A (P1 P2 : _ -> Prop) (t : tree A)
    : P1 PTree.empty -> P2 t -> sep P1 P2 t.
  Proof.
    intros; exists PTree.empty, t;
      basic_utils_crush.
  Qed.
  Hint Resolve sep_empty_left : utils.
  
  Lemma sep_empty_right A (P1 P2 : _ -> Prop) (t : tree A)
    : P2 PTree.empty -> P1 t -> sep P1 P2 t.
  Proof.
    intros; exists t, PTree.empty;
      basic_utils_crush.
  Qed.
  Hint Resolve sep_empty_right : utils.

  
  Lemma not_has_key_empty A j
    : ~ has_key j (@PTree.empty A).
  Proof.
    unfold has_key;
      case_match;
      basic_utils_crush.
  Qed.
  Hint Resolve not_has_key_empty : utils.

  Hint Unfold and1 : utils.
  Hint Unfold not1 : utils.

  
  Lemma singleton_points i j
    : i <> j -> tree_pointing_to j (singleton i j).
  Proof.
    econstructor 2; basic_utils_crush.
  Qed.
  Hint Resolve singleton_points : utils.

  Lemma disjoint_remove' A i1 i2 (pa1 pa : tree A)
    : disjoint_sum pa1 (singleton i1 i2) pa ->
      pa1 = remove i1 pa.
  Proof.
    intro H; eapply disjoint_unique_l; eauto.
    pose proof (disjoint_remove _ i1 i2 pa).
    enough (pa = set i1 i2 pa) as H'
        by (rewrite <- H' in *; auto).
    eapply extensionality;
      intro i.
    destruct (Pos.eq_dec i i1).
    2:{ rewrite gso; auto. }
    basic_utils_crush.
    specialize (H i1);
      revert H;
      repeat (case_match; basic_utils_crush; try tauto; try congruence).
      revert H;
        repeat (case_match; basic_utils_crush; try tauto; try congruence).
  Qed.

  (*
  (*TODO: should I require a self loop here?*)
  Lemma tree_split pa i
    : tree_pointing_to i pa ->
       forall j k,
         Some k = get j pa ->
         j <> i ->
         sep (tree_pointing_to i) (tree_pointing_to j) (set j j pa).
  Proof.
    unfold sep.
    induction 1;
      intros;
      basic_utils_crush.
    {
      pose proof (disjoint_remove' _ _ _ _ _ H0); subst.
      destruct (Pos.eq_dec j i1); subst.
      {
        
      rewrite ?gso in * by eauto; simpl in*; congruence.
    }
    {
   *)

  
(*
  Lemma disjoint_sum_remove A (pa1 pa2 pa : tree A) i
    :  disjoint_sum pa1 pa2 pa ->
       disjoint_sum (remove i pa) (remove i pa) (remove i pa).
  Proof.
    intros H i'.
    destruct (Pos.eq_dec i i'); subst.
    {
      basic_utils_crush.
      case_match.
      repeat (case_match; basic_utils_crush;
              rewrite ?gro in * by eauto; try tauto; try congruence).
      {
        revert H; 
        repeat (case_match; basic_utils_crush;
              rewrite ?gro in * by eauto; try tauto; try congruence).*)


  
  Lemma disjoint_sum_has_key_l A (pa1 pa2 pa : tree A) k
    : disjoint_sum pa1 pa2 pa ->
      has_key k pa1 ->
      has_key k pa.
  Proof.
    intro H;
      specialize (H k);
      unfold has_key.
    repeat (revert H;
            case_match;
            basic_utils_crush;
            try tauto; try congruence).
  Qed.
  Hint Resolve disjoint_sum_has_key_l : utils.
  
  Lemma disjoint_sum_has_key_r A (pa1 pa2 pa : tree A) k
    : disjoint_sum pa1 pa2 pa ->
      has_key k pa2 ->
      has_key k pa.
  Proof.
    intro H;
      specialize (H k);
      unfold has_key.
    repeat (revert H;
            case_match;
            basic_utils_crush;
            try tauto; try congruence).
  Qed.
  Hint Resolve disjoint_sum_has_key_r : utils.

  (*
  Lemma tree_pointing_to_get_in_tree i pa
    : tree_pointing_to i pa ->
      forall j k, Some k = get j pa ->
                  k = i \/ has_key k pa.
  Proof.
    induction 1;
      intros;
      basic_utils_crush.
    {
      pose proof H2.
      specialize (H2 j);
        revert H2.
      rewrite <- !H3.
      basic_utils_crush.
      destruct (Pos.eq_dec i1 j); subst.
      {
        revert H2;
          basic_utils_crush.
        revert H2;
          case_match; auto; tauto.
      }
      {
        revert H2;
          case_match;
          rewrite !gso, !gempty by eauto;
          auto; try tauto.
        intro; subst.
        apply IHtree_pointing_to in HeqH2.
        right.
        intuition subst.
        {
          eapply disjoint_sum_has_key_r; eauto.
          unfold has_key.
          rewrite gss.
          auto.
        }
        {
          eapply disjoint_sum_has_key_l; eauto.
        }
      }
    }
    {
      pose proof (disjoint_get_some _ _ _ _ _ _ H1 H2).
      firstorder eauto with utils.
    }
  Qed.
*)
        
    (*
  (*can use above + induction on size of pa?
    issue: removing the wrong node breaks invariants
   *)
  Lemma tree_pointing_to_get_diff i pa
    : tree_pointing_to i pa ->
      forall j k, Some k = get j pa ->
                  j <> i.
  Proof.    
    induction 1;
      intros;
      basic_utils_crush.
    {
      eapply IHtree_pointing_to; eauto.
    }
    {
    }*)


  Lemma disjoint_sum_set_left A pa1 pa2 pa i (j : A)
    : None = get i pa2 ->
      disjoint_sum pa1 pa2 pa ->
      disjoint_sum (set i j pa1) pa2 (set i j pa).
  Proof.
    intros H1 H2 i';
      specialize (H2 i');
      revert H2.
    destruct (Pos.eq_dec i' i); subst;
      basic_utils_crush;
      rewrite <- ?H1; auto;
    rewrite ?gso by eauto;
      auto;
    repeat (case_match;
            basic_utils_crush;
            try tauto;
            try congruence).
  Qed.

  
  Lemma disjoint_sum_set_right A pa1 pa2 pa i (j : A)
    : None = get i pa1 ->
      disjoint_sum pa1 pa2 pa ->
      disjoint_sum pa1 (set i j pa2) (set i j pa).
  Proof.
    intros H1 H2 i';
      specialize (H2 i');
      revert H2.
    destruct (Pos.eq_dec i' i); subst;
      basic_utils_crush;
      rewrite <- ?H1; auto;
    rewrite ?gso by eauto;
      auto;
    repeat (case_match;
            basic_utils_crush;
            try tauto;
            try congruence).
  Qed.

  
  
  Lemma disjoint_sum_set_right' A pa1 pa2 pa i (j : A)
    : None = get i pa ->
      disjoint_sum pa1 pa2 pa ->
      disjoint_sum pa1 (set i j pa2) (set i j pa).
  Proof.
    intros.
    enough (None = get i pa1) by eauto using disjoint_sum_set_right.
    specialize (H0 i);
      rewrite <- H in H0;
      repeat (revert H0;
              case_match;
            basic_utils_crush;
            try tauto;
              try congruence).
  Qed.

  
  
  Lemma disjoint_sum_set_left' A pa1 pa2 pa i (j : A)
    : None = get i pa ->
      disjoint_sum pa1 pa2 pa ->
      disjoint_sum (set i j pa1) pa2 (set i j pa).
  Proof.
    intros.
    enough (None = get i pa2) by eauto using disjoint_sum_set_left.
    specialize (H0 i);
      rewrite <- H in H0;
      repeat (revert H0;
              case_match;
            basic_utils_crush;
            try tauto;
              try congruence).
  Qed.
  
  
  Lemma remove_set_diff A i j (k:A) pa
    : i <> j -> remove i (set j k pa) = set j k (remove i pa).
  Proof.
    intros; apply extensionality; intro i'.
    destruct (Pos.eq_dec i' i); subst;
      basic_utils_crush;
      rewrite ?gso by eauto;
      basic_utils_crush.
    rewrite gro by eauto.
    destruct (Pos.eq_dec i' j); subst;
      basic_utils_crush;
      rewrite ?gso by eauto;
      basic_utils_crush.
    rewrite gro by eauto.
    auto.
  Qed.
  
  Lemma remove_remove_diff A i j (pa : tree A)
    : i <> j -> remove i (remove j pa) = (remove j (remove i pa)).
  Proof.
    intros; apply extensionality; intro i'.
    destruct (Pos.eq_dec i' i); subst;
      basic_utils_crush;
      rewrite ?gro by eauto;
      basic_utils_crush.
    destruct (Pos.eq_dec i' j); subst;
      basic_utils_crush;
      rewrite ?gso by eauto;
      basic_utils_crush.
    rewrite !gro by eauto.
    auto.
  Qed.

  
  Lemma disjoint_sum_has_key A (pa1 pa2 pa : tree A) k
    : disjoint_sum pa1 pa2 pa ->
      has_key k pa ->
      has_key k pa1 \/  has_key k pa2.
  Proof.
    intro H;
      specialize (H k);
      unfold has_key.
    repeat (revert H;
            case_match;
            basic_utils_crush;
            try tauto; try congruence).
  Qed.
  Hint Resolve disjoint_sum_has_key : utils.

  
  Lemma sep_implies_not_has_key A P1 P2 (t : tree A) i
    : sep P1 P2 t ->
      (forall t, P1 t -> ~ has_key i t) ->
      (forall t, P2 t -> ~ has_key i t) ->
      ~ has_key i t.
  Proof.
    unfold sep;
      intros;
      break.
    intro Hk.
    eapply disjoint_sum_has_key in H; eauto.
    firstorder.
  Qed.

  
  Lemma has_key_singleton A i j (k : A)
    : has_key i (singleton j k) <-> i = j.
  Proof.
    unfold has_key.
    destruct (Pos.eq_dec i j); subst;
      basic_utils_crush.
    rewrite gso, gempty in *; tauto.
  Qed.
  Hint Rewrite has_key_singleton : utils.

  
  Lemma has_key_sep_distr A P1 P2 (t : tree A) j
    : has_key j t ->
      sep P1 P2 t ->
      sep (and1 P1 (has_key j)) P2 t
      \/ sep P1 (and1 P2 (has_key j)) t.
  Proof.
    unfold sep; intros; break.
    pose proof (disjoint_sum_has_key _ _ _ _ _ H0 H).
    destruct H3; [left | right];
      exists x, x0;
      basic_utils_crush.
  Qed.
  
  Lemma key_not_root i pa j
    : tree_pointing_to i pa ->
      has_key j pa ->
      i <> j.
  Proof.
    induction 1.
    {
      unfold has_key;
      case_match;
      basic_utils_crush;
      try tauto; try congruence.
    }
    {
      intros Hk Heq; subst.
      eapply sep_implies_not_has_key;
        unfold and1 in *;
        basic_utils_crush.
    }
    {
      intro Hk.
      pose proof (has_key_sep_distr _ _ _ _ _ Hk H).
      clear H Hk; destruct H0;
        unfold sep, and1 in *; break;
        eauto.
    }
  Qed.


  
  Lemma disjoint_remove_left A (pa1 pa2 pa : tree A) j
    : has_key j pa1 ->
      disjoint_sum pa1 pa2 pa ->
      disjoint_sum (remove j pa1) pa2 (remove j pa).
  Proof.
    intros Hk H i;
      specialize (H i);
      destruct (Pos.eq_dec i j);
      unfold has_key in *;
      revert Hk;
      basic_utils_crush;
      revert H Hk;
      repeat (case_match;
              subst;
              autorewrite with utils;
              try tauto;
              try congruence);
      intros;
      rewrite ?gro in * by eauto;
      try congruence.
  Qed.
  Hint Resolve disjoint_remove_left : utils.

  
  Definition node_to_opt_K {A B} (t : tree' A)
    (k : tree A -> option A -> tree A -> B) :=
    match t with
    | Node001 tr => k Empty None (Nodes tr)
    | Node010 x => k Empty (Some x) Empty
    | Node011 x tr => k Empty (Some x) (Nodes tr)
    | Node100 tl => k (Nodes tl) None Empty
    | Node101 tl tr => k (Nodes tl) None (Nodes tr)
    | Node110 tl x => k (Nodes tl) (Some x) Empty
    | Node111 tl x tr => k (Nodes tl) (Some x) (Nodes tr)
    end.

  
  Definition node_to_opt_K' {A B C} (t : tree' A)
    (k : tree A -> option A -> tree A -> B -> C) :=
    fun b =>
    match t with
    | Node001 tr => k Empty None (Nodes tr) b
    | Node010 x => k Empty (Some x) Empty b 
    | Node011 x tr => k Empty (Some x) (Nodes tr) b
    | Node100 tl => k (Nodes tl) None Empty b 
    | Node101 tl tr => k (Nodes tl) None (Nodes tr) b
    | Node110 tl x => k (Nodes tl) (Some x) Empty b
    | Node111 tl x tr => k (Nodes tl) (Some x) (Nodes tr) b
    end.

  Section Inner.
    Context {A : Type}.
    Context (tree'_merge : tree' A -> tree' A -> tree' A).
    (*Used in the empty case, which disappears in evaluation*)
    Context (default : tree' A).

    Definition option_fst (x y : option A) :=
      match x, y with
      | Some x, Some y => Some x
      | Some x, None => Some x
      | None, Some y => Some y
      | None, None => None
      end.
    
    Definition tree_op (x y : tree A) :=
      match x, y with
      | Nodes x, Nodes y => Nodes (tree'_merge x y)
      | Nodes x, Empty => Nodes x
      | Empty, Nodes y => Nodes y
      | Empty, Empty => Empty
      end.        

    Definition merge_help t1l (x1 : option A) t1r '(t2l,x2, t2r) :=
      match tree_op t1l t2l,
        option_fst x1 x2,
        tree_op t1r t2r with
      (* Never happens *)
      | Empty, None, Empty => default
      | Empty, None, Nodes tr => (Node001 tr)
      | Empty, Some x, Empty => (Node010 x)
      | Empty, Some x, Nodes tr => (Node011 x tr)
      | Nodes tl, None, Empty => (Node100 tl)
      | Nodes tl, None, Nodes tr => (Node101 tl tr)
      | Nodes tl, Some x, Empty => (Node110 tl x)
      | Nodes tl, Some x, Nodes tr => (Node111 tl x tr)
      end.

    
    Definition body (t1 t2 : tree' A) : tree' A :=
    (node_to_opt_K t2
      (fun a b c => node_to_opt_K' t1 merge_help (a,b,c))).

    Definition body' :=
      Eval cbv [merge_help tree_op option_fst body node_to_opt_K' node_to_opt_K]
        in body.
  End Inner.

  
  
  (*TODO: can be generalized into a map2*)
  (* left-biased *)
  
  Fixpoint tree'_merge' {A} (t1 t2 : tree' A) {struct t1} : tree' A :=
    body' tree'_merge' t1 t2.

  Definition tree'_merge := Eval cbv [tree'_merge' body'] in @tree'_merge'.
  
  Definition tree_merge {A} (t1 t2 : tree A) :=
    match t1, t2 with
    | Empty, _ => t2
    | Nodes t', Empty => Nodes t'
    | Nodes t1', Nodes t2' =>
        Nodes (tree'_merge' t1' t2')
    end.

  
  
  Definition disjoint {A} (t1 t2: tree A) : Prop :=
    forall i,
      match get i t1, get i t2 with
      | None, None
      | Some _, None
      | None, Some _ => True
      | Some _, Some _ => False
      end.
  
  Lemma disjoint_sum_implies_disjoint A (t1 t2 t3: tree A)
    : disjoint_sum t1 t2 t3 ->
      disjoint t1 t2.
  Proof.
    intros H i; specialize (H i); revert H;
      repeat case_match; tauto.
  Qed.

  Lemma disjoint_tree_merge A (t1 t2: tree A)
    : disjoint t1 t2 ->
      disjoint_sum t1 t2 (tree_merge t1 t2).
  Proof.
    intros H i; specialize (H i); revert H.
    destruct t1; destruct t2;
      unfold tree_merge;
      simpl;
      try congruence.
    1,2: intros _; case_match; tauto.
    case_match; case_match; try tauto;
      revert dependent t1;
        revert dependent t0;
      induction i;
        destruct t0; destruct t1;
        simpl in *;
      intros; try congruence;
      rewrite <- ?HeqH, <- ?HeqH0; auto;
      eapply IHi; eauto.
  Qed.
      
  Lemma disjoint_sum_assoc A (pa1 pa2 pa pa11 pa12 : tree A)
    : disjoint_sum pa1 pa2 pa ->
      disjoint_sum pa11 pa12 pa1 ->
      exists pa2',
        disjoint_sum pa11 pa2 pa2'
        /\ disjoint_sum pa12 pa2' pa.
  Proof.
    exists (tree_merge pa11 pa2); split.
    {
      apply disjoint_tree_merge.
      admit.
    }
    {
      
      
    (*TODO: really want concat here *)
  Admitted.

  Lemma tree_split pa i
    : tree_pointing_to i pa ->
       forall j,
         has_key j pa ->
         sep (tree_pointing_to i)
           (and1 (not1 (has_key i)) (tree_pointing_to j)) (remove j pa).
  Proof.
    Admitted (*TODO: fix up
    induction 1;
      intros;
      basic_utils_crush.
    {
      pose proof (disjoint_remove' _ _ _ _ _ H2);
        subst.
      destruct (Pos.eq_dec j i1); subst.
      {
        exists PTree.empty, (remove i1 pa).
        intuition eauto with utils.
      }
      {
        eapply disjoint_sum_has_key in H3; eauto.
        unfold has_key in *; rewrite gso, gempty in * by eauto;
          intuition subst.
        apply IHtree_pointing_to in H4.
        unfold sep in *; break.
        exists (set i1 i2 x), x0;
          intuition eauto with utils.
        {
          erewrite remove_remove_diff in H3; eauto.
          replace (remove j pa) with (set i1 i2 (remove i1 (remove j pa))).
          {
            eapply disjoint_sum_set_left; auto.
            specialize (H3 i1);
              repeat (revert H3;
                      case_match;
                      basic_utils_crush;
                      try tauto; try congruence).
          }
          apply extensionality.
          intro i.
          destruct (Pos.eq_dec i i1);
            basic_utils_crush;
            rewrite ?gro by eauto.
          {
            eapply disjoint_sum_right;
              basic_utils_crush.
          }
          {
            rewrite gso by eauto.
            rewrite gro by eauto.
            reflexivity.
          }            
        }
        {
          assert (~ has_key i1 x).
          {
            unfold has_key.
            specialize (H3 i1);
              revert H3.
            case_match; try tauto; subst.
            rewrite gro; eauto.
            rewrite grs.
            case_match; auto.
          }
          econstructor 2; cycle 3.
          {
            eapply disjoint_sum_set_right';
              eauto with utils.
            revert H7;
              unfold has_key;
              case_match; try tauto.
          }              
          1:eauto.
          {
            unfold has_key.
            revert H0.
            rewrite gro; eauto.

            case_match; subst; try tauto.
            intros _.
            case_match; subst; try tauto.
            intros _.
            specialize (H3 i2);
              revert H3.
            rewrite <- !HeqH1.
            destruct (Pos.eq_dec i2 j); subst;
              basic_utils_crush;
              revert H3;  case_match; try tauto.
            rewrite ! gro by eauto.
            rewrite <- HeqH0.
            auto.
          }
          {
            auto.
          }
        }
        {
          specialize (H3 i2);
            revert H7 H0 H3.
          repeat (case_match; subst;
                  autorewrite with utils; try tauto;
                  try congruence).
          intros _ _ ?; subst.
          destruct (Pos.eq_dec i2 j);
            basic_utils_crush.
          rewrite gro in HeqH3 by eauto.
          congruence.
        }
      }
    }
    {
      eapply disjoint_sum_has_key in H2; eauto.
      basic_utils_crush.
      {
        pose proof (IHtree_pointing_to1 _ H3).
        unfold sep in *; break.
        assert (tree_pointing_to i (set j i x0)).
        {
          econstructor 2; eauto with utils.
          {
            intro; subst;
              eapply key_not_root.
            - apply H.
            - apply H3.
            - auto.
          }
          {
            apply disjoint_sum_set_right';
              basic_utils_crush.
            enough (~ has_key j x0).
            {
              revert H7; unfold has_key; case_match; tauto.
            }
            intro Hk.
            eapply key_not_root.
            - apply H6.
            - apply Hk.
            - auto.
          }
        }
        {
          assert (disjoint_sum (remove j pa1) pa2 (remove j pa))
            by eauto with utils.
          epose proof (disjoint_sum_assoc _ _ _ _ _ _ H8 H2);
            break.
          exists x1, x0; repeat split; auto.
          2:{
            econstructor 3; cycle 2; eauto.
          }
          apply disjoint_sum_comm; auto.
        }
      }
      {
        pose proof (IHtree_pointing_to2 _ H3).
        unfold sep in *; break.
        assert (tree_pointing_to i (set j i x0)).
        {
          econstructor 2; eauto with utils.
          {
            intro; subst;
              eapply key_not_root.
            - apply H0.
            - apply H3.
            - auto.
          }
          {
            apply disjoint_sum_set_right';
              basic_utils_crush.
            enough (~ has_key j x0).
            {
              revert H7; unfold has_key; case_match; tauto.
            }
            intro Hk.
            eapply key_not_root.
            - apply H6.
            - apply Hk.
            - auto.
          }
        }
        {
          assert (disjoint_sum pa1 (remove j pa2) (remove j pa)).
          {
            eapply disjoint_sum_comm.
            eapply disjoint_remove_left; eauto.
            eapply disjoint_sum_comm.
            auto.
          }
          eapply disjoint_sum_comm in H8.
          epose proof (disjoint_sum_assoc _ _ _ _ _ _ H8 H2);
            break.
          exists x1, x0; repeat split; auto.
          2:{
            econstructor 3; cycle 2; eauto.
          }
          apply disjoint_sum_comm; auto.
        }
      }
        
    }
  Qed.*).
  
  Lemma set_remove_same A i (j:A) pa
    : set i j (remove i pa) = set i j pa.
  Proof.
    apply extensionality;
      intro i';
      destruct (Pos.eq_dec i i');
      subst;
      basic_utils_crush;
      rewrite ?gso, ?gro by eauto;
      basic_utils_crush.
  Qed.

  
  
  Lemma sep_set_right A (P1 P2 P2' : _ -> Prop) i (j:A) t
    : ~ has_key i t ->
      sep P1 P2' t ->
      (forall t, P2' t -> P2 (set i j t)) ->
      sep P1 P2 (set i j t).
  Proof.
    intros Hk Hs H.
    unfold sep in *; break.
    exists x, (set i j x0).
    basic_utils_crush.
    eapply disjoint_sum_set_right'; auto.
    revert Hk;
      unfold has_key;
      case_match;
      basic_utils_crush;
      try tauto.
  Qed.
  
  Lemma sep_set_left A (P1 P2 P1' : _ -> Prop) i (j:A) t
    : ~ has_key i t ->
      sep P1' P2 t ->
      (forall t, P1' t -> P1 (set i j t)) ->
      sep P1 P2 (set i j t).
  Proof.
    intros Hk Hs H.
    unfold sep in *; break.
    exists (set i j x), x0.
    basic_utils_crush.
    eapply disjoint_sum_set_left'; auto.
    revert Hk;
      unfold has_key;
      case_match;
      basic_utils_crush;
      try tauto.
  Qed.

  Lemma not_has_key_remove A i (t : tree A)
    : has_key i (remove i t) -> False.
  Proof.
    unfold has_key;
      basic_utils_crush.
  Qed.
  Hint Resolve not_has_key_remove : utils.

  
  Lemma remove_not_has_key A i (t : tree A)
    : ~ has_key i t ->
      remove i t = t.
  Proof.
    intros.
    apply extensionality.
    intro i';
      revert H; unfold has_key;
      destruct (Pos.eq_dec i i');
      basic_utils_crush.
    {
      revert H; case_match; try tauto.
    }
    {
      rewrite gro; eauto.
    }
  Qed.


  Lemma tree_does_not_contain_root i t
    : tree_pointing_to i t -> ~ has_key i t.
  Proof.
    intros H Hk.
    eapply key_not_root; eauto.
  Qed.
  Hint Resolve tree_does_not_contain_root : utils.
  
  Lemma path_compression' i pa j
    : i <> j ->
      has_key j pa ->
      tree_pointing_to i pa ->
        tree_pointing_to i (set j i pa).
  Proof.
    intros Hij Hk H.
    eapply tree_split with (j:=j) in H; eauto.
    {
      econstructor 3.
      rewrite <- set_remove_same.
      eapply sep_set_right;
        basic_utils_crush.
      econstructor 2; eauto.
      rewrite <- (set_remove_same _ _ _ t0).
      eapply sep_set_right.
      1: basic_utils_crush.
      {
        eapply sep_empty_right;
          basic_utils_crush.
        1: exact eq_refl.
        destruct H0.
        assert (~ has_key j t0) by eauto with utils.
        rewrite remove_not_has_key; eauto.
        basic_utils_crush.
      }
      {
        basic_utils_crush.
      }
    }
  Qed.

  
  Lemma sep_set_left' A (P1 P2 P1' : _ -> Prop) i (j:A) t
    : sep P1' P2 t ->
      (forall t', (has_key i t <-> has_key i t') -> P1' t' -> P1 (set i j t')) ->
      (forall t', P2 t' -> ~ has_key i t') ->
      sep P1 P2 (set i j t).
  Proof.
    intros Hk Hs H.
    unfold sep in *; break.
    exists (set i j x), x0.
    basic_utils_crush.
    {
      eapply disjoint_sum_set_left; auto.
      specialize (H _ H2).
      revert H;
        unfold has_key;
        case_match;
        basic_utils_crush;
        try tauto.
    }
    {
      eapply Hs; eauto.
      specialize (H _ H2).
      specialize (H0 i).
      unfold has_key in *.
      revert H H0;
        repeat (case_match; subst; autorewrite with utils;
                try tauto; try congruence).
    }
  Qed.
  
    
  Lemma path_compression i pa
    : parent_tree_at i pa ->
      forall j,
        has_key j pa ->
        parent_tree_at i (set j i pa).
  Proof.
    intros.
    unfold parent_tree_at in *.
    destruct (Pos.eq_dec i j);
      subst.
    {
      (*
      assert (k = j).
      {
        enough (Some j = get j pa) by congruence.
        eapply sep_get_r;
          basic_utils_crush.
      }
      subst.*)
      replace (set j j pa) with pa; eauto.
      apply extensionality;
        intro i;
        destruct (Pos.eq_dec i j);
        subst;
        basic_utils_crush.
      2:rewrite gso; eauto.
      symmetry.
      eapply sep_get_r; eauto.
      basic_utils_crush.
    }
    {
      eapply sep_set_left';
        basic_utils_crush.
      eapply path_compression'; eauto.
    }
  Qed.
      

  Definition emp {A} (t : tree A) := t = PTree.empty.
  
  Fixpoint forest (l : list positive) : tree positive -> Prop :=
    match l with
    | [] => emp
    | i::l => sep (parent_tree_at i) (forest l)
    end.

  
  Lemma pointing_no_cycles i pa
    : tree_pointing_to i pa ->
      forall j k,
      Some k = get j pa ->
      j <> k.
  Proof.
    induction 1;
      unfold sep, and1, not1 in *;
      basic_utils_crush.
    {
      specialize (H0 k);
        revert H0;
        rewrite <- H1.
      case_match;
        destruct (Pos.eq_dec k i1);
        basic_utils_crush;
        revert H0;
        rewrite gso; eauto.
    }
    {
      specialize (H k);
        revert H;
        rewrite <- H0.
      case_match;
        case_match;
        eauto.
    }
  Qed.

  Lemma cycles_are_root j pa
    : parent_tree_at j pa ->
      forall i,
      Some i = get i pa ->
      i = j.
  Proof.
    unfold parent_tree_at.
    intros.
    destruct (Pos.eq_dec i j);
      basic_utils_crush.
    exfalso.
    unfold sep in *; break.
    pose proof (disjoint_get_some _ _ _ _ _ _  H H0).
    subst.
    rewrite gso, gempty in *; eauto.
    intuition try congruence.
    eapply pointing_no_cycles; eauto.
  Qed.

  (*TODO: ~has_key length condition is a bit awkward*)
  Lemma alloc_spec (R : _ -> Prop) u u' i
    : ~ has_key u.(length) u.(parent) ->
      R u.(parent) ->
      (u', i) = alloc u ->
      sep (parent_tree_at i) R u'.(parent).
  Proof.
    destruct u; simpl;
      intros.
    safe_invert H1; simpl.
    unfold parent_tree_at.
    simpl.
    eapply sep_impl.
    1: eauto.
    {
      intros a Pa.
      let T := type of Pa in
      unify T (and1 (not1 (has_key length0)) R a).
      eapply (proj2 Pa).
    }
    eapply sep_set_left'.
    {
      eapply sep_empty_left; basic_utils_crush.
      exact eq_refl.
    }
    {
      intros; subst.
      eapply sep_empty_left; basic_utils_crush.
    }
    {
      basic_utils_crush.
      destruct H1; eauto.
    }
  Qed.

  Definition submap {A} (t1 t2 : tree A) :=
    forall j k, Some k = get j t1 ->
                Some k = get j t2.

  
  Lemma disjoint_sum_submap_l A (x x0 t : tree A)
    : disjoint_sum x x0 t ->
      submap x t.
  Proof.
    intros H j k;
      specialize (H j);
      revert H;
      repeat case_match;
      try tauto;
      basic_utils_crush;
      try congruence.
  Qed.
  Hint Resolve disjoint_sum_submap_l : utils.
  
  Lemma disjoint_sum_submap_r A (x x0 t : tree A)
    : disjoint_sum x x0 t ->
      submap x0 t.
  Proof.
    intros H j k;
      specialize (H j);
      revert H;
      repeat case_match;
      try tauto;
      basic_utils_crush;
      try congruence.
  Qed.
  Hint Resolve disjoint_sum_submap_r : utils.
  
  Lemma sep_impl_submap {A} {P1 P1' P2 P2' : tree A -> Prop} t
    : (forall t', submap t' t -> P1 t' -> P1' t') ->
      (forall t', submap t' t -> P2 t' -> P2' t') ->
      sep P1 P2 t -> sep P1' P2' t.
  Proof.
    intros; unfold sep in *;
      break.
    exists x, x0; basic_utils_crush.
  Qed.

  Lemma sep_by_left A P1 P2 (t : tree A) (Q : Prop)
    : sep P1 P2 t ->
      (forall t', P1 t' -> Q) ->
      Q.
  Proof.
    unfold sep; firstorder.
  Qed.

  
  Lemma sep_by_right A P1 P2 (t : tree A) (Q : Prop)
    : sep P1 P2 t ->
      (forall t', P2 t' -> Q) ->
      Q.
  Proof.
    unfold sep; firstorder.
  Qed.


  
  Lemma find_aux_has_key mr pa p t0 p0
    : Some (t0, p0) = find_aux mr pa p ->
      has_key p pa.
  Proof.
    unfold has_key.
    destruct mr;
      simpl; try congruence.
    case_match; try tauto.
    congruence.
  Qed.

  
  Lemma find_aux_end_loop mr pa p t0 p0
    : Some (t0, p0) = find_aux mr pa p ->
      Some p0 = get p0 pa.
  Proof.
    revert pa p t0 p0.
    induction mr;
      basic_goal_prep;
      basic_utils_crush.
    revert H.
    case_match; try congruence.
    destruct (Pos.eq_dec p1 p);
      basic_utils_crush.
    revert H.
    pose proof n; apply Pos.eqb_neq in n; rewrite n.
    case_match;
      basic_utils_crush.
  Qed.

  Ltac destruct_pos_eqb i j :=
    let Hneq := fresh "Hneq" in
    let Hneq' := fresh "Hneq" in
    destruct (Pos.eq_dec i j) as [? | Hneq];
    [ subst; rewrite Pos.eqb_refl
    | pose proof Hneq as Hneq'; apply Pos.eqb_neq in Hneq'; rewrite Hneq'].

  (* TODO: seems doable but challenging to deal with cycles
  Lemma pa_closure_set' t0 p0 i
    : equivalence_closure (pa_rel (set i p0 t0)) p0 i.
  Proof.
    constructor 1; basic_utils_crush.
  Qed.
    
  Lemma pa_closure_set t0 a b p0 i
    : Some p0 = get p0 t0 ->
      equivalence_closure (pa_rel t0) a b ->
      equivalence_closure (pa_rel t0) p0 i ->
      equivalence_closure (pa_rel (set i p0 t0)) a b.
  Proof.
    intros Hg Heq; revert p0 i Hg.
    induction Heq;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct (Pos.eq_dec b i); subst.
      {
        TODO: what if I decide eq closure?
        constructor 1.
        eapply eq_clo_trans.
        {
          constructor 1; eauto.
        }
        
        eapply eq_clo_trans.
        1:eapply eq_clo_sym; eauto.
        constructor 1; eauto.
      }
      
        a
        
  
  lemma find_aux_preserves_rel mr pa i pa' i'
    : Some (pa', i') = find_aux mr pa i ->
      (forall a b, equivalence_closure (pa_rel pa) a b
                   <-> equivalence_closure (pa_rel pa') a b)
      /\ equivalence_closure (pa_rel pa) i' i.
  Proof.
    revert pa i pa' i'.
    induction mr;
      basic_goal_prep.
    { basic_utils_crush. }
    {
      revert H.
      case_match; try congruence.
      destruct_pos_eqb p i.
      { basic_utils_crush. }
      case_match; try congruence.
      break.
      apply IHmr in HeqH0.
      break.
      basic_utils_crush.
      {
        rewrite H in H2.
        assert ( equivalence_closure (pa_rel pa) p0 i).
        { basic_utils_crush. }
        rewrite H in H1.
      2:{
   *)
  
  Lemma sep_has_key_right A P1 P2 (t : tree A) i
    : sep P1 P2 t ->
      (forall t', submap t' t -> P2 t' -> has_key i t') ->
      has_key i t.
  Proof.
    unfold sep;
      intros; break.
    assert (submap x0 t) by eauto with utils.
    specialize (H i);
      specialize (H0 _ H3 H2).
    revert H H0;
      unfold has_key.
    repeat case_match; autorewrite with utils; try tauto.
  Qed.

  
  Lemma sep_has_key_left A P1 P2 (t : tree A) i
    : sep P1 P2 t ->
      (forall t', submap t' t -> P1 t' -> has_key i t') ->
      has_key i t.
  Proof.
    unfold sep;
      intros; break.
    assert (submap x t) by eauto with utils.
    specialize (H i);
      specialize (H0 _ H3 H1).
    revert H H0;
      unfold has_key.
    repeat case_match; autorewrite with utils; try tauto.
  Qed.

  
  
  Lemma pointing_to_has_next_key i t j k
    :  tree_pointing_to i t ->
       Some k = get j t ->
       k = i \/ has_key k t.
  Proof.
    intro H; revert j k;
      induction H;
      intros.
    { basic_utils_crush. }
    {
      destruct (Pos.eq_dec j i1); subst.
      {
        left.
        eapply sep_get_r in H0; cycle 1.
        {
          intros; subst.
          erewrite gss.
          reflexivity.
        }
        congruence.
      }
      {
        apply has_key_sep_distr with (j:=j) in H0.
        2:{ unfold has_key; rewrite <- H1; eauto. }
        destruct H0.
        2:{
          exfalso.
          eapply sep_by_right; eauto.
          intros.
          destruct H2; basic_utils_crush.
        }
        right.
        {
          destruct H0; unfold and1 in*; break.
          unfold has_key in H4;
            revert H4; case_match; try tauto.
          subst.
          pose proof (disjoint_get_some _ _ _ _ _ _ H0 H1).
          rewrite gso,gempty in H3; eauto.
          intuition try congruence.
          assert (k = p) by congruence; subst.
          specialize (H5 _ _ HeqH4).
          intuition subst.
          {
            eapply disjoint_sum_has_key_r; eauto.
            basic_utils_crush.
          }
          {
            eapply disjoint_sum_has_key_l; eauto.
          }            
        }
      }
    }
    {
      unfold sep, and1 in *.
      break.
      assert (has_key j pa) by (unfold has_key; rewrite <- H0; eauto).
      pose proof (disjoint_sum_has_key _ _ _ _ _ H H5).
      destruct H6 as [H6 | H6];
        revert H6; unfold has_key; case_match; try tauto;
        intros _.
      {
        pose proof (disjoint_sum_submap_l _ _ _ _ H _ _ HeqH6).
        assert (k = p) by congruence; subst.
        apply H4 in HeqH6.
        intuition; right.
        revert H7;
          unfold has_key;
          repeat case_match; try tauto.
        pose proof (disjoint_sum_submap_l _ _ _ _ H _ _ HeqH7).
        congruence.
      }
      {
        pose proof (disjoint_sum_submap_r _ _ _ _ H _ _ HeqH6).
        assert (k = p) by congruence; subst.
        apply H3 in HeqH6.
        intuition; right.
        revert H7;
          unfold has_key;
          repeat case_match; try tauto.
        pose proof (disjoint_sum_submap_r _ _ _ _ H _ _ HeqH7).
        congruence.
      }
    }
  Qed.
  
  Lemma tree_at_has_next_key i t j k
    :  parent_tree_at i t ->
       Some k = get j t ->
       has_key k t.
  Proof.
    intros.
    unfold parent_tree_at in *.
    unfold sep in *; break; subst.
    assert (has_key i t).
    {
      subst.
      eapply disjoint_sum_has_key_r; eauto.
      basic_utils_crush.
    }
    destruct (Pos.eq_dec k i); subst; eauto.
    {
      pose proof (H j) as H';
      revert H';
      repeat case_match;
      basic_utils_crush;
        try tauto.
      {
        pose proof (pointing_to_has_next_key _ _ _ _ H1 HeqH3).
        intuition subst; eauto.
        eapply disjoint_sum_has_key_l; eauto.
      }
      {
        destruct (Pos.eq_dec j i); subst;
          basic_utils_crush.
        rewrite gso, gempty in HeqH0; subst; eauto.
        congruence.
      }

    }
  Qed.

  
  
  Lemma has_key_sep_distr' A P1 P2 (t : tree A) j
    : has_key j t ->
      sep P1 P2 t ->
      sep (and1 P1 (has_key j)) (and1 P2 (not1 (has_key j))) t
      \/ sep (and1 P1 (not1 (has_key j))) (and1 P2 (has_key j)) t.
  Proof.
    unfold sep; intros; break.
    pose proof (disjoint_sum_has_key _ _ _ _ _ H0 H).
    destruct H3; [left | right];
      exists x, x0;
      basic_utils_crush.
    all: unfold and1; split; eauto.
    all: intro Hk;
      basic_utils_crush.
  Qed.

  
  Lemma has_key_from_parent_left A pa1 pa2 pa j (k:A)
    : disjoint_sum pa1 pa2 pa ->
      has_key j pa1 ->
      Some k = get j pa ->
      Some k = get j pa1.
  Proof.
    intros.
    revert H0; unfold has_key.
    specialize (H j); revert H;
      rewrite <- H1; repeat case_match; try tauto.
    congruence.
  Qed.
  Hint Resolve has_key_from_parent_left  : utils.


  Lemma find_aux_same_keys mr i i' pa pa'
    : Some (pa', i') = find_aux mr pa i ->
      forall j, has_key j pa -> has_key j pa'.
  Proof.
    revert i i' pa pa'.
    induction mr;
      basic_goal_prep;
      [ basic_utils_crush |].
    revert H0 H.
    unfold has_key.
    repeat case_match; try tauto; try congruence.
    basic_utils_crush.
    eapply IHmr with (j:=j) in HeqH2.
    {
      destruct (Pos.eq_dec j i);
        basic_utils_crush.
      rewrite gso in HeqH4; auto.
      revert HeqH2; unfold has_key; rewrite <- HeqH4.
      auto.
    }
    {
      unfold has_key; rewrite <- HeqH; auto.
    }
  Qed.
  
  Lemma find_aux_spec' mr i j pa1 pa2 pa i' pa'
    : disjoint_sum pa1 pa2 pa ->
      has_key j pa1 ->
      parent_tree_at i pa1 ->
      Some (pa', i') = find_aux mr pa j ->
      i' = i
      /\ (sep (and1 (has_key j) (parent_tree_at i)) (eq pa2)) pa'.
  Proof.
    revert i j pa i' pa'.
    induction mr;
      basic_goal_prep;
      [ basic_utils_crush |].
    {
      revert H2;
        case_match;
        try congruence;
        subst.
      destruct_pos_eqb p j.
      {
        autorewrite with utils.
        intros; break; subst; unfold sep, and1; intuition.
        1:eapply cycles_are_root; basic_utils_crush.
        exists pa1, pa2; intuition.
      }
      {
        case_match; try congruence.
        break.
        intro H'; safe_invert H'.
        assert (has_key p pa1).
        {
          eapply tree_at_has_next_key; basic_utils_crush.
        }
        specialize (IHmr _ p _ _ _ H H2 H1 HeqH0).
        intuition subst.
        unfold sep, and1 in *; break.
        subst.
        exists (set j i x), x0.
        intuition.
        {
          eapply disjoint_sum_set_left; eauto.
          specialize (H j); revert H;
            rewrite <- HeqH2;
            revert H0;
            unfold has_key;
            repeat case_match; try tauto.
        }
        1:unfold has_key;basic_utils_crush.
        eapply path_compression; eauto.
        basic_utils_crush.
        assert (has_key j t0).
        {
          eapply find_aux_same_keys; eauto.
          unfold has_key; rewrite <- HeqH2; auto.
        }
        unfold has_key in H5.
        revert H5.
        case_match; try tauto.
        intros _.
        eapply disjoint_get_some in HeqH5; eauto.
        intuition subst.
        {
          unfold has_key; rewrite <- H5; auto.
        }
        {
          exfalso.
          specialize (H j).
          revert H.
          rewrite <- ! H5.
          revert H0.
          unfold has_key;
            repeat case_match; try tauto.
        }
      }
    }
  Qed.

  
  Lemma find_aux_spec mr i j R pa i' pa'
    : (sep (and1 (has_key j) (parent_tree_at i)) R) pa ->
      Some (pa', i') = find_aux mr pa j ->
      i' = i
      /\ (sep (and1 (has_key j) (parent_tree_at i)) R) pa'.
  Proof.
    intros.
    unfold sep, and1 in H; break.
    pose proof (find_aux_spec' _ _ _ _ _ _ _ _ H H1 H3 H0).
    intuition.
    eapply sep_impl; cycle 2;eauto.
    intros; subst; auto.
  Qed.

  (*TODO: relate to equiv closure*)
  Lemma find_spec canonical u i u' i'
    : forest canonical u.(parent) ->
      Some (u', i') = find u i ->
      In i' canonical
      /\ forest canonical u'.(parent).
  Proof.
    unfold find.
    destruct u; cbn [parent Mbind Mret option_monad].
    case_match; try congruence; break.
    intros Hf H'; safe_invert H'.
    simpl.
    pose proof (find_aux_has_key _ _ _ _ _ HeqH).
    Lemma has_key_in_forest
      : has_key i t ->
        forest l
      
    TODO: awkward w/ canonical order
    revert HeqH.
    case_match; try congruence.
    
  Lemma equivalence_closure_tree
  
  lemma find_aux_preserves_rel mr pa i pa' i'
    : Some (pa', i') = find_aux mr pa i ->
      (forall a b, equivalence_closure (pa_rel pa) a b
                   <-> equivalence_closure (pa_rel pa') a b)
      /\ equivalence_closure (pa_rel pa) i' i.


  Lemma union_spec
    : sep (sep (parent_tree_at i) (parent_tree_at j)) R u.( ->
      Some (u'


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
