
From coqutil Require Import Map.Interface Map.Solver.


From Utils Require Import Base Props Eqb.

Section __.
  Context (A : Type)
    (Eqb_A : Eqb A)
    (Eqb_A_ok : Eqb_ok Eqb_A)
    (mem : map.map A A)
    (mem_ok : map.ok mem).

  (* TODO: move to Eqb *)
  #[local] Instance eqb_boolspec
    : forall x y : A, BoolSpec (x = y) (x <> y) (eqb x y).
  Proof.
    intros.
    pose proof (eqb_spec x y).
    destruct (eqb x y); constructor; eauto.
  Qed.

  Ltac maps_equal :=
    eapply map.map_ext;
    intros;
    map_solver_core_impl mem_ok;
    repeat lazymatch goal with
      | |- context c [eqb ?a ?b] =>
          pose proof (eqb_spec a b);
          destruct (eqb a b)
      end;
    subst;
    try congruence.
  

  Definition disjoint_sum (t1 t2 t12: mem) : Prop :=
    forall i,
      match map.get t1 i, map.get t2 i, map.get t12 i with
      | None, None, None => True
      | Some j, None, Some j' => j = j'
      | None, Some j, Some j' => j = j'
      | _, _, _ => False
      end.
  
  Definition sep (P1 : _ -> Prop) (P2 : _ -> Prop)
    (t12 : mem) : Prop :=
    exists t1 t2, disjoint_sum t1 t2 t12 /\ (P1 t1) /\ (P2 t2).

  Definition lift (P : Prop) (m : mem) := P /\ m = map.empty.
  Definition emp := (lift True).

  Definition ptsto i j (m : mem) : Prop := m = map.singleton i j.

  
  Lemma emp_inv (m : mem)
    : emp m <-> m = map.empty.
  Proof.
    unfold emp, lift; intuition eauto.
  Qed.
  #[local] Hint Rewrite emp_inv : utils.

  
  Lemma ptsto_inv i j (m : mem)
    : ptsto i j m <-> m = map.singleton i j.
  Proof.  intuition eauto. Qed.
  #[local] Hint Rewrite ptsto_inv : utils.

  Hint Rewrite map.get_empty : utils.
  
  Definition has_key i (t : mem) :=
    if map.get t i then True else False.
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
  
  Lemma sep_impl {P1 P1' P2 P2' : mem -> Prop}
    : Uimpl1 P1 P1' ->
      Uimpl1 P2 P2' ->
      Uimpl1 (sep P1 P2) (sep P1' P2').
  Proof.
    intros; unfold sep in *;
      break.
    exists x, x0; basic_utils_crush.
  Qed.

  Lemma disjoint_sym' (pa1 pa2 pa : mem)
    : disjoint_sum pa1 pa2 pa ->
      disjoint_sum pa2 pa1 pa.
  Proof.
    unfold disjoint_sum.
    intros H i; specialize (H i).
    repeat case_match; eauto.
  Qed.

  
  Lemma disjoint_sym (pa1 pa2 pa : mem)
    : disjoint_sum pa1 pa2 pa <->
      disjoint_sum pa2 pa1 pa.
  Proof.
    split; apply disjoint_sym'.
  Qed.

  Lemma sep_sym' P1 P2 : Uimpl1 (sep P1 P2) (sep P2 P1).
  Proof.
    unfold sep;
      intros; break.
    apply disjoint_sym in H.
    eauto.
  Qed.

  (* TODO: lift rewrite w/ Proper instance *)
  Lemma sep_sym P1 P2 : forall m, sep P1 P2 m <-> sep P2 P1 m.
  Proof.
    split; apply sep_sym'.
  Qed.

 Lemma disjoint_sum_right (pa1 pa2 pa : mem) i (j : A)
    : disjoint_sum pa1 pa2 pa ->
      Some j = map.get pa2 i ->
      Some j = map.get pa i.
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

  

  Lemma disjoint_sum_left pa1 pa2 pa i (j : A)
    : disjoint_sum pa1 pa2 pa ->
      Some j = map.get pa1 i ->
      Some j = map.get pa i.
  Proof.
    intros; eapply disjoint_sum_right; cycle 1; eauto using disjoint_sym'.
  Qed.

  
  
  Lemma set_set_comm a c (b d : A) (p : mem)
    : a <> c -> (map.put (map.put p c d) a b) = (map.put (map.put p a b) c d).
  Proof. intros; maps_equal. Qed.
  
  Lemma disjoint_get_some (pa1 pa2 pa : mem) (k :A) j
    : disjoint_sum pa1 pa2 pa ->
      Some k = map.get pa j ->
      Some k = map.get pa1 j \/ Some k = map.get pa2 j.
  Proof.
    intro H; specialize (H j); revert H;
      repeat (case_match; try tauto);
      intros; subst; (right + left); congruence.
  Qed.

  
  Lemma disjoint_sum_update_left (pa1 pa2 pa : mem) j (k : A) i
    : disjoint_sum pa1 pa2 pa ->
      Some k = map.get pa1 j ->
      disjoint_sum (map.put pa1 j i) pa2 (map.put pa j i).
  Proof.
    intros H1 H2 j';
      specialize (H1 j');
      revert H1;
      pose proof (eqb_spec j j');
      destruct (eqb j j');
      subst;
      [ rewrite <- !H2 |].
    {
      repeat (case_match; intros; subst; try tauto; try congruence).
      all: rewrite ?map.get_put_same in HeqH0.
      all: rewrite ?map.get_put_same in HeqH1.
      all: try congruence.
    }
    {
      repeat (case_match; intros; subst; try tauto; try congruence).
      all: rewrite ?map.get_put_diff in HeqH1 by eauto; try congruence.
      all: rewrite ?map.get_put_diff in HeqH3 by eauto; try congruence.
      all: revert H1; case_match;intros; subst; try tauto; try congruence.
    }
  Qed.
  
  
  Lemma disjoint_sum_update_right (pa1 pa2 pa : mem) j (k : A) i
    : disjoint_sum pa1 pa2 pa ->
      Some k = map.get pa2 j ->
      disjoint_sum pa1 (map.put pa2 j i) (map.put pa j i).
  Proof.
    eauto using disjoint_sym', disjoint_sum_update_left.
  Qed.
  
  Lemma disjoint_empty_left (a : mem)
    : disjoint_sum map.empty a a.
  Proof.
    intro i.
    rewrite map.get_empty.
    case_match; subst; auto.
  Qed.
  #[local] Hint Resolve disjoint_empty_left : utils.
  
  Lemma disjoint_empty_right (a : mem)
    : disjoint_sum a map.empty a.
  Proof.
    eauto using disjoint_sym', disjoint_empty_left.
  Qed.
  #[local] Hint Resolve disjoint_empty_right : utils.

  
  Lemma disjoint_empty_left' (a b : mem)
    : disjoint_sum map.empty a b <-> a = b.
  Proof.
    split; subst; basic_utils_crush.
    maps_equal.
    specialize (H k); revert H.
    rewrite map.get_empty.
    repeat case_match; intros; subst; auto; try tauto.
  Qed.
  #[local] Hint Rewrite disjoint_empty_left' : utils.
  
  Lemma disjoint_empty_right' (a b : mem)
    : disjoint_sum a map.empty b <-> a = b.
  Proof.
    rewrite disjoint_sym, disjoint_empty_left'; intuition idtac.
  Qed.
  #[local] Hint Rewrite disjoint_empty_right' : utils.

  
  Lemma sep_get_r P1 P2 t (j:A) i
    : sep P1 P2 t ->
      (forall t', P2 t' -> Some j = map.get t' i) ->
      Some j = map.get t i.
  Proof.
    unfold sep;
      intros; break.
    specialize (H i);
      specialize (H0 _ H2);
      rewrite <- H0 in H;
      revert H.
    repeat (case_match; autorewrite with utils; try tauto).
    congruence.
  Qed.

  
  Lemma sep_get_l P1 P2 t (j:A) i
    : sep P1 P2 t ->
      (forall t', P1 t' -> Some j = map.get t' i) ->
      Some j = map.get t i.
  Proof.
    unfold sep;
      intros; break.
    specialize (H i);
      specialize (H0 _ H1);
      rewrite <- H0 in H;
      revert H.
    repeat (case_match; autorewrite with utils; try tauto).
    congruence.
  Qed.


  (* TODO
  
  Lemma disjoint_remove A i1 i2 (pa : mem)
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
                       
  Lemma disjoint_unique_l A (t1 t2 t t1' : mem)
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
                   
  Lemma disjoint_unique_r A (t1 t2 t t2' : mem)
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
                 
  Lemma disjoint_unique_out A (t1 t2 t t' : mem)
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

  
  Lemma disjoint_sum_comm A (pa1 pa2 pa : mem)
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
  

  Lemma sep_empty_left A (P1 P2 : _ -> Prop) (t : mem)
    : P1 PTree.empty -> P2 t -> sep P1 P2 t.
  Proof.
    intros; exists PTree.empty, t;
      basic_utils_crush.
  Qed.
  Hint Resolve sep_empty_left : utils.
  
  Lemma sep_empty_right A (P1 P2 : _ -> Prop) (t : mem)
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

  Lemma disjoint_remove' A i1 i2 (pa1 pa : mem)
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

  


  Lemma disjoint_sum_has_key_l A (pa1 pa2 pa : mem) k
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
  
  Lemma disjoint_sum_has_key_r A (pa1 pa2 pa : mem) k
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
  
  Lemma remove_remove_diff A i j (pa : mem)
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

  
  Lemma disjoint_sum_has_key A (pa1 pa2 pa : mem) k
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

  


  Lemma sep_implies_not_has_key A P1 P2 (t : mem) i
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
  
  Lemma has_key_sep_distr A P1 P2 (t : mem) j
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

  
  
  Lemma disjoint_remove_left A (pa1 pa2 pa : mem) j
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

  
*)

End __.


Arguments sep {A}%type_scope {mem} (P1 P2)%function_scope t12.
Arguments ptsto {A}%type_scope {mem} i j m.
Arguments emp {A}%type_scope {mem} m.
Arguments lift {A}%type_scope {mem} P%type_scope m.


#[export] Hint Rewrite emp_inv : utils.
#[export] Hint Rewrite ptsto_inv : utils.

#[export] Hint Resolve disjoint_empty_left : utils.
#[export] Hint Resolve disjoint_empty_right : utils.

#[export] Hint Rewrite disjoint_empty_left' : utils.
#[export] Hint Rewrite disjoint_empty_right' : utils.
