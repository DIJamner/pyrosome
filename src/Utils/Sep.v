From coqutil Require Import Map.Interface.
Require Import Lists.List.
Import ListNotations.

Require Import Setoid.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Sorting.Permutation.

From Utils Require Import Base Booleans Eqb Options Lists ExtraMaps
  Permutation.


(*TODO: move A-parameterized things to separate file?*)
Section Lifted.
  Context (A : Type).
  
  Definition and1 (P1 P2 : A -> Prop) a : Prop :=
    P1 a /\ P2 a.
  Hint Unfold and1 : utils.
  
  Definition not1 (P : A -> Prop) a : Prop :=
    ~ P a.
  Hint Unfold not1 : utils.

  Definition impl1 (P1 P2 : A -> Prop) a :=
    P1 a -> P2 a.
  Hint Unfold impl1 : utils.
  
  Definition Uimpl1 (P1 P2 : A -> Prop) :=
    forall a, P1 a -> P2 a.
  Definition Uiff1 (P1 P2 : A -> Prop) :=
               forall a, P1 a <-> P2 a.
  
  Add Parametric Relation : (A -> Prop) Uiff1
      reflexivity proved by ltac:(cbn;firstorder)
      symmetry proved by ltac:(cbn;firstorder)
      transitivity proved by ltac:(cbn;firstorder)
      as Uiff1_rel.
  
  Add Parametric Relation : (A -> Prop) Uimpl1
      reflexivity proved by ltac:(cbn;firstorder)
      transitivity proved by ltac:(cbn;firstorder)
      as Uimpl1_rel.

  Lemma and1_comm (P Q : A -> Prop)
    : Uiff1 (and1 P Q) (and1 Q P).
  Proof.
    cbv; firstorder.
  Qed.

  #[export] Instance and1_iff1_mor
    : Proper (Uiff1 ==> Uiff1 ==> Uiff1) and1.
  Proof.
    cbv [Proper respectful Uiff1 and1].
    firstorder.
  Qed.
  #[export] Instance and1_impl1_mor
    : Proper (Uimpl1 ==> Uimpl1 ==> Uimpl1) and1.
  Proof.
    cbv [Proper respectful Uimpl1 and1].
    firstorder.
  Qed.

    
  Lemma Uimpl1_and1_l (P Q : A -> _)
    : Uimpl1 (and1 P Q) P.
  Proof.
    cbv; firstorder.
  Qed.
  #[local] Hint Resolve Uimpl1_and1_l : utils.
  
  Lemma Uimpl1_and1_r (P Q : A -> _)
    : Uimpl1 (and1 P Q) Q.
  Proof.
    cbv; firstorder.
  Qed.
  #[local] Hint Resolve Uimpl1_and1_r : utils.

  

End Lifted.

#[export] Existing Instance Uimpl1_rel_relation.
#[export] Existing Instance Uimpl1_rel_Reflexive.
#[export] Existing Instance Uimpl1_rel_Transitive.
#[export] Existing Instance Uimpl1_rel.

#[export] Existing Instance Uiff1_rel_relation.
#[export] Existing Instance Uiff1_rel_Reflexive.
#[export] Existing Instance Uiff1_rel_Symmetric.
#[export] Existing Instance Uiff1_rel_Transitive.
#[export] Existing Instance Uiff1_rel.

Arguments Uiff1 {A}%type_scope (P1 P2)%function_scope.
Arguments Uimpl1 {A}%type_scope (P1 P2)%function_scope.
Arguments and1 {A}%type_scope (P1 P2)%function_scope.
Arguments not1 {A}%type_scope (P)%function_scope.
Arguments impl1 {A}%type_scope (P1 P2)%function_scope.


#[export] Hint Resolve Uimpl1_and1_l : utils.
#[export] Hint Resolve Uimpl1_and1_r : utils.

Section __.
  Context {A B : Type}
    {mem : map.map A B}.
  
  Definition has_key i (t : mem) :=
    if map.get t i then True else False.
End __.

Hint Unfold has_key : utils.

  
Section __.
  Context (A : Type)
    (Eqb_A : Eqb A)
    (Eqb_A_ok : Eqb_ok Eqb_A)
    (mem : map.map A A)
    (mem_ok : map.ok mem).
  
  Definition sep (P1 : _ -> Prop) (P2 : _ -> Prop)
    (t12 : mem) : Prop :=
    exists t1 t2, map.split t12 t1 t2 /\ (P1 t1) /\ (P2 t2).

  Definition lift (P : Prop) (m : mem) := P /\ m = map.empty.
  Definition emp := (lift True).

  Definition ptsto i j (m : mem) : Prop := m = map.singleton i j.

  
  Lemma emp_inv (m : mem)
    : emp m <-> m = map.empty.
  Proof.
    unfold emp, lift; intuition eauto.
  Qed.
  #[local] Hint Rewrite emp_inv : utils.


  (* TODO: change ptsto to a notation?*)
  Lemma ptsto_inv i j
    : Uiff1 (ptsto i j) (@eq mem (map.singleton i j)).
  Proof. unfold Uiff1, ptsto; intuition subst; auto. Qed.
  #[local] Hint Rewrite ptsto_inv : utils.

  (* TODO: the prior lemma would cover this if
     setoid_rewrite worked under application.
   *)
  Lemma ptsto_inv_applied i j (m : mem)
    : ptsto i j m <-> m = map.singleton i j.
  Proof.  intuition eauto. Qed.
  #[local] Hint Rewrite ptsto_inv_applied : utils.

  Hint Rewrite map.get_empty : utils.
  
  
  #[export] Instance impl1_iff1_mor {B}
    : Proper (@Uiff1 B ==> Uiff1 ==> iff) Uimpl1.
  Proof.
    cbv [Proper Basics.impl Uiff1 Uimpl1 respectful].
    intros; intuition (subst; firstorder eauto).
  Qed.
  
  #[export] Instance app_impl1_mor {B}
    : Proper (@Uimpl1 B ==> eq ==> Basics.impl) (fun a b => a b).
  Proof.
    cbv [Proper Basics.impl Uimpl1 respectful].
    intros; intuition (subst; eauto).
  Qed.
  
  (*TODO: Doesn't seem to work for `rewrite` *)
  #[export] Instance app_iff1_mor {B}
    : Proper (@Uiff1 B ==> eq ==> iff) (fun a b => a b).
  Proof.
    cbv [Proper iff Uiff1 respectful].
    intros; intuition (subst; firstorder eauto).
  Qed.

  (*TODO: subrelation *)
  Definition Uiff_to_Uimpl {A} {P1 P2 : A -> Prop}
    : Uiff1 P1 P2 -> Uimpl1 P1 P2 :=
    fun eq a => proj1 (eq a).
    
  
  Lemma sep_impl {P1 P1' P2 P2' : mem -> Prop}
    : Uimpl1 P1 P1' ->
      Uimpl1 P2 P2' ->
      Uimpl1 (sep P1 P2) (sep P1' P2').
  Proof.
    cbv [Uimpl1];
    intros; unfold sep in *;
      break.
    exists x, x0; basic_utils_crush.
  Qed.

  #[export] Instance sep_impl1_mor : Proper (Uimpl1 ==> Uimpl1 ==> Uimpl1) sep.
  Proof.
    cbv [Proper Uiff1 respectful].
    intros; eapply sep_impl; eauto.
  Qed.
  
  #[export] Instance sep_iff1_mor : Proper (Uiff1 ==> Uiff1 ==> Uiff1) sep.
  Proof.
    cbv [Proper Uiff1 respectful].
    intros; firstorder eauto using sep_impl.
  Qed.
  
  Lemma sep_comm_impl P1 P2 : Uimpl1 (sep P1 P2) (sep P2 P1).
  Proof.
    cbv [Uimpl1 sep];
      intros; break.
    apply Properties.map.split_comm in H.
    eauto.
  Qed.

  Lemma sep_comm P1 P2 : Uiff1 (sep P1 P2) (sep P2 P1).
  Proof.
    split; apply sep_comm_impl.
  Qed.
  
  Lemma set_set_comm a c (b d : A) (p : mem)
    : a <> c -> (map.put (map.put p c d) a b) = (map.put (map.put p a b) c d).
  Proof. intros; maps_equal. Qed.

  Fixpoint seps l : mem -> Prop :=
    match l with
    | [] => emp
    | P::l' => sep P (seps l')
    end.

  Lemma impl1_refl B (P : B -> Prop) : Uimpl1 P P.
  Proof.
    reflexivity.
  Qed.
  Hint Resolve impl1_refl : utils.


  Lemma iff1_refl B (P : B -> Prop) : Uiff1 P P.
  Proof.
    reflexivity.
  Qed.
  Hint Resolve iff1_refl : utils.

  
  Lemma sep_consequence (P1 P2 Q1 Q2 : mem -> Prop)
    : (forall m, P1 m -> P2 m) ->
      (forall m, Q1 m -> Q2 m) ->
      forall m, sep P1 Q1 m -> sep P2 Q2 m.
  Proof.
    unfold sep; firstorder eauto.
  Qed.

  Definition seps_Uimpl1 l1 l2 :=
    Uimpl1 (seps l1) (seps l2).
  
  Definition seps_Uiff1 l1 l2 :=
    Uiff1 (seps l1) (seps l2).
  
  #[export] Instance seps_impl1_mor
    : Proper (seps_Uimpl1 ==> Uimpl1) seps.
  Proof.
    cbv; auto.
  Qed.
  
  #[export] Instance seps_iff1_mor
    : Proper (seps_Uiff1 ==> Uiff1) seps.
  Proof.
    cbv; auto.
  Qed.

  #[export] Instance cons_impl1_mor
    : Proper (Uimpl1 ==> seps_Uimpl1 ==> seps_Uimpl1) (@cons (mem -> Prop)).
  Proof.
    cbv [Proper respectful seps_Uimpl1 Uimpl1].
    basic_goal_prep;
      basic_utils_crush.
    simple eapply sep_consequence; eauto.
  Qed.
  
  #[export] Instance cons_iff1_mor
    : Proper (Uiff1 ==> seps_Uiff1 ==> seps_Uiff1) (@cons (mem -> Prop)).
  Proof.
    cbv [Proper respectful seps_Uiff1 Uiff1].
    basic_goal_prep;
      basic_utils_crush.
    all: revert dependent a.
    all:simple eapply sep_consequence; firstorder eauto.
  Qed.

  
  Add Parametric Relation : (list (mem -> Prop)) seps_Uiff1
      reflexivity proved by ltac:(cbn;firstorder)
      symmetry proved by ltac:(cbn;firstorder)
      transitivity proved by ltac:(cbn;firstorder)
      as seps_Uiff1_rel.
  
  Add Parametric Relation : (list (mem -> Prop)) seps_Uimpl1
      reflexivity proved by ltac:(cbn;firstorder)
      transitivity proved by ltac:(cbn;firstorder)
      as seps_Uimpl1_rel.
  
  Lemma emp_iff (m  : mem) : emp m <-> m = map.empty.
  Proof.
    unfold emp, lift;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  #[local] Hint Rewrite Properties.map.split_empty_l
    Properties.map.split_empty_r : utils.
  
  Lemma sep_emp_r P : Uiff1 (sep P emp) P.
  Proof.
    unfold Uiff1, sep;
      split;
      basic_goal_prep;
      basic_utils_crush.
    exists a, map.empty.
    basic_utils_crush.
  Qed.
  #[local] Hint Rewrite sep_emp_r : utils.

  
  Lemma sep_emp_l P : Uiff1 (sep emp P) P.
  Proof.
    rewrite sep_comm; eauto.
    apply sep_emp_r.
  Qed.
  #[local] Hint Rewrite sep_emp_l : utils.

  
  Lemma seps_tl : Uiff1 (seps []) emp.
  Proof.
    reflexivity.
  Qed.
  #[local] Hint Rewrite seps_tl : utils.

  Lemma seps_emp_hd l : seps_Uiff1 (emp::l) l.
  Proof.
    unfold seps_Uiff1; cbn.
    basic_utils_crush.
  Qed.
  #[local] Hint Rewrite seps_emp_hd : utils.

  
  Lemma sep_seps_l l P
    : Uiff1 (sep (seps l) P) (seps (P::l)).
  Proof.
    basic_goal_prep.
    rewrite sep_comm; basic_utils_crush.
  Qed.
  #[local] Hint Rewrite sep_seps_l : utils.
  
  Lemma sep_seps_r l P
    : Uiff1 (sep P (seps l)) (seps (P::l)).
  Proof.
    basic_goal_prep; basic_utils_crush.
  Qed.
  #[local] Hint Rewrite sep_seps_r : utils.
  
  
  #[local] Hint Rewrite @map.get_empty : utils.
  #[local] Hint Rewrite map.get_put_same : utils.
  #[local] Hint Rewrite map.get_put_diff using congruence : utils.
  
  Lemma map_split_singleton_r (m : mem) x i j
    : map.split m x (map.singleton i j)
      <-> map.get x i = None /\ m = map.put x i j.
  Proof.
    unfold map.singleton.
    split;
      basic_goal_prep.
    {
      pose proof H.
      eapply Properties.map.get_split with (k:=i) in H.
      assert (map.get x i = None) by basic_utils_crush.
      intuition idtac;
        maps_equal;
        basic_utils_crush.
      eapply Properties.map.get_split with (k:=k) in H0.
      basic_utils_crush.
      congruence.
    }
    {
      basic_utils_crush.
      apply Properties.map.split_comm.
      apply Properties.map.split_undef_put.
      auto.
    }
  Qed.

         
  Lemma map_split_singleton_l (m : mem) x i j
    : map.split m (map.singleton i j) x
      <-> map.get x i = None /\ m = map.put x i j.
  Proof.
    rewrite Properties.map.split_comm.
    apply map_split_singleton_r.
  Qed.
  
  Lemma not1_has_key j (m : mem)
    :  not1 (has_key j) m <-> map.get m j = None.
  Proof.
    unfold not1, has_key;
      case_match;
      basic_utils_crush.
  Qed.

  

  Lemma seps_impl1_refl l : seps_Uimpl1 l l.
  Proof.
    reflexivity.
  Qed.
  #[local] Hint Resolve seps_impl1_refl : utils.


  Lemma seps_iff1_refl l: seps_Uiff1 l l.
  Proof.
    reflexivity.
  Qed.
  Hint Resolve seps_iff1_refl : utils.

   Lemma sep_assoc P Q H
    : Uiff1 (sep (sep P Q) H) (sep P (sep Q H)).
  Proof.
    unfold Uiff1,sep;
      split;
      basic_goal_prep.
    all: unfold map.split in *;
        basic_goal_prep; subst.
    1:rewrite Properties.map.disjoint_putmany_l in H6.
    2:rewrite Properties.map.disjoint_putmany_r in H6.
    1: exists x1, (map.putmany x2 x0).
    2: exists (map.putmany x x1), x2.
    all:basic_goal_prep;
        basic_utils_crush.
    all: rewrite ?Properties.map.putmany_assoc; try reflexivity.
    {
      rewrite Properties.map.disjoint_putmany_r.
      basic_utils_crush.
    }
    2:{
      rewrite Properties.map.disjoint_putmany_l.
      basic_utils_crush.
    }
    all: eexists; eexists;
      basic_utils_crush.
  Qed.

    Lemma sep_concat l1 l2
    : Uiff1 (seps (l1++l2)) (sep (seps l1) (seps l2)).
  Proof.
    revert l2.
    induction l1;
      basic_goal_prep;
      basic_utils_crush.
    repeat change (seps (?a :: ?l)) with (sep a (seps l)).
    rewrite sep_assoc.
    rewrite IHl1.
    reflexivity.
  Qed.
      
    
  Lemma sep_sequent_concat
    len1 len2 l1 l2
    : seps_Uimpl1 (firstn len1 l1) (firstn len2 l2) ->
      seps_Uimpl1 (skipn len1 l1) (skipn len2 l2) ->
      seps_Uimpl1 l1 l2.
  Proof.
    intros Hf Hs.
    rewrite <- firstn_skipn with (l:=l1) (n:=len1).
    rewrite <- firstn_skipn with (l:=l2) (n:=len2).
    (*TODO: fix this rewrite *)
    unfold seps_Uimpl1.
    rewrite !sep_concat.
    rewrite Hf, Hs; reflexivity.
  Qed.
  

  Lemma seps_swap x y l
    : seps_Uiff1 (y :: x :: l) (x :: y :: l).
  Proof.
    unfold seps_Uiff1.
    unfold seps; fold seps.
    rewrite sep_comm.
    rewrite !sep_assoc.
    rewrite sep_comm with (P1:= (seps l)).
    reflexivity.
  Qed.
  
  Lemma seps_permutation l1 l2
    : Permutation l1 l2 ->
      seps_Uiff1 l1 l2.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      rewrite IHPermutation;
        reflexivity.
    }
    {
      apply seps_swap.
    }
    {
      rewrite IHPermutation1; eauto.
    }
  Qed.

  (* TODO: move to permutation *)
  Arguments permute {A}%type_scope (l perm)%list_scope.

  
  #[export] Instance seps_Uimpl1_iff1_mor
    : Proper (seps_Uiff1 ==> seps_Uiff1 ==> iff) seps_Uimpl1.
  Proof.
    cbv [Proper respectful seps_Uiff1 seps_Uimpl1].
    firstorder.
  Qed.

  
  #[export] Instance seps_Uimpl1_app_mor
    : Proper (seps_Uimpl1 ==> seps_Uimpl1 ==> seps_Uimpl1) (@app _).
  Proof.    
    cbv [Proper respectful]; intros.
    unfold seps_Uimpl1.
    rewrite !sep_concat.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma sep_sequent_focus perm1 perm2 l1 l2
    : Is_true (no_dupb perm1) ->
      Is_true (no_dupb perm2) ->
      (seps_Uimpl1 (select_all l1 perm1) (select_all l2 perm2)) ->
      (seps_Uimpl1 (remove_all l1 perm1) (remove_all l2 perm2)) ->
      (forall m, seps l1 m -> seps l2 m).
  Proof.
    intros Hnd1 Hnd2 Hs Hr.
    change (seps_Uimpl1 l1 l2).
    rewrite seps_permutation with (l1:=l1) (l2:= permute l1 perm1),
        seps_permutation with (l1:=l2) (l2:= permute l2 perm2).
    { 
      unfold permute.
      apply seps_Uimpl1_app_mor; eauto.
    }
    all:symmetry;
      apply permute_is_Permutation.
    all: apply no_dups_extend_perm_permutation.
    all: eapply use_no_dupb; eauto; typeclasses eauto.
  Qed.


  (*TODO: move to ExtraMaps.v or some place similar*)
  
  Lemma putmany_singleton m (j k : A)
    : (map.putmany m (map.singleton j k)) = map.put m j k.
  Proof.
    unfold map.singleton.
    rewrite <- Properties.map.put_putmany_commute,
      Properties.map.putmany_empty_r.
    auto.
  Qed.
  
  (* TODO: give seps a separate `lift` argument? *)
  Lemma sep_lift_r P Q (m : mem)
    : (sep P (lift Q)) m <-> P m /\ Q.
  Proof.
    unfold lift, sep;
      split;
      basic_goal_prep;
      subst;
      rewrite ?Properties.map.split_empty_r in H;
      subst.
    { intuition eauto. }
    {
      exists m, map.empty.
      intuition eauto.
      rewrite ?Properties.map.split_empty_r.
      eauto.
    }
  Qed.
  #[local] Hint Rewrite sep_lift_r : utils.
  
  (* TODO: give seps a separate `lift` argument? *)
  Lemma sep_lift_l P Q (m : mem)
    : (sep (lift Q) P) m <-> P m /\ Q.
  Proof.
    unfold lift, sep;
      split;
      basic_goal_prep;
      subst;
      rewrite ?Properties.map.split_empty_l in H;
      subst.
    { intuition eauto. }
    {
      exists map.empty, m.
      intuition eauto.
      rewrite Properties.map.split_empty_l.
      eauto.
    }
  Qed.
  #[local] Hint Rewrite sep_lift_l : utils.


  
  Lemma and1_eq_l m P
    : Uiff1 (and1 (@eq mem m) P)
        (sep (@eq mem m) (lift (P m))).
  Proof.
    unfold Uiff1, and1; intuition subst; auto;
      basic_utils_crush.    
  Qed.
  #[local] Hint Rewrite and1_eq_l : utils.

  Lemma and1_eq_r m P
    : Uiff1 (and1 P (@eq mem m))
        (sep (@eq mem m) (lift (P m))).
  Proof.
    rewrite and1_comm.
    apply and1_eq_l.
  Qed.
  #[local] Hint Rewrite and1_eq_r : utils.

    
  
  Lemma seps_Uiff1_cons_sep (P : mem ->Prop) Q l
    : seps_Uiff1 ((sep P Q)::l) (P::Q::l).
  Proof.
    unfold seps_Uiff1;
      basic_goal_prep.
    rewrite sep_assoc; eauto.
    reflexivity.
  Qed.
  #[local] Hint Rewrite seps_Uiff1_cons_sep : utils.

  
  Lemma seps_Uiff1_cons_seps (l' l : list (mem ->Prop))
    : seps_Uiff1 ((seps l')::l) (l'++l).
  Proof.
    unfold seps_Uiff1;
      basic_goal_prep.
    induction l';
      basic_goal_prep;
      basic_utils_crush.
    rewrite <- !sep_seps_r; eauto.
    rewrite sep_assoc; eauto.
    rewrite IHl'.
    reflexivity.
  Qed.
  #[local] Hint Rewrite seps_Uiff1_cons_seps : utils.

  

  (*TODO: replace this with something automated.
    Include a separate lifted section in seps_Uimpl1?
   *)
  Lemma seps_Uimpl1_cons_lift_l (P : Prop) (l1 l2 : list (mem->Prop))
    : (P -> seps_Uimpl1 (l1) l2) ->
      seps_Uimpl1 (lift P :: l1) l2.
  Proof.
    unfold seps_Uimpl1.
    intro H.
    change (seps (?x::?l)) with (sep x (seps l)).
    intros H' m.
    basic_utils_crush.
  Qed.


  (* TODO: move to a dedicated maps file *)
  Lemma map_get_singleton (i j j0 k : A)
    : map.get (map.singleton i j) j0 = Some k
      <-> (i = j0 /\ j = k).
  Proof.
    unfold map.singleton.
    split; basic_goal_prep.
    2:basic_utils_crush.
    pose proof (eqb_spec i j0);
      destruct (eqb i j0);
      basic_utils_crush.
  Qed.
  #[local] Hint Rewrite map_get_singleton : utils.

  
  Lemma and1_emp_l P
    : Uiff1 (and1 emp P)
        (lift (P map.empty)).
  Proof.
    unfold Uiff1, and1, lift; intuition subst; auto;
      basic_utils_crush.    
  Qed.
  #[local] Hint Rewrite and1_emp_l : utils.

    
  Lemma and1_emp_r P
    : Uiff1 (and1 P emp)
        (lift (P map.empty)).
  Proof.
    unfold Uiff1, and1, lift; intuition subst; auto;
      basic_utils_crush.    
  Qed.
  #[local] Hint Rewrite and1_emp_r : utils.

  
  #[export] Instance lift_Uiff1_mor
    : Proper (iff ==> Uiff1) lift.
  Proof.
    cbv [Proper respectful Uimpl1 and1].
    firstorder.
  Qed.

  
  Lemma sep_sequent_focus' perm1 perm2 l1 l2
    : Is_true (no_dupb perm1) ->
      Is_true (no_dupb perm2) ->
      (seps_Uimpl1 (Permutation.select_all l1 perm1) (Permutation.select_all l2 perm2)) ->
      (seps_Uimpl1 (Permutation.remove_all l1 perm1) (Permutation.remove_all l2 perm2)) ->
      (seps_Uimpl1 l1 l2).
  Proof.
    intros.
    pose proof (sep_sequent_focus _ _ _ _ H H0 H1 H2) as H'.
    intro.
    apply H'.
  Qed.

End __.

Arguments sep {A}%type_scope {mem} (P1 P2)%function_scope t12.
Arguments ptsto {A}%type_scope {mem} i j m.
Arguments emp {A}%type_scope {mem} m.
Arguments lift {A}%type_scope {mem} P%type_scope m.

Arguments seps {A}%type_scope {mem} l%list_scope _ : simpl never.

Arguments seps_Uiff1 {A}%type_scope {mem} (l1 l2)%list_scope.
Arguments seps_Uimpl1 {A}%type_scope {mem} (l1 l2)%list_scope.


#[export] Existing Instance seps_Uimpl1_rel_relation.
#[export] Existing Instance seps_Uimpl1_rel_Reflexive.
#[export] Existing Instance seps_Uimpl1_rel_Transitive.
#[export] Existing Instance seps_Uimpl1_rel.

#[export] Existing Instance seps_Uiff1_rel_relation.
#[export] Existing Instance seps_Uiff1_rel_Reflexive.
#[export] Existing Instance seps_Uiff1_rel_Symmetric.
#[export] Existing Instance seps_Uiff1_rel_Transitive.
#[export] Existing Instance seps_Uiff1_rel.

#[export] Hint Resolve iff1_refl : utils.
#[export] Hint Resolve impl1_refl : utils.

#[export] Hint Resolve seps_impl1_refl : utils.
#[export] Hint Resolve seps_iff1_refl : utils.

#[export] Hint Rewrite emp_inv : utils.
#[export] Hint Rewrite ptsto_inv ptsto_inv_applied : utils.


Arguments sep_emp_l A%type_scope {Eqb_A Eqb_A_ok mem mem_ok} P%function_scope a.
Arguments sep_emp_r A%type_scope {Eqb_A Eqb_A_ok mem mem_ok} P%function_scope a.
#[export] Hint Rewrite sep_emp_r using typeclasses eauto : utils.
#[export] Hint Rewrite sep_emp_l using typeclasses eauto : utils.

#[export] Hint Rewrite seps_tl using typeclasses eauto : utils.
#[export] Hint Rewrite seps_emp_hd using typeclasses eauto : utils.


#[export] Hint Rewrite sep_seps_l using typeclasses eauto  : utils.
#[export] Hint Rewrite sep_seps_r using typeclasses eauto : utils.


#[export] Hint Rewrite @Properties.map.split_empty : utils.
#[export] Hint Rewrite @Properties.map.split_empty_l : utils.
#[export] Hint Rewrite @Properties.map.split_empty_r : utils.

(*
#[export] Hint Resolve resolve_split_empty_left : utils.
#[export] Hint Resolve resolve_split_empty_right : utils.
*)

#[export] Hint Rewrite emp_iff : utils.
#[export] Hint Rewrite @map.get_empty : utils.
#[export] Hint Rewrite @map.get_put_same : utils.
#[export] Hint Rewrite @map.get_put_diff using congruence : utils.


#[export] Hint Rewrite map_split_singleton_r using typeclasses eauto : utils.
#[export] Hint Rewrite map_split_singleton_l using typeclasses eauto : utils.
#[export] Hint Rewrite not1_has_key : utils.


#[export] Hint Rewrite putmany_singleton using typeclasses eauto : utils.


#[export] Hint Rewrite and1_eq_l and1_eq_r using typeclasses eauto : utils.

#[export] Hint Rewrite sep_lift_r using typeclasses eauto : utils.

#[export] Hint Rewrite seps_Uiff1_cons_sep seps_Uiff1_cons_seps
  using typeclasses eauto : utils.


#[export] Hint Rewrite map_get_singleton using typeclasses eauto : utils.

#[export] Hint Rewrite and1_emp_l and1_emp_r using typeclasses eauto : utils.


Arguments seps_Uimpl1_cons_lift_l {A}%type_scope {Eqb_A Eqb_A_ok} 
  {mem mem_ok} P%type_scope (l1 l2)%list_scope _%function_scope 
  a _.

(* TODO: obselete this collection of definitions and tactics
   with a proper way to rewrite under function application.
 *)
Definition sep_app {A} (P : A -> Prop) a := P a.


#[export] Instance sep_app_mor {B}
  : Proper (Uiff1 (A:=B) ==> eq ==> iff) (sep_app).
Proof.    
  cbv [Proper respectful Uiff1 sep_app]; intros; subst; eauto.
Qed.

Ltac sep_isolate :=
  repeat lazymatch goal with
    | H : sep ?A ?B ?a |- _ => change (sep_app (sep A B) a) in H
    | H : seps ?l ?a |- _ => change (sep_app (seps l) a) in H
    | |- sep ?A ?B ?a => change (sep_app (sep A B) a)
    | |- seps ?l ?a => change (sep_app (seps l) a)
    end.

Ltac seprewrite :=
  sep_isolate;
  autorewrite with bool rw_prop inversion utils in *;
  unfold sep_app in *.



Arguments sep_sequent_focus' {A}%type_scope {Eqb_A} {Eqb_A_ok} {mem mem_ok}
  (perm1 perm2 l1 l2)%list_scope.

Ltac sep_focus' p1 p2 :=
  simple apply sep_sequent_focus' with (perm1 := p1) (perm2 := p2);
  [ vm_compute; exact I | vm_compute; exact I | cbn.. ].

Ltac sep_apply_focused p1 p2 l :=
  sep_focus' p1 p2;
  [  cbv [seps seps_Uimpl1];
     intros m H; seprewrite;
     revert m H; solve[simple apply l]
  |].
