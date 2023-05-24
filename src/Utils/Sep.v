From coqutil Require Import Map.Interface.
Require Import Lists.List.
Import ListNotations.

Require Import Setoid.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Sorting.Permutation.

From Utils Require Import Base Booleans Props Eqb Options Lists ExtraMaps
  Permutation.

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

  
  Lemma ptsto_inv i j (m : mem)
    : ptsto i j m <-> m = map.singleton i j.
  Proof.  intuition eauto. Qed.
  #[local] Hint Rewrite ptsto_inv : utils.

  Hint Rewrite map.get_empty : utils.
  
  Definition has_key i (t : mem) :=
    if map.get t i then True else False.
  Hint Unfold has_key : utils.

  (*TODO: move A-parameterized things to separate file*)
  Definition and1 {A} (P1 P2 : A -> Prop) a : Prop :=
    P1 a /\ P2 a.
  Hint Unfold and1 : utils.
  
  Definition not1 {A} (P : A -> Prop) a : Prop :=
    ~ P a.
  Hint Unfold not1 : utils.

  Definition impl1 {A} (P1 P2 : A -> Prop) a :=
    P1 a -> P2 a.
  Hint Unfold impl1 : utils.
  
  Definition Uimpl1 {A} (P1 P2 : A -> Prop) :=
    forall a, P1 a -> P2 a.
  Definition Uiff1 {A} (P1 P2 : A -> Prop) :=
               forall a, P1 a <-> P2 a.
  
  Add Parametric Relation A : (A -> Prop) Uiff1
      reflexivity proved by ltac:(cbn;firstorder)
      symmetry proved by ltac:(cbn;firstorder)
      transitivity proved by ltac:(cbn;firstorder)
      as Uiff1_rel.
  
  Add Parametric Relation A : (A -> Prop) Uimpl1
      reflexivity proved by ltac:(cbn;firstorder)
      transitivity proved by ltac:(cbn;firstorder)
      as Uimpl1_rel.

  
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
      (forall m, seps (select_all l1 perm1) m ->
                 seps (select_all l2 perm2) m) ->
      (forall m, seps (remove_all l1 perm1) m ->
                 seps (remove_all l2 perm2) m) ->
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
  


End __.

Arguments sep {A}%type_scope {mem} (P1 P2)%function_scope t12.
Arguments ptsto {A}%type_scope {mem} i j m.
Arguments emp {A}%type_scope {mem} m.
Arguments lift {A}%type_scope {mem} P%type_scope m.
Arguments has_key {A}%type_scope {mem} i t.

Arguments seps {A}%type_scope {mem} l%list_scope _ : simpl never.

Arguments seps_Uiff1 {A}%type_scope {mem} (l1 l2)%list_scope.
Arguments seps_Uimpl1 {A}%type_scope {mem} (l1 l2)%list_scope.

#[export] Existing Instance Uimpl1_rel_relation.
#[export] Existing Instance Uimpl1_rel_Reflexive.
#[export] Existing Instance Uimpl1_rel_Transitive.
#[export] Existing Instance Uimpl1_rel.

#[export] Existing Instance Uiff1_rel_relation.
#[export] Existing Instance Uiff1_rel_Reflexive.
#[export] Existing Instance Uiff1_rel_Symmetric.
#[export] Existing Instance Uiff1_rel_Transitive.
#[export] Existing Instance Uiff1_rel.

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
#[export] Hint Rewrite ptsto_inv : utils.

#[export] Hint Rewrite sep_emp_r : utils.
#[export] Hint Rewrite sep_emp_l : utils.

#[export] Hint Rewrite seps_tl : utils.
#[export] Hint Rewrite seps_emp_hd : utils.


#[export] Hint Rewrite sep_seps_l : utils.
#[export] Hint Rewrite sep_seps_r : utils.


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


#[export] Hint Rewrite map_split_singleton_r : utils.
#[export] Hint Rewrite map_split_singleton_l : utils.
#[export] Hint Rewrite not1_has_key : utils.

