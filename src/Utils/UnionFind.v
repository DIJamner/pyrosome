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



Require Import Lists.List.

From coqutil Require Import Map.Interface.
Import ListNotations.

Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.

From Utils Require Import Utils Monad Sep Relations Decidable Options.
Import StateMonad.



Section __.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)
      (* TODO: is this needed since I also have zero?
      (default_idx: WithDefault idx) *)
      (idx_map : map.map idx idx)
      (idx_map_ok : map.ok idx_map)
      (* We use nats for rank because we do recursion on the max rank.
         These should be of size log(n), so they might be fine for performance.
         TODO: experiment with positive, int63 for ranks & profile
         *)
      (rank_map : map.map idx nat).

  (* For keeping track of fresh idxs.
     TODO: decide whether a separate type is worth having.

     TODO: for reasoning about int63, we have to allow allocation to fail
     or somehow handle overflow (although it will never happen)
   *)
  Context
    (lt : idx -> idx -> Prop)
      (succ : idx -> idx)
      (zero : idx).

  Definition in_bounds c := exists c', lt c c'.
  Context
    (succ_lt : forall c, in_bounds c -> lt c (succ c))
      (lt_trans : forall a b c, a < b -> b < c -> a < c)
      (lt_antisym : forall a b, a < b -> a <> b).


  Record union_find :=
    MkUF {
        (* We use nats for rank because we do recursion on them.
           TODO: all ranks or just max rank?
           TODO: use N/positive?
         *)
        rank : rank_map;
        parent : idx_map;
        (* we include an upper bound on the rank for purposes of termination *)
        max_rank : nat;
        next : idx;
      }.

  Definition empty : union_find :=
    MkUF map.empty map.empty 0 zero.

  (*TODO: write w/ state monad for clarity?*)

  (* allocates a distinct identifier at the end *)
  Definition alloc '(MkUF ra pa mr l) :=
    (MkUF (map.put ra l 0%nat) (map.put pa l l) mr (succ l), l).

  (*TODO: should also decrease ranks for memory reasons *)
  Fixpoint find_aux' (mr : nat) f i : option (idx_map * idx) :=
    match mr with
    | O => None
    | S mr =>
          @! let fi <- map.get f i in
            if eqb fi i then
              ret (f,i)
            else
              let (f, r) <- find_aux' mr f fi in
              let f := map.put f i r in
              ret (f,r)
    end.
                   
  
  Definition find' '(MkUF ra pa mr l) x  : option _ :=
    @! let (f,cx) <- find_aux' (S mr) pa x in
      ret (MkUF ra f mr l, cx).

  (*TODO: needs to return the root id (check)*)
  (* Note: returns None if either id is not in the map *)
  Definition union' h x y : option _ :=
    @! let (h, cx) <- find' h x in
      let (h, cy) <- find' h y in
      if eqb cx cy then ret (h, cx) else
      (*  let '(ra, pa, mr, l) := h in*)
        let rx <- map.get h.(rank) cx in
        let ry <- map.get h.(rank) cy in
        match Nat.compare ry rx with
        | Lt => @!ret (MkUF (h.(rank))
                         (map.put h.(parent) cy cx)
                         (h.(max_rank))
                         h.(next), cx)
        | Gt => @!ret (MkUF (h.(rank))
                         (map.put h.(parent) cx cy) 
                         (h.(max_rank))
                         (h.(next)), cy)
        | Eq => @!ret (MkUF (map.put h.(rank) cx (Nat.succ rx))
                         (map.put h.(parent) cy cx)
                         (max h.(max_rank) (Nat.succ rx))
                         h.(next), cx)
        end.

  Definition interp_uf (u : union_find) (a b : idx) : Prop :=
    match find' u a, find' u b with
    | Some (_, a'), Some (_, b') => a' = b'
    | _, _ => False
    end.

  Lemma interp_uf_sym u a b
    : interp_uf u a b -> interp_uf u b a.
  Proof.
    unfold interp_uf;
      repeat case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma interp_uf_trans u a b c
    : interp_uf u a b -> interp_uf u b c -> interp_uf u a c.
  Proof.
    unfold interp_uf;
      repeat case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  (*TODO: backport this? Need `Defined` for fixpoint*)
  Lemma sep_impl_defined
    : forall (A : Type) (mem : map.map A A)
             (P1 P1' P2 P2' : mem -> Prop),
      (forall a : mem, P1 a -> P1' a) ->
      (forall a : mem, P2 a -> P2' a) ->
      forall a : mem, sep P1 P2 a -> sep P1' P2' a.
  Proof.
    intros;
    unfold sep in *;
      break;
      eauto 10.
  Defined.

  
  Unset Elimination Schemes.
  Inductive forest_ptsto : idx -> idx_map -> Prop :=
  | empty_forest i : forest_ptsto i map.empty
  | forest_join i m
    : sep (forest_ptsto i) (forest_ptsto i) m ->
      forest_ptsto i m
  | forest_node i j
    : i <> j ->
      forall m, sep (and1 (forest_ptsto i) (not1 (has_key j))) (ptsto i j) m ->
      forest_ptsto j m.
  Set Elimination Schemes.
  Hint Constructors forest_ptsto : utils.

  Section ForestInd.
    Context (P : idx -> idx_map -> Prop)
      (P_empty : forall (i : idx) , P i map.empty)
      (P_join : forall (i : idx) (m : idx_map),
          sep (and1 (forest_ptsto i) (P i)) (and1 (forest_ptsto i) (P i)) m ->
          P i m)
      (P_node : forall (i j : idx),
          i <> j ->
          forall (m : idx_map),
            sep (and1 (and1 (forest_ptsto i) (not1 (has_key j))) (P i))
              (ptsto i j) m ->
            P j m).
                 
    Fixpoint forest_ptsto_ind
      (i : idx) (r : idx_map) (f2 : forest_ptsto i r) : P i r.
      refine (match f2 in (forest_ptsto i0 r0) return (P i0 r0) with
              | empty_forest i0 => P_empty i0
              | forest_join i0 m x => P_join i0 m _
              | forest_node i0 j H m x => P_node i0 j H m _
              end).
      Proof.
        all: eapply sep_impl_defined; try eassumption; auto.
        all: unfold and1 in *; intuition eauto using forest_ptsto_ind.
      Qed.

  End ForestInd.

 

  Inductive uf_order (m : idx_map) : idx -> idx -> Prop :=
  | uf_order_base i j : (*TODO: indclude this?*) i <> j -> map.get m i = Some j -> uf_order m i j
  | uf_order_trans i j k : uf_order m i j -> uf_order m j k -> uf_order m i k.

  
  Lemma uf_order_empty i j
    : uf_order map.empty i j <-> False.
  Proof.
    intuition idtac.
    induction H; basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite uf_order_empty : utils.

  Lemma uf_order_has_key_l m k1 k2
    : uf_order m k1 k2 ->
      has_key k1 m.
  Proof.
    unfold has_key.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    rewrite H0; eauto.
  Qed.


    
  Lemma forest_ptsto_none m i
    : forest_ptsto i m -> map.get m i = None.
  Proof.
    induction 1;
      unfold sep, and1 in *;
      basic_goal_prep;
      basic_utils_crush.
    {
      apply Properties.map.get_split with (k:=i) in H;
        basic_utils_crush; congruence.
    }
  Qed.
  Hint  Resolve forest_ptsto_none : utils.
  
  Lemma sep_ptsto_put_r (P : idx_map -> Prop) m i j
    : map.get m i = None ->
      P m ->
      sep P (ptsto i j) (map.put m i j).
  Proof.
    unfold sep;
      basic_goal_prep;
      basic_utils_crush.
    exists m, (map.singleton i j);
      basic_utils_crush.
  Qed.
    
  Lemma forest_node' i j m
    : i <> j ->
      map.get m j = None ->
      (forest_ptsto i) m -> forest_ptsto j (map.put m i j).
  Proof.
    intros; eapply forest_node; eauto.
    apply sep_ptsto_put_r; unfold and1; basic_utils_crush.
  Qed.
  Hint Resolve forest_node' : utils.

  Lemma sep_get_split (m : idx_map) k j P Q
    : map.get m j = Some k ->
      sep P Q m ->
      (sep (and1 P (fun m => map.get m j = Some k)) Q m)
      \/ (sep P (and1 Q (fun m => map.get m j = Some k)) m).
  Proof.
    unfold sep in *;
      basic_goal_prep.
      pose proof H0 as H'.
      apply Properties.map.get_split with (k:=j) in H0.
      rewrite !H in H0.
      basic_utils_crush; [left | right].
      all: exists x, x0.
      all: unfold and1, has_key.
      all: rewrite <- H0.
      all: intuition eauto.
  Qed.
  
  Lemma sep_get_split' (m : idx_map) k j P Q
    : map.get m j = Some k ->
      sep P Q m ->
      (sep (and1 P (fun m => map.get m j = Some k)) (and1 Q (not1 (has_key j))) m)
      \/ (sep (and1 P  (not1 (has_key j))) (and1 Q (fun m => map.get m j = Some k)) m).
  Proof.
    unfold sep in *;
      basic_goal_prep.
      pose proof H0 as H'.
      apply Properties.map.get_split with (k:=j) in H0.
      rewrite !H in H0.
      basic_utils_crush; [left | right].
      all: exists x, x0.
      all: unfold not1, and1, has_key.
      all: rewrite <- H0.
      all: intuition eauto.
      all: rewrite H4 in H3; eauto.
  Qed.

  Lemma empty_forest': forall i : idx, Uimpl1 emp (forest_ptsto i).
  Proof.
    intros i m;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma forest_join' i
    : seps_Uiff1 [forest_ptsto i; forest_ptsto i] [forest_ptsto i].
  Proof.
    cbv [seps seps_Uiff1];
      basic_goal_prep;
      basic_utils_crush.
    split.
    { eapply forest_join. }
    { intros.
      eapply sep_consequence.
      2: eapply empty_forest'.
      all: eauto.
      (*TODO: get rewrite to work *)
      eapply sep_emp_l; eauto.
    }
  Qed.

  
  Lemma sep_to_seps' P Q (m : idx_map)
    : sep P Q m <-> seps [P; Q] m.
  Proof.
    unfold seps;
      split; eapply sep_consequence;
      basic_goal_prep;
      seprewrite;
      basic_utils_crush.
  Qed.

  
  Lemma sep_to_seps (P Q : idx_map -> Prop)
    : Uiff1 (sep P Q) (seps [P; Q]).
  Proof.
    unfold seps;
      split; eapply sep_consequence;
      basic_goal_prep;
      seprewrite;
      basic_utils_crush.
  Qed.
  
  Ltac cancel_prep H :=
    let m := lazymatch type of H with _ ?m => m end in
    revert H;
    repeat lazymatch goal with H : context [?m] |- _ => clear H end;
    revert m.
  
  Arguments sep_sequent_focus {A}%type_scope
    {Eqb_A Eqb_A_ok mem mem_ok}
    (perm1 perm2 l1 l2)%list_scope _ _ (_ _)%function_scope 
    m _.
  Ltac sep_focus p1 p2 :=        
    apply sep_sequent_focus with (perm1:=p1) (perm2:=p2);
    [ vm_compute; exact I
    | vm_compute; exact I
    | cbn..].

  
  Lemma distribute_get (m : idx_map) i j P Q
    : map.get m i = Some j ->
      sep P Q m ->
      let H m := map.get m i = Some j in
      sep (and1 P H) Q m \/ sep P (and1 Q H) m.
  Proof.
    unfold sep; basic_goal_prep;
      basic_utils_crush.
    pose proof H0.
    apply Properties.map.get_split with (k:=i) in H0;
      destruct H0;
      [left | right];
      exists x, x0;
      unfold and1;
      basic_utils_crush.
    all: congruence.
  Qed.

  Ltac cancel_prep' H :=
  let m := lazymatch type of H with
           | _ ?m => m
           end in
  let l1 := lazymatch type of H with seps ?l1 _ => l1 end in
  let l2 := lazymatch goal with |- seps ?l2 m => l2 end in
  revert H;
  repeat lazymatch goal with
    | H:context [ ?m ] |- _ => clear H
    end;
  revert m;
  change (seps_Uimpl1 l1 l2).


  Lemma distribute_not_has_key (i : idx) P Q
    : Uiff1 (and1 (not1 (has_key i)) (sep P Q))
        (sep (and1 P (not1 (has_key i))) (and1 Q (not1 (has_key i)))).
  Proof.
    unfold Uiff1, and1, not1, sep, has_key;
      basic_goal_prep.
    case_match;
      split; basic_goal_prep; try tauto.
    {
      exfalso.
      eapply Properties.map.get_split with (k:=i) in H; eauto.
      destruct H; basic_goal_prep.
      { rewrite <- H,case_match_eqn in H3; tauto. }
      { rewrite <- H, case_match_eqn in H2; tauto. }
    }
    {
      exists x, x0.
      pose proof H0.
      eapply Properties.map.get_split with (k:=i) in H0; eauto.
      destruct H0; basic_goal_prep;rewrite <- H0, case_match_eqn;
        basic_utils_crush.
      { rewrite H4 in H5; auto. }
      { rewrite H4 in H5; auto. }
    }
    {
      intuition auto.
      exists x, x0.
      pose proof H.
      eapply Properties.map.get_split with (k:=i) in H; eauto.
    }
  Qed.
  
  Lemma distribute_not_has_key_seps (i : idx) l
    : Uiff1 (and1 (not1 (has_key i)) (seps l))
        (seps (map (and1 (not1 (has_key i))) l)).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    
    rewrite <- !sep_seps_r; eauto.
    rewrite distribute_not_has_key.
    rewrite <- IHl.
    rewrite and1_comm.
    rewrite and1_comm with (P:= (seps l)).
    reflexivity.
  Qed.
      
      
      
  Lemma forest_ptsto_split i m
    : forest_ptsto i m -> forall j k, map.get m j = Some k -> seps [forest_ptsto j; ptsto j k; forest_ptsto i] m.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      eapply sep_get_split in H; eauto.
      destruct H.
      {  
        eapply sep_consequence
          with (P2:= seps [forest_ptsto j; ptsto j k; forest_ptsto i])
               (Q2:= (forest_ptsto i))in H; [|  unfold and1, has_key in *..];
          basic_goal_prep; eauto.
        seprewrite.        
        cancel_prep' H.
        sep_apply_focused [0;3] [2] forest_join.
        reflexivity.
      }
      {
        eapply sep_consequence with (P2:=forest_ptsto i)
                                    (Q2:= seps [forest_ptsto j; ptsto j k; forest_ptsto i]) in H; eauto.
        
        2:{ unfold and1; basic_goal_prep; eauto. }
        2:{ unfold and1; basic_goal_prep; eauto. }
        seprewrite.
        cancel_prep' H.
        sep_apply_focused [0;3] [2] forest_join.
        reflexivity.
      }
    }
    {
      eapply distribute_get in H0; eauto;
        destruct H0 as [H0 | H0];
        apply sep_to_seps in H0.
      2:{
        seprewrite.
        cancel_prep' H0.
        sep_focus' [2;0;1] [0;1;2]; try reflexivity.
        apply seps_Uimpl1_cons_lift_l.
        intro.
        basic_utils_crush.
        rewrite Uimpl1_and1_l.
        rewrite Uimpl1_and1_l.
        rewrite <- (empty_forest' k).
        basic_utils_crush.
      }
      {
        cancel_prep' H0.
        basic_utils_crush.
        setoid_replace
          (and1
       (and1 (and1 (forest_ptsto i) (not1 (has_key j)))
          (fun m : idx_map =>
           forall j1 k0 : idx,
           map.get m j1 = Some k0 ->
           seps [forest_ptsto j1; ptsto j1 k0; forest_ptsto i] m))
       (fun m : idx_map => map.get m j0 = Some k))
          with (seps [forest_ptsto j0; ptsto j0 k; (and1 (forest_ptsto i) (not1 (has_key j)))])
               using relation (@Uimpl1 idx_map).
        {
          basic_utils_crush.
          basic_goal_prep.
          basic_utils_crush.
          
          sep_focus' [2;3] [2]; [|reflexivity].
          unfold seps_Uimpl1, Uimpl1.
          cbv [seps].
          basic_goal_prep.
          seprewrite.
          eapply forest_node; eauto.
          seprewrite; eauto.
        }
        {
          unfold Uimpl1, and1.
          basic_goal_prep;
            basic_utils_crush.
          apply H2 in H1.

          assert (not1 (has_key j) a).
          {
            unfold not1, has_key.
            rewrite H3; tauto.
          }
          clear H2.
          pose proof (conj H4 H1).
          pattern a in H2.
          change (fun r => ?f r /\ ?g r)
            with (and1 f g) in H2.
          change (?f ?a) with (sep_app f a) in H2.
          rewrite distribute_not_has_key_seps in H2.
          unfold sep_app in *.
          cancel_prep' H2.
          basic_goal_prep.
          basic_utils_crush.
          rewrite Uimpl1_and1_r.
          sep_focus' [2] (@nil nat).
          {
            cbv [seps_Uimpl1 lift Uimpl1 seps].
            basic_goal_prep;
              seprewrite;
              basic_utils_crush.
          }
          rewrite and1_comm.
          reflexivity.
        }
      }
    }
  Qed.

  
  Lemma sep_has_key (k : idx) P
    : Uimpl1 (sep (has_key k) P) (has_key k).
  Proof.
    cbv [ Uimpl1 sep has_key].
    basic_goal_prep.
    case_match; eauto.
    revert H0; case_match; eauto.
    apply Properties.map.get_split with (k:=k) in H.
    intuition congruence.
  Qed.

  
  Definition in_before {A} l (a b : A) : Prop :=
    exists n m,
      nth_error l n = Some a
      /\ nth_error l m = Some b
      /\ n < m.
  

  Definition mem_order k (l : list idx) : _ -> Prop :=
    and1 (fun _ => ~ In k l)
    (and1 (fun m => Permutation l (map.keys m))
       (fun m => forall i j, map.get m i = Some j ->
                             (in_before l j i \/ j = k))).

  Hint Rewrite Properties.map.split_empty_l : utils.

  Lemma and1_lift_l P (Q : idx_map -> Prop)
    : Uiff1 (and1 (fun _ => P) Q) (sep (lift P) Q).
  Proof.
    unfold and1, lift, sep, Uiff1;
      basic_goal_prep.
    intuition (basic_goal_prep; subst; eauto).
    {
      exists map.empty, a.
      basic_utils_crush.
    }
    { autorewrite with utils in *; subst; auto. }
  Qed.
  Hint Rewrite and1_lift_l : utils.

  Definition exists1 {A B} (f : A -> B -> Prop) :=
    fun m => exists x, f x m.
  
  Lemma and1_exists_r A B (P : B -> Prop) Q
    : Uiff1 (and1 P (exists1 Q)) (exists1 (fun x : A => and1 P (Q x))).
  Proof.
    cbv [Uiff1 and1 exists1].
    firstorder idtac.
  Qed.
  Hint Rewrite and1_exists_r : utils.

  
  Lemma sep_exists_r A (P : idx_map -> Prop) Q
    : Uiff1 (sep P (exists1 Q)) (exists1 (fun x : A => sep P (Q x))).
  Proof.
    cbv [Uiff1 and1 exists1].
    firstorder idtac.
  Qed.
  Hint Rewrite sep_exists_r : utils.
  
  Lemma sep_exists_l A (P : idx_map -> Prop) Q
    : Uiff1 (sep (exists1 Q) P) (exists1 (fun x : A => sep (Q x) P)).
  Proof.
    cbv [Uiff1 and1 exists1].
    firstorder idtac.
  Qed.
  Hint Rewrite sep_exists_l : utils.

  Hint Rewrite nth_error_nil : utils.
  
  Lemma in_before_empty A (i j : A)
    : in_before [] i j <-> False.
  Proof.
    unfold in_before; intuition idtac;
      basic_goal_prep.
    basic_utils_crush.
  Qed.
  Hint Rewrite in_before_empty : utils.


  Lemma unfold_exists1 A B (P : A -> B -> Prop) m
    : exists1 P m = exists x, P x m.
  Proof. reflexivity. Qed.
  Hint Rewrite unfold_exists1 : utils.

  
  Lemma in_before_app A x x0 (i j : A)
    :  in_before (x ++ x0) i j
       <->  in_before x i j
            \/ in_before x0 i j
            \/ (In i x /\ In j x0).
  Proof.
    unfold in_before;
      split;
      basic_goal_prep.
    {
      destruct (PeanoNat.Nat.ltb_spec x2 (length x)).
      2:destruct (PeanoNat.Nat.ltb_spec x1 (length x)).
      {
        erewrite nth_error_app1 in *; eauto.
        left.
        exists x1, x2; basic_utils_crush.
      }
      {
        right; right.
        erewrite nth_error_app1 in H by eauto.
        erewrite nth_error_app2 in H0 by eauto.
        split; eapply nth_error_In; eauto.
      }
      {
        right; left.
        erewrite nth_error_app2 in *; eauto.
        exists (x1 - length x), (x2 - length x); basic_utils_crush.
        Lia.lia.
      }
    }
    {
      destruct H as [H | [ H | H] ];
        basic_goal_prep.
      {
        exists x1, x2.
        erewrite !nth_error_app1.
        1:basic_utils_crush.
        all: apply nth_error_Some; congruence.
      }
      {
        exists (x1 + length x), (x2 + length x);
          erewrite !nth_error_app2.
        1: rewrite !PeanoNat.Nat.add_sub.
        1:basic_utils_crush.
        all: Lia.lia.
      }
      {
        apply In_nth_error in H,H0.
        basic_goal_prep.
        exists x2, (x1 + length x).
        erewrite nth_error_app1.
        1:erewrite !nth_error_app2.
        1:rewrite !PeanoNat.Nat.add_sub.
        1:basic_utils_crush.
        all: try Lia.lia.
        1: enough (x2 < length x) by Lia.lia.
        all: apply nth_error_Some; congruence.
      }
    }
  Qed.
  Hint Rewrite in_before_app : utils.

  
  Lemma iff_or_exact_cancel_l A B
    : (A <-> A \/ B) <-> (B -> A).
  Proof. intuition idtac. Qed.
  Hint Rewrite iff_or_exact_cancel_l : utils.

  Lemma not_or_iff A B : ~ (A \/ B) <-> ~ A /\ ~ B.
  Proof. intuition idtac. Qed.
  Hint Rewrite not_or_iff : utils.

  (*TODO: move to Sep.v*)
  #[export] Instance seps_Uiff1_app_mor:
  Morphisms.Proper (seps_Uiff1 ==> seps_Uiff1 ==> seps_Uiff1)
    (app (A:=idx_map -> Prop)).
  Proof.
    cbv [Morphisms.Proper Morphisms.respectful]; intros.
    unfold seps_Uiff1.
    rewrite !sep_concat; eauto.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (*TODO: ove to Sep.v*)
  Hint Rewrite sep_lift_l : utils.

  
  Lemma split_has_key_l a (x x0 : idx_map) (k:idx)
    : map.split a x x0 ->
      has_key k x ->
      has_key k a.
  Proof.
    unfold has_key.
    case_match; [| tauto].
    intros H _.
    apply Properties.map.get_split with (k:=k) in H;
      destruct H; basic_goal_prep;
      basic_utils_crush; [|congruence].
    rewrite H, case_match_eqn; auto.
  Qed.
  Hint Resolve split_has_key_l : utils.
  
  
  Lemma split_has_key_r a (x x0 : idx_map) (k:idx)
    : map.split a x x0 ->
      has_key k x0 ->
      has_key k a.
  Proof.
    rewrite Properties.map.split_comm.
    apply split_has_key_l.
  Qed.
  Hint Resolve split_has_key_r : utils.

  Lemma split_all_iff A (P Q : A -> Prop)
    : (forall x, P x <-> Q x) ->
      (forall x, P x -> Q x)
      /\ (forall x, Q x -> P x).
  Proof.
    firstorder eauto.
  Qed.
  
  Lemma map_keys_app (m : idx_map) l
    : map.keys m ++ l
      = (map.fold (fun acc k _ => k :: acc) l m).
  Proof.
    unfold map.keys.
    apply Properties.map.fold_two_spec with (r01:=[]) (r02:=l) (m:=m);
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Hint Rewrite @Properties.map.fold_empty : utils.

  (*
  Lemma map_keys_fold_disjoint (m : idx_map) m'
    : map.disjoint m m' ->
      (map.fold (fun (acc : list idx) (k _ : idx) => k :: acc) (map.keys m') m)
      = map.fold (fun acc k _ =>
                    if map.get m' k then acc else k :: acc) (map.keys m') m.
  Proof.
    apply Properties.map.fold_two_spec with (r01:=(map.keys m')) (r02:=(map.keys m')) (m:=m);
      basic_goal_prep;
      basic_utils_crush.

    rewrite !Properties.map.fold_put.
    {
      cbv.*)

  Section Perm.

    Context (A B : Type)
      (f : A -> list B -> list B)
      (f_comm : forall (a1 a2 : A) r, Permutation (f a1 (f a2 r))
                                        (f a2 (f a1 r)))
      (f_cong : forall a b r, Permutation a b ->
                              Permutation (f r a) (f r b)).
    
    Lemma fold_right_change_order_equiv
      : forall l1 l2 : list A,
        Permutation l1 l2 ->
        forall r1, Permutation (fold_right f r1 l1) (fold_right f r1 l2).
    Proof.
      induction 1; intros.
      - reflexivity.
      - simpl. f_equal. eauto.
      - simpl. apply f_comm.
      - rewrite IHPermutation1, IHPermutation2. reflexivity.
    Qed.

  End Perm.

  (*TODO: ok here*)

  Section Perm.

      Context (A B : Type)
        (f: list B -> idx -> idx -> list B)
        (f_comm: forall r k1 v1 k2 v2, Permutation (f (f r k1 v1) k2 v2)
                                         (f (f r k2 v2) k1 v1))
        (f_cong : forall a b k v, Permutation a b ->
                                  Permutation (f a k v) (f b k v)).
      
      
      
      Lemma fold_put_equiv
        : forall r0 (m : idx_map) k v,
          map.get m k = None ->
          Permutation
            (map.fold f r0 (map.put m k v)) (f (map.fold f r0 m) k v).
      Proof.
        intros.
        do 2 rewrite coqutil.Map.Properties.map.fold_to_tuples_fold.
        match goal with
        | |- Permutation ?L (f (List.fold_right ?F r0 (map.tuples m)) k v) =>
            change (Permutation L (List.fold_right F r0 (cons (k, v) (map.tuples m))))
        end.
        
        eapply fold_right_change_order_equiv.
        - intros [k1 v1] [k2 v2] r. apply f_comm.
        - basic_goal_prep; eauto.
        - apply NoDup_Permutation.
          + apply Properties.map.tuples_NoDup.
          + constructor.
            * pose proof (Properties.map.tuples_spec m k v). intuition congruence.
            * apply Properties.map.tuples_NoDup.
          + intros [k0 v0].
            rewrite (Properties.map.tuples_put m k v H).
            reflexivity.
      Qed.
    End Perm.
    
    Lemma map_key_cons_permutation (m : idx_map) k v
      : map.get m k = None ->
        Permutation (k ::map.keys m) (map.keys (map.put m k v)).
    Proof.
      unfold map.keys.
      intros.
      rewrite fold_put_equiv; eauto.
      basic_goal_prep;
        basic_utils_crush.
      apply perm_swap.
    Qed.

    
    Lemma fold_right_map_fst A B (l : list (A * B))
      : fold_right (fun '(k, _) (r : list _) => k :: r) [] l
        = map fst l.
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    (*TODO: move to utils*)
    Hint Resolve incl_nil_l : utils.

    Lemma pair_fst_in_exists:
      forall [S A : Type] (l : named_list S A) (n : S),
        In n (map fst l) -> exists a, In (n, a) l.
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      apply IHl in H0; break.
      exists x; eauto.
    Qed.

    Lemma incl_fst_put_tuple i i0
      :  forall gen0 : idx_map,
        incl (map fst (map.tuples gen0))
          (map fst (map.tuples (map.put gen0 i i0))).
    Proof.
      intros gen0 i1 Hin.
      
      apply pair_fst_in_exists in Hin.
      break.
      
      pose proof (eqb_spec i i1);
        destruct (eqb i i1); subst.
      all:eapply pair_fst_in.
      all: rewrite Properties.map.tuples_spec in *.
      all: basic_utils_crush.
    Qed.    
    
    
    Lemma map_split_incl_r (a x x0 : idx_map)
      : map.split a x x0 ->
        incl (map.keys x0) (map.keys a).
    Proof.
      unfold map.split;
        basic_goal_prep; subst.
      unfold map.putmany.
      unfold map.keys in *.
      rewrite ! Properties.map.fold_to_tuples_fold.
      rewrite !fold_right_map_fst.
      generalize (map.tuples x0).
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      {
        enough (exists z, (In (i,z) (map.tuples
                                       (map.put
                                          (fold_right (fun '(k, v) (r : idx_map) => map.put r k v) x l) i
                                          i0)))).
        {
          basic_goal_prep.
          basic_utils_crush.
        }
        {
          
          eexists.
          rewrite Properties.map.tuples_spec.
          basic_utils_crush.
        }
      }
      {
        eapply incl_tran; eauto.
        clear IHl.
        set (fold_right _ _ _) as gen;
          generalize gen.
        clear gen; intro gen.
        apply incl_fst_put_tuple .
      }
    Qed.
    
    Lemma map_split_incl1 (a x x0 : idx_map)
      : map.split a x x0 ->
        incl (map.keys x ++ map.keys x0) (map.keys a).
    Proof.
      intro.
      apply incl_app; eauto using map_split_incl_r.
      apply Properties.map.split_comm in H.
      eauto using map_split_incl_r.
    Qed.

    Lemma map_keys_in (m : idx_map) k
      : In k (map.keys m) -> exists v, map.get m k = Some v.
    Proof.
      unfold map.keys.
      rewrite Properties.map.fold_to_tuples_fold.
      rewrite fold_right_map_fst.
      intro.
      
      apply pair_fst_in_exists in H.
      break.
      exists x.
      apply Properties.map.tuples_spec.
      auto.
    Qed.
    
    Lemma map_keys_in' (m : idx_map) k
      : In k (map.keys m) <-> if map.get m k then True else False.
    Proof.
      case_match; intuition eauto.
      {
        eapply Properties.map.in_keys; eauto.
      }
      {
        eapply map_keys_in in H;
          basic_goal_prep.
        congruence.
      }
    Qed.
    
    Lemma map_split_incl2 (a x x0 : idx_map)
      : map.split a x x0 ->
        incl (map.keys a) (map.keys x ++ map.keys x0).
    Proof.
      intros Hsplit i Hin.
      autorewrite with utils.
      rewrite !map_keys_in' in *.
      eapply Properties.map.get_split with (k:=i) in Hsplit; eauto.
      intuition subst.
      {
        rewrite H1, <- H0.
        case_match; eauto.
      }
      {
        rewrite H1, <- H0.
        case_match; eauto.
      }
    Qed.

    Lemma dispoint_notin (x x0 : idx_map)
      : map.disjoint x x0 ->
        (forall x1 : idx, In x1 (map.keys x) -> ~ In x1 (map.keys x0)).
    Proof.
      unfold map.disjoint.
      intros.
      rewrite !map_keys_in' in  *.
      revert H0; case_match; case_match; intuition eauto.
    Qed.

    Lemma split_disjoint (a x x0 : idx_map)
      : map.split a x x0 ->
        map.disjoint x x0.
    Proof.
      unfold map.split.
      intuition eauto.
    Qed.
    Hint Resolve split_disjoint : utils.

    Lemma nodup_split_keys (a x x0 : idx_map)
      : map.split a x x0 ->
        NoDup (map.keys x ++ map.keys x0).
    Proof.
      intro Hsplit.
      apply List.NoDup_app_iff.
      repeat split; eauto using Properties.map.keys_NoDup.
      all: intros.
      all: try eapply Properties.map.keys_NoDup.
      all: eapply dispoint_notin; eauto with utils.
      apply Properties.map.split_comm in Hsplit.
      all: eauto with utils.
    Qed.
    
    Lemma map_split_permutation (a x x0 : idx_map)
      : map.split a x x0 ->
        Permutation (map.keys x ++ map.keys x0) (map.keys a).
    Proof.
      intros.
      eapply NoDup_Permutation.
      - eapply nodup_split_keys; eauto.
      - apply Properties.map.keys_NoDup.
      -
        intros.
        split; [apply map_split_incl1
               | apply map_split_incl2]; eauto.
    Qed.

    Lemma mem_order_split i l1 l2
      : Uimpl1 (sep (mem_order i l1) (mem_order i l2)) (mem_order i (l1++l2)).
    Proof.
      unfold mem_order.
      seprewrite.
      rewrite !sep_to_seps.
      seprewrite.
      cbn [app].
      sep_focus' [0;2] [0].
      {
        cbv [seps_Uimpl1 seps Uimpl1].
        intros.
        basic_utils_crush.
      }
      
      cbv [seps_Uimpl1 seps].
      seprewrite.
      cbv [Uimpl1 sep and1].
      basic_goal_prep.
      split.
      {
        rewrite <- map_split_permutation; eauto.
        rewrite H0, H1.
        reflexivity.
      }
      {
        
        basic_goal_prep;
          basic_utils_crush.

        pose proof (eqb_spec i j);
          destruct (eqb i j); auto; left.
        
        
        apply Properties.map.get_split with (k:=i0) in H;
          destruct H; basic_goal_prep.
        {
          left.
          rewrite H in H4.
          apply H3 in H4.
          destruct H4; [intuition idtac |congruence].
        }
        {
          right; left.
          rewrite H in H4.
          apply H2 in H4.
          destruct H4; [intuition idtac |congruence].
        }
      }
    Qed.

    
    Lemma has_key_empty (i : idx) : has_key i (map.empty : idx_map) <-> False.
    Proof. unfold has_key; basic_utils_crush. Qed.
    Hint Rewrite has_key_empty : utils.

    Lemma map_keys_empty : map.keys (map:=idx_map) map.empty = [].
    Proof.
      unfold map.keys.
      basic_utils_crush.
    Qed.
    Hint Rewrite map_keys_empty : utils.
    
    Lemma mem_order_empty i :  mem_order i [] map.empty.
    Proof.
      unfold mem_order, and1.
      basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Resolve mem_order_empty : utils.

    
    Lemma seps_Uimpl1_and l (P Q : idx_map -> _)
      : seps_Uimpl1 l [P] ->
        seps_Uimpl1 l [Q] ->
        seps_Uimpl1 l [and1 P Q].
    Proof.
      cbv [seps_Uimpl1].
      generalize (seps l); intro.
      cbv [seps].
      seprewrite.
      cbv [Uimpl1 and1].
      firstorder fail.
    Qed.

    
    Lemma has_key_put m (i j i0 : idx)
      : has_key i0 (map.put m i j) <-> i = i0 \/ has_key i0 m.
    Proof.
      unfold has_key.
      pose proof (eqb_spec i i0);
        destruct (eqb i i0); subst;
        basic_utils_crush.
    Qed.
    Hint Rewrite has_key_put : utils.
    
    Lemma in_before_cons x (i i0 j0 : idx)
      :  i <> i0 ->
         in_before x j0 i0 ->
         in_before (i :: x) j0 i0.
    Proof.
      unfold in_before.
      basic_goal_prep.
      exists (S x0), (S x1).
      cbn.
      intuition Lia.lia.
    Qed.
    Hint Resolve in_before_cons : utils.

    
    Lemma in_before_first (i i0 : idx) x
      : i <> i0 ->
        In i0 x ->
        in_before (i :: x) i i0.
    Proof.
      unfold in_before.
      intros.
      apply In_nth_error in H0.
      basic_goal_prep.
      exists 0, (S x0).
      cbn.
      intuition Lia.lia.
    Qed.
    Hint Resolve in_before_first : utils.
    
    Lemma mem_order_cons i x j
      : i<>j ->
        ~ In j x ->
        Uimpl1 (sep (*(and1*) (mem_order i x)(* (not1 (has_key j)))*) (ptsto i j))
          (mem_order j (i::x)).
    Proof.
      intros Hneq Hnin.
      unfold mem_order.
      seprewrite.
      rewrite !sep_to_seps.
      (*    rewrite and1_comm.
    rewrite distribute_not_has_key_seps.*)
      seprewrite.
      sep_focus' (@nil nat) [0].
      {
        cbv [seps_Uimpl1 seps].
        seprewrite.
        cbv [Uimpl1 lift emp].
        intuition idtac.
      }
      apply seps_Uimpl1_cons_lift_l; intro.
      apply seps_Uimpl1_and.
      {
        rewrite Uimpl1_and1_l.
        cbv [seps_Uimpl1 seps].
        seprewrite.
        cbv [Uimpl1 lift emp].
        unfold sep; intros.
        basic_goal_prep.
        subst.
        autorewrite with utils in *.
        basic_goal_prep.
        subst.
        rewrite <- map_key_cons_permutation by auto.
        rewrite H1; eauto.
      }
      {
        cbv [seps_Uimpl1 seps].
        seprewrite.
        cbv [Uimpl1 lift emp and1].
        unfold sep; intros.
        basic_goal_prep.
        subst.
        autorewrite with utils in *.
        basic_goal_prep.
        subst.
        pose proof (eqb_spec i i0);
          destruct (eqb i i0); subst;
          basic_utils_crush.
        left.
        pose proof H1.
        apply H4 in H1.
        
        basic_utils_crush.
        apply in_before_first; eauto.
        rewrite H2.
        eapply Properties.map.in_keys; eauto.
      }
    Qed.

    
    Lemma mem_order_none_not_in i x m1 j
      : mem_order i x m1 ->
        map.get m1 j = None ->
        ~ In j x.
    Proof.
      unfold mem_order, and1;
        basic_goal_prep;
        basic_utils_crush.
      rewrite H1 in H3.
      unfold has_key in H3.
      rewrite map_keys_in' in H3.
      rewrite H0 in H3.
      auto.
    Qed.
    
    Lemma forest_ptsto_order i m
      : forest_ptsto i m -> exists1 (mem_order i) m.
    Proof.
      induction 1;
        basic_goal_prep;
        basic_utils_crush.
      {
        repeat (seprewrite;
                basic_utils_crush).
        
        exists (x++x0).
        apply mem_order_split.
        eapply sep_consequence; try eassumption;
          unfold and1; intuition subst.
      }
      {      
        repeat (seprewrite;
                basic_utils_crush).
        exists (i::x).
        apply mem_order_cons; eauto.
        2:{
          sep_isolate.
          rewrite !sep_to_seps in *.
          seprewrite.
          cancel_prep' H0.
          rewrite Uimpl1_and1_r.
          reflexivity.
        }
        {
          destruct H0 as [m1 [m2 [Hsplit [ H0l H0r] ] ] ].
          unfold and1 in *.
          basic_utils_crush.
          revert H0.
          eapply mem_order_none_not_in; eauto.
        }
      }
    Qed.
    
    Lemma forest_ptsto_has_next i m
      : forest_ptsto i m -> forall j k, map.get m j = Some k -> i = k \/ has_key k m.
    Proof.
      
      intros.
      
      pose proof (eqb_spec i k);
        destruct (eqb i k); auto; right.

      pose proof (forest_ptsto_order _ _ H).
      destruct H2.
      unfold mem_order in *.
      unfold and1 in *.
      basic_goal_prep.
      apply H4 in H0.
      intuition (subst; try tauto).
      unfold in_before in *.
      basic_goal_prep.
      
      eapply nth_error_In in H0,H5; eauto.
      rewrite H3 in H0, H5.
      apply map_keys_in'; eauto.
    Qed.


    Definition forest_list l : idx_map -> Prop :=
      seps (map forest_ptsto l).
    
    Definition forest_roots l : idx_map -> Prop :=
      seps (map (fun i => ptsto i i) l).

    Definition tree i : idx_map -> Prop :=
      sep (forest_ptsto i) (ptsto i i).

    
    Definition forest l := seps (map tree l).
    (*sep (forest_list l) (forest_roots l).*)

    
    (*TODO: move to Sep.v*)
    Lemma sep_empty (P Q : idx_map -> Prop)
      : sep P Q map.empty <-> P map.empty /\ Q map.empty.
    Proof.
      unfold sep.
      split; basic_goal_prep.
      {
        erewrite Properties.map.split_empty in H.
        basic_utils_crush.
      }
      {
        exists map.empty, map.empty.
        basic_utils_crush.
      }
    Qed.
    Hint Rewrite sep_empty : utils.

    
    (* TODO: move to *)
    Lemma seps_empty
      : Uiff1 (seps (mem:=idx_map) []) emp.
    Proof.
      cbv [seps].
      basic_utils_crush.
    Qed.
    Hint Rewrite seps_empty : utils.
    
    Lemma seps_empty' m
      : seps (mem:=idx_map) [] m <-> emp m.
    Proof.
      cbv [seps].
      basic_utils_crush.
    Qed.
    Hint Rewrite seps_empty' : utils.

    (*TODO: rename the other one*)
    Lemma empty_forest_rooted : forest [] map.empty.
    Proof.
      unfold forest, forest_list, forest_roots.
      basic_utils_crush.
      all:cbn.
      all:basic_utils_crush.
    Qed.

    
    Lemma distribute_get_seps (m : idx_map) i j l
      : map.get m i = Some j ->
        seps l m ->
        let H m := map.get m i = Some j in
        exists l1 l2 x, l = l1++x::l2 /\
                          seps (l1++(and1 x H)::l2) m.
    Proof.
      revert m.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      
      change (seps (?a::?l)) with (sep a (seps l)) in H0.
      eapply distribute_get in H0; eauto.
      destruct H0.
      {
        exists [], l, a;
          basic_utils_crush.
      }
      {
        destruct H0 as [? [? [? [? ?] ] ] ].
        unfold and1 in H3; basic_goal_prep.
        specialize (IHl _ H4 H3).
        basic_goal_prep; subst.
        exists (a::x1), x2, x3.
        basic_utils_crush.
        change (sep a (seps (x1 ++ and1 x3 H1 :: x2)) m).
        exists x, x0; basic_utils_crush.
      }
    Qed.

    
    
    Lemma distribute_get_seps' (m : idx_map) i j l
      : map.get m i = Some j ->
        seps l m ->
        let H m := map.get m i = Some j in
        exists x m', In x l /\ (and1 x H) m'.
    Proof.
      revert m.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      
      change (seps (?a::?l)) with (sep a (seps l)) in H0.
      eapply distribute_get in H0; eauto.
      destruct H0.
      {
        destruct H0 as [? [? [? [? ?] ] ] ].
        exists a;
          basic_utils_crush.
      }
      {
        destruct H0 as [? [? [? [? ?] ] ] ].
        unfold and1 in H3; basic_goal_prep.
        specialize (IHl _ H4 H3).
        basic_goal_prep; subst.
        exists x1, x2.
        basic_utils_crush.
      }
    Qed.

    
    Lemma in_before_cons_inv A (a:A) l j
      : a <>j -> in_before (a :: l) j j -> in_before l j j.
    Proof.
      unfold in_before;
        basic_goal_prep.
      destruct x; cbn in *; [congruence| ].
      destruct x0; cbn in *; [congruence| ].
      exists x, x0; basic_utils_crush.
      Lia.lia.
    Qed.
    
    
    Lemma in_before_antirefl A l (j:A)
      : NoDup l -> ~ in_before l j j.
    Proof.
      induction l; basic_goal_prep;
        basic_utils_crush.
      safe_invert H.
      apply IHl; auto.
      eapply in_before_cons_inv; eauto.
      intro; subst.
      clear IHl.
      unfold in_before in*.
      basic_goal_prep.
      destruct x0; [Lia.lia|].
      cbn in *.
      apply nth_error_In in H0; auto.
    Qed.
    
    Lemma forest_root_loop_canonical l f' j
      : forest_roots l f' ->
        Some j = map.get f' j ->
        In j l.
    Proof.
      unfold forest_roots.
      revert f'.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      
      pose proof (eqb_spec a j).
      destruct (eqb a j); subst; auto; right.
      change (seps (?a :: ?l)) with (sep a (seps l)) in H.
      destruct H as [? [? [? [? ?] ] ] ].
      eapply IHl; eauto.
      basic_utils_crush.
    Qed.

    
    Lemma map_split_3_ways (m x1 x2 y1 y2 : idx_map)
      :  map.split m x1 x2 ->
         map.split x2 y1 y2 ->
         map.split m y1 (map.putmany x1 y2).
    Proof.
      unfold map.split.
      intuition subst.
      {
        rewrite Properties.map.putmany_comm; eauto.
        rewrite <- Properties.map.putmany_assoc.
        f_equal.
        apply Properties.map.putmany_comm.
        apply Properties.map.disjoint_putmany_r in H2.
        apply Properties.map.disjoint_comm.
        intuition subst.
      }
      {
        apply Properties.map.disjoint_putmany_r in H2.
        apply Properties.map.disjoint_putmany_r.
        intuition subst.
        apply Properties.map.disjoint_comm.
        eauto.
      }
    Qed.

    Lemma split_put_left (r x x0 : idx_map) i j
      :    map.get x0 i = None ->
           map.split r x x0 ->
           map.split (map.put r i j) (map.put x i j) x0.
    Proof.
      
      intros.
      my_case Hget (map.get r i).
      2:{      
        pose proof (Properties.map.split_undef_put _ i j Hget).
        replace (map.put x i j) with (map.putmany (map.put map.empty i j) x).
        {
          rewrite Properties.map.split_comm.
          eapply  map_split_3_ways; eauto.
          rewrite Properties.map.split_comm.
          assumption.
        }
        {
          rewrite Properties.map.putmany_comm.
          {
            eapply putmany_singleton; eauto.
          }
          {
            unfold map.split in *; intuition subst.
            apply Properties.map.disjoint_putmany_r in H4.
            intuition subst.
          }
        }
      }
      {
        pose proof (Properties.map.get_split i _ _ _ H0).
        rewrite !Hget in H1.
        rewrite !H in H1.
        basic_utils_crush.
        rewrite Properties.map.split_comm.
        unfold map.split in *.
        intuition subst.
        {
          rewrite Properties.map.putmany_comm; auto.
          apply Properties.map.put_putmany_commute.
        }
        {
          unfold map.disjoint in *.
          intros.
          eapply H4 with (k:=k); eauto.
          pose proof (eqb_spec i k); destruct (eqb i k); subst; eauto.
          basic_utils_crush.
        }
      }
    Qed.

    
    Lemma sep_ptsto_put (x1 : idx_map) i j (Q : _ -> Prop)
      : map.get x1 i = None -> Q x1 -> sep Q (ptsto i j) (map.put x1 i j).
    Proof.
      intros.
      unfold sep.
      exists x1, (map.singleton i j).
      basic_utils_crush.
    Qed.

    
    Lemma disjoint_put_r x1 x5 (i i0 : idx)
      : map.disjoint x1 (map.put x5 i i0) -> map.disjoint x1 x5.
    Proof.
      unfold map.disjoint.
      intros.
      eapply H; eauto.
      instantiate (1:=if eqb i k then i0 else v2).
      pose proof (eqb_spec i k); destruct (eqb i k);[ subst i |];
        basic_utils_crush.
    Qed.
    
    Lemma forest_ptsto_put r i j
      : i<>j ->
        forest_ptsto j r ->
        forest_ptsto j (map.put r i j).
    Proof.
      intros.
      my_case Hget (map.get r i).
      2:{
        eapply forest_join.
        exists (map.put map.empty i j), r;
          basic_utils_crush.
        eapply split_put_left; eauto.
        eapply Properties.map.split_empty_l.
        auto.
      }
      {
        revert H Hget.
        induction H0;
          basic_goal_prep;
          basic_utils_crush.
        {
          unfold and1 in *;
            destruct H as [? [? [? ?] ] ]; break.
          pose proof (Properties.map.get_split i _ _ _ H).
          eapply forest_join.
          
          basic_utils_crush.
          {
            rewrite Hget in H5.
            symmetry in H5; apply H6 in H5.
            exists (map.put x i i1), x0;
              basic_utils_crush.
            eapply split_put_left; eauto.
          }
          {
            rewrite Hget in H5.
            symmetry in H5.
            specialize (H4 H5).
            exists x, (map.put x0 i i1);
              basic_utils_crush.
            eapply Properties.map.split_comm.
            eapply split_put_left; eauto.
            eapply Properties.map.split_comm; eauto.
          }
        }
        {
          pose proof (eqb_spec i i1); destruct (eqb i i1); subst.
          {
            replace (map.put m i1 j) with m.
            {
              apply forest_node with (i:=i1); eauto.
              cancel_prep H0.
              apply sep_consequence;
                basic_goal_prep;
                basic_utils_crush.
              unfold and1 in *.
              intuition subst.
            }
            {
              assert (map.get m i1 = Some j).
              {
                destruct H0 as [?  [? ?] ]; break.
                clear H2.
                
                basic_utils_crush.
              }
              symmetry; eapply Properties.map.put_idemp.
              eauto.
            }
          }
          {
            (*eapply forest_join.*)
            pose proof (distribute_get  _ _ _ _ _ Hget H0).
            destruct H3.
            2:{
              eapply sep_consequence in H3.
              2,3: eauto.
              2:{
                clear.
                unfold and1.
                basic_goal_prep.
                instantiate (1:= lift False).
                basic_utils_crush.
              }
              basic_utils_crush.
            }
            {
              clear H0.
              eapply sep_consequence in H3.
              2,4: eauto.
              2:{
                unfold and1; basic_goal_prep.
                clear H5.
                eapply forest_ptsto_split in H0; [|eauto].
                instantiate (1:= and1 (seps [forest_ptsto i; ptsto i i0; forest_ptsto i1]) ( not1 (has_key j))).
                unfold and1; eauto.
              }
              seprewrite.
              unfold and1, seps in H3.
              unfold sep in H3; break.
              eapply forest_join.
              repeat (break; subst; autorewrite with utils in *; eauto; try typeclasses eauto).
              exists (map.put x1 i j), (map.put x5 i1 j).
              basic_utils_crush.
              2:{
                eapply forest_node with (i:=i); eauto.
                basic_utils_crush.
                apply sep_ptsto_put; basic_utils_crush.
                unfold and1; basic_utils_crush.
                eapply Properties.map.get_split with (k:=j)  in H3.
                basic_utils_crush.
                congruence.
              }
              2:{
                eapply forest_node with (i:=i1); eauto.
                apply sep_ptsto_put; basic_utils_crush.
                unfold and1; basic_utils_crush.
                eapply Properties.map.get_split with (k:=j)  in H3.
                basic_utils_crush.
                congruence.
              }
              {
                revert H3.
                unfold map.split; basic_goal_prep; basic_utils_crush.
                2:{
                  unfold map.disjoint in *.
                  intros.
                  epose proof (eqb_spec i k); destruct (eqb i k); subst;
                    epose proof (eqb_spec i1 k); destruct (eqb i1 k); subst;
                    basic_utils_crush.
                  {
                    eapply H7; eauto.
                    basic_utils_crush.
                  }
                  {
                    pose proof (Properties.map.putmany_spec  x1 (map.put x5 i i0) k).
                    firstorder congruence.
                  }
                  {
                    pose proof (Properties.map.putmany_spec  x1 (map.put x5 i i0) k).
                    destruct H12; break.
                    1:firstorder congruence.
                    rewrite map.get_put_diff in H12 by eauto.
                    congruence.
                  }
                }
                {
                  rewrite <- !Properties.map.put_putmany_commute.
                  rewrite (Properties.map.putmany_comm (map.put x1 i j)).
                  {
                    rewrite <- !Properties.map.put_putmany_commute.
                    rewrite Properties.map.putmany_comm.
                    {
                      rewrite Properties.map.put_put_diff by eauto.
                      rewrite Properties.map.put_put_same.
                      reflexivity.
                    }
                    {
                      eapply disjoint_put_r; eauto.
                    }
                  }
                  {
                    unfold map.disjoint in *.
                    intros.
                    pose proof (eqb_spec i k); destruct (eqb i k);[ subst i |];
                      basic_utils_crush.
                    {
                      eapply H7; eauto.
                      basic_utils_crush.
                    }
                    {
                      eapply H7; eauto.
                      basic_utils_crush.
                    }
                  }
                }
              }
            }
          }
        }
      }
    Qed.

    Hint Rewrite Properties.map.put_put_same : utils.
    Lemma tree_put r i j
      : tree j r ->
        tree j (map.put r i j).
    Proof.
      pose proof (eqb_spec i j); destruct (eqb i j);[ subst i |].
      {
        intro H.
        replace (map.put r j j) with r; eauto.
        unfold tree in *.
        unfold sep in H; break.
        
        basic_utils_crush.
      }
      {
        unfold tree, sep; basic_goal_prep.
        exists (map.put x i j), x0.
        basic_utils_crush.
        {
          rewrite Properties.map.put_put_diff by eauto.
          auto.
        }
        {
          eapply forest_ptsto_put; eauto.
        }
      }
    Qed.
    Hint Resolve tree_put : utils.

    Hint Rewrite map.get_remove_same : utils.
    Hint Rewrite map.get_remove_diff using congruence : utils.
    
    Lemma disjoint_put_remove (x x0 : idx_map) i j
      : map.disjoint x x0 ->
        map.disjoint (map.put x i j) (map.remove x0 i).
    Proof.
      unfold map.disjoint.
      basic_goal_prep.
      eqb_case i k;
        basic_utils_crush.
    Qed.
      
    Lemma split_put_put_remove (r x x0 : idx_map) i j
      :  map.split r x x0 ->
         map.split (map.put r i j) (map.put x i j) (map.remove x0 i).
    Proof.
      unfold map.split.
      basic_goal_prep; subst.
      split.
      {
        rewrite Properties.map.putmany_comm; eauto.
        rewrite Properties.map.put_putmany_commute.
        rewrite Properties.map.putmany_comm with (x:= map.put x i j).
        2:{
          eapply disjoint_put_remove; eauto.
        }
        rewrite <-! Properties.map.put_putmany_commute.
        eapply map.map_ext; intros.
        eqb_case i k;
          basic_utils_crush.
        rewrite !Properties.map.get_putmany_dec.
        case_match; eauto.
        basic_utils_crush.
      }
      {
        eapply disjoint_put_remove; eauto.        
      }
    Qed.

    
    Lemma get_of_sep_l P1 P2 (m : idx_map) i j
      : sep P1 P2 m ->
        (forall m', P1 m' -> map.get m' i = Some j) ->
        map.get m i = Some j.
    Proof.
      basic_goal_prep.
      destruct H; break.
      eapply H0 in H1.
      basic_utils_crush.
      eapply Properties.map.get_split_grow_r; eauto.
    Qed.
    
    Lemma get_of_seps L P (m : idx_map) i j
      : seps L m ->
        In P L ->
        (forall m', P m' -> map.get m' i = Some j) ->
        map.get m i = Some j.
    Proof.
      revert m;
      induction L;
        repeat change (seps (?a::?l)) with (sep a (seps l)) in *;
        basic_goal_prep;
        basic_utils_crush.
      {
        eapply get_of_sep_l in H; eauto.
      }
      {
        eapply sep_comm in H; eauto.
        eapply get_of_sep_l in H; eauto.
      }
    Qed.

    
    Lemma forest_notin l m a
      : ~ has_key a m -> forest l m -> ~ In a l.
    Proof.
      enough (and1 (not1 (has_key a)) (forest l) m -> ~ In a l).
      { unfold and1, not1 in *; intuition fail. }
      unfold forest.
      revert m.
      induction l; basic_goal_prep;
        basic_utils_crush.
      {
        intros.
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        apply distribute_not_has_key in H.
        destruct H; break.

        clear H1 IHl.
        unfold tree, sep, and1, not1, has_key in *.
        revert H0; case_match; intuition break.
        basic_utils_crush.
      }
      {
        intros.
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        apply distribute_not_has_key in H.
        destruct H; break.
        eapply and1_comm in H2.
        eauto.
      }
    Qed.
          
    
    Lemma forest_no_dup l m
      : forest l m -> NoDup l.
    Proof.
      unfold forest.
      revert m.
      induction l; basic_goal_prep;
        constructor;
        basic_utils_crush.
      {
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        unfold sep in *; break.
        eapply forest_notin; eauto.
        unfold has_key.
        case_match; try tauto.
        exfalso.
        unfold tree, sep in H1; break; basic_utils_crush.
        eapply Properties.map.get_split with (k:=a) in H; destruct H; intuition try congruence.
        basic_utils_crush.
      }
      {
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        unfold sep in *; break.
        eauto.
      }
    Qed.

    
          
  Lemma tree_split i m
    : tree i m -> forall j k, map.get m j = Some k -> j <> i -> seps [forest_ptsto j; ptsto j k; tree i] m.
  Proof.
    unfold tree.
    intros.
    rewrite sep_to_seps' in H.
    enough (seps [(and1 (forest_ptsto i) (fun m => map.get m j = Some k)); ptsto i i] m).
    {
      clear H.
      cancel_prep' H2.
      rewrite seps_Uiff1_cons_sep; eauto.
      sep_focus' [1] [3]; [reflexivity|].
      intros m H.
      simple eapply forest_ptsto_split.
      { unfold and1, seps in *; seprewrite; intuition subst. }
      { unfold and1, seps in *; seprewrite; intuition subst. }
    }
    {
      eapply distribute_get in H; eauto.
      destruct H;
        basic_goal_prep;
        unfold seps;
        seprewrite;
        basic_utils_crush.
      exfalso.
      seprewrite.
      eapply sep_assoc in H; eauto.
      basic_utils_crush.
    }
  Qed.
  
    Lemma forest_split m i l j
      : ~ In i l ->
        map.get m i = Some j ->
        (forest l) m ->
        seps [forest_ptsto i; ptsto i j; (forest l)] m.
    Proof.
      unfold forest.
      revert m; induction l;
        basic_goal_prep;
        seprewrite.
      {
        seprewrite.
        basic_utils_crush.
      }
      {
        repeat change (seps (?a::?l)) with (sep a (seps l)) in *.
        eapply distribute_get in H1; eauto; destruct H1.
        {
          clear H0.
          unfold sep in H1; break.
          eapply sep_assoc; eauto.
          eapply sep_comm; eauto.
          eapply sep_assoc; eauto.
          eapply sep_comm; eauto.
          eapply sep_assoc; eauto.
          exists x0, x; basic_utils_crush.
          1: eapply Properties.map.split_comm; eauto.
          rewrite sep_to_seps'.
          seprewrite.
          sep_isolate.
          rewrite <- ptsto_inv.
          unfold and1,sep_app in *.
          break.
          eapply tree_split; eauto.
        }
        {
          eapply sep_assoc; eauto.
          eapply sep_comm; eauto.
          eapply sep_assoc; eauto.
          destruct H1; unfold and1 in H1; break.
          exists x, x0; basic_utils_crush.
          eapply IHl in H4; eauto.
          rewrite sep_to_seps' in *.
          cancel_prep' H4.
          seprewrite.
          rewrite (seps_permutation _ _ _ _ _ _ _ (Permutation_app_comm _ _)).
          reflexivity.
        }
      }
    Qed.

     Lemma forest_ptsto_no_cycle (m : idx_map) k i
      : forest_ptsto k m ->
        ~ map.get m i = Some i.
      induction 1; basic_goal_prep;
        basic_utils_crush.
      {
        eapply sep_get_split in H; eauto.
        destruct H; unfold sep, and1 in *; break;
          basic_utils_crush.
      }
      {
        eapply sep_get_split in H0; eauto.
        destruct H0; unfold sep, and1 in *; break;
          basic_utils_crush.
      }
    Qed.

    Lemma tree_cycle (m : idx_map) k i
      : tree k m ->
        map.get m i = Some i ->
        i = k.
    Proof.
      unfold tree.
      intros.
      eapply sep_get_split in H; eauto.
      destruct H; unfold sep, and1 in *; break;
        basic_utils_crush.
      exfalso.
      eapply forest_ptsto_no_cycle; eauto.
    Qed.
    
    Lemma forest_root_iff i l m
      : forest l m -> In i l <-> map.get m i = Some i.
    Proof.
      unfold forest;
        revert m;
        induction l;
        basic_goal_prep.
      {
        basic_utils_crush.
      }
      {
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        eqb_case a i.
        {
          split; try now intuition eauto.
          intros.
          clear H0.
          eapply get_of_sep_l; eauto.
          intros; unfold tree in *.
          eapply sep_comm in H0; eauto.
          eapply get_of_sep_l; eauto.
          intros; basic_utils_crush.
        }
        etransitivity.
        {
          instantiate (1:= In i l);
            basic_utils_crush.
        }
        unfold sep in H; break.
        pose proof H2.
        apply IHl in H2.
        rewrite H2.
        clear H2 IHl.
        eapply Properties.map.get_split with (k:=i) in H.

        destruct H.
        {
          break.
          rewrite H, H2.
          autorewrite with utils.
          my_case Hget (map.get x i); try intuition congruence.
          eqb_case i i0; try intuition congruence.
          
          exfalso.
          eapply tree_cycle in H1; eauto.
        }
        {
          break.
          rewrite H.
          reflexivity.
        }
      }
    Qed.

    
    Lemma tree_join j m
      : sep (tree j) (forest_ptsto j) m -> tree j m.
    Proof.
      unfold tree.
      rewrite !sep_to_seps' in *.
      intro H;
        cancel_prep' H.
      seprewrite.
      sep_focus' [1] [1]; [reflexivity|].
      intros m H; cbv [seps] in *;
      seprewrite.
      apply forest_join; eauto.
    Qed.

    
    Lemma not_put_put_same (m : idx_map) j x3 x1 i1 i2
      :  ~ map.split m (map.put x3 j i1) (map.put x1 j i2).
    Proof.
      unfold map.split.
      intro; break.
      subst.
      unfold map.disjoint in *.
      eapply H0 with (k:=j);
        basic_utils_crush.
    Qed.
    
    (* could be reformulated w/out the separate 'tree' in the input, but this is the form we use it in anyway *)
    Lemma forest_put r i j l
      : ~ In i l ->
        sep (tree j) (forest l) r ->
        sep (tree j) (forest l) (map.put r i j).
    Proof.
      intros Hnin ?.
      my_case Hget (map.get r i).
      1: eapply distribute_get in H; eauto; destruct H.
      {
        clear Hget.
        unfold sep, and1 in *.
        break.
        exists (map.put x i j), x0.
        basic_utils_crush.
        eapply split_put_left; eauto.
        eapply Properties.map.get_split with (k:=i) in H;
          intuition congruence.
      }
      {
        eqb_case i i0.
        {
          exfalso; apply Hnin.
          unfold sep,and1 in *; break.
          rewrite forest_root_iff; [|eauto]; eauto.
        }
        {
          rename Hnin into H1.
          eapply sep_consequence in H.
          2,3: eauto.
          2:{
            clear; intros.
            unfold and1 in *; break.
            eapply forest_split; eauto.
          }
          seprewrite.
          cbv [seps] in *.

          

          
          rewrite sep_to_seps' in *.
          seprewrite.

          enough (seps [tree j; forest_ptsto i; eq (map.singleton i j); forest l]  (map.put r i j)).
          {
            clear H.
            revert H2.
            generalize ((map.put r i j)); intros.
            cancel_prep' H2.
            
            sep_focus' [3] [1]; [reflexivity|].
            intros m H.
            cbv [seps] in *.
            
            seprewrite.
            eapply tree_join.
            assert (i <> j).
            {
              clear Hget.
              unfold tree in *.
              seprewrite.
              unfold sep in *;
                break;
                basic_utils_crush.
              eapply not_put_put_same; eauto.
            }
            enough (sep (tree j) (sep (and1 (forest_ptsto i) (not1 (has_key j))) (eq (map.singleton i j))) m).
            {
              clear H.
              eapply sep_consequence; try eassumption; eauto.
              intros.
              eapply forest_node with (j:=j); eauto.
              eapply sep_consequence; try eassumption; eauto.
              intros; seprewrite; eauto.
            }
            {
              assert (map.get m j = Some j).
              {
                eapply get_of_sep_l; eauto.
                intros.
                clear H;
                  unfold tree in *.
                seprewrite.
                basic_utils_crush.
                eapply sep_comm in H3; eauto.
                eapply get_of_sep_l; eauto.
                intros.
                basic_utils_crush.
              }
              eapply sep_get_split' in H; eauto.
              destruct H.
              2:{
                exfalso.
                unfold and1, tree, sep in *.
                break; subst.
                basic_utils_crush.
              }
              {              
                eapply sep_consequence; try eassumption;
                  intros;
                  seprewrite.
                1:unfold and1 in *; break; eauto.
                eapply and1_comm in H4.
                eapply distribute_not_has_key in H4.
                eapply sep_consequence; try eassumption;
                  intros;
                  seprewrite; subst; eauto.
                clear H H4.
                unfold and1 in *;
                  basic_utils_crush.
              }
            }
          }
          {
            unfold seps, sep in *; break.
            repeat (break; subst; autorewrite with utils in *; eauto ; try typeclasses eauto;[]).
            do 2 eexists; intuition try eassumption.
            2:{
              do 2 eexists; split; [|intuition try eassumption].
              2:{
                do 2 eexists; split; [|intuition try eassumption].
                2:{
                  do 2 eexists; split; [|intuition try eassumption].
                  2:basic_utils_crush.                
                  basic_utils_crush.
                  apply eqb_boolspec;eauto.
                }       
                basic_utils_crush.
              }
              instantiate (1:= (map.put x0 i j)).
              eapply Properties.map.split_comm.
              replace (map.put x5 i j) with (map.put (map.put x5 i i0) i j) by basic_utils_crush.
              eapply split_put_left.
              {
                eapply Properties.map.get_split with (k:=i) in H3;
                  destruct H3;
                  break;
                  basic_utils_crush.
              }
              {
                eapply Properties.map.split_comm; eauto.              
              }
            }
            eapply Properties.map.split_comm; eauto.  
            eapply split_put_left; eauto.
            {
              eapply Properties.map.get_split with (k:=i) in H;
                destruct H;
                break;
                basic_utils_crush.
              exfalso.
              erewrite Properties.map.get_split_grow_l in H6; eauto;
                basic_utils_crush.
            }
            
            eapply Properties.map.split_comm; eauto.
          }
        }
      }
      {
        unfold sep in H; break.
        exists (map.put x i j), x0;
          basic_utils_crush.
        eapply split_put_left; eauto.
        eapply Properties.map.get_split with (k:=i) in H.
        intuition try congruence.
      }
    Qed.
    
    
    
    Lemma find_aux_spec' mr f i f' j k
      :  tree k f ->
         find_aux' mr f i = Some (f', j) ->
         j = k /\ tree j f'.
    Proof.    
      revert f i f' j.
      induction mr;
        basic_goal_prep; [congruence|].
      revert H0; case_match; [|congruence].
      case_match; autorewrite with bool inversion utils in *;
        subst.
      {
        basic_goal_prep; subst.
        pose proof H.
        eapply tree_cycle in H; eauto; subst.
        intuition subst.
      }
      {
        case_match; [| congruence].
        basic_goal_prep.
        autorewrite with bool inversion utils in *; basic_goal_prep;
          subst.
        eapply IHmr in  case_match_eqn1; eauto.
        basic_goal_prep; subst.
        eauto using tree_put.
      }
    Qed.



    Hint Resolve Properties.map.same_domain_refl : utils.
    
    Lemma find_aux_domain mr f i f' j
      : find_aux' mr f i = Some (f', j) ->
        map.same_domain f f'.
    Proof.
      revert f f' i j.
      induction mr;
        basic_goal_prep.
      { basic_utils_crush. }
      {
        revert H; case_match; [|congruence].
        eqb_case i0 i.
        1: basic_goal_prep; basic_utils_crush.
        case_match; [|congruence].
        break.
        basic_utils_crush.
        apply IHmr in  case_match_eqn0.
        eapply Properties.map.same_domain_trans; eauto.
        assert (has_key i r).
        {
          unfold has_key; case_match; eauto.
          clear IHmr.
          unfold map.same_domain, map.sub_domain in *; break.
          eapply H0 in case_match_eqn.
          break.
          congruence.
        }
        unfold has_key in*.
        revert H0; case_match;[|tauto].
        intros _.
        eapply Properties.map.same_domain_put_r; eauto with utils.
      }
    Qed.


    Lemma sep_get_some_r P Q (m : idx_map) i j
      : sep P Q m ->
        (forall m', Q m' -> map.get m' i = Some j) ->
        map.get m i = Some j.
    Proof.
      destruct 1 as [? [? [? [? ?] ] ] ].
      intro HQ.
      eapply HQ in H1.
      eapply Properties.map.get_split_grow_l; eauto.
    Qed.
    
    Lemma find_aux_frame mr f i f' j Q f_Q
      :  sep Q (eq f) f_Q ->
         find_aux' mr f i = Some (f', j) ->
         exists f'_Q, find_aux' mr f_Q i = Some (f'_Q, j) /\ sep Q (eq f') f'_Q.
    Proof.
      revert f f' i j f_Q.
      induction mr;
        basic_goal_prep.
      { basic_utils_crush. }
      {
        revert H0.
        case_match; [|congruence].
        replace ( map.get f_Q i) with (Some i0).
        2:{
          my_case Hget (map.get f_Q i).
          {
            eapply sep_get_split' in H; eauto.
            destruct H; unfold sep, and1 in *;
              basic_goal_prep;
              basic_utils_crush;
              congruence.
          }
          {
            assert (and1 (not1 (has_key i)) (sep Q (eq f)) f_Q).
            {
              split; eauto.
              unfold has_key, not1.
              case_match;
                basic_utils_crush.
            }
            apply distribute_not_has_key in H0.
            clear H.
            unfold sep, and1, not1, has_key in H0.
            basic_goal_prep;
              basic_utils_crush.
            rewrite case_match_eqn in H2.
            tauto.
          }
        }
        {
          eqb_case i0 i.
          {
            basic_goal_prep;
              basic_utils_crush.
          }
          {
            case_match; [|congruence].
            break.
            basic_goal_prep;
              basic_utils_crush.
            (* assert (map.get f_Q i = Some i0) as HgetQ.
          {
            eapply sep_get_some_r; eauto.
            basic_goal_prep; subst.
            eauto.
          }*)
            pose proof case_match_eqn0  as Heqaux.
            eapply IHmr in case_match_eqn0 ; eauto.
            break.
            exists (map.put x i j).
            rewrite H1.
            basic_utils_crush.
            
            
            clear IHmr H.
            unfold sep in *.
            break; subst.
            do 2 eexists; intuition eauto.
            apply Properties.map.split_comm.
            apply split_put_left.
            {
              apply find_aux_domain in Heqaux.
              destruct Heqaux.
              unfold map.sub_domain in *.
              eapply H3 in case_match_eqn.
              break.
              apply Properties.map.get_split with (k:=i) in H;
                intuition congruence.
            }
            {
              eapply Properties.map.split_comm; eauto.
            }
          }
        }
      }
    Qed.



    Lemma forest_cycle (m : idx_map) l i
      : forest l m ->
        map.get m i = Some i ->
        In i l.
    Proof.
      unfold forest.
      revert m i; induction l;
        basic_goal_prep;
        basic_utils_crush.
      change (seps (?a::?l)) with (sep a (seps l)) in H.    
      eapply distribute_get in H; eauto.
      destruct H; [left | right].
      {
        unfold and1, sep in *; break.
        symmetry;
          eapply tree_cycle; eauto.
      }
      {
        unfold and1, sep in *; break.
        eapply IHl; eauto.
      }
    Qed.

    Lemma find_aux_in l mr f i f' j
      :  forest l f ->
         find_aux' mr f i = Some (f', j) ->
         In j l.
    Proof.    
      revert f f' i j.
      induction mr;
        basic_goal_prep;
        [congruence|].
      revert H0; case_match; [|congruence].
      eqb_case i0 i.
      {
        basic_goal_prep;
          basic_utils_crush.
        eapply forest_cycle; eauto.
      }
      {
        case_match; [|congruence].
        break.
        intros; basic_utils_crush.
      }
    Qed.

    Lemma in_forest_split j l m
      : In j l ->
        forest l m ->
        exists l1 l2,
          l = l1++j::l2 /\
            sep (tree j) (forest (l1++l2)) m.
    Proof.
      revert m.
      unfold forest.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      {
        exists [], l.
        basic_utils_crush.
      }
      {
        change (seps (?a::?l)) with (sep a (seps l)) in H0.
        unfold sep in H0; break.
        eapply IHl in H2; eauto.
        break.
        exists (a::x1), x2.
        subst.
        split.
        1:basic_utils_crush.
        cbn.
        change (seps (?a::?l)) with (sep a (seps l)).
        eapply sep_comm; eauto.      
        eapply sep_assoc; eauto.
        clear H1.
        exists x, x0; basic_utils_crush.
        seprewrite.
        eauto.
      }
    Qed.

    Hint Rewrite map.get_remove_same Properties.map.put_remove_same : utils.

    
    Lemma tree_singleton j : tree j (map.singleton j j).
    Proof.
      unfold tree.
      exists map.empty; eexists;
        basic_utils_crush.
    Qed.
    Hint Resolve tree_singleton : utils.

    Hint Rewrite map.get_remove_diff using congruence : utils.
    
    Lemma split_put_remove (i i0 : idx) f x x0
      : Some i0 = map.get f i ->
        map.split f x x0 ->
        map.split f (map.put x i i0) (map.remove x0 i).
    Proof.
      intros.
      enough (map.disjoint (map.put x i i0) (map.remove x0 i)).
      {
        unfold map.split in *;
          basic_goal_prep.
        basic_utils_crush.
        rewrite Properties.map.putmany_comm with (x:=(map.put x i i0)) by eauto.
        rewrite <- Properties.map.put_putmany_commute.
        eapply map.map_ext.
        intros.
        eqb_case k i;
          basic_utils_crush.
        rewrite Properties.map.putmany_comm by eauto.
        rewrite !Properties.map.get_putmany_dec.
        case_match; basic_utils_crush.
      }
      {
        unfold map.split in *;
          basic_goal_prep.
        eauto using disjoint_put_remove.
      }
    Qed.


    
    Lemma get_singleton_same
      : forall (k v : idx), map.get (map.singleton k v) k = Some v.
    Proof.
      unfold map.singleton; basic_utils_crush.
    Qed.
    Hint Rewrite get_singleton_same : utils.
    Hint Rewrite map_keys_in' : utils.
    
    Definition reachable (m : idx_map) := equivalence_closure (fun i j => map.get m i = Some j).
    
    Lemma forest_ptsto_next k x i i0
      : forest_ptsto k x -> Some i0 = map.get x i -> k = i0 \/ has_key i0 x.
    Proof.
      intro H; revert i i0; induction H;
        basic_goal_prep; basic_utils_crush.
      {
        eapply distribute_get in H; eauto.
        destruct H; unfold sep, and1 in *; break.
        1: symmetry in H4; eapply H5 in H4.
        2: symmetry in H3; eapply H4 in H3.
        all: intuition eauto using split_has_key_l, split_has_key_r.
      }
      {
        eapply distribute_get in H0; eauto.
        destruct H0; unfold sep, and1 in *; break;
          basic_utils_crush.
      }
    Qed.
    
    Lemma tree_next k x i i0
      : tree k x -> Some i0 = map.get x i -> has_key i0 x.
    Proof.
      eqb_case i i0.
      {
        unfold has_key.
        intros _ H; rewrite <- H; eauto.
      }    
      unfold tree; basic_goal_prep.
      eapply distribute_get in H0; eauto.
      unfold sep, and1 in *; basic_goal_prep.
      destruct H0; basic_goal_prep;
        basic_utils_crush.
      eapply forest_ptsto_next in H2; eauto.
    Qed.

    
    Lemma find_aux_spec'' mr l k f i f' j
      : sep (and1 (tree k) (has_key i)) (forest l) f ->
        find_aux' mr f i = Some (f', j) ->
        j = k /\ forest (k::l) f'.
    Proof.
      revert k l f i f' j.
      induction mr;
        basic_goal_prep; [congruence|].
      revert H0; case_match; [|congruence].
      case_match; autorewrite with bool inversion utils in *;
        subst.
      {
        basic_goal_prep; subst.
        split.
        {
          unfold and1, sep, has_key in H; break.
          eapply tree_cycle; eauto.
          eapply Properties.map.get_split with (k:=j) in H.
          destruct H; break; try congruence.
          rewrite H3 in H2.
          exfalso.
          eauto.
        }
        {
          unfold forest in *.
          cbn [map].
          eapply sep_consequence in H.
          2,4: eauto.
          2:{
            unfold and1.
            intros.
            break.
            exact H0.
          }
          
          seprewrite.
          eauto.
        }
      }
      {
        case_match; [| congruence].
        basic_goal_prep.
        autorewrite with bool inversion utils in *; basic_goal_prep;
          subst.
        eapply IHmr with (k:=k) (l:=l)in case_match_eqn1; eauto.
        2:{
          unfold sep, and1 in *; break.
          exists x, x0; intuition eauto.
          basic_goal_prep; subst.
          eapply tree_next with (i:=i); eauto.
          eapply Properties.map.get_split with (k:=i) in H; eauto.
          unfold has_key in H2.
          revert H2; case_match; try tauto.
          intros _.
          destruct H;
            basic_utils_crush.
          congruence.
        }
        {
          basic_goal_prep; split; auto; subst.
          unfold forest in *.
          cbn in *.
          change (seps (?P :: ?L)) with (sep P (seps L)) in *.
          eapply forest_put; eauto.
          unfold and1,sep in H; break.
          rewrite forest_root_iff; eauto.
          intro.
          unfold has_key in H3.
          revert H3; case_match; try congruence.
          eapply Properties.map.get_split with (k:= i) in H;
            intuition congruence.
        }
      }
    Qed.

    (*TODO: move to Bool*)
    Lemma negb_true : negb true = false.
    Proof. reflexivity. Qed.
    Hint Rewrite negb_true : utils.
    
    Lemma forest_has_key_tree i f l j
      : map.get f i = Some j ->
        forest l f ->
        exists k, In k l /\ sep (and1 (tree k) (has_key i))
                              (forest (List.removeb (@eqb _ _) k l))
                              f.
    Proof.
      intros H1 H2.
      assert (NoDup l) by eauto using forest_no_dup.
      revert f j H H1 H2.
      unfold forest.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      
      change (seps (?P :: ?L)) with (sep P (seps L)) in *.
      destruct H2; break.
      my_case Hget (map.get x i).
      {
        exists a; split;[intuition eauto | exists x, x0]; unfold and1, has_key.
        rewrite Hget.
        basic_utils_crush.
        safe_invert H.
        replace (List.removeb (eqb (A:=idx)) a l) with l; eauto.
        rewrite List.removeb_not_In; eauto.
      }
      {
        eapply Properties.map.get_split_r in H1; eauto.
        safe_invert H.
        eapply IHl in H1; eauto.
        break.
        exists x1; split; eauto.
        destruct H1; break.
        exists x2, (map.putmany x x3).
        split; [eapply map_split_3_ways; eauto|unfold and1..].
        replace (eqb x1 a) with false;
          cbn.
        2:{
          basic_utils_crush.
        }
        clear IHl; unfold and1 in *;
          basic_utils_crush.
        exists x, x3;
          basic_utils_crush.
        unfold map.split;
          basic_utils_crush.
        eapply Properties.map.disjoint_comm.
        eapply Properties.map.shrink_disjoint_l; eauto.
        2: eapply Properties.map.split_comm;eauto.
        eapply Properties.map.disjoint_comm.
        eapply split_disjoint; eauto.
      }
    Qed.     
    
    Lemma find_aux_reachable_out k l mr f i f' j
      : sep (and1 (tree k) (has_key i)) (forest l) f ->
        find_aux' mr f i = Some (f', j) ->
        reachable f i j.
    Proof.
      revert f f' i j.
      induction mr;
        basic_goal_prep; [ congruence|].
      revert H0; case_match;[|congruence].
      eqb_case i0 i.
      {
        intros; basic_utils_crush.
        eapply  eq_clo_base; eauto.
      }
      {
        case_match; [|congruence].
        break.
        intros.
        safe_invert H1.
        eapply IHmr in case_match_eqn0.
        {
          break.
          eapply eq_clo_trans; eauto.
          eapply eq_clo_base; eauto.
        }
        eapply distribute_get in H; eauto.
        destruct H.
        {
          eapply sep_consequence;[| | | eauto]; eauto.
          unfold and1; basic_goal_prep.
          intuition subst.
          symmetry in H2; eapply tree_next in H2; eauto.
        }
        {
          exfalso.
          clear IHmr.
          unfold sep, and1 in *;
            break.
          eapply Properties.map.get_split with (k:=i) in H; eauto.
          destruct H; break; try congruence.
          unfold has_key in H4.
          rewrite H5 in H4; eauto.
        }
      }
    Qed.

    Lemma reachable_empty j k
      : reachable map.empty j k <-> j = k.
    Proof.
      unfold reachable.
      intuition (subst; eauto with utils).
      induction H;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite reachable_empty : utils.

    Hint Rewrite has_key_empty : utils.

    Add Parametric Relation m : idx (reachable m)
        reflexivity proved by (eq_clo_refl _)
        symmetry proved by (eq_clo_sym _)
        transitivity proved by (eq_clo_trans _)
        as reachable_rel.

    Instance split_l_reachable_subrelation
      m m_l m_r (_ : map.split m m_l m_r)
      : subrelation (reachable m_l) (reachable m).
    Proof.
      unfold reachable, subrelation.
      induction 1; basic_goal_prep;
        basic_utils_crush.
      eapply eq_clo_base.
      eapply Properties.map.get_split_grow_r; eauto.
    Qed.
    
    Instance split_r_reachable_subrelation
      m m_l m_r (_ : map.split m m_l m_r)
      : subrelation (reachable m_r) (reachable m).
    Proof.
      unfold reachable, subrelation.
      induction 1; basic_goal_prep;
        basic_utils_crush.
      eapply eq_clo_base.
      eapply Properties.map.get_split_grow_l; eauto.
    Qed.

    
    Lemma has_key_split m (x x0 : idx_map) (i:idx)
      : map.split m x x0 ->
        has_key i m <-> has_key i x \/ has_key i x0.
    Proof.
      intros.
      unfold has_key.
      case_match; intuition idtac.
      {
        eapply Properties.map.get_split with (k:=i) in H; eauto.
        destruct H; [ left | right]; break;
          case_match;
          basic_utils_crush;
          congruence.
      }
      {
        revert H1; case_match; try tauto.
        eapply Properties.map.get_split with (k:=i) in H; eauto.
        destruct H; break; congruence.
      }
      {
        revert H1; case_match; try tauto.
        eapply Properties.map.get_split with (k:=i) in H; eauto.
        destruct H; break; congruence.
      }
    Qed.

    Lemma reachable_forest_ptsto_head1 i m
      : forest_ptsto i m ->
        forall j, j <> i -> In j (map.keys m) -> reachable m j i.
    Proof.
      induction 1;
        basic_goal_prep.
      { basic_utils_crush. }
      {
        unfold sep, and1 in *; break.
        revert H1.
        rewrite <- map_split_permutation by eauto.
        rewrite in_app_iff.
        destruct 1 as [H' | H']; [eapply H5 in H' | eapply H4 in H']; eauto.
        all:[> eapply split_l_reachable_subrelation; now eauto
            | eapply split_r_reachable_subrelation; now eauto].
      }
      {
        eqb_case j0 i.
        {
          eapply eq_clo_base.
          unfold sep, and1 in *.
          basic_utils_crush.
        }
        {
          unfold not1, sep, and1 in *; break.
          etransitivity.
          2:{
            eapply eq_clo_base with (a:= i).
            basic_utils_crush.
          }
          eapply split_l_reachable_subrelation; eauto.
          eapply H6; eauto.
          basic_utils_crush.
        }
      }
    Qed.
    
    Lemma reachable_forest_ptsto_head2 i m j
      : reachable m j i ->
        forall k,
          forest_ptsto k m ->
          j <> i -> (i <> k -> In i (map.keys m)) /\ (j <> k -> In j (map.keys m)).
    Proof.
      induction 1;
        basic_goal_prep.
      {
        basic_utils_crush.
        2:rewrite H; auto.
        {
          eapply forest_ptsto_has_next in H0; eauto.
          basic_utils_crush.
        }
      }
      { tauto. }
      {
        eqb_case a b; eauto.
        eqb_case b c; eauto.
        specialize (IHequivalence_closure1 _ H1 H3).
        specialize (IHequivalence_closure2 _ H1 H4).
        break.
        intuition subst.
      }
      {
        apply and_comm.
        eauto.
      }
    Qed.
    
    Lemma reachable_forest_ptsto_head i m
      : forest_ptsto i m ->
        forall j, j <> i -> reachable m j i <-> (has_key j m).
    Proof.
      intros.
      enough (reachable m j i <-> In j (map.keys m)).
      {
        etransitivity; eauto.
        basic_utils_crush.
      }
      intuition eauto using reachable_forest_ptsto_head1, reachable_forest_ptsto_head2.
      eapply  reachable_forest_ptsto_head2; eauto.
    Qed.

    
    Lemma reachable_forest_ptsto_head' i m
      : forest_ptsto i m ->
        forall j, reachable m j i <-> (j = i \/ has_key j m).
    Proof.
      intros; eqb_case j i;
        intuition eauto using reachable_forest_ptsto_head with utils;
        try reflexivity.
      {
        right.
        rewrite reachable_forest_ptsto_head in H1; eauto.
      }
      {
        rewrite reachable_forest_ptsto_head; eauto.
      }
    Qed.

    
    Lemma some_has_key m (a b : idx)
      : map.get m a = Some b -> has_key a m.
    Proof.
      unfold has_key; intro H; rewrite H; exact I.
    Qed.
    Hint Resolve some_has_key : utils.
    
    Lemma reachable_forest_ptsto i m
      : forest_ptsto i m ->
        forall j k, reachable m j k <-> j=k \/ ((j=i\/has_key j m) /\ (k=i\/has_key k m)).
    Proof.
      intros.
      split; basic_goal_prep.
      2:{
        rewrite <- !reachable_forest_ptsto_head' in * by eauto.
        destruct H0; subst; [reflexivity|].
        break.
        etransitivity; eauto; symmetry; eauto.
      }
      {
        induction H0; basic_goal_prep.
        {
          eqb_case a b;[basic_utils_crush| right].
          eapply forest_ptsto_next in H; eauto.
          destruct H; subst; basic_utils_crush.
        }
        { basic_utils_crush. }
        {
          eqb_case a c; [intuition subst|right].
          destruct IHequivalence_closure1;
            destruct IHequivalence_closure2; subst;
            intuition idtac.
        }
        
        {
          intuition congruence.
        }
      }
    Qed.

    Lemma reachable_loop_iff m j
      : map.get m j = None -> forall a b, reachable (map.put m j j) a b <-> reachable m a b.
    Proof.
      intros.
      split; intro H'; induction H';
        basic_goal_prep;
        basic_utils_crush.
      all: try reflexivity.
      all: try now (etransitivity; eauto).
      {
        eqb_case j a;
          basic_utils_crush.
        1:reflexivity.
        {
          eapply eq_clo_base; eauto.
        }
      }
      {
        eapply eq_clo_base;
          basic_utils_crush.
      }
    Qed.
    
    Lemma reachable_tree i j m k
      : tree k m -> reachable m j i <-> j = i \/ (has_key j m /\ has_key i m).
    Proof.
      unfold tree.
      intros.
      unfold sep in H; break;
        repeat (autorewrite with bool utils in *; break; subst).
      rewrite reachable_loop_iff by eauto.
      rewrite  reachable_forest_ptsto by eauto.
      basic_utils_crush.
    Qed.

    Lemma forest_next l x i i0
      : forest l x -> Some i0 = map.get x i -> has_key i0 x.
    Proof.
      revert x.
      unfold forest;
        induction l;
        basic_goal_prep;
        basic_utils_crush.
      change (seps (?a::?l)) with (sep a (seps l)) in *.
      eapply distribute_get in H; eauto.
      clear H0.
      unfold sep, and1 in H;
        destruct H; break.
      {
        eapply split_has_key_l; eauto.
        eapply tree_next; eauto.
      }
      {
        eapply split_has_key_r; eauto.
      }
    Qed.

    (* basically tree_next *)
    
    Definition closed_graph m :=
      forall a b : idx, map.get m a = Some b -> has_key b m.

    
    Lemma reachable_closed i j m
      : closed_graph m -> reachable m j i -> j = i \/ (has_key j m /\ has_key i m).
    Proof.
      intro.
      induction 1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma split_closed_reachable' m m1 m2 i j
      : map.split m m1 m2 ->
        closed_graph m1 ->
        closed_graph m2 ->
        reachable m i j -> reachable m1 i j \/ reachable m2 i j.
    Proof.
      intros.
      induction H2;
        basic_goal_prep.
      {
        eapply Properties.map.get_split with (k:= a) in H;
          destruct H; break; [left | right]; eapply eq_clo_base;
          congruence.      
      }
      { left; reflexivity. }
      {
        destruct IHequivalence_closure1;
          destruct IHequivalence_closure2;
          try solve [(left + right); etransitivity; eauto].
        all: pose proof H2 as H2'; pose proof H3 as H3'.
        all: apply reachable_closed in H2, H3; eauto.
        all: intuition subst; break.
        all: try (left; reflexivity).
        all: eauto.
        all: exfalso; basic_utils_crush.
        all: eauto using split_both_have_key.
      }
      {
        unfold reachable in *;intuition eauto with utils.
      }
    Qed.

    
    Lemma split_closed_reachable m m1 m2 i j
      : map.split m m1 m2 ->
        closed_graph m1 ->
        closed_graph m2 ->
        reachable m i j <-> reachable m1 i j \/ reachable m2 i j.
    Proof.
      split; eauto using split_closed_reachable'.
      intro H'; destruct H';
        [eapply split_l_reachable_subrelation
        | eapply split_r_reachable_subrelation]; eauto.
    Qed.


    Lemma tree_has_root a x
      : tree a x -> has_key a x.
    Proof.
      unfold tree.
      unfold sep;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Resolve tree_has_root : utils.

    Lemma reachable_forest' l m
      : forest l m ->
        forall i j,
          reachable m i j -> i = j \/ exists k, In k l /\ reachable m i k /\ reachable m j k.
    Proof.
      unfold forest.
      revert m.
      induction l;
        basic_goal_prep;
        repeat (autorewrite with bool utils in*;
                break; subst).
      { basic_utils_crush. }
      {
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        unfold sep in H; break.
        rewrite split_closed_reachable in H0; eauto.
        2: unfold closed_graph; intros; eapply tree_next; eauto.
        2: unfold closed_graph; intros; eapply forest_next; eauto.
        rewrite reachable_tree in * by eauto.
        eqb_case i j; [now intuition idtac|].
        right.
        destruct H0;
          [ exists a| eapply IHl in H0]; eauto.
        {
          intuition break.
          all:[>eapply split_l_reachable_subrelation
              | eapply split_l_reachable_subrelation]; eauto.
          all: eapply reachable_tree; intuition eauto with utils.
        }
        {
          intuition break.        
          exists x1; intuition eauto.
          all:[>eapply split_r_reachable_subrelation
              | eapply split_r_reachable_subrelation]; eauto.
        }
      }
    Qed.

    
    Lemma reachable_forest l m
      : forest l m ->
        forall i j,
          reachable m i j <-> i = j \/ exists k, In k l /\ reachable m i k /\ reachable m j k.
    Proof.
      split; [ apply reachable_forest'; eauto|].
      destruct 1; break; subst; [reflexivity|].
      etransitivity; eauto.
      symmetry; eauto.
    Qed.   
    
    Instance forest_perm_Proper
      : Proper ((@Permutation _) ==> eq ==> iff) forest.
    Proof.
      unfold forest, respectful, Proper; intros; subst.
      revert y0.
      change (seps_Uiff1 (map tree x) (map tree y)).
      induction H;
        basic_goal_prep;
        seprewrite;
        basic_utils_crush.
      { rewrite IHPermutation; reflexivity. }
      {
        unfold seps_Uiff1.
        repeat change (seps (?a::?l)) with (sep a (seps l)) in *.
        rewrite <- sep_assoc; eauto.
        rewrite sep_comm; eauto.
        rewrite <- sep_assoc; eauto.
        rewrite sep_comm; eauto.
        eapply sep_iff1_mor; eauto; [reflexivity|].
        rewrite sep_comm; eauto.
        reflexivity.
      }
      {
        etransitivity; eauto.
      }
    Qed.
    
    Lemma find_auxforest l mr f i f' j
      : (forest l) f ->
        find_aux' mr f i = Some (f', j) -> forest l f'.
    Proof.
      intros.
      my_case Hget (map.get f i).
      2:{
        destruct mr; cbn in*; try congruence.
        rewrite Hget in H0; congruence.
      }
      eapply forest_has_key_tree in Hget; eauto.
      break.
      eapply find_aux_spec'' in H2; eauto.
      break; subst.
      rewrite removeb_perm in H3; eauto with utils.
      eapply forest_no_dup; eauto.
    Qed.

    Lemma find_aux_has_key mr f i f' j
      : find_aux' mr f i = Some (f', j) ->
        has_key i f.
    Proof.
      destruct mr;
        basic_goal_prep;
        try congruence.
      revert H; case_match;[|congruence].
      intros _.
      unfold has_key; rewrite case_match_eqn; auto.
    Qed.
    
    Lemma find_aux_reachable_out' l mr f i f' j
      : forest l f ->
        find_aux' mr f i = Some (f', j) ->
        reachable f i j.
    Proof.
      intros.
      pose proof H0 as H'; eapply find_aux_has_key in H'; eauto.
      revert H'; unfold has_key; case_match; try tauto; intros _.
      eapply forest_has_key_tree in case_match_eqn; eauto; break.
      eapply find_aux_reachable_out in H2; eauto.
    Qed.
    
    Lemma reachable_tree_put r i j
      : tree j r ->
        reachable r i j ->
        forall a b, reachable r a b <-> reachable (map.put r i j) a b.
    Proof.
      intros.
      rewrite !reachable_tree in *; eauto.
      2: eapply tree_put; eauto.
      destruct H0; basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma tree_closed k f : tree k f -> closed_graph f.
    Proof.
      unfold closed_graph; intros; eapply tree_next; eauto.
    Qed.
    Hint Resolve tree_closed : utils.
    
    Lemma forest_closed l f : forest l f -> closed_graph f.
    Proof.
      unfold closed_graph; intros; eapply forest_next; eauto.
    Qed.
    Hint Resolve forest_closed : utils.


    Lemma split_put_left' r x x0 (i j : idx)
      : has_key i x ->
        map.split r x x0 ->
        map.split (map.put r i j) (map.put x i j) x0.
    Proof.
      unfold has_key; case_match; try tauto.
      intros; eapply split_put_left; eauto.
      eapply Properties.map.get_split with (k:=i) in H0; eauto.
      intuition congruence.
    Qed.


    Lemma forest_reachable_in l m i j
      : forest l m ->
        In i l ->
        In j l ->
        reachable m i j ->
        i = j.
    Proof.
      intro H.
      pose proof (forest_no_dup _ _ H).
      revert H H0.
      unfold forest.
      revert m;
        induction l;
        basic_goal_prep.
      { basic_utils_crush. }
      {
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        safe_invert H0.
        unfold sep in *; break.
        eapply split_closed_reachable in H3; eauto with utils.
        rewrite reachable_tree with (m:=x) in * by eauto.
        destruct H1; subst.
        {
          destruct H2; subst; eauto.
          intuition (subst; try congruence).
          {
            exfalso.
            eapply split_both_have_key; eauto.
            eapply forest_root_iff in H1; eauto.
            unfold has_key; rewrite H1; eauto.
          }
          {
            eapply reachable_closed in H2; eauto with utils.
            intuition eauto.
            exfalso.
            eapply split_both_have_key with (x:=i); eauto.
            eapply tree_has_root; eauto.
          }
        }
        destruct H2; subst.
        {
          intuition eauto.
          {
            exfalso.
            eapply split_both_have_key with (x:=i); eauto.
            eapply forest_root_iff in H1; eauto.
            unfold has_key; rewrite H1; eauto.
          }        
          {
            eapply reachable_closed in H2; intuition eauto with utils.
            exfalso.
            eapply split_both_have_key with (x:=j); eauto.
            1:eapply tree_has_root; eauto.
          }
        }
        intuition subst.
        {
          exfalso.
          eapply split_both_have_key with (x:=i); eauto.
          eapply forest_root_iff in H1; eauto.
          unfold has_key; rewrite H1; eauto.
        }
        eauto.
      }
    Qed.

    
    Lemma forest_put' r i j l
      : ~ In i l ->
        In j l ->
        forest l r ->
        forest l (map.put r i j).
    Proof.
      intros Hi Hj.
      intro H.
      pose proof (forest_no_dup _ _ H).
      rewrite <- removeb_perm with (x:=j) in H, Hi; eauto.
      rewrite <- removeb_perm with (x:=j); eauto.
      eapply forest_put; eauto.
      basic_utils_crush.
    Qed.
    
    Lemma reachable_put1 l r i j
      : forest l r ->
        In j l ->
        reachable r i j ->
        forall a b, reachable r a b <-> reachable (map.put r i j) a b.
    Proof.
      eqb_case i j.
      {
        intros.
        replace (map.put r j j) with r; try reflexivity.
        eapply map.map_ext.
        intro k; eqb_case k j; [|basic_utils_crush].
        autorewrite with bool utils; eauto.
        eapply forest_root_iff; eauto.
      }     
      revert r.
      unfold forest; induction l;
        basic_goal_prep.
      { basic_utils_crush. } 
      change (seps (?a::?l)) with (sep a (seps l)) in *.
      unfold sep in *; break.
      rewrite split_closed_reachable in H2; eauto with utils.
      destruct H1; subst; destruct H2.
      {
        assert (map.split (map.put r i j) (map.put x i j) x0).
        {
          rewrite reachable_tree in H1; eauto.
          destruct H1;[congruence|].
          break.
          eapply split_put_left'; eauto.
        }
        rewrite !split_closed_reachable by eauto with utils.
        rewrite split_closed_reachable with (m:= map.put r i j); eauto with utils.
        rewrite <- reachable_tree_put; eauto.
        reflexivity.
      }
      {
        eapply reachable_closed in H1; eauto with utils.
        destruct H1;[congruence|].
        break.
        exfalso.
        eapply split_both_have_key; eauto with utils.
      }
      {
        eapply reachable_closed in H2; eauto with utils.
        destruct H2;[congruence|].
        break.
        exfalso.
        eapply split_both_have_key; eauto with utils.
        eapply forest_root_iff in H1; eauto.
        unfold has_key; rewrite H1; eauto.
      }
      {
        assert (map.split (map.put r i j) x (map.put x0 i j)).
        {
          eapply reachable_closed in H2; eauto with utils.
          destruct H2;[congruence|].
          break.
          eapply Properties.map.split_comm.
          eapply split_put_left'; eauto.
          eapply Properties.map.split_comm; eauto.
        }
        rewrite !split_closed_reachable by eauto with utils.
        rewrite split_closed_reachable with (m:= map.put r i j); eauto with utils.
        1:rewrite <- IHl; eauto; reflexivity.
        eapply forest_closed.
        assert (~ In i l).
        {
          intro.
          eapply forest_reachable_in in H4; eauto.
        }
        eapply forest_put'; eauto.
      }
    Qed.
    
    Lemma find_aux_reachable_iff l mr f i f' j
      : (forest l) f ->
        find_aux' mr f i = Some (f', j) ->
        iff2 (reachable f) (reachable f').
    Proof.    
      revert f f' i j.
      induction mr;
        basic_goal_prep; [ congruence|].
      revert H0; case_match;[|congruence].
      eqb_case i0 i.
      {
        intros; basic_utils_crush.
      }
      {
        case_match; [|congruence].
        break.
        intros.
        safe_invert H1.
        pose proof case_match_eqn0.
        eapply IHmr in case_match_eqn0.
        {
          eapply iff2_trans; eauto.
          assert (reachable r i j).
          {
            eapply case_match_eqn0.
            etransitivity.
            2:eapply find_aux_reachable_out'; eauto.
            eapply eq_clo_base; eauto.
          }
          intros a b.
          eapply reachable_put1; eauto using find_auxforest.
          eapply find_aux_in; eauto.
        }
        eauto.
      }
    Qed.

    
    Lemma find_aux_spec_partial l mr f i f' j
      : forest l f ->
        find_aux' mr f i = Some (f', j) ->
        In j l /\ forest l f' /\ reachable f i j /\ iff2 (reachable f) (reachable f').
    Proof.
      intros.
      my_case Hget (map.get f i).
      2:{
        destruct mr; cbn in*; try congruence.
        rewrite Hget in H0; congruence.
      }
      eapply forest_has_key_tree in Hget; eauto.
      break.
      eapply find_aux_spec'' in H2; eauto.
      break; subst.
      split; [eapply find_aux_in|]; eauto.
      pose proof H3.
      rewrite removeb_perm in H3; eauto using forest_no_dup.
      intuition eauto using find_auxforest,
        find_aux_reachable_iff,
        find_aux_reachable_out'.
    Qed.
    
    Definition uf_rel uf1 := reachable uf1.(parent).

    Definition parent_rel m := transitive_closure (fun i j : idx => map.get m i = Some j).

    
    Lemma parent_rel_put m i j k l
      : parent_rel (map.put m i j) k l ->
        parent_rel m i j ->
        parent_rel m k l.
    Proof.
      unfold parent_rel.
      induction 1; basic_goal_prep;
        eqb_case i a;basic_utils_crush.
      etransitivity; eauto.  
    Qed.
    
    Instance split_l_subrelation
      m m_l m_r (_ : map.split m m_l m_r)
      : subrelation (fun i j : idx => map.get m_l i = Some j)
          (fun i j : idx => map.get m i = Some j).
    Proof.
      unfold reachable, subrelation.
      basic_goal_prep.
      basic_utils_crush.
      eapply Properties.map.get_split_grow_r; eauto.
    Qed.
    
    Instance split_r_subrelation
      m m_l m_r (_ : map.split m m_l m_r)
      : subrelation (fun i j : idx => map.get m_r i = Some j)
          (fun i j : idx => map.get m i = Some j).
    Proof.
      unfold reachable, subrelation.
      basic_goal_prep.
      basic_utils_crush.
      eapply Properties.map.get_split_grow_l; eauto.
    Qed.
    
    Lemma parent_rel_put_same x x0 i0
      : parent_rel (map.put x0 x i0) x i0.
    Proof.
      constructor.
      basic_utils_crush.
    Qed.
    Hint Resolve parent_rel_put_same : utils.

    (*TODO: move to maps file*)
    Lemma get_singleton_diff
      : forall (k k' v : idx), k <> k' -> map.get (map.singleton k v) k' = None.
    Proof.
      unfold map.singleton; basic_utils_crush.
    Qed.
    Hint Rewrite get_singleton_diff using eassumption : utils.

    
    Lemma parent_rel_put_new (m : idx_map) (i j k l : idx)
      : parent_rel m k l -> map.get m i = None -> parent_rel (map.put m i j) k l.
    Proof.
      intros; eapply transitive_closure_subrelation; eauto.
      intros ? ? ?.
      basic_utils_crush.
    Qed.

    Lemma parent_rel_empty x i : parent_rel map.empty x i <-> False.
    Proof.
      unfold parent_rel.
      intuition.
      induction H;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite parent_rel_empty : utils.
    
    Lemma forest_ptsto_parent i f
      : forest_ptsto i f ->
        forall x, In x (map.keys f) <->
                  (parent_rel f) x i.
    Proof.
      induction 1;
        basic_goal_prep;
        basic_utils_crush.
      {
        case_match; try tauto.
        unfold and1 in *; destruct H; break.
        pose proof H as Hsplit.
        eapply Properties.map.get_split with (k:=x) in Hsplit.
        pose proof case_match_eqn as cme.
        intuition idtac; rewrite H6 in *;
          eapply forest_ptsto_has_next in case_match_eqn; (intuition eauto); subst.
        {
          eapply transitive_closure_subrelation;
            [eapply split_l_subrelation; eauto| eapply H4].
          basic_utils_crush.
          rewrite cme.
          auto.
        }
        {
          eapply transitive_closure_subrelation;
            [eapply split_l_subrelation; eauto| eapply H4].
          basic_utils_crush.
          rewrite cme.
          auto.
        }
        {
          eapply transitive_closure_subrelation;
            [eapply split_r_subrelation; eauto| eapply H3].
          basic_utils_crush.
          rewrite cme.
          auto.
        }
        {
          eapply transitive_closure_subrelation;
            [eapply split_r_subrelation; eauto| eapply H3].
          basic_utils_crush.
          rewrite cme.
          auto.
        }
      }
      2:{
        case_match; try tauto.
        unfold and1, not1 in *; destruct H0; break.
        pose proof H0 as Hsplit.
        pose proof case_match_eqn as cme.
        eapply Properties.map.get_split with (k:=x) in Hsplit.
        unfold ptsto in *.
        subst.
        eqb_case i x; basic_utils_crush.
        {
          etransitivity; eauto with utils.
          eapply parent_rel_put_new; eauto.
          eapply H4.
          basic_utils_crush.
          rewrite cme; auto.
        }
        {
          etransitivity; eauto with utils.
          eapply parent_rel_put_new; eauto.
          eapply H4.
          basic_utils_crush.
          rewrite cme; auto.
        }
      }
      {
        revert H0; clear.
        induction 1;
        basic_goal_prep;
        basic_utils_crush;
        repeat (case_match; try congruence);
        basic_utils_crush.
      }
      {
        revert H1; clear.
        induction 1;
        basic_goal_prep;
        basic_utils_crush;
        repeat (case_match; try congruence);
        basic_utils_crush.
      }
    Qed.
    
    (* Note: partial spec. Characterizing when it returns None doesn't help with using
     union find for egraphs.
     *)
    Lemma find_spec' (uf uf' : union_find) i j l
      : forest l uf.(parent) ->
        find' uf i = Some (uf', j) ->
        forest l uf'.(parent)
        /\ In j l
        /\ iff2 (uf_rel uf) (uf_rel uf') /\ (uf_rel uf i j).
    Proof.
      destruct uf, uf'.
      unfold find', uf_rel.
      my_case Haux (find_aux' (S max_rank0) parent0 i); cbn;[| congruence].
      intros; break.
      safe_invert H0.
      eapply find_aux_spec_partial in Haux; intuition eauto.
    Qed.
    
    Lemma tree_parent i f
      : tree i f ->
        forall x, In x (map.keys f) <->
                    (parent_rel f) x i.
    Proof.
      unfold tree.
      intros.
      destruct H; break.
      unfold ptsto in *; cbn in *; subst.
      erewrite <- map_split_permutation; eauto.
      replace (map.keys (map.singleton i i)) with [i].
      2:{
        unfold map.keys, map.singleton.
        rewrite Properties.map.fold_singleton.
        reflexivity.
      }
      rewrite Permutation_app_comm.
      cbn.
      rewrite forest_ptsto_parent; eauto.
      split; basic_goal_prep; intuition subst.
      {
        eapply trans_clo_base.
        eapply Properties.map.get_split_grow_l; eauto.
        basic_utils_crush.
      }
      {
        eapply transitive_closure_subrelation; eauto.
        intros ? ? ?.
        eapply Properties.map.get_split_grow_r; eauto.
      }
      {
        eqb_case i x; intuition auto.
        right.
        revert H H2.
        induction H1;
          basic_goal_prep;
          basic_utils_crush.
        {
          eapply forest_ptsto_parent; eauto.
          basic_utils_crush.
          rewrite H; auto.
        }
        { eqb_case c b; intuition unfold parent_rel; eauto with utils. }
      }
    Qed.

    Lemma counted_parent_decidable n m x i
      : {count_step_closure (fun i j : idx => map.get m i = Some j) n x i}
        + {~count_step_closure (fun i j : idx => map.get m i = Some j) n x i}.
    Proof.
      revert m x i; induction n;
        basic_goal_prep.
      {
        destruct (map.get m x) eqn:Hg; [| right].
        2:{ intro H; safe_invert H; congruence. }
        eqb_case i0 i; [| right].
        2:{ intro H'; safe_invert H'; congruence. }
        left.
        basic_utils_crush.
      }
      {
        destruct (map.get m x) eqn:Hg; [| right].
        2:{ intro H; safe_invert H; congruence. }
        destruct (IHn m i0 i); [left;econstructor; eauto | right; intro].
        safe_invert H.
        eapply n0.
        assert (b = i0) by congruence; subst; auto.
      }
    Qed.
    
    Lemma step_limit' f m x i
      : count_step_closure (fun i j : idx => map.get f i = Some j) m x i ->
        exists l, length l <= length (map.keys f)
                  /\ (exists n, n <= length l
                               /\ count_step_closure (fun i j : idx => map.get f i = Some j) n x i)
                  /\ NoDup l
                  /\ incl l (map.keys f)
                  /\ all (fun y => exists n, n <= length l
                                  /\ count_step_closure (fun i j => map.get f i = Some j) n y i) l.
    Proof.
      induction 1; basic_goal_prep.
      {
        exists [];
          basic_goal_prep;
          basic_utils_crush.
        {
          pose proof (map_keys_in' f a).
          rewrite H in H0.
          destruct (map.keys f); basic_goal_prep; intuition.
        }
      }
      {
        destruct (inb a x) eqn:Hin;
          basic_utils_crush.
        {
          exists x;
          basic_goal_prep;
            basic_utils_crush.
          eapply in_all in H5; eauto.
        }            
        exists (a :: x);
          basic_goal_prep;
          basic_utils_crush.
        {
          assert (incl (a::x) (map.keys f)).
          {
            basic_goal_prep; basic_utils_crush.
            rewrite H; auto.
          }
          eapply NoDup_incl_length in H7;
            basic_utils_crush.
        }
        {
          exists (S x0);
            basic_goal_prep;
            basic_utils_crush.
          Lia.lia.
        }
        { rewrite H; auto. }
        {
          exists (S x0);
            basic_goal_prep;
            basic_utils_crush.
          Lia.lia.
        }
        {
          eapply all_wkn; eauto.
          repeat basic_goal_prep;
            intuition auto.
          eexists; eauto.
        }
      }
    Qed.

    Lemma step_limit f m x i
      : count_step_closure (fun i j : idx => map.get f i = Some j) m x i ->
        exists n, n <= length (map.keys f)
                  /\ count_step_closure (fun i j : idx => map.get f i = Some j) n x i.
    Proof.
      intro H.
      eapply step_limit' in H.
      basic_goal_prep;
        basic_utils_crush.
      exists x1; intuition Lia.lia.
    Qed.
    
    Lemma parent_decidable f x i
      : {parent_rel f x i} + {~parent_rel f x i}.
    Proof.
      unfold parent_rel.
      enough ({exists n, count_step_closure (fun i j : idx => map.get f i = Some j) n x i}
              + {~ exists n, count_step_closure (fun i j : idx => map.get f i = Some j) n x i})
        as Hcounted.
      {
        destruct Hcounted; [ left | right];
          basic_goal_prep;
          [ eapply transitive_iff_count_step
          | intro H'; eapply transitive_iff_count_step in H'];
          basic_goal_prep;
          try eexists;
          basic_utils_crush.
      }
      enough ({exists n, n <= length (map.keys f)
                         /\ count_step_closure (fun i j : idx => map.get f i = Some j) n x i}
              + {~ exists n, n <= length (map.keys f)
                         /\ count_step_closure (fun i j : idx => map.get f i = Some j) n x i})
        as Hcounted.
      {
        destruct Hcounted; [ left | right; intro];
          basic_goal_prep;
          basic_utils_crush.
        eapply n.
        eapply step_limit in H.
        basic_goal_prep.
        exists x0; basic_utils_crush.
      }
      eapply bounded_exists_decidable.
      intros; apply counted_parent_decidable.
    Qed.
    
    Lemma intermediate_parent f x b i
      : parent_rel f x b -> parent_rel f x i -> b = i \/ parent_rel f b i \/ parent_rel f i b.
    Proof.
      eqb_case b i; intuition auto.
      destruct (parent_decidable f b i);
        intuition auto.
      right; right.
      revert i H n H1.
      induction H0;
        basic_goal_prep;
        basic_utils_crush.
      {
        inversion H1; subst; clear H1.
        { congruence. }
        { replace b0 with b in * by congruence; tauto. }
      }
      {
        inversion H2; subst; clear H2.
        { replace b with i in * by congruence; eauto. }
        { replace b0 with b in * by congruence; eauto. }
      }
    Qed.

    
    Lemma root_no_parents f i b
      : forest_ptsto i f ->
        ~ parent_rel f i b.
    Proof.
      intros ? ?.
      eapply transitive_closure_leftmost in H0; break.
      eapply forest_ptsto_none in H; congruence.
    Qed.
        
    Lemma forest_ptsto_root_limit i f
      : forest_ptsto i f ->
        forall x, In x (map.keys f) <-> limit (parent_rel f) x i.
    Proof.
      unfold limit.
      intuition eauto.
      all: try eapply forest_ptsto_parent; eauto.
      rewrite forest_ptsto_parent in * by eauto.
      pose proof (intermediate_parent _ _ _ _ H1 H0).
      intuition auto.
      exfalso.
      eapply root_no_parents; eauto.
    Qed.

    Lemma map_get_dom m x
      : dom (fun i j : idx => map.get m i = Some j) x <-> has_key x m.
    Proof.
      unfold dom, has_key;
        case_match;
        intuition eauto;
        break; congruence.
    Qed.

    Lemma forest_codom i m
      : forest_ptsto i m ->
        forall x, codom (fun i j : idx => map.get m i = Some j) x ->
                  x = i \/ dom (fun i j : idx => map.get m i = Some j) x.
    Proof.
      unfold codom; basic_goal_prep.
      eapply forest_ptsto_next in H; eauto.
      rewrite map_get_dom.
      intuition eauto.
    Qed.
    
    Lemma mem_step_split_iff m l r
      : map.split m l r ->
        iff2 (fun i j : idx => map.get m i = Some j)
          (or2 (fun i j : idx => map.get l i = Some j)
             (fun i j : idx => map.get r i = Some j)).
    Proof.
      unfold iff2, or2; basic_goal_prep.
      eapply Properties.map.get_split with (k:=a) in H;
        basic_utils_crush.
      all: try (left; congruence).
      all: try (right; congruence).
      all: congruence.
    Qed.
    
    Lemma parent_rel_loop m x y
      : parent_rel m x y -> map.get m x = Some x -> y = x.
    Proof.
      induction 1;
        basic_goal_prep;
        basic_utils_crush.
      all: try congruence.
      replace a with b in * by congruence.
      eauto.
    Qed.
    
    Lemma parent_rel_add_loop x0 i x y
      : map.get x0 i = None -> x<>i -> parent_rel (map.put x0 i i) x y <-> parent_rel x0 x y.
    Proof.
      intros.
      split.
      all:unfold parent_rel in *;
      induction 1;
        basic_goal_prep;
        basic_utils_crush;
        eqb_case i b;
        basic_goal_prep;
        basic_utils_crush.
      { eapply parent_rel_loop in H2; basic_utils_crush. }
      1,2:constructor 1; basic_utils_crush.
      { inversion H2; basic_utils_crush; congruence. }
      { econstructor 2; basic_utils_crush. }
    Qed.

    (*TODO: move to maps file*)
    Lemma has_key_putmany (i:idx) (m1 m2 : idx_map)
      : has_key i (map.putmany m1 m2) <-> has_key i m1 \/ has_key i m2.
    Proof.
      unfold has_key.
      rewrite Properties.map.get_putmany_dec.
      my_case H2 (map.get m2 i);
        [ basic_utils_crush
        | case_match]; intuition fail.
    Qed.
    Hint Rewrite has_key_putmany : utils.

    (*TODO: move to coqutil *)
    Lemma remove_put m (i j : idx)
      : (map.remove (map.put m i j) i) = (map.remove m i).
    Proof.
      eapply map.map_ext.
      intro k.
      eqb_case k i;
        basic_utils_crush.
    Qed.
    Hint Rewrite remove_put : utils.
    
    Lemma remove_none (m : idx_map) (i:idx)
      : map.get m i = None -> (map.remove m i) = m.
    Proof.
      intros;
        eapply map.map_ext.
      intro k.
      eqb_case k i;
        basic_utils_crush.
    Qed.

    Lemma tree_in_forest i l
      : In i l ->
        (* Needed for the right-to-left direction since l could have multiple 'i's in it*)
        NoDup l ->
        seps_Uiff1 (map tree l) (tree i :: map tree (removeb (eqb (A:=idx)) i l)).
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      {
        my_case Hinb (inb i l);
          basic_utils_crush.
        { safe_invert H0; tauto. }
        {
          rewrite removeb_not_In; eauto.
          reflexivity.
        }
      }
      {
        safe_invert H0; intuition eauto.
        rewrite -> H0.
        eqb_case i a; cbn;
          basic_utils_crush.
        erewrite seps_permutation.
        1:reflexivity.
        all: eauto using perm_swap.
      }
    Qed.
    
    Lemma tree_append i j m
      :  seps [tree j; tree i] m ->
         tree j (map.put m i j).
    Proof.
      intros.
      assert (i<>j).
      {
        change (sep (tree j) (sep (tree i) emp) m) in H.
        seprewrite.
        let P := open_constr:(_) in
        let Q := open_constr:(_) in
        assert (sep P Q m).
        {
          eapply sep_consequence; try eassumption.
          all: apply tree_has_root.
        }
        intro; subst.
        clear H.
        destruct H0 as [m1 [m1' [Ha [Hb ?] ] ] ]; subst.
        eapply split_both_have_key; eauto.
      }
      unfold tree in *.    
      seprewrite.
      assert (seps [eq (map.singleton j j);
                    forest_ptsto j;
                    (and1 (forest_ptsto i) (not1 (has_key j)));
                    eq (map.singleton i i)] m).
      {
        revert dependent m.
        sep_focus [1;2] [0;2]; try reflexivity.
        intros m Hm.
        eapply sep_get_split'  with (j:=j) (k:=j) in Hm.
        2:{
          eapply get_of_seps; eauto.
          { left; eauto. }
          unfold map.singleton; basic_goal_prep;
            subst;
            basic_utils_crush.
        }
        destruct Hm.
        {
          eapply sep_consequence; eauto.
          seprewrite.
          eauto.
        }
        {
          exfalso.
          seprewrite.
          destruct H as [? [? [? [ [? [? ] ] ] ] ] ].
          cbv [lift] in *.
          intuition eauto.
        }
      }
      change (seps (?a::?l)) with (sep a (seps l)) in H1.
      destruct H1 as [m1 [m1' [Ha [Hb ?] ] ] ]; subst.
      exists (map.put m1' i j), (map.singleton j j).
      intuition eauto.
      {
        eapply split_put_left; eauto.
        2: eapply Properties.map.split_comm; eauto.
        unfold map.singleton.
        basic_utils_crush.
      }
      apply forest_join.
      destruct H1 as [m2 [m2' [H1a [H1b ?] ] ] ].
      exists m2, (map.put m2' i j).
      intuition eauto.
      {
        eapply Properties.map.split_comm.
        eapply split_put_left'; eauto.
        2: eapply Properties.map.split_comm; eauto.
        seprewrite.
        destruct H1 as [m3 [m3' [H2a [H2b ?] ] ] ].
        rewrite has_key_split; subst; eauto.
        basic_utils_crush.
      }
      apply forest_node with (i:=i); eauto.
      destruct H1 as [m3 [m3' [H2a [H2b ?] ] ] ].
      seprewrite.
      subst.
      exists m3, (map.singleton i j).
      basic_utils_crush.
    Qed.
    
    Lemma tree_append_in_seps r i j l
      : In i l ->
        seps (tree j :: map tree l) r ->
        seps (tree j :: map tree (removeb (eqb (A:=idx)) i l)) (map.put r i j).
    Proof.
      intros.
      assert (NoDup l).
      {
        destruct H0 as [m1 [m1' [Ha [Hb ?] ] ] ].
        eapply forest_no_dup; eauto.
      }
      assert (seps (tree j :: (tree i :: map tree (removeb (eqb (A:=idx)) i l))) r).
      {
        revert r H0.
        change (seps_Uimpl1 (tree j :: map tree l)
                  (tree j :: tree i :: map tree (removeb (eqb (A:=idx)) i l))).
        rewrite tree_in_forest; eauto.
        reflexivity.
      }
      clear H0.
      change (?a::?b::?l) with ([a;b]++l) in H2.
      eapply sep_concat in H2; eauto.
      destruct H2 as [m [m' [Ha [Hb ?] ] ] ].
      change (seps (?a::?l)) with (sep a (seps l)).
      exists (map.put m i j), m'.
      intuition eauto.
      {
        eapply split_put_left'; eauto.
        eapply sep_has_key.
        eapply sep_comm; [eauto..|].
        change (sep (tree j) (sep (tree i) emp) m) in Hb.
        eapply sep_consequence; try eassumption.
        all: intros; eauto.
        seprewrite.
        eapply tree_has_root.
        auto.
      }
      {
        eapply tree_append; eauto.
      }
    Qed.

    
    Lemma tree_append_in_seps' r i j l
      : In i l ->
        In j l ->
        i<> j ->
        seps (map tree l) r ->
        seps (map tree (removeb (eqb (A:=idx)) i l)) (map.put r i j).
    Proof.
      intros Hini Hinj Hneq.
      eapply in_split in Hinj.
      break.
      subst.
      rewrite <- Permutation_middle.
      cbn.
      eqb_case i j; eauto; try tauto.
      cbn.
      eapply tree_append_in_seps.
      basic_utils_crush.
      cbn in *.
      basic_utils_crush.
    Qed.
    
    Lemma forest_put_in r i j l
      : i<> j -> In i l -> In j l -> forest l r ->
        forest (List.removeb (eqb (A:=_))i l) (map.put r i j).
    Proof.
      intro.
      unfold forest.
      revert r; induction l;
        basic_goal_prep;
        basic_utils_crush.
      {
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        unfold sep in *; break.
        eapply in_forest_split in H0; eauto; break; subst.
        clear H3.
        assert (Permutation (x1 ++ j :: x2) (j :: x1 ++ x2)) as Hrw.
        {
          change (j :: x2) with ([j] ++ x2).
          rewrite Permutation_app_swap_app.
          reflexivity.
        }
        rewrite Hrw.
        replace (List.removeb (eqb (A:=idx)) i ( j :: x1 ++ x2))
          with (j::List.removeb (eqb (A:=idx)) i (x1 ++ x2)).
        2:{
          cbn.
          eqb_case i j; subst; cbn; eauto; tauto.
        }
        cbn.
        change (seps (?a::?l)) with (sep a (seps l)) in *.
        unfold sep in H4; break.
        exists (map.put (map.putmany x3 x) i j), x4.
        basic_utils_crush.
        {
          eapply split_put_left'.
          {
            basic_utils_crush.
          }
          {
            eapply Properties.map.split_comm; eauto.
            rewrite Properties.map.putmany_comm.
            {
              eapply map_split_3_ways; eauto using Properties.map.split_comm.
              eapply Properties.map.split_comm; eauto.
            }
            eapply Properties.map.sub_domain_disjoint.
            1: eapply Properties.map.disjoint_comm; eapply split_disjoint; eauto.
            unfold map.split in H0; break; subst.
            eapply Properties.map.sub_domain_putmany_r;
              eapply Properties.map.sub_domain_refl.
          }
        }
        {
          eapply tree_join.
          exists x3, (map.put x i j);
            basic_utils_crush.
          2:{
            eapply forest_node; eauto.
            exists (map.remove x i), (map.singleton i j).
            basic_utils_crush.
            unfold and1.
            unfold tree in *.
            clear IHl.
            unfold sep in*.
            basic_utils_crush.
            { rewrite remove_none; eauto. }
            {
              my_case Hget (map.get x7 j); try tauto.
              exfalso.
              eapply split_both_have_key with (x:=j) in H1; eauto;
                basic_utils_crush.
              eapply split_has_key_l; eauto.
              basic_utils_crush.
            }
          }
          rewrite Properties.map.put_putmany_commute.
          unfold map.split; intuition eauto.
          assert (map.disjoint x3 x).
          {           
            eapply Properties.map.sub_domain_disjoint.
            1: eapply Properties.map.disjoint_comm; eapply split_disjoint; eauto.
            unfold map.split in H0; break; subst.
            eapply Properties.map.sub_domain_putmany_r;
              eapply Properties.map.sub_domain_refl.
          }
          {
            apply Properties.map.disjoint_comm.
            eapply Properties.map.sub_domain_disjoint.
            1: apply Properties.map.disjoint_comm; eauto.
            apply tree_has_root in H2;
              revert H2;
              unfold has_key;
              case_match; intros; try tauto.
            eapply Properties.map.sub_domain_put_l; eauto using Properties.map.sub_domain_refl.
          }
        }
        {
          rewrite removeb_not_In; eauto.
          rewrite forest_root_iff; eauto.
          apply tree_has_root in H2.
          intro H'.
          eapply split_both_have_key; auto.
          2: eassumption.
          1: eassumption.
          eapply Properties.map.get_split_grow_l in H0; eauto.
          unfold has_key; rewrite H0; eauto.  
        }
      }
      {
        cbn.
        eapply tree_append_in_seps; eauto.
      }
      {
        eqb_case i a; cbn.
        {
          exfalso.
          eapply seps_has_key_conflict; auto.
          change (sep (tree a) (seps (map tree l)) r) in H2.
          eapply sep_consequence; try eassumption.
          1: eapply tree_has_root.
          intros.
          unfold has_key.
          rewrite (proj1 (forest_root_iff _ _ _ H1)); eauto.
        }
        {
          change (seps (map tree (a::l)) r) in H2.
          change (seps (map tree (a::removeb (eqb (A:=idx)) i l)) (map.put r i j)).
          replace (a :: removeb (eqb (A:=idx)) i l)
            with (removeb (eqb (A:=idx)) i (a::l)).
          {
            eapply tree_append_in_seps'; cbn; eauto.
          }
          {
            cbn.
            eqb_case i a; cbn; try tauto.
          }
        }
      }
    Qed.
    
    Lemma reachable_direct m a b
      : map.get m a = Some b ->
        reachable m a b.
    Proof.
      intro.
      eapply eq_clo_base; eauto.
    Qed.
    Hint Resolve reachable_direct : utils.

    
    Lemma reachable_unloop m i a b z
      : map.get m i = Some i ->
        reachable m a b ->
        reachable (map.put m i z) a b.
    Proof.
      unfold reachable.
      induction 2;
        basic_goal_prep;
        subst;
        intuition (subst; eauto using eq_clo_base, eq_clo_refl, eq_clo_trans,eq_clo_sym).
      {
        eqb_case i a;
          [ replace b with a by congruence; eapply eq_clo_refl
          | eapply eq_clo_base].
        basic_utils_crush.
      }
    Qed.
    
    Lemma union_closure_put_singleton (i:idx) m z
      : map.get m i = Some i ->
        iff2 (reachable (map.put m i z))
          (union_closure (reachable m) (singleton_rel i z)).
    Proof.
      intro Hget.
      unfold union_closure.
      split; induction 1;
        basic_goal_prep;
        subst;
        intuition (subst; unfold reachable; eauto using eq_clo_base, eq_clo_refl, eq_clo_trans,eq_clo_sym).
      {
        eqb_case i a;
          basic_utils_crush.
      }
      {
        eapply reachable_unloop; eauto.
      }
      {
        unfold singleton_rel in *;
          basic_utils_crush.
        eapply eq_clo_base;
          basic_utils_crush.
      }
    Qed.
    
    Lemma union_spec' u x u' y z l
      : forest l u.(parent) ->
        union' u x y = Some (u', z) ->
        exists l',
          forest l' u'.(parent)
          /\ In z l'
          /\ iff2 (uf_rel u') (union_closure (uf_rel u) (singleton_rel x y))
          /\ uf_rel u' y z.
    Proof.
      unfold union'.
      my_case Hfx (find' u x);break;cbn;[| congruence].
      my_case Hfy (find' u0 y);break;cbn;[| congruence].
      intro.
      eapply find_spec' in Hfx, Hfy; break; eauto.
      eqb_case i i0.
      {
        exists l.
        basic_goal_prep;
          basic_utils_crush.
        2:{
          eapply H6; eauto.
        }
        {
          rewrite <- H6.
          rewrite <- H2.
          apply H2 in H7.
          assert (uf_rel u y x) as H' by (etransitivity; [|symmetry]; eauto).
          revert H'; clear.
          intro.
          unfold uf_rel, reachable.
          rewrite union_closure_subrel; [reflexivity|].
          unfold singleton_rel.
          basic_goal_prep; subst.
          symmetry.
          eapply H'.
        }
      }
      repeat (case_match; [|congruence]).
      case_match.
      {
        basic_goal_prep;
          basic_utils_crush.
        exists (List.removeb (eqb (A:=_)) i0 l).
        basic_goal_prep;
          basic_utils_crush.
        {
          eapply forest_put_in; eauto.
        }
        { eapply remove_In_ne; eauto. }
        {
          unfold uf_rel in *.
          cbn.
          rewrite union_closure_singleton_sym.
          rewrite union_closure_singleton_transport.
          2: eassumption.
          rewrite union_closure_singleton_sym.
          rewrite union_closure_singleton_transport.
          2:{
            apply H2.
            eassumption.
          }       
          rewrite union_closure_singleton_sym.
          rewrite union_closure_put_singleton.
          {
            rewrite H2, H6.
            reflexivity.
          }
          eapply forest_root_iff; eauto.
        }
        {
          unfold uf_rel.
          cbn.
          apply H6 in H7.
          eapply eq_clo_trans.
          {
            apply reachable_unloop; eauto.
            eapply forest_root_iff; eauto.
          }
          {
            eapply eq_clo_base.
            basic_utils_crush.
          }
        }
      }
      {
        basic_goal_prep;
          basic_utils_crush.
        exists (List.removeb (eqb (A:=_)) i0 l).
        basic_goal_prep;
          basic_utils_crush.
        {
          eapply forest_put_in; eauto.
        }
        { eapply remove_In_ne; eauto. }
        {
          unfold uf_rel in *.
          cbn.
          rewrite union_closure_singleton_sym.
          rewrite union_closure_singleton_transport.
          2: eassumption.
          rewrite union_closure_singleton_sym.
          rewrite union_closure_singleton_transport.
          2:{
            apply H2.
            eassumption.
          }       
          rewrite union_closure_singleton_sym.
          rewrite union_closure_put_singleton.
          {
            rewrite H2, H6.
            reflexivity.
          }
          eapply forest_root_iff; eauto.
        }
        {
          unfold uf_rel.
          cbn.
          apply H6 in H7.
          eapply eq_clo_trans.
          {
            apply reachable_unloop; eauto.
            eapply forest_root_iff; eauto.
          }
          {
            eapply eq_clo_base.
            basic_utils_crush.
          }
        }
      }
      {
        basic_goal_prep;
          basic_utils_crush.
        exists (List.removeb (eqb (A:=_)) i l).
        basic_goal_prep;
          basic_utils_crush.
        {
          eapply forest_put_in; eauto.
        }
        { eapply remove_In_ne; eauto. }
        {
          unfold uf_rel in *.
          cbn.
          rewrite union_closure_singleton_sym.
          rewrite union_closure_singleton_transport.
          2: eassumption.
          rewrite union_closure_singleton_sym.
          rewrite union_closure_singleton_transport.
          2:{
            apply H2.
            eassumption.
          }       
          rewrite union_closure_singleton_sym.
          rewrite union_closure_put_singleton.
          {
            rewrite union_closure_singleton_sym.
            rewrite H2, H6.
            reflexivity.
          }
          eapply forest_root_iff; eauto.
        }
        {
          unfold uf_rel.
          cbn.
          apply H6 in H7.
          eapply reachable_unloop.
          2: eauto.
          eapply forest_root_iff; eauto.
        }
      }
    Qed.

    Lemma closed_graph_PER_shared_parent m
      : closed_graph m ->
        iff2 (PER_closure (fun i j : idx => map.get m i = Some j))
             (fun x y => exists i, parent_rel m x i /\ parent_rel m y i).
    Proof.
      split.
      2:{
        unfold parent_rel.
        basic_goal_prep;
          basic_utils_crush.
        etransitivity; [| symmetry]; eapply trans_PER_subrel; eauto.
      }
      {
        induction 1;
          basic_goal_prep;
          basic_utils_crush.
        {
          pose proof H0 as H0';
            eapply H in H0;
            unfold has_key in *;
            case_match; intuition.
          exists i.
          unfold parent_rel.
          basic_utils_crush.
        }
        {
          pose proof (intermediate_parent _ _ _ _ H0 H3).
          intuition subst; eauto.
          {
            exists x0; unfold parent_rel in *;
              basic_utils_crush.
            etransitivity;
              basic_utils_crush.
          }
          {
            exists x; unfold parent_rel in *;
              basic_utils_crush.
            etransitivity;
              basic_utils_crush.
          }
        }
      }
    Qed.
    
    Lemma closed_graph_equiv_to_PER m
      : closed_graph m ->
        iff2 (PER_closure (fun i j : idx => map.get m i = Some j))
          (fun x y =>
             equivalence_closure (fun i j : idx => map.get m i = Some j) x y
             /\ has_key y m).
    Proof.
      split.
      {
        intuition.
        1: apply PER_equiv_subrel; eauto.
        1: inversion H0;
        basic_goal_prep;
        basic_utils_crush.
        all: rewrite PER_step in *; break;
          basic_utils_crush.
      }
      {
        basic_goal_prep.
        eapply PER_trans_equiv; eauto.
        unfold has_key in *; repeat case_match; try tauto.
        etransitivity; [|symmetry].
        all:eapply PER_clo_base; eauto.
      }
    Qed.

    Definition uf_rel_PER m :=
      PER_closure (fun i j : idx => map.get m.(parent) i = Some j).

    Definition state_put i r : state idx_map unit :=
      fun s => (tt, map.put s i r).
    
    Definition state_get i : state idx_map idx :=
      fun s => (unwrap_with_default (H:=i) (map.get s i), s).
    
    (* assumes mr > the max chain length in the state *)
    Fixpoint find_aux (mr : nat) (i : idx) : state idx_map idx :=
      match mr with
      | 0 => fun s => (i, s)
      | S mr0 => fun x =>
                   match map.get x i with
                   | Some a => if eqb a i then (i, x)
                               else let (x1, y) := find_aux mr0 a x in
                                    (x1, map.put y i x1)
                   | None => (i,x) (*shouldn't happen *)
                   end
      end.

    Definition find :=
      fun '{| rank := ra; parent := pa; max_rank := mr; next := l |} (x : idx) =>
        let (cx, f) := find_aux (S mr) x pa in
        ({| rank := ra; parent := f; max_rank := mr; next := l |}, cx).

    Definition union h x y :=
      let (h, cx) := find h x in
      let (h, cy) := find h y in
      if eqb cx cy then (h, cx) else
        (* assume the ranks exist *)
        let rx := unwrap_with_default (H:=0) (map.get h.(rank) cx) in
        let ry := unwrap_with_default (H:=0) (map.get h.(rank) cy) in
        match Nat.compare ry rx with
        | Lt => (MkUF (h.(rank))
                         (map.put h.(parent) cy cx)
                         (h.(max_rank))
                         h.(next), cx)
        | Gt => (MkUF (h.(rank))
                         (map.put h.(parent) cx cy) 
                         (h.(max_rank))
                         (h.(next)), cy)
        | Eq => (MkUF (map.put h.(rank) cx (Nat.succ rx))
                         (map.put h.(parent) cy cx)
                         (max h.(max_rank) (Nat.succ rx))
                         h.(next), cx)
        end.
        
    Record union_find_ok uf l :=
      {
        uf_forest : forest l uf.(parent); 
        rank_covers_domain : forall k v,
        map.get uf.(parent) k = Some v -> exists r, map.get uf.(rank) k = Some r;
        rank_increasing : forall i j, map.get uf.(parent) i = Some j ->
                                      i <> j ->
                                      option_relation Peano.lt (map.get uf.(rank) i)
                                        (map.get uf.(rank) j);
        maximum_rank : forall i r, map.get uf.(rank) i = Some r ->
                                   r <= uf.(max_rank);                  
      }.

    Definition steps_bounded_by {A} (R: A -> A -> Prop) max a b :=
      forall n, count_step_closure R n a b ->
               (* (* Include the reflexive case to work more nicely in instances
                   where a -> ... -> a in a non-trivial loop?
                 *)
                a = b \/ *)
                      exists m, count_step_closure R m a b
                             /\ m < max.

    Lemma union_find_step_bound uf l i y r
      : union_find_ok uf l ->
        map.get uf.(rank) i = Some r ->
        steps_bounded_by (fun i j : idx => map.get uf.(parent) i = Some j)
          (S (max_rank uf) - r) i y.
    Proof.
      unfold steps_bounded_by; cbn -[Nat.sub]; repeat intro.
      revert r H0.
      induction H1; repeat intro.
      {
        eapply maximum_rank in H1; eauto.
        eexists; basic_utils_crush.
        Lia.lia.
      }
      {
        eqb_case a b.
        {
          eapply count_step_implies_transitive in H1.
          eapply parent_rel_loop in H1; eauto.
        }
        pose proof (rank_increasing _ _ H _ _ H0 H3).
        rewrite H2 in *; cbn -[Nat.sub] in *.
        case_match; try tauto.
        specialize (IHcount_step_closure n0);
          intuition; break.
        eexists; basic_utils_crush.
        pose proof (maximum_rank _ _ H).
        Lia.lia.
      }
    Qed.

    
    Lemma steps_bounded_by_wkn x y m r1 r2
      : r1 < r2 ->
        steps_bounded_by (fun i j : idx => map.get m i = Some j) r1 x y ->
        steps_bounded_by (fun i j : idx => map.get m i = Some j) r2 x y.
    Proof.
      unfold steps_bounded_by; basic_goal_prep.
      specialize (H0 n).
      intuition eauto; break.
      eexists; intuition eauto.
    Qed.
    
    Instance gt_transitive : Transitive gt.
    Proof. unfold Transitive; Lia.lia. Qed.
    
    Lemma rank_lt_parent uf l
      : union_find_ok uf l ->
        forall i j : idx,
          parent_rel uf.(parent) i j ->
          i <> j ->
        option_relation Peano.lt (map.get uf.(rank) i) (map.get uf.(rank) j).
    Proof.
      intros ? i j;
        induction 1;
        basic_goal_prep;
        basic_utils_crush.
      { eapply rank_increasing; eauto. }
      {
        eqb_case b c.
        { eapply rank_increasing; eauto. }
        eqb_case a b; intuition eauto.
        {
          intuition.
          etransitivity; try eassumption.
          eapply rank_increasing; eauto.
        }
      }
    Qed.
    
    Lemma find_aux'_find_aux uf l i
      (* TODO relate to rank array? use a prop of that instead? *)
      : union_find_ok uf l ->
        has_key i uf.(parent) ->
        let p := find_aux (S uf.(max_rank)) i uf.(parent) in
        find_aux' (S uf.(max_rank)) uf.(parent) i = Some (snd p, fst p).
    Proof.
      intros H.
      pose proof (rank_lt_parent _ _ H).
      revert H.
      destruct uf; destruct 1; cbn -[find_aux find_aux'] in *.
      intro Hkey.
      pose proof Hkey as Hkey'.
      unfold has_key in Hkey'; case_match; try tauto; clear Hkey'.
      eapply rank_covers_domain0 in case_match_eqn; break.
      assert (forall (j : idx) (rj : nat),
                 j = i \/ parent_rel parent0 i j ->
                 map.get rank0 j = Some rj -> rj - x < S max_rank0) as max_rank_max.
      {
        intros j' rj ? H'; pose proof (maximum_rank0 j' rj H').
        destruct H1; subst; Lia.lia.
      }
      clear maximum_rank0.
      revert max_rank_max.
      change max_rank0 with (pred (S max_rank0)) at 1.
      assert (S max_rank0 > 0) as Hgt by Lia.lia.
      revert Hgt; generalize (S max_rank0); clear max_rank0.
      intro mr.
      clear i0.
      revert i x H Hkey.
      induction mr;
        basic_goal_prep.
      { Lia.lia. }
      {
        unfold has_key in *; case_match; try tauto.
        eqb_case i0 i; eauto.
        destruct mr.
        {
          exfalso.
          pose proof case_match_eqn as Hc1.
          eapply forest_closed in case_match_eqn; eauto.
          unfold has_key in *; case_match; try tauto.
          
          pose proof Hc1 as Hc2.
          eapply rank_covers_domain0 in case_match_eqn0; break.
          eapply rank_increasing0 in Hc1; eauto.
          rewrite H, H2 in *.
          cbn in *.
          eapply max_rank_max in H2; [| right; constructor 1; eauto].
          Lia.lia.
        }          
        {
          pose proof case_match_eqn as H'.
          eapply forest_closed in H'; eauto.
          unfold has_key in H'; destruct (map.get parent0 i0) eqn:Hi0; try tauto; clear H'.
          eapply rank_covers_domain0 in Hi0; destruct Hi0 as [ri0 Hi0].
          erewrite IHmr; try Lia.lia.
          { case_match; reflexivity. }
          { eauto. }
          { eapply forest_closed; eauto. }
          {
            clear IHmr.
            intros; intuition subst.
            {
              replace rj with ri0 by congruence.
              Lia.lia.
            }
            {
              pose proof case_match_eqn as Hc1.
              pose proof case_match_eqn as Hc2.
              eapply rank_increasing0 in case_match_eqn; eauto.
              eapply rank_covers_domain0 in Hc2.
              break.
              rewrite H2, Hi0 in *.
              cbn in *.
              enough (rj - x0 < S (S mr)) by Lia.lia.
              autorewrite with inversion in *; break; subst.
              eapply max_rank_max; cycle 1; try eassumption.
              right; etransitivity; try eassumption.
              constructor 1; eauto.
            }
          }
        }
      }
    Qed.
    

    (*
    Context (rank_map_ok : map.ok rank_map).
     *)
    
    Lemma find'_find uf i l
      : union_find_ok uf l ->
        has_key i uf.(parent) ->
        find' uf i = Some (find uf i).
    Proof.
      intros; break.
      unfold find, find'; cbn -[find_aux' find_aux].
      eapply find_aux'_find_aux in H; eauto.
      destruct uf; cbn -[find_aux' find_aux] in *.
      rewrite H.
      case_match; reflexivity.
    Qed.

    Lemma forest_parent l f
      : forest l f -> forall x : idx, has_key x f <-> exists i, parent_rel f x i /\ In i l.
    Proof.
      basic_goal_prep.
      intuition auto.
      2:{
        break.
        inversion H0;
          subst;
          unfold has_key;
          rewrite H2; auto.
      }
      {
        unfold has_key in *; case_match; try tauto.
        eapply forest_has_key_tree in case_match_eqn; eauto.
        break.
        exists x0; intuition eauto.
        unfold parent_rel.
        unfold and1 in *.
        destruct H2; break.
        eapply transitive_closure_subrelation.
        2:{
          eapply tree_parent; eauto.
          rewrite map_keys_in'.
          basic_utils_crush.
        }
        { eapply split_l_subrelation; eauto. }
      }
    Qed.

    
    Lemma forest_root_limit l f
      : forest l f ->
        forall x, has_key x f <-> exists i, In i l /\ limit (parent_rel f) x i.
    Proof.
      unfold limit.
      intros H1 x.
      pose proof (forest_parent _ _ H1 x).
      intuition eauto; break; intuition eauto.
      exists x0; intuition eauto.
      eqb_case b x0; intuition eauto; right.
      pose proof (intermediate_parent _ _ _ _ H2 H4).
      intuition subst;auto.
      {
        constructor 1.
        eapply forest_root_iff; eauto.
      }
      {
        eapply forest_root_iff in H3; eauto.
        eapply parent_rel_loop in H6; eauto.
        subst; basic_utils_crush.
      }
    Qed.
      
    Lemma union_find_limit uf l i j
      : union_find_ok uf l ->
        limit (parent_rel uf.(parent)) i j
        <-> In j l /\ parent_rel uf.(parent) i j.
    Proof.
      unfold limit.
      intro H.
      assert (forall A B C, (A -> (B <-> C)) -> (A /\ B <-> C /\ A))
        by intuition.
      apply H0.
      intro H1.
      split.
      2:{
        intros.
        eqb_case b j; intuition auto; right.
        pose proof (intermediate_parent _ _ _ _ H1 H3).
        intuition subst; eauto; try tauto.
        exfalso.
        inversion H5; subst; eauto;
          eapply forest_root_iff in H2; eauto using uf_forest.
        { congruence. }
        { eapply parent_rel_loop in H5; eauto. }
      }
      {
        intros.
        assert (exists x, parent_rel (parent uf) i x /\ In x l).
        {
          eapply forest_parent; eauto using uf_forest.
          unfold has_key; inversion H1; subst; rewrite H3; eauto.
        }
        break.
        pose proof H3.
        eapply H2 in H3; intuition subst; eauto.
        pose proof H4.
        eapply forest_root_iff in H4; eauto using uf_forest.
        eapply parent_rel_loop in H4; eauto.
        subst; auto.
      }
    Qed.

    
    Lemma find'_preserves_domain uf uf' j i
      : find' uf i = Some (uf', j) ->
        forall x,
        has_key x uf.(parent) <-> has_key x uf'.(parent).
    Proof.
      destruct uf; unfold find; cbn -[find_aux'].
      generalize (S max_rank0) as mr; intro.
      case_match; try congruence.
      break.
      intro; autorewrite with inversion in *.
      break; subst; cbn -[find_aux'].
      revert parent0 r i j case_match_eqn.
      induction mr;
        basic_goal_prep;
        try congruence.
      case_match; try congruence.
      eqb_case i0 i; autorewrite with inversion in *; break; subst;
        try reflexivity.
      case_match; try congruence.
      break; autorewrite with inversion in *; break; subst.
      rewrite has_key_put.
      rewrite IHmr; eauto.
      intuition subst.
      rewrite <- IHmr; eauto.
      basic_utils_crush.
    Qed.      
        
      
    Lemma find_preserves_ok uf l uf' j i
      : union_find_ok uf l ->
        subrelation (parent_rel uf'.(parent)) (parent_rel uf.(parent)) ->
        find' uf i = Some (uf', j) ->
        forest l uf'.(parent) ->
        union_find_ok uf' l.
    Proof.
      intros H Hsub; pose proof (rank_lt_parent _ _ H).
      destruct uf, uf', H;
        constructor;
        cbn -[find' find_aux'] in *;
        auto.
      {
        intros.
        pose proof H.
        eapply find'_preserves_domain with (x:=k) in H; cbn in H.
        unfold has_key in H.
        rewrite H2 in H; cbn in H.
        case_match; try tauto.
        eapply rank_covers_domain0 in case_match_eqn.
        break.
        exists x.
        unfold find' in *; basic_goal_prep;
          repeat case_match;
          basic_utils_crush.
        { inversion H6; subst; eauto. }
        { inversion H6; subst; eauto. }
      }
      {
        unfold find' in *;
          repeat (cbn -[find_aux'] in *;
                  case_match; cbn -[find_aux'] in *;
                  try congruence).
        inversion H; subst.
        intros.
        eapply H0; eauto.
        eapply Hsub.
        constructor; eauto.
      }
      {
        unfold find' in *;
          repeat (cbn -[find_aux'] in *;
                  case_match; cbn -[find_aux'] in *;
                  try congruence).
        inversion H; subst.
        intros.
        eapply maximum_rank0; eauto.
      }
    Qed.

    Lemma higher_rank_unchanged i0 uf l mr i j parent' r0 r
      : union_find_ok uf l ->
        find_aux' mr uf.(parent) i = Some (parent', j) ->
        map.get uf.(rank) i0  = Some r0 ->
        map.get uf.(rank) i = Some r ->
        r0 < r ->
        map.get uf.(parent) i0 = map.get parent' i0.
    Proof.
      destruct uf;
        intros [];
        basic_goal_prep.
      clear rank_covers_domain0 maximum_rank0.      
      generalize dependent parent0.
      generalize dependent i.
      generalize dependent r.
      revert j parent'.
      induction mr;
        basic_goal_prep;
        basic_utils_crush.
      case_match; try congruence.
      eqb_case i1 i; basic_utils_crush.
      case_match; try congruence.
      break.
      basic_utils_crush.
      eqb_case i i0.
      {
        replace r with r0 in * by congruence.
        Lia.lia.
      }
      basic_utils_crush.
      pose proof case_match_eqn.
      eapply rank_increasing0 in case_match_eqn; eauto.
      rewrite H1 in *.
      cbn in *.
      case_match; try tauto.
      eapply IHmr.
      2:eauto.
      4:eauto.
      all: eauto.
    Qed.
    
    Lemma find_parent_subrelation uf l i uf' j
      : union_find_ok uf l ->
        find' uf i = Some (uf', j) ->
        subrelation (parent_rel (parent uf')) (parent_rel (parent uf))
        /\ parent_rel uf'.(parent) i j.
    Proof.
      destruct uf, uf';
        unfold find';
        cbn -[find' find_aux'] in *.
      case_match; try congruence.
      break.
      intro Hok.
      inversion 1; subst.
      clear H.
      revert parent0 i parent1 j case_match_eqn Hok.
     
      generalize (S max_rank1) as mr; induction mr;
        basic_goal_prep; try congruence.
      case_match; try congruence.
      eqb_case i0 i; basic_utils_crush.
      { reflexivity. }
      { constructor; eauto. }
      {
        case_match; try congruence.
        break.
        basic_utils_crush.
        pose proof case_match_eqn1 as Hfind.
        eapply IHmr in case_match_eqn1; eauto.
        break.
        etransitivity; try eassumption.
        intros ? ? ?.
        eapply parent_rel_put; eauto.
        etransitivity; try eassumption.
        constructor.
        change parent0
          with {| rank := rank1;
                 parent := parent0;
                 max_rank := max_rank1;
                 next := next1 |}.(parent) in case_match_eqn0.
        pose proof case_match_eqn0 as Hcm.
        pose proof case_match_eqn0 as Hcm'.
        eapply forest_closed in case_match_eqn0; eauto using uf_forest.
        unfold has_key in *; case_match; try tauto.
        eapply rank_covers_domain in Hcm, case_match_eqn; eauto.
        basic_goal_prep.
        change parent0
          with {| rank := rank1;
                 parent := parent0;
                 max_rank := max_rank1;
                 next := next1 |}.(parent) in Hfind.
        eapply higher_rank_unchanged in Hfind;
          [| eauto ..]; cbn in *; try congruence.
        change parent0
          with {| rank := rank1;
                 parent := parent0;
                 max_rank := max_rank1;
                 next := next1 |}.(parent) in Hcm'.
        eapply rank_increasing in Hcm'; eauto.
        basic_goal_prep.
        rewrite H3, H4 in *; basic_goal_prep.
        auto.
      }
      {
        case_match; try congruence.
        break.
        basic_utils_crush.        
      }
    Qed.      

    Lemma parent_rel_has_key m a b
      : parent_rel m a b -> has_key a m.
    Proof.
      unfold has_key;
        inversion 1; subst; rewrite H0; auto.
    Qed.
        
    Lemma root_inverse_subrelation l m m'
      : forest l m ->
        forest l m' ->
        subrelation (parent_rel m') (parent_rel m) ->
        (forall x, has_key x m <-> has_key x m') ->
        forall a b,
          In b l ->
          parent_rel m a b ->
          parent_rel m' a b.
    Proof.
      intros.
      pose proof H4.
      eapply parent_rel_has_key in H4.
      pose proof H4.
      eapply H2 in H6.
      {
        eapply forest_root_limit in H6; eauto; break.
        unfold limit in *.
        break.
        pose proof H7.
        eapply H1 in H7.
        pose proof (intermediate_parent _ _ _ _ H5 H7).
        intuition subst; eauto.
        {
          replace b with x in *; eauto.
          eapply parent_rel_loop; eauto.
          eapply forest_root_iff; eauto.
        }
        {
          replace x with b in *; eauto.
          eapply parent_rel_loop; eauto.
          eapply forest_root_iff; eauto.
        }
      }
    Qed.

    (*TODO: break up into smaller lemmas?*)
    Lemma find_spec (uf uf' : union_find) i j l
      : union_find_ok uf l ->
        has_key i uf.(parent) ->
        find uf i = (uf', j) ->
        union_find_ok uf' l        
        /\ In j l
        /\ parent_rel uf'.(parent) i j
        /\ subrelation (parent_rel uf'.(parent)) (parent_rel uf.(parent))
        /\ iff2 (limit (parent_rel uf.(parent))) (limit (parent_rel uf'.(parent)))
        /\ forall x : idx, has_key x uf.(parent) <-> has_key x uf'.(parent).
        (* inferrable: /\ (limit (parent_rel uf'.(parent)) i j).*)
    Proof.
      intros.
      pose proof (find'_find _ _ _ H H0).
      rewrite H1 in H2.
      clear H1.
      pose proof H2.
      eapply find_spec' in H2; eauto using uf_forest.
      assert (subrelation (parent_rel (parent uf')) (parent_rel (parent uf))).
      {
        eapply find_parent_subrelation; eauto.
      }
      break.
      pose proof (find_preserves_ok _ _ _ _ _ H H3 H1 H2).
      intuition eauto.
      {
        eapply find_parent_subrelation in H1; intuition eauto.
      }          
      {
        unfold iff2.
        intros a b.
        rewrite !union_find_limit by eauto.
        intuition eauto.
        eapply root_inverse_subrelation.
        6:eauto.
        all: eauto using uf_forest.
        intros; eapply find'_preserves_domain; eauto.
      }
      all: eapply find'_preserves_domain in H1; intuition eauto.
    Qed.

    Lemma union_find_unique l m a x y
      : union_find_ok m l ->
        limit (parent_rel m.(parent)) a x ->
        limit (parent_rel m.(parent)) a y ->
        x = y.
    Proof.
      intros.
      rewrite union_find_limit in * by eauto.
      intuition.
      eapply forest_reachable_in; eauto using uf_forest.
      apply PER_equiv_subrel;
        etransitivity; [symmetry|];
        apply trans_PER_subrel; eauto.
    Qed.

    
    Lemma transitive_limit m a b x1
      : parent_rel m a b ->
        limit (parent_rel m) b x1 ->
        limit (parent_rel m) a x1.
    Proof.
      unfold limit.
      intuition eauto.
      { etransitivity; eauto. }
      {
        eqb_case b0 x1; intuition eauto; right.
        pose proof H0.
        eapply intermediate_parent in H0; try exact H.
        intuition subst; eauto.
        2:{ etransitivity; eauto. }
        {
          eapply H2 in H0; intuition subst; eauto.
        }
      }
    Qed.
    
    Lemma confluent_limit m a b x1
      : parent_rel m a b ->
        limit (parent_rel m) a x1 ->
        b = x1 \/ limit (parent_rel m) b x1.
    Proof.
      unfold limit.
      intuition eauto.
      eqb_case b x1; intuition auto; right.
      pose proof H1.
      eapply intermediate_parent in H1; try exact H.
      intuition subst; eauto.
      {
        eapply H2; eauto.
        etransitivity; cycle 1; eassumption.
      }
      {
        eapply H2 in H.
        intuition eauto.
      }
      {
        eapply H2; eauto.
        etransitivity; cycle 1; eassumption.
      }
    Qed.

    Context (rank_map_ok : map.ok rank_map).

    
    Lemma parent_rel_r_has_key m a x0
      : closed_graph m -> parent_rel m a x0 ->
        has_key x0 m.
    Proof.
      induction 2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Lemma unloop_parent l m x y a b
      : forest l m ->
        In x l ->
        a <> x ->
        parent_rel m a b ->
        parent_rel (map.put m x y) a b.
    Proof.
      intros ? ?.
      eapply forest_root_iff in H0; eauto.
      clear l H.
      intros ? ?.
      revert H0 H.
      induction H1;
        basic_goal_prep;
        basic_utils_crush.
      { constructor 1; basic_utils_crush. }
      {
        eqb_case b x.
        {
          replace c with x in *.
          { constructor 1; basic_utils_crush. }
          { eapply parent_rel_loop in H1; eauto. }
        }
        { econstructor 2; basic_utils_crush. }
      }
    Qed.
        

    Lemma root_redirect_spec uf uf' x y l rx ry ry'
      : union_find_ok uf l ->
        In x l ->
        In y l ->
        x <> y ->
        map.get uf.(rank) x = Some rx ->
        map.get uf.(rank) y = Some ry ->
        rx <= ry ->
        (*allows for successor or not *)
        rx < ry' ->
        ry <= ry' ->
        uf' = MkUF (map.put uf.(rank) y ry')
                     (map.put uf.(parent) x y)
                     (Nat.max uf.(max_rank) ry')
                     uf.(next) ->
        let l' := (removeb eqb x l) in
        union_find_ok uf' l'
        /\ In y l'
        /\ incl l' l
        /\ iff2 (uf_rel_PER uf')
             (union_closure_PER (uf_rel_PER uf) (singleton_rel x y)).
    Proof.
      cbn; intros; subst.
      assert (forall A B, (A /\ (A -> B)) -> A /\ B) as Hprop
          by intuition; apply Hprop; clear Hprop.
      intuition eauto.
      {
        destruct uf, H; constructor; cbn in *; eauto.
        { eapply forest_put_in; eauto. }
        {
          basic_goal_prep.
          eqb_case k y; basic_utils_crush.
          eqb_case k x; basic_utils_crush.
        }
        {
          basic_goal_prep.
          eqb_case i x; basic_utils_crush.
          { rewrite H3; cbn; Lia.lia. }
          eqb_case i y; basic_utils_crush.
          {
            assert (map.get parent0 y = Some y).
            { eapply forest_root_iff; eauto. }
            replace j with y in * by congruence.
            rewrite H4; cbn.
            exfalso.
            basic_utils_crush.
          }
          pose proof H as H';
            eapply rank_covers_domain0 in H';
            break.
          rewrite H11.
          eqb_case y j.
          {
            basic_utils_crush.
            cbn.
            eapply rank_increasing0 in H; eauto.
            rewrite H11, H4 in *; cbn in *.
            Lia.lia.
          }
          basic_utils_crush.
          eapply rank_increasing0 in H; eauto.
          rewrite H11 in *.
          cbn in *; case_match; tauto.
        }
        {
          intros; eqb_case i y;
            basic_utils_crush.
          1: Lia.lia.
          eapply maximum_rank0 in H; Lia.lia.
        }
      }
      { eapply In_removeb_diff; eauto. }
      { repeat intro; eapply In_removeb_In; eauto. }
      {
        split; intros.
        {
          unfold uf_rel_PER in *; cbn in *.
          apply union_clo_PER_l.
          induction H9; basic_goal_prep.
          {
            eqb_case x a; basic_goal_prep;
              autorewrite with utils inversion in *;
              basic_goal_prep; subst; eauto.
            { constructor 1; right; cbv; intuition auto. }
            { constructor 1; left; eauto. }
          }
          { etransitivity; eauto. }
          { symmetry; auto. }
        }
        {
          unfold uf_rel_PER; cbn.
          induction H9; basic_goal_prep;
            [| etransitivity; eauto | symmetry; auto ].
          unfold singleton_rel in *.
          eqb_case a x.
          {
            intuition subst; eauto.
            {
              eqb_case x b.
              {
                etransitivity; [| symmetry]; constructor 1;
                  basic_utils_crush.
              }
              {
                unfold uf_rel_PER in *.
                eapply closed_graph_PER_shared_parent in H10;
                  eauto using uf_forest, forest_closed.
                break.
                eapply parent_rel_loop in H10.
                2:{ eapply forest_root_iff; eauto using uf_forest. }
                subst.
                symmetry.
                eapply trans_PER_subrel.
                (*TODO: should be a lemma*)
                clear H H8.
                revert H9.
                induction H11; basic_goal_prep;
                  basic_utils_crush.
                { constructor 1; basic_utils_crush. }
                {
                  eqb_case b c.
                  { constructor 1; basic_utils_crush. }
                  { eapply trans_clo_step; basic_utils_crush. }
                }
              }
            }
            { constructor; basic_utils_crush. }
          }
          {
            intuition eauto.
            unfold uf_rel_PER in *.
            eapply closed_graph_PER_shared_parent in H11;
                  eauto using uf_forest, forest_closed.
            break.
            eqb_case b x.
            {
              eapply parent_rel_loop in H11.
              2:{ eapply forest_root_iff; eauto using uf_forest. }
              subst.
              eapply trans_PER_subrel.
              eapply unloop_parent; eauto using uf_forest.
            }
            {
              etransitivity;[|symmetry];
                eapply trans_PER_subrel.
              all: eapply unloop_parent; eauto using uf_forest.
            }
          }
        }
      }
    Qed.

    Lemma forest_PER_shared_parent l m
      : forest l m ->
        iff2 (PER_closure (fun i j : idx => map.get m i = Some j))
          (fun x y : idx => exists i : idx, limit (parent_rel m) x i
                                            /\ limit (parent_rel m) y i).
    Proof.
      split.
      2:{
        basic_goal_prep.
        unfold limit in *.
        eapply closed_graph_PER_shared_parent; eauto using forest_closed.
        eexists; intuition eauto.
      }
      {
        intros.
        eapply closed_graph_PER_shared_parent in H0; eauto using forest_closed.
        basic_goal_prep.
        pose proof H0;
          pose proof H1;
          eapply parent_rel_has_key in H0, H1.
        eapply forest_root_limit in H0, H1; eauto.
        break.
        pose proof H2; pose proof H3;
          eapply confluent_limit in H2, H3; eauto.
        intuition subst; eauto using transitive_limit.
      }
    Qed.
        
    
    (*TODO: break into smaller lemmas?*)
    Lemma union_spec uf uf' x y z l
      : union_find_ok uf l ->
        has_key x uf.(parent) ->
        has_key y uf.(parent) ->
        union uf x y = (uf', z) ->
        exists l',
          union_find_ok uf' l' 
          /\ In z l'
          /\ incl l' l
          /\ iff2 (uf_rel_PER uf') (union_closure_PER (uf_rel_PER uf) (singleton_rel x y)).
    Proof.
      unfold union; intros.
      do 2 case_match.
      eapply find_spec in case_match_eqn; eauto; break.
      eapply find_spec in case_match_eqn0; eauto; break.
      2: eapply H8; now eauto.
      eqb_case i i0.
      {
        autorewrite with inversion in *; break; subst.
        exists l; basic_utils_crush.
        unfold uf_rel_PER.
        rewrite union_closure_PER_subrel.
        2:{
          intros.
          unfold singleton_rel in *; break; subst.
          etransitivity;[| symmetry].
          all:apply trans_PER_subrel; apply H6; eauto.
        }
        split; intro HPER; apply closed_graph_PER_shared_parent in HPER;
          try (eapply forest_closed; eapply uf_forest; eauto);
          break.
        {
          eapply H12 in H2, H15.
          eapply H6 in H2, H15.
          etransitivity;[|symmetry]; eapply trans_PER_subrel; eauto.
        }
        {
          pose proof (parent_rel_has_key _ _ _ H2).
          pose proof (parent_rel_has_key _ _ _ H15).
          eapply forest_root_limit in H16, H17; eauto using uf_forest.
          break.
          assert (limit (parent_rel (parent uf)) b x1).
          {
            eapply union_find_limit; intuition eauto.
            eapply H18 in H2; intuition subst; eauto.
            etransitivity; eauto.
          }
          eapply H7 in H18, H20.
          eapply H13 in H18, H20.          
          etransitivity;[|symmetry]; eapply trans_PER_subrel; eauto;
            [ eapply H18 | eapply H20].
        }
      }
      case_match.
      {
        inversion H2; clear H2.
        symmetry in H17.
        subst z.
        pose proof H4; eapply forest_root_iff in H4; eauto using uf_forest.
        pose proof H10; eapply forest_root_iff in H10; eauto using uf_forest.
        eapply rank_covers_domain in H4, H10; eauto.
        break.
        rewrite H4, H10 in *; cbn in *.
        rewrite PeanoNat.Nat.compare_eq_iff in *.
        pose proof H17;
        eapply root_redirect_spec in H17; subst; try eassumption; eauto; try Lia.lia.
        eexists; intuition eauto.
        etransitivity; try eassumption.
        clear H21.
        unfold uf_rel_PER.
        rewrite !union_clo_PER_l.

        assert (limit (parent_rel (parent u)) x i).
        { eapply union_find_limit; eauto. }
        assert (limit (parent_rel (parent u)) y i0).
        { eapply union_find_limit; eauto. }
        eapply H13 in H20, H21; destruct H20, H21.
        rewrite <- union_closure_PER_singleton_transport; eauto.
        rewrite union_closure_PER_singleton_sym.
        rewrite <- union_closure_PER_singleton_transport; eauto.
        etransitivity; [|apply union_clo_PER_l].
        etransitivity; [symmetry;apply union_clo_PER_l|].
        eapply union_closure_PER_Proper; try reflexivity.
        rewrite !forest_PER_shared_parent; eauto using uf_forest.
        split; repeat intro; break; eexists; split;
          try apply H7; eauto; try apply H13; eauto;
          try apply H7; eauto.
      }
      {
        inversion H2; clear H2.
        symmetry in H17.
        subst z.
        pose proof H4; eapply forest_root_iff in H4; eauto using uf_forest.
        pose proof H10; eapply forest_root_iff in H10; eauto using uf_forest.
        eapply rank_covers_domain in H4, H10; eauto.
        break.
        rewrite H4, H10 in *; cbn in *.
        rewrite PeanoNat.Nat.compare_lt_iff in *.
        pose proof H17;
        replace (rank u0) with (map.put (rank u0) i x1) in H17.
        2:{
          eapply map.map_ext; intro k; eqb_case k i;
            basic_utils_crush.
        }
        replace (max_rank u0) with (Nat.max (max_rank u0) x1) in H17.
        2:{
          eapply maximum_rank in H4; eauto.
          Lia.lia.
        }
        eapply root_redirect_spec in H17; subst; try eassumption; eauto; try Lia.lia.
        replace (map.put (rank u0) i x1) with (rank u0) in H17.
        2:{
          eapply map.map_ext; intro k; eqb_case k i;
            basic_utils_crush.
        }
        replace (Nat.max (max_rank u0) x1) with (max_rank u0) in H17.
        2:{
          eapply maximum_rank in H4; eauto.
          Lia.lia.
        }
        eexists; intuition eauto.
        etransitivity; try eassumption.
        clear H21.
        unfold uf_rel_PER.
        rewrite !union_clo_PER_l.

        assert (limit (parent_rel (parent u)) x i).
        { eapply union_find_limit; eauto. }
        assert (limit (parent_rel (parent u)) y i0).
        { eapply union_find_limit; eauto. }
        eapply H13 in H20, H21; destruct H20, H21.
        rewrite <- union_closure_PER_singleton_transport; eauto.
        rewrite union_closure_PER_singleton_sym.
        rewrite <- union_closure_PER_singleton_transport; eauto.
        etransitivity; [|apply union_clo_PER_l].
        etransitivity; [symmetry;apply union_clo_PER_l|].
        eapply union_closure_PER_Proper; try reflexivity.
        rewrite !forest_PER_shared_parent; eauto using uf_forest.
        split; repeat intro; break; eexists; split;
          try apply H7; eauto; try apply H13; eauto;
          try apply H7; eauto.
      }
      {
        inversion H2; clear H2.
        symmetry in H17.
        subst z.
        pose proof H4; eapply forest_root_iff in H4; eauto using uf_forest.
        pose proof H10; eapply forest_root_iff in H10; eauto using uf_forest.
        eapply rank_covers_domain in H4, H10; eauto.
        break.
        rewrite H4, H10 in *; cbn in *.
        rewrite PeanoNat.Nat.compare_gt_iff in *.
        pose proof H17.
        replace (rank u0) with (map.put (rank u0) i0 x0) in H17.
        2:{
          eapply map.map_ext; intro k; eqb_case k i0;
            basic_utils_crush.
        }
        replace (max_rank u0) with (Nat.max (max_rank u0) x0) in H17.
        2:{
          eapply maximum_rank in H10; eauto.
          Lia.lia.
        }
        eapply root_redirect_spec in H17; subst; try eassumption; eauto; try Lia.lia.
        replace (map.put (rank u0) i0 x0) with (rank u0) in H17.
        2:{
          eapply map.map_ext; intro k; eqb_case k i0;
            basic_utils_crush.
        }
        replace (Nat.max (max_rank u0) x0) with (max_rank u0) in H17.
        2:{
          eapply maximum_rank in H10; eauto.
          Lia.lia.
        }
        eexists; intuition eauto.
        etransitivity; try eassumption.
        clear H21.
        unfold uf_rel_PER.
        rewrite !union_clo_PER_l.

        assert (limit (parent_rel (parent u)) x i).
        { eapply union_find_limit; eauto. }
        assert (limit (parent_rel (parent u)) y i0).
        { eapply union_find_limit; eauto. }
        eapply H13 in H20, H21; destruct H20, H21.
        rewrite union_closure_PER_singleton_sym.
        rewrite <- union_closure_PER_singleton_transport; eauto.
        rewrite union_closure_PER_singleton_sym.
        rewrite <- union_closure_PER_singleton_transport; eauto.
        etransitivity; [|apply union_clo_PER_l].
        etransitivity; [symmetry;apply union_clo_PER_l|].
        eapply union_closure_PER_Proper; try reflexivity.
        rewrite !forest_PER_shared_parent; eauto using uf_forest.
        split; repeat intro; break; eexists; split;
          try apply H7; eauto; try apply H13; eauto;
          try apply H7; eauto.
      }
    Qed.

    
  Lemma find_preserves_domain (uf uf': union_find) l i j
    : union_find_ok uf l ->
      Sep.has_key i uf.(parent) ->
      find uf i = (uf', j) ->
      forall x,
        Sep.has_key x uf.(parent) <->
          Sep.has_key x uf'.(parent).
  Proof using idx_map_ok Eqb_idx_ok.
    intros.
    eapply find'_find in H; eauto; try Lia.lia.
    rewrite H1 in *.
    eapply find'_preserves_domain in H; eauto.
  Qed.
    
End __.
 

Arguments UnionFind.find {idx}%type_scope {Eqb_idx idx_map rank_map} pat x.
Arguments parent {idx}%type_scope {idx_map rank_map} u.
Arguments union_find_ok {idx}%type_scope {idx_map} {rank_map} uf l%list_scope.
