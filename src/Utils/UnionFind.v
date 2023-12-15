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

From Utils Require Import Utils Monad Sep.



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
  Fixpoint find_aux (mr : nat) f i : option (idx_map * idx) :=
    match mr with
    | O => None
    | S mr =>
          @! let fi <- map.get f i in
            if eqb fi i then
              ret (f,i)
            else
              let (f, r) <- find_aux mr f fi in
              let f := map.put f i r in
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
    match find u a, find u b with
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

  (*
  (* TODO: custom remove fn to improve performance over firstn skipn *)
  Lemma cancel_at_ns n1 n2 l1 l2
    : (forall m, nth n1 l1 (lift True) m -> nth n2 l2 (lift False) m) ->
      (forall m, seps (firstn n1 l1 ++ skipn (S n1) l1) m ->
                 seps (firstn n2 l2 ++ skipn (S n2) l2) m) ->
      (forall m, seps l1 m -> seps l2 m).
  Admitted.

  Lemma sep_apply_at_n l_lem P_lem
    (lemma : forall m, seps l_lem m -> P_lem m)
    n l1 l2
    : (forall m, seps l1 m ->
                 seps (firstn n l2 ++ l_lem ++ skipn (S n) l2) m) ->
      P_lem = nth n l2 (lift False) ->
      (forall m, seps l1 m -> seps l2 m).
  Proof. Admitted.

  
  Lemma sep_apply_at_n_in_H l_lem P_lem
    (lemma : forall m, P_lem m -> seps l_lem m)
    n l1 l2
    : (forall m, seps (firstn n l1 ++ l_lem ++ skipn (S n) l1) m ->
                 seps l2 m) ->
      P_lem = nth n l1 (lift True) ->
      (forall m, seps l1 m -> seps l2 m).
  Proof. Admitted.
  *)
  
(*

  Lemma sep_sequent_focus perm1 perm2 l1 l2
    : NoDup perm1 ->
      NoDup perm2 ->
    (forall m, seps (select_all l1 perm1) m ->
                    seps (select_all l2 perm2) m) ->
    (forall m, seps (remove_all l1 perm1) m ->
                    seps (remove_all l2 perm2) m) ->
      (forall m, seps l1 m -> seps l2 m).
  Proof.
    intros Hnd1 Hnd2 Hs Hr m.
    rewrite seps_permutation with (l1:=l1) (l2:= permute l1 perm1),
        seps_permutation with (l1:=l2) (l2:= permute l2 perm2)
      by eauto using permute_permutation.
    unfold permute.
    rewrite !sep_concat.
    eapply sep_consequence; eauto.
  Qed.*)

  (*
    Lemma sep_sequent_apply l1_lem l2_lem
    (lemma : forall m, seps l1_lem m -> seps l2_lem m)
    n1s n2s l1 l2
    : NoDup n1s ->
      NoDup n2s ->
    (forall m, seps (map (fun n1 => nth n1 l1 (lift True)) n1s) m ->
                    seps (map (fun n2 => nth n2 l2 (lift False)) n2s) m) ->
      (forall m, seps (firstn n1 l1 ++ skipn (S n1) l1) m ->
                 seps (firstn n2 l2 ++ skipn (S n2) l2) m) ->
      (forall m, seps l1 m -> seps l2 m).
  Admitted.
    Proof. Admitted.
   *)

  
 (*
  Lemma forest_node'' i j
    : i <> j -> forall m, seps [and1 (forest_ptsto i) (not1 (has_key j)); ptsto i j] m ->
                          forest_ptsto j m.
  Proof.
    intros.
    eapply forest_node; eauto.
    unfold seps in *.
    unfold and1 in *;
      basic_utils_crush.
    seprewrite.
    rewrite sep_emp_r in H0.
    autorewrite with utils in *.
    ; eauto.

    TODO: how to get H0 to rewrite?
    autorewrite with utils in *.
    eapply sep_consequence; [| | eassumption];
  Qed.
  *)

  
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

  
  Lemma sep_sequent_focus perm1 perm2 l1 l2
    : Is_true (no_dupb perm1) ->
      Is_true (no_dupb perm2) ->
      (seps_Uimpl1 (Permutation.select_all l1 perm1) (Permutation.select_all l2 perm2)) ->
      (seps_Uimpl1 (Permutation.remove_all l1 perm1) (Permutation.remove_all l2 perm2)) ->
      (seps_Uimpl1 (mem:=idx_map) l1 l2).
  Proof.
  Admitted.

  Ltac sep_focus' p1 p2 :=
  simple apply sep_sequent_focus with (perm1 := p1) (perm2 := p2);
   [ vm_compute; exact I | vm_compute; exact I | cbn.. ].

  (*TODO: move to Sep.v*)
  Ltac sep_apply_focused p1 p2 l :=
    sep_focus' p1 p2;
    [  cbv [seps seps_Uimpl1];
       intros m H; seprewrite;
       revert m H; solve[simple apply l]
    |].

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
      { rewrite <- H, <-HeqH in H3; tauto. }
      { rewrite <- H, <-HeqH in H2; tauto. }
    }
    {
      exists x, x0.
      pose proof H0.
      eapply Properties.map.get_split with (k:=i) in H0; eauto.
      destruct H0; basic_goal_prep;rewrite <- H0, <-HeqH;
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
      destruct H as [H | [ H | H]];
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

  
  Lemma split_has_key_l a x x0 (k:idx)
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
    rewrite H, <- HeqH; auto.
  Qed.
  Hint Resolve split_has_key_l : utils.
  
  
  Lemma split_has_key_r a x x0 (k:idx)
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

    
    Lemma has_key_empty (i : idx) : has_key i map.empty <-> False.
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
          destruct H0 as [m1 [m2 [Hsplit [ H0l H0r]]]].
          unfold and1 in *.
          basic_utils_crush.
          revert H0.
          eapply mem_order_none_not_in; eauto.
        }
      }
    Qed.
    
    (*
  Inductive ptsto_trans m : idx -> idx -> Prop :=
  | ptsto_trans1 i j : map.get m i = Some j -> ptsto_trans m i j
  | ptsto_trans_step i j k
    :  map.get m i = Some j ->
       ptsto_trans m j k ->
       ptsto_trans m i k.

  
  Lemma ptsto_trans_empty i j
    : ptsto_trans map.empty i j <-> False.
  Proof.
    intuition idtac.
    induction H;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite ptsto_trans_empty : utils.
  
  Lemma forest_ptsto_trans_nonrefl m i
    : forest_ptsto i m ->
      forall j, ~ ptsto_trans m j j.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    (*
    argument:
      -j ->k is on one side for some k
      -either k = i or k on the same side: issue: this is the lemma below!*)
  Abort.*)
    
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
        destruct H0 as [? [? [? [? ?]]]].
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
        destruct H0 as [? [? [? [? ?]]]].
        exists a;
          basic_utils_crush.
      }
      {
        destruct H0 as [? [? [? [? ?]]]].
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
      destruct H as [? [? [? [? ?]]]].
      eapply IHl; eauto.
      basic_utils_crush.
    Qed.

    (*
  Lemma forest_loop_canonical l f' j
    : forest l f' ->
      Some j = map.get f' j ->
      In j l.
  Proof.
    unfold forest, tree.
    intros.
    eapply distribute_get in H; [|eauto].
    destruct H.
    {
      exfalso.
      destruct H as [? [? [? [? ?]]]].
      unfold and1 in *; basic_goal_prep;
        basic_utils_crush.
      clear H2 H.
      unfold forest_list in *.
      eapply  distribute_get_seps' in H1; eauto.
      basic_goal_prep.
      rewrite in_map_iff in H.
      basic_goal_prep.
      subst.
      unfold and1 in *;
        basic_goal_prep.
      apply forest_ptsto_order in H.
      destruct H.
      unfold mem_order, and1 in *.
      basic_goal_prep.
      assert (has_key j x2).
      {
        unfold has_key; rewrite H1; exact I.
      }
      apply H5 in H1.
      destruct H1;
        [ eapply in_before_antirefl; eauto | subst].
      {
        rewrite H4.
        apply Properties.map.keys_NoDup.
      }
      {
        apply H.
        rewrite H4.
        apply map_keys_in'; eauto.
      }
      }
    {
      destruct H as [? [? [? [? ?]]]].
      unfold and1 in *.
      
      basic_goal_prep.
      eapply forest_root_loop_canonical; eauto.      
    }
  Qed.
     *)

    
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
            destruct H as [? [? [? ?]]]; break.
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
                destruct H0 as [?  [? ?]]; break.
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
         find_aux mr f i = Some (f', j) ->
         j = k /\ tree j f'.
    Proof.    
      revert f i f' j.
      induction mr;
        basic_goal_prep; [congruence|].
      revert H0; case_match; [|congruence].
      case_match; autorewrite with bool utils in *;
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
        autorewrite with bool utils in *; basic_goal_prep;
          subst.
        symmetry in HeqH2.
        eapply IHmr in HeqH2; eauto.
        basic_goal_prep; subst.
        eauto using tree_put.
      }
    Qed.



    Hint Resolve Properties.map.same_domain_refl : utils.
    
    Lemma find_aux_domain mr f i f' j
      : find_aux mr f i = Some (f', j) ->
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
        symmetry in HeqH0; apply IHmr in HeqH0.
        eapply Properties.map.same_domain_trans; eauto.
        assert (has_key i r).
        {
          unfold has_key; case_match; eauto.
          clear IHmr.
          unfold map.same_domain, map.sub_domain in *; break.
          symmetry in HeqH.
          eapply H0 in HeqH.
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
      destruct 1 as [? [? [? [? ?]]]].
      intro HQ.
      eapply HQ in H1.
      eapply Properties.map.get_split_grow_l; eauto.
    Qed.
    
    Lemma find_aux_frame mr f i f' j Q f_Q
      :  sep Q (eq f) f_Q ->
         find_aux mr f i = Some (f', j) ->
         exists f'_Q, find_aux mr f_Q i = Some (f'_Q, j) /\ sep Q (eq f') f'_Q.
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
            rewrite <- HeqH0 in H2.
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
            symmetry in HeqH1.
            (* assert (map.get f_Q i = Some i0) as HgetQ.
          {
            eapply sep_get_some_r; eauto.
            basic_goal_prep; subst.
            eauto.
          }*)
            pose proof HeqH1 as Heqaux.
            eapply IHmr in HeqH1; eauto.
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
              symmetry in HeqH0.
              destruct Heqaux.
              unfold map.sub_domain in *.
              eapply H3 in HeqH0.
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
         find_aux mr f i = Some (f', j) ->
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

    Section Closure.
      Context {A : Type}
        (R : A -> A -> Prop).
      Inductive equivalence_closure : A -> A -> Prop :=
      | eq_clo_base a b : R a b -> equivalence_closure a b
      | eq_clo_refl a : equivalence_closure a a
      | eq_clo_trans a b c : equivalence_closure a b -> equivalence_closure b c -> equivalence_closure a c
      | eq_clo_sym a b : equivalence_closure a b -> equivalence_closure b a.
      Hint Constructors equivalence_closure : utils.
    End Closure.
    Hint Constructors equivalence_closure : utils.
    
    Definition reachable (m : idx_map) := equivalence_closure (fun i j => map.get m i = Some j).
    Definition iff2 {A B} R1 R2 := forall (a:A) (b:B), R1 a b <-> R2 a b.

    Lemma iff2_refl A B (R : A -> B -> Prop) : iff2 R R.
    Proof. unfold iff2; firstorder fail. Qed.
    Hint Resolve iff2_refl : utils.
    
    Lemma iff2_trans A B (R1 R2 R3 : A -> B -> Prop) : iff2 R1 R2 -> iff2 R2 R3 -> iff2 R1 R3.
    Proof.
      unfold iff2.
      intros.
      rewrite H.
      eauto.
    Qed.
    (*Hint Resolve iff2_trans : utils.*)

    Lemma equivalence_closure_proper A
      : Proper (iff2 ==> iff2) (@equivalence_closure A).
    Proof.
      cbv.
      (*Enough to prove one side *)
      enough (forall x y : A -> A -> Prop,
                 (forall a b : A, (x a b -> y a b)) ->
                 forall a b : A,
                   (equivalence_closure x a b -> equivalence_closure y a b)).
      { intros; break; split; eapply H; eapply H0. }
      {
        intros.
        induction H0; basic_goal_prep;
          basic_utils_crush.
      }
    Qed.

    (* Doesn't work b/c of cycles; need trees, sep
    Lemma find_aux_spec mr f i f' j
      : find_aux mr f i = Some (f', j) ->
        reachable f i j
        /\ iff2 (reachable f) (reachable f').
    Proof.
      unfold reachable.
      revert f i f' j.
      induction mr;
        basic_goal_prep.
      1:basic_utils_crush.
      revert H; case_match;[|congruence].
      eqb_case i0 i.
      {
        basic_utils_crush.
      }
      {
        case_match;[|congruence].
        break.
        basic_goal_prep;
          autorewrite with utils in *;
          break; subst.
        symmetry in HeqH0; apply IHmr in HeqH0.
        basic_utils_crush.
        eapply iff2_trans; eauto.
        clear H1.
        intros i1 j1.
        
        eqb_case i i1.
        2:{
          apply equivalence_closure_proper.
          intros i1 j1.
        
        }
        }*)

   

   
(*    
    Lemma find_aux_split mr f i f' j
      :  find_aux mr f i = Some (f', j) ->
         exists ft fQ ft', map.split f ft fQ
                           /\ find_aux mr ft i = Some (ft', j)
                           /\ tree j ft
                           /\ In i (map.keys ft).
    Proof.
      revert f f' i j.
      induction mr;
        basic_goal_prep;
        basic_utils_crush.
      revert H; case_match;[|congruence].
      eqb_case i0 i.
      {
        basic_goal_prep;
          basic_utils_crush.
        exists (map.singleton j j), (map.remove f' j), (map.singleton j j).
        basic_utils_crush.
        {
          rewrite Properties.map.put_idemp; eauto.
        }
      }
      {
        case_match;[|congruence].
        basic_goal_prep;
          basic_utils_crush.
        symmetry in HeqH0; eapply IHmr in HeqH0.
        break.
        exists (map.put x i i0) , (map.remove x0 i), (map.put x1 i j).
        split.
        {
          eapply split_put_remove; eauto.
        }
        {
          basic_utils_crush.
          2:{
            revert H3; case_match; [intros _|tauto].
            eapply tree_split with (j:= i) in H2; eauto.
            2:{
            {
              replace (map.put x i i0) with x.
              2:{
                eapply map.map_ext.
                intro k; eqb_case k i;
                  basic_utils_crush.
                unfold seps,sep in H2.
                break.
                repeat (autorewrite with utils in *; break; subst; try eapply eqb_boolspec; eauto;[]).
                eapply Properties.map.get_split_grow_l; eauto.
                basic_utils_crush.
              }
              eapply tree_
              replace 
              basic_utils_crush.
              eapply tree_join.
              destruct H2.
            TODO: use mem_order ?
            TODO: need tree insert lemma; stronger than tree_put (i0 in tree, not = j)
                                                   Note: need i notin x? if not, could induce cycle
          replace (map.get x i) with (Some i0).
          {
            basic_utils_crush.
            rewrite H1.
            reflexivity.
          }
          {
            pose proof H0.
            apply Properties.map.get_split with (k:= i) in H0; eauto.
            basic_utils_crush.
            1:congruence.
            exfalso.
            TODO: need i in tree j
          }
      case_match;[|congruence].
        
    }
 *)

  
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
      find_aux mr f i = Some (f', j) ->
      j = k /\ forest (k::l) f'.
  Proof.
    revert k l f i f' j.
    induction mr;
      basic_goal_prep; [congruence|].
      revert H0; case_match; [|congruence].
      case_match; autorewrite with bool utils in *;
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
        autorewrite with bool utils in *; basic_goal_prep;
          subst.
        symmetry in HeqH2.
        
        (*
        assert (has_key i r).
        {
          assert (has_key i f) by admit.
          eapply find_aux_domain in HeqH2.
          unfold map.same_domain, map.sub_domain in HeqH2.
          break.
          unfold has_key in *.
          revert H0; repeat (case_match; try tauto).
          symmetry in HeqH2.
          eapply H1 in HeqH2.
          break; congruence.
        }*)
        
        
        eapply IHmr with (k:=k) (l:=l)in HeqH2; eauto.
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
      find_aux mr f i = Some (f', j) ->
      reachable f i j.
  Proof.
    revert f f' i j.
    induction mr;
      basic_goal_prep; [ congruence|].
    revert H0; case_match;[|congruence].
    eqb_case i0 i.
    {
      symmetry in HeqH0.
      intros; basic_utils_crush.
      eapply  eq_clo_base; eauto.
    }
    {
      case_match; [|congruence].
      break.
      symmetry in HeqH1.
      intros.
      safe_invert H1.
      eapply IHmr in HeqH1.
      {
        break.
        eapply eq_clo_trans; eauto.
        eapply eq_clo_base; eauto.
      }
      symmetry in HeqH0.
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

  
  Lemma has_key_split m x x0 (i:idx)
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
  
  Lemma split_both_have_key (x:idx) m m1 m2
    : map.split m m1 m2 ->
      has_key x m1 ->
      has_key x m2 ->
      False.
  Proof.
    unfold has_key;
      repeat case_match;
      try tauto.
    intros.
    eapply Properties.map.get_split with (k:= x) in H;
      intuition congruence.
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

  Lemma removeb_perm x l
    : NoDup l -> Permutation (x :: List.removeb (eqb (A:=idx)) x l) l.
  Admitted.
  
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
      find_aux mr f i = Some (f', j) -> forest l f'.
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
    : find_aux mr f i = Some (f', j) ->
      has_key i f.
  Proof.
    destruct mr;
      basic_goal_prep;
      try congruence.
    revert H; case_match;[|congruence].
    intros _.
    unfold has_key; rewrite <- HeqH; auto.
  Qed.
        
  Lemma find_aux_reachable_out' l mr f i f' j
    : forest l f ->
      find_aux mr f i = Some (f', j) ->
      reachable f i j.
  Proof.
    intros.
    pose proof H0 as H'; eapply find_aux_has_key in H'; eauto.
    revert H'; unfold has_key; case_match; try tauto; intros _.
    symmetry in HeqH1; eapply forest_has_key_tree in HeqH1; eauto; break.
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
   
  (*
  Lemma reachable_put r i j
    : reachable r i j ->
      iff2 (reachable r) (reachable (map.put r i j)).
  Proof.
    
    induction 1.*)
  
  Lemma find_aux_reachable_iff l mr f i f' j
    : (forest l) f ->
      find_aux mr f i = Some (f', j) ->
      iff2 (reachable f) (reachable f').
  Proof.    
    revert f f' i j.
    induction mr;
      basic_goal_prep; [ congruence|].
    revert H0; case_match;[|congruence].
    eqb_case i0 i.
    {
      symmetry in HeqH0.
      intros; basic_utils_crush.
    }
    {
      case_match; [|congruence].
      break.
      symmetry in HeqH1.
      intros.
      safe_invert H1.
      pose proof HeqH1.
      eapply IHmr in HeqH1.
      {
        eapply iff2_trans; eauto.
        assert (reachable r i j).
        {
          eapply HeqH1.
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

     
  Lemma find_aux_spec l mr f i f' j
    : forest l f ->
      find_aux mr f i = Some (f', j) ->
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
 
  (*
  Definition uf_ok (uf : union_find) :=
    exists l, forest l uf.(parent).*)

  Definition uf_rel uf1 := reachable uf1.(parent).
  
  (* Note: partial spec. Characterizing when it returns None doesn't help with using
     union find for egraphs.
   *)
  Lemma find_spec (uf uf' : union_find) i j l
    : forest l uf.(parent) ->
      find uf i = Some (uf', j) ->
      forest l uf'.(parent)
      /\ In j l
      /\ iff2 (uf_rel uf) (uf_rel uf') /\ (uf_rel uf i j).
  Proof.
    destruct uf, uf'.
    unfold find, uf_rel.
    my_case Haux (find_aux (S max_rank0) parent0 i); cbn;[| congruence].
    intros; break.
    safe_invert H0.
    eapply find_aux_spec in Haux; intuition eauto.
  Qed.
  
  Definition union_closure {A : Type} (R1 R2 : A -> A -> Prop) :=
    equivalence_closure (fun a b => R1 a b \/ R2 a b).

  Definition singleton_rel {A : Type} (x y : A) a b : Prop := a = x /\ b = y.

  Definition impl2 {A} (R1 R2 : _ -> _ -> Prop) : Prop := forall a b : A, R1 a b -> R2 a b.
  
  Instance equivalence_closure_impl_proper A
    : Proper (@impl2 A ==> impl2) equivalence_closure.
  Proof.
    unfold Proper, respectful, impl2.
    intros.
    induction H0; basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma union_clo_equiv_l A (R1 R2 : A -> _)
    : iff2 (union_closure (equivalence_closure R1) R2)
        (union_closure R1 R2).
  Proof.
    unfold union_closure.
    split.
    {
      induction 1; basic_goal_prep;
        basic_utils_crush.
      eapply equivalence_closure_impl_proper; eauto.
      unfold impl2; intuition eauto.
    }
    {
      induction 1; basic_goal_prep;
        basic_utils_crush.
    }
  Qed.

  Lemma iff2_sym A B (R1 R2 : A -> B -> Prop) : iff2 R1 R2 -> iff2 R2 R1.
  Proof using.
    unfold iff2; intuition; eapply H; eauto.
  Qed.

   Add Parametric Relation A B : (A -> B -> Prop) (@iff2 A B)
      reflexivity proved by ltac:(intros a b; intuition)
      symmetry proved by (@iff2_sym A B)
      transitivity proved by (@iff2_trans A B)
       as iff2_rel.
   
   Lemma union_closure_subrel A (R1 R2 : A -> A -> Prop)
     : (forall a b, R2 a b -> (equivalence_closure R1) a b) ->
       iff2 (union_closure (equivalence_closure R1) R2) (equivalence_closure R1).
   Proof.
     intros.
     split.
     2:{
       intros; eapply union_clo_equiv_l.
       unfold union_closure.
       eapply equivalence_closure_impl_proper; eauto.
       intros a' b' H'; intuition.
     }
     {
      induction 1; basic_goal_prep;
        basic_utils_crush.
     }
   Qed.


   Lemma has_key_putmany (i:idx) m1 m2
     : has_key i (map.putmany m1 m2) <-> has_key i m1 \/ has_key i m2.
   Proof.
     unfold has_key.
     rewrite Properties.map.get_putmany_dec.
     my_case H2 (map.get m2 i);
       [ basic_utils_crush
       | case_match]; intuition fail.
   Qed.
   Hint Rewrite has_key_putmany : utils.

   
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
       replace (List.removeb (eqb (A:=idx)) i (x1 ++ j :: x2))
         with (j::List.removeb (eqb (A:=idx)) i (x1 ++ x2))
         by admit (*TODO: permutation*).
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
           admit (*Lemma disjoint_proper : Proper (map.same_domain ==> map.same_domain ==> iff) map.disjoint.*).
         }
       }
       {
         replace ((List.removeb (eqb (A:=idx)) i (x1 ++ x2))) with
         (x1++x2) by admit.
         exact H4.
       }
     }
     {
       cbn.
       (*TODO: similar to last goal?*)
   Abort.
  
  Lemma union_spec u x u' y z l
    : forest l u.(parent) ->
      union u x y = Some (u', z) ->
      exists l',
        forest l' u'.(parent)
        /\ In z l'
        /\ iff2 (uf_rel u') (union_closure (uf_rel u) (singleton_rel x y))
        /\ uf_rel u' y z.
  Proof.
    unfold union.
    my_case Hfx (find u x);break;cbn;[| congruence].
    my_case Hfy (find u0 y);break;cbn;[| congruence].
    intro.
    eapply find_spec in Hfx, Hfy; break; eauto.
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
        (*TODO: need new forest_put; also: where did removeb go?
        eapply forest_put'.
        apply H4 in H5.
        apply H1 in H2,H5.
        clear n n0 HeqH7 HeqH0 HeqH1.*)
        (*TODO: lost that i0, z canonical, breaking forest_put*)
  Admitted.


  End __.
