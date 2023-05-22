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
  | forest_node i j m
    : i <> j -> sep (and1 (forest_ptsto i) (not1 (has_key j))) (ptsto i j) m ->
      forest_ptsto j m.
  Set Elimination Schemes.
  Hint Constructors forest_ptsto : utils.

  Section ForestInd.
    Context (P : idx -> idx_map -> Prop)
      (P_empty : forall (i : idx) , P i map.empty)
      (P_join : forall (i : idx) (m : idx_map),
          sep (and1 (forest_ptsto i) (P i)) (and1 (forest_ptsto i) (P i)) m ->
          P i m)
      (P_node : forall (i j : idx) (m : idx_map),
          i <> j -> sep (and1 (and1 (forest_ptsto i) (not1 (has_key j))) (P i)) (ptsto i j) m ->  P j m).
                 
    Fixpoint forest_ptsto_ind
      (i : idx) (r : idx_map) (f2 : forest_ptsto i r) : P i r.
      refine (match f2 in (forest_ptsto i0 r0) return (P i0 r0) with
              | empty_forest i0 => P_empty i0
              | forest_join i0 m x => P_join i0 m _
              | forest_node i0 j m H x => P_node i0 j m H _
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

  
  Lemma putmany_singleton m (j k : idx)
    : (map.putmany m (map.singleton j k)) = map.put m j k.
  Proof.
    unfold map.singleton.
    rewrite <- Properties.map.put_putmany_commute,
      Properties.map.putmany_empty_r.
    auto.
  Qed.
  Hint Rewrite putmany_singleton : utils.


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
  
  Lemma sep_assoc (P Q H : idx_map -> _)
    : Uiff1 (sep (sep P Q) H) (sep P (sep Q H)).
  Proof.
    unfold Uiff1,sep;
      split;
      basic_goal_prep.
    {
      exists x1, (map.putmany x2 x0);
        basic_utils_crush.
  Admitted.
  
  Lemma sep_concat (l1 l2 : list (idx_map -> _))
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
    len1 len2 (l1 l2 : list (idx_map -> _))
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
  
  Fixpoint remove_all' {A} perm (l : list A) idx :=
    match l with
    | [] => []
    | a::l' => if inb idx perm
               then remove_all' perm l' (S idx)
               else a::remove_all' perm l' (S idx)
    end.
  Definition remove_all {A} (l : list A) perm :=
    remove_all' perm l 0.

  Fixpoint select_all {A} (l : list A) perm:=
    match perm with
    | [] => []
    | n::perm' =>
        match nth_error l n with
        | Some a => a::select_all l perm'
        | None => []
        end
    end.
  
  (*TODO: if slow, write a version that computes in (near) linear time *)
  Definition permute {A} (l : list A) (perm : list nat) :=
    (select_all l perm) ++ (remove_all l perm).

  Import Coq.Sorting.Permutation.

  Lemma permute_permutation A (l : list A) perm
    : NoDup perm ->
      Permutation l (permute l perm).
  Admitted.


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
  Qed.

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

  
  Lemma forest_node'' i j
    : i <> j -> forall m, seps [and1 (forest_ptsto i) (not1 (has_key j)); ptsto i j] m ->
                          forest_ptsto j m.
  Proof.
    intros.
    eapply forest_node; eauto.
    unfold seps in *.
    eapply sep_consequence; [| | eassumption]; unfold and1 in *;
      basic_utils_crush.
  Qed.

  
  Lemma sep_to_seps P Q m
    : sep P Q m <-> seps [P; Q] m.
  Proof.
    unfold seps;
      split; eapply sep_consequence;
      basic_goal_prep;
    basic_utils_crush.
  Qed.
  
  Ltac cancel_prep H :=
    let m := lazymatch type of H with _ ?m => m end in
    revert H;
    repeat lazymatch goal with H : context [?m] |- _ => clear H end;
    revert m.
  Ltac sep_focus p1 p2 :=        
    apply sep_sequent_focus with (perm1:=p1) (perm2:=p2);
    [ eapply use_no_dupb;[typeclasses eauto | vm_compute; exact I]
    | eapply use_no_dupb;[typeclasses eauto | vm_compute; exact I]
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
               (Q2:= (forest_ptsto i))in H; [| clear; unfold and1, has_key in *..];
          basic_goal_prep; eauto.
        basic_utils_crush.
        cancel_prep H.
        sep_focus [0;3] [2]; [eapply forest_join'|].
        eauto.
      }
      {
        eapply sep_consequence with (P2:=forest_ptsto i)
                                    (Q2:= seps [forest_ptsto j; ptsto j k; forest_ptsto i]) in H.
        
        2:{ unfold and1; basic_goal_prep; eauto. }
        2:{ unfold and1; basic_goal_prep; eauto. }
        change (sep ?P (seps ?l)) with (seps (P::l)) in H.
        cancel_prep H.
        sep_focus [0;3] [2]; [eapply forest_join'|].
        eauto.
      }
    }
    {
      eapply distribute_get in H0; eauto;
        destruct H0 as [H0 | H0];
        apply sep_to_seps in H0.
      2:{
        TODO: need Proper rw for seps
      
      TODO: cases i = j0; include H1 in H0
      cancel_prep H0.
      apply (sep_apply_at_n _ _ (forest_node'' i j H)) with (n:= 2); auto; cbn [app firstn skipn].
      apply cancel_at_ns with (n1:=1) (n2:=3); [ solve [auto] |cbn].
      
    }
  Qed.

Question: incorporate and1 into seps via list-of-lists?
  eapply sep_apply_at_n_in_H with (n:= 1).
        
          (*TODO: cancel H (ptsto i j) *)
      unfold and1, sep in *; break.
      basic_utils_crush.
      
      pose proof (eqb_spec i j);
        destruct (eqb i j);
        basic_utils_crush.
      {      
        exists (map.put x j k), map.empty.
        basic_utils_crush.
        1: apply eqb_boolspec; eauto.
        exists x.
        eexists; basic_utils_crush.
      }
      {
        exists (map.put x2 j k), (map.put x1 i j0).
        basic_utils_crush.
        1:admit.
        2: eapply forest_node'; eauto.
        2:admit.
        exists x2, (map.singleton j k); basic_utils_crush.
      }
    }
    {
      unfold and1, sep in *; break.
      pose proof H as H'.
      apply Properties.map.get_split with (k:=j) in H;
        basic_utils_crush.
      {
        rewrite H in H0; intuition break.
        clear H3.
        eexists; eexists.
        split; [| split].
        2:{
          eexists; eexists.
          split; [| split].
          3: eauto.
          2: eauto.
          eauto.
        }
        {
          clear H5.
          instantiate (1:=map.putmany x0 x2).
          Properties.map.split_disjoint_putmany
          
        {
          rewrite H in H0; intuition break.
        clear H3.
        exists (map.putmany (map.putmany x0 x3) x4); exists x2;
          basic_utils_crush.
        1:admit.
        exists ((map.putmany x0 x3))
        TODO: putmany
        
        eauto.
      congruence.
      TODO: split in j
      basic_utils_crush.
      
      {
        apply H3 in H0; break.
        repeat eexists;
          basic_utils_crush.
        {
          unfold map.singleton.
          rewrite <- Properties.map.put_putmany_commute,
            Properties.map.putmany_empty_r.
          TODO: contradiction in goal
          cbn.
          intuition eauto.
        exists ?, x3.
        exists (map.put x i j), map.empty.
        basic_utils_crush.
        revert j.
        2: eauto with utils.
        exists x, x0;
        intuition eauto.
      {
        bas
        eapply H3 in H0.
      basic_utils_crush.
      pose proof (eqb_spec i j0);
        destruct (eqb i j0);
        basic_utils_crush.
      pose proof (eqb_spec i k);
        destruct (eqb i k);
        basic_utils_crush.
      apply H4 in H0; auto.
    }
    {
      unfold and1, sep in *; break.
      pose proof H.
      eapply Properties.map.get_split with (k:=j) in H.
      basic_utils_crush.
      {
        rewrite H in H0.
        eapply H5 in H0;
          basic_utils_crush.
        firstorder.
        rewrite H.
        my_case Hg (map.get x k); auto.
        
      
    }


  
  Lemma forest_ptsto_has_next i m
    : forest_ptsto i m -> forall j k, map.get m j = Some k -> i = k \/ has_key k m.
  Proof.
    unfold has_key.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    2:{
      unfold and1, sep in *; break.
      basic_utils_crush.
      pose proof (eqb_spec j k);
        destruct (eqb j k); auto; right.
      basic_utils_crush.
      pose proof (eqb_spec i j0);
        destruct (eqb i j0);
        basic_utils_crush.
      apply H3 in H0.
      basic_utils_crush.
      pose proof (eqb_spec i k);
        destruct (eqb i k);
        basic_utils_crush.
    }
    {
      unfold and1, sep in *; break.
      pose proof (eqb_spec i k);
        destruct (eqb i k); auto; right.
      eapply Properties.map.get_split with (k:=j) in H.
      basic_utils_crush.
      {
        rewrite H in H0.
        eapply H4 in H0;
          basic_utils_crush.
        firstorder.
        rewrite H.
        my_case Hg (map.get x k); auto.
        
      
    }
      apply H3.
        H m i k

          Properties.map.get_split

  
  (* For specification purposes, does not appear in implementation *)
  Context (idx_set : map.map idx unit)
  (idx_set_ok : map.ok idx_set).

        Definition forest_set s m : Prop :=
          sep_all s forest_ptsto m.
      
  Lemma forest_at_uf_order_antirefl i m
    : forest_ptsto i m -> forall j k, uf_order m j k -> j <> k.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      unfold and1,sep in *; break.

      assert (has_key k m) by (eapply uf_order_has_key_l; eauto).
      Existing Instance eqb_boolspec.
      pose proof (Properties.map.get_split (key_eqb:=@eqb _ _) k _ _ _ H).
      destruct H6;
        break.
      {
        unfold has_key in *.
        rewrite H6 in H5.
        revert H5; case_match; [intros _|tauto].
        TODO: need forest_implies_in
        TODO: need i0 
        eapply H0; eauto.
        TODO: will need stronger IH for this
        TODO: order_disjoint
      
    Lemma uf_order_disjoint
      : disjoint_sum m1 m2 m ->
        has_key m1 k1 ->
        has_key m2 k2 ->
        uf_order m1
    TODO: key property combining separate orders
    
    intro; subst.
  
  (* includes a list of the ids *)
  Unset Elimination Schemes.
  Inductive forest_ptsto_list : list idx -> idx -> idx_map -> Prop :=
  | empty_forest_list i m : emp m -> forest_ptsto_list [] i m
  | forest_join_list i m l1 l2
    : sep (forest_ptsto_list l1 i) (forest_ptsto_list l2 i) m ->
      forest_ptsto_list (l1++l2) i m
  | forest_node_list l1 i j m
    : sep (forest_ptsto_list l1 i) (ptsto i j) m ->
      forest_ptsto_list (i::l1) j m.
  Hint Constructors forest_ptsto_list : utils.
  Set Elimination Schemes.

  Section ForestListInd.
    Context (P : list idx -> idx -> idx_map -> Prop)
      (P_empty : forall (i : idx) (m : idx_map), emp m -> P [] i m)
      (P_join : forall  (i : idx) (m : idx_map) l1 l2,
          (*TODO: really, should combine the 2 seps*)
          sep (forest_ptsto_list l1 i) (forest_ptsto_list l2 i) m ->
          sep (P l1 i) (P l2 i) m ->
          P (l1++l2) i m)
      (P_node : forall l (i j : idx) (m : idx_map),
          sep (forest_ptsto_list l i) (ptsto i j) m ->
          sep (P l i) (ptsto i j) m ->  P (i::l) j m).
                 
    Fixpoint forest_ptsto_list_ind
      l (i : idx) (r : idx_map) (f2 : forest_ptsto_list l i r) : P l i r.
      refine (match f2 in (forest_ptsto_list l0 i0 r0) return (P l0 i0 r0) with
              | empty_forest_list i0 m x => P_empty i0 m x
              | forest_join_list i0 m l1 l2 x => P_join i0 m l1 l2 x _
              | forest_node_list l1 i0 j m x => P_node l1 i0 j m x _
              end).
      Proof.
        all: eapply sep_impl_defined; try eassumption.
        all: try apply forest_ptsto_list_ind.
        all: auto.
      Qed.

  End ForestListInd.

  (*TODO: move to Sep.v*)
  Lemma sep_exists_l A P Q (m : idx_map)
    : sep (fun m => exists x : A, P x m) Q m
      <-> exists x : A, sep (P x) Q m.
  Proof.
    unfold sep;
      intuition (break; repeat eexists; eauto).
  Qed.
  Hint Rewrite sep_exists_l : utils.
  
  Lemma sep_exists_r A P Q (m : idx_map)
    : sep P (fun m => exists x : A, Q x m) m
      <-> exists x : A, sep P (Q x) m.
  Proof.
    unfold sep;
      intuition (break; repeat eexists; eauto).
  Qed.
  Hint Rewrite sep_exists_r : utils.
  
  Lemma forest_list_exists i m
    : forest_ptsto i m ->
      exists l, forest_ptsto_list l i m.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  (*TODO: move to utils.
   TODO: add sim. rewrite
   *)
  Hint Resolve incl_nil_l : utils.

  Require Import  Coq.Sorting.Permutation.

  (*TODO: move to coqutil*)
  Lemma map_keys_empty k v (m : map.map k v) (_ : map.ok m)
    : map.keys (map :=m) map.empty = [].
  Proof.
    unfold map.keys.
    apply Properties.map.fold_empty.
  Qed.
  Hint Rewrite map_keys_empty : utils.

  Hint Rewrite disjoint_empty_right' : utils.
  Hint Rewrite disjoint_empty_left' : utils.
  
  (*Local Existing Instance decidable_from_eqb_ok.*)

  Lemma disjoint_is_split m1 m2 m
    : disjoint_sum idx idx_map m1 m2 m
      <-> map.split m m1 m2.
  Proof.
    unfold map.split.
  Admitted.
  
  Lemma disjoint_sum_permut_keys x x0 m
    : disjoint_sum idx idx_map x x0 m ->
      Permutation (map.keys x ++ map.keys x0) (map.keys m).
  Proof.
    revert x0 m.
    apply Properties.map.map_ind with (m:=x);
      basic_goal_prep;
      basic_utils_crush.
    pose proof H1; rewrite  disjoint_is_split in H1.
    (*erewrite @Properties.map.split_comm with (ok:=idx_map_ok) in H1.*)
    epose proof (Properties.map.split_put_l2r _ _ _ _ _ H0 H1).
  Admitted.

    
  Lemma forest_list_range l i m
    : forest_ptsto_list l i m ->
      Permutation l (map.keys m).
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    {
      clear H; unfold sep in *.
        basic_goal_prep.
      eapply Permutation_trans.
      1: eapply Permutation_app; eauto.
      apply disjoint_sum_permut_keys; eauto.
    }
    {
      clear H; unfold sep in *.
      basic_goal_prep;
        basic_utils_crush.
      rewrite disjoint_is_split in H.
      unfold map.singleton in *.
      eapply Properties.map.split_put_r2l in H.
      2: basic_utils_crush.
      erewrite @Properties.map.split_empty_r in H; eauto; [|shelve].
      subst.
      unfold map.keys.
      (*
      TODO: need this lemma up to permutation
      erewrite Properties.map.fold_put.
       *)
      (*
      eapply Permutation_trans.
      1: eapply Permutation_app; eauto.
      apply disjoint_sum_permut_keys; eauto.
      cbn.
      apply incl_app.
      {
        unfold sep in *; break.
       *)
      admit.
  Admitted.

  (*
  Properties.map.keys_NoDup
  *)
    
  Definition tree_at i := 
    sep (forest_ptsto i) (ptsto i i).

  Fixpoint forest_at l :=
    match l with
    | [] => emp
    | i::l' =>
        sep (tree_at i) (forest_at l')
    end.

  Definition forest m := exists l, forest_at l m.


  Definition index_order {A} l (a b : A) : Prop :=
    exists n m,
      nth_error l n = Some a
      /\ nth_error l m = Some b
      /\ n < m.
  Require Import  Coq.Classes.RelationClasses.
  
  Lemma index_order_transitive {A} l (a b c : A)
    : NoDup l ->
      index_order l a b ->
      index_order l b c ->
      index_order l a c.
  Proof.
    unfold index_order;
      basic_goal_prep.
    exists x1, x0;
      intuition auto.
    enough (x2 = x) by Lia.lia.
  Admitted.

  Lemma index_order_antirefl {A} l (a b : A)
    : NoDup l ->
      index_order l a b ->
      a <> b.
  Admitted.

  (*TODO: write inv lemma, move to utils (or replace w/ fix) *)
  Hint Constructors NoDup : util.
  
  Lemma forest_ptsto_nodup l i m :
    forest_ptsto_list l i m ->
    NoDup l.
  Proof.
    intro H; apply forest_list_range in H.
    rewrite H.
    eapply Properties.map.keys_NoDup.
  Admitted.

  
      
  Lemma forest_ptsto_order l i m :
    forest_ptsto_list l i m ->
    forall x x', map.get m x = Some x' ->
                       (In x l /\ x = x') \/ index_order l x x'.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
(*    {
      exists []; basic_utils_crush.
      constructor.
    }
    {
      unfold sep in H0; break.
      exists (x1++x2); intuition idtac.
      TODO: need to know that the 2 are disjoint via disjoint_sum
        basic_utils_crush.
      TODO: don't get IHs here...
 *)
    Admitted.
    
  Lemma tree_at_order i m :
    tree_at i m ->
    exists l,
      NoDup l
      /\ (forall x x', map.get m x = Some x' ->
                       (In x l /\ x = x') \/ index_order l x x').
  Proof.
    (*
    intro H; apply 
    unfold tree_at.
    basic_goal_prep;
      basic_utils_crush.
    exists [i]; split; [repeat constructor|];
      basic_goal_prep;
      basic_utils_crush.
    left.
    unfold ptsto in H1; subst.
    *)
  Abort.
  
  Lemma find_cases u x u' y
    : find u x = Some (u', y) ->
      forest u.(parent) ->
      (x = y /\ map.get u.(parent) x = Some x)
      \/ (x <> y /\ exists u'' z, map.get u.(parent) x = Some z
                                  /\ u'.(parent) = map.put u''.(parent) x y
                                  /\ find u z = Some (u'',y)).
  Proof.
    unfold find.
    destruct u.
    basic_goal_prep.
    my_case H' (map.get parent0 x);[|congruence].
    pose proof (eqb_spec i x).
    destruct (eqb i x); subst.
    { intuition congruence. }
    my_case H'' (find_aux max_rank0 parent0 i); [| congruence].
    break.
    right.
    safe_invert H.
    simpl.
    TODO: want to say that find result ordered after input
    TODO: nocycles
    revert H.
    case_match.

  Lemma find_preserves_forest_at l
    : forall u,
      forest_at l u.(parent) ->
      forall u' x y,
        find u x = Some (u', y) ->
        forest_at l u'.(parent).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.

    
    1rewrite map.get_empty.

    
  Lemma find_idempotent1 u x u' y
    : forest u.(parent) ->
      find u x = Some (u', y) ->
      find u y = Some (u, y).
  Proof.
    destruct u.
    unfold find.
    cbn.
  
  Lemma find_equiv u x u' y
    : find u x = Some (u', y) -> interp_uf u x y.
  Abort.
  
  Lemma find_preserves_interp u x u' y
    (* Note: could probably prove = instead of <-> *)
    : find u x = Some (u', y) -> forall a b, interp_uf u a b <-> interp_uf u' a b.
  Abort.

  Lemma union_spec u x u' y
    : union u x y = Some (u', y) ->
        forall a b, interp_uf u' a b <-> interp_uf u a b \/ (interp_uf u a x /\ interp_uf u b y).
  Admitted.

  Lemma union_monotonic u x u' y
    : union u x y = Some (u', y) ->
      forall a b, interp_uf u a b -> interp_uf u' a b.
  Proof.
    intros; rewrite union_spec; intuition eauto.
  Qed.

  Lemma union_refl_in u x u' y
    : union u x y = Some (u', y) -> interp_uf u x x.
  Admitted.
  
  Lemma union_refl_out u x u' y
    : union u x y = Some (u', y) -> interp_uf u y y.
  Admitted.
    
  Lemma union_relates u x u' y
    : union u x y = Some (u', y) -> interp_uf u' x y.
  Proof.
    intros; rewrite union_spec; [| eauto];intuition eauto using union_refl_in, union_refl_out.
  Qed.

  

Hint Rewrite gempty : utils.
Hint Rewrite Pos.eqb_refl : utils.
Hint Rewrite gss : utils.
Hint Rewrite grs : utils.

  
Local Arguments empty {_}%type_scope.


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
     
  Admitted.

  
  Section All1.
    Context {A B}
      (P : A -> B -> Prop).
    
    (* A Fixpoint version of List.Forall *)
    Fixpoint all1 l : B -> Prop :=
      match l with
      | [] => fun _ => True
      | e::l' => and1 (P e) (all1 l')
      end.
  End All1.

  
  Definition emp {A} (t : tree A) := t = PTree.empty.
  
  Section SepAll.
    Context {A B}
      (P : A -> tree B -> Prop).
    
    (* A Fixpoint version of List.Forall *)
    Fixpoint sep_all l : tree B -> Prop :=
      match l with
      | [] => emp
      | e::l' => sep (P e) (sep_all l')
      end.
  End SepAll.

  
  
  Definition iff1 {A} (P1 P2 : A -> Prop) :=
    forall a, P1 a <-> P2 a.
  
  Add Parametric Relation {A} : (A -> Prop) (@iff1 A)
  reflexivity proved by (fun P a => iff_refl (P a))
  symmetry proved by (fun P1 P2 pf a => iff_sym (pf a))
  transitivity proved by (fun P1 P2 P3 pf1 pf2 a => iff_trans (pf1 a) (pf2 a))
      as iff1_instance.
  
  Add Parametric Morphism {A} :
    (@sep A) with signature
      @iff1 (tree A) ==> @iff1 (tree A) ==> @iff1 (tree A)
        as sep_partial_mor.
  Proof.
    unfold iff1; firstorder.
  Qed.

  
  Add Parametric Morphism {A} :
    (@sep A) with signature
      @iff1 (tree A) ==> @iff1 (tree A) ==> @eq (tree A) ==> @iff
        as sep_full_mor.
  Proof.
    unfold iff1; firstorder.
  Qed.

  
  Add Parametric Morphism {A} :
    (@and1 A) with signature
      @iff1 A ==> @iff1 A ==> @iff1 A
        as and1_partial_mor.
  Proof.
    unfold iff1; firstorder.
  Qed.

  
  Add Parametric Morphism {A} :
    (@and1 A) with signature
      @iff1 A ==> @iff1 A ==> @eq A ==> @iff
        as and1_full_mor.
  Proof.
    unfold iff1; firstorder.
  Qed.

  (* TODO: requires lifting iff1 to funext/iff2
  Add Parametric Morphism {A} :
    (@sep_all A) with signature
      @iff2 (tree A) ==> @eq (list _) ==> @eq (tree A) ==> @iff
        as sep_full_mor.
  Proof.
    unfold iff1; firstorder.
  Qed.
   *)

  Notation "A <=> B" := (iff1 A B) (at level 95, no associativity) : type_scope.
  
  Lemma sep_emp_l A (P : tree A -> Prop)
    : sep emp P <=> P.
  Proof.
    unfold sep, emp;
      firstorder subst;
      basic_utils_crush.
  Qed.
  Hint Rewrite sep_emp_l : utils.
  
  Lemma sep_emp_r A (P : tree A -> Prop)
    : sep P emp <=> P.
  Proof.
    unfold sep, emp;
      firstorder subst;
      basic_utils_crush.
  Qed.
  Hint Rewrite sep_emp_r : utils.
  
  Lemma sep_assoc A (P1 P2 P3 : tree A -> Prop)
    : sep (sep P1 P2) P3 <=> sep P1 (sep P2 P3).
  Proof.
    unfold sep, emp, iff1;
      intuition (break; subst).
    {
      eapply disjoint_sum_comm in H0.
      pose proof (disjoint_sum_assoc _ _ _ _ _ _ H H0).
      break.
      exists x1.
      eexists; repeat split;eauto.
    }
    {
      eapply disjoint_sum_comm in H.
      pose proof (disjoint_sum_assoc _ _ _ _ _ _ H H1).
      break.
      eexists.
      exists x2.
      split; [ eapply disjoint_sum_comm; eauto|].
      repeat split; eauto; eexists; eexists; repeat split; cycle 2; eauto.
      eapply disjoint_sum_comm; auto.
    }
  Qed.
  Hint Rewrite sep_assoc : utils.

  
  Lemma sep_emp_l_app A (P : tree A -> Prop)
    : forall t, sep emp P t <-> P t.
  Proof.
    unfold sep, emp;
      firstorder subst;
      basic_utils_crush.
  Qed.
  Hint Rewrite sep_emp_l_app : utils.
  
  Lemma sep_emp_r_app A (P : tree A -> Prop)
    : forall t, sep P emp t <-> P t.
  Proof.
    unfold sep, emp;
      firstorder subst;
      basic_utils_crush.
  Qed.
  Hint Rewrite sep_emp_r_app : utils.

Section UnionFind.

  
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

  Unset Elimination Schemes.
  Inductive parent_tree : Set :=
  | pt_points : positive -> list parent_tree -> parent_tree.
  Set Elimination Schemes.

  (*Stronger induction principle w/ better subterm knowledge
   *)
  Fixpoint parent_tree_ind
    (P : parent_tree -> Prop)
    (IHC : forall n l, all P l ->
                       P (pt_points n l))
    (e : parent_tree) { struct e} : P e :=
    match e with
    | pt_points n l =>
        let fix loop l :=
          match l return List.fold_right (fun t => and (P t)) True l with
          | [] => I
          | e' :: l' => conj (parent_tree_ind _ IHC e') (loop l')
          end in
        IHC n l (loop l)
    end.

  Fixpoint parent_tree_rect
    (P : parent_tree -> Type)
    (IHC : forall n l,
        List.fold_right (fun t => prod (P t)) unit l ->
        P (pt_points n l))
    (e : parent_tree) {struct e} : P e :=
    match e with
    | pt_points n l =>
        let fix loop l :=
          match l return List.fold_right (fun t => prod (P t)) unit l with
          | [] => tt
          | e' :: l' => (parent_tree_rect _ IHC e', loop l')
          end in
        IHC n l (loop l)
    end.
    

  Definition points_to (t : parent_tree) :=
    let (i,l) := t in i.

  (*TODO: move to Utils.v*)
  Section Some.
    Context {A : Type}
      (P : A -> Prop).
    Fixpoint some (l : list A) :=
      match l with
      | [] => False
      | a::l => P a \/ some l
      end.
  End Some.

  Fixpoint In_tree i (p : parent_tree) : Prop :=
    let (j,l) := p in
    i = j \/ some (In_tree i) l.

  
  Definition parent_tree_equiv (p1 p2: parent_tree) :=
    (forall i, In_tree i p1 <-> In_tree i p2).

  Definition maps {A} i j (pa : tree A) := Some i = get j pa.

  Definition pure {A} P (_:tree A) : Prop := P.

  Notation "x //\\ y" := (and1 x y) (at level 80, right associativity).

  Notation "%% p" := (pure p) (at level 76, right associativity).
  
  Fixpoint tree_pointing_to (t : parent_tree) : tree positive -> Prop :=
    let (i, l) := t in
    sep (sep_all (fun j => %%i <> j //\\ maps i j) (map points_to l))
      (sep_all tree_pointing_to l).

  Definition parent_tree_at t : tree _ -> Prop :=
    sep (tree_pointing_to t)
      (eq (singleton (points_to t) (points_to t))). 
  
  Lemma root_cycle i pa
    : parent_tree_at i pa ->
      Some (points_to i) = get (points_to i) pa.
  Proof.
    unfold parent_tree_at.
    intros; eapply sep_get_r; eauto.
    basic_utils_crush.
  Qed.

  Definition single_tree i j := pt_points j [pt_points i []].

  Hint Unfold pure maps : utils.
  Lemma singleton_points i j
    : i <> j -> tree_pointing_to (single_tree i j) (singleton i j).
  Proof.
    cbn -[get set]; basic_utils_crush.
    unfold and1, pure, maps.
    basic_utils_crush.
  Qed.
  Hint Resolve singleton_points : utils.

  
  Lemma has_key_singleton A i j (k : A)
    : has_key i (singleton j k) <-> i = j.
  Proof.
    unfold has_key.
    destruct (Pos.eq_dec i j); subst;
      basic_utils_crush.
    rewrite gso, gempty in *; tauto.
  Qed.
  Hint Rewrite has_key_singleton : utils.

  
  Lemma emp_empty A (t : tree A)
    : emp t <-> t = PTree.empty.
  Proof.
    firstorder.
  Qed.
  Hint Rewrite emp_empty : utils.


  Lemma pure_true_l A (P : tree A -> Prop)
    : %% True //\\ P <=> P.
  Proof.
    unfold pure.
    firstorder.
  Qed.
  Hint Rewrite pure_true_l : utils.

  Lemma iff1_reflexive_rew A (P : A -> Prop) : P <=> P <-> True.
  Proof.
    firstorder.
  Qed.
  Hint Rewrite iff1_reflexive_rew: utils.
  
  Lemma sep_and_pure_l A P (Q R : tree A -> Prop)
    : sep (%% P //\\ Q) R <=> %%P //\\ sep Q R.
  Proof.
    firstorder.
  Qed.
  Hint Rewrite sep_and_pure_l: utils.
  
  Lemma sep_and_pure_r A P (Q R : tree A -> Prop)
    : sep R (%% P //\\ Q) <=> %%P //\\ sep R Q.
  Proof.
    firstorder.
  Qed.
  Hint Rewrite sep_and_pure_r: utils.

  (*TODO: which way to rew?*)
  Lemma and1_pure A P Q
    : %% (P /\ Q) <=> @pure A P //\\ %% Q.
  Proof.
    firstorder.
  Qed.
  Hint Rewrite and1_pure: utils.

  Lemma and1_assoc A (P Q R : A -> Prop)
    : (P //\\ Q) //\\ R <=> P //\\Q //\\R.
  Proof.
    firstorder.
  Qed.
  Hint Rewrite and1_assoc: utils.

    
  Lemma sep_all_pure_l A B P (Q : A -> tree B -> Prop) (l : list A)
    : sep_all (fun j => %% P j //\\ Q j) l
        <=> %%(all P l) //\\ sep_all Q l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    rewrite IHl.
    basic_utils_crush.
  Qed.
  Hint Rewrite sep_all_pure_l : utils.
  
  Lemma key_not_root i pa j
    : tree_pointing_to i pa ->
      has_key j pa ->
      points_to i <> j.
  Proof.
    revert pa.
    induction i.
    {
      revert H; induction l;
        basic_goal_prep.
      1:basic_utils_crush.
      break.
      specialize (IHl ltac:(assumption)).
      basic_utils_crush.
      eapply iff1_instance_Transitive in H0.
      3:{
        symmetry.
        simple eapply sep_and_pure_l.
      }
      2:{
        (*
        eapply sep_partial_mor; [| reflexivity].
        
      2: eapply sep_mor_Proper.
      etransitivity in H0.
      rewrite sep_and_pure_l in H0.
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
         *)
        Admitted.



(*




















  
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
*)
        
End UnionFind.



Definition forest_equiv (f1 f2 : list parent_tree) :=
  exists f1', Permutation.Permutation f1 f1'
              /\ Forall2 parent_tree_equiv f1' f2.

Definition equiv_by_forest f i1 i2 :=
  exists t, In t f
            /\ In_tree i1 t
            /\ In_tree i2 t.

(*Temporary axioms for use in fleshing out the rest*)
Parameter (uf_ok : union_find -> list parent_tree -> Prop).
Axiom (empty_ok : uf_ok empty []).
Axiom (find_spec
        : forall f u i u' i',
          uf_ok u f ->
          Some (u', i') = find u i ->
          equiv_by_forest f i i'
          /\ exists f', forest_equiv f f' /\ uf_ok u' f').


Definition forest_subrel (f1 f2 : list parent_tree) :=
  (* f1 small eq, so can have more trees *)
  forall i1 i2, equiv_by_forest f1 i1 i2 -> equiv_by_forest f2 i1 i2.

Definition tree_union_l (t1 t2 : parent_tree) :=
  let (i, l) := t1 in
  pt_points i (t2::l).

Axiom (union_spec
        : forall u i j u' i' f,
          uf_ok u f ->
          Some (u', i') = union u i j ->
          (*accounts for the case where i ~ j already
           so that we can assume they have separate trees in the other branch*)
          (u' = u /\ equiv_by_forest f i i' /\ equiv_by_forest f j i')
          \/ exists f' it jt,
              Permutation.Permutation f (jt::it::f')
              /\ In_tree i it
              /\ In_tree j jt
              /\ exists ijt',
                (ijt' = (tree_union_l it jt)
                 \/ ijt' = tree_union_l jt it)
                /\ uf_ok u' (ijt'::f')
                /\ points_to ijt' = i').

