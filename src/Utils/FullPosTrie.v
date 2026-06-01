(* ============================================================================
   A LAWFUL positive-list-keyed map: the "fattened" pos_trie.

   The existing [pos_trie] (PosListMap.v) is NOT a lawful map: its [map.ok] is
   provably false because a [pos_trie_leaf] cannot also carry children, so
   inserting a longer key onto a leaf discards it.  That trie is fine for the
   e-graph QUERY tries (which are uniform-depth and feed pt_spaced_intersect),
   but the e-graph DB tables need a genuine [map.ok].

   This file defines a separate, fully-lawful map over [list positive] keys by
   adding a third constructor [fpt_both] that carries BOTH a value (for the
   key that ends here) AND a child PTree.  get/put/remove/fold then become total
   and the full coqutil [map.ok] holds UNCONDITIONALLY (no depth restriction).

   pt_spaced_intersect is NOT defined here and is not needed: the DB tables are
   never intersected.  So the scary intersection-correctness proof stays on the
   original pos_trie.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List Lia.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Tries Require Import Canonical.
From Utils Require Import TrieMap TrieMapFold.

Set Implicit Arguments.

Section __.
  Context {A : Type}.

  Inductive fpt' :=
  | fpt_leaf (a : A)                              (* the empty suffix ends here *)
  | fpt_node (m : PTree.tree' fpt')               (* only longer keys, no value here *)
  | fpt_both (a : A) (m : PTree.tree' fpt').       (* value here AND longer keys *)

  (* None is the empty map *)
  Definition fpt := option fpt'.

  (* --- get ----------------------------------------------------------------- *)
  Fixpoint fpt_get' (pt : fpt') (k : list positive) {struct k} : option A :=
    match k with
    | [] =>
        match pt with
        | fpt_leaf a => Some a
        | fpt_both a _ => Some a
        | fpt_node _ => None
        end
    | p :: k' =>
        match pt with
        | fpt_leaf _ => None
        | fpt_node m
        | fpt_both _ m =>
            match PTree.get' p m with
            | Some pt' => fpt_get' pt' k'
            | None => None
            end
        end
    end.

  Definition fpt_get (pt : fpt) (k : list positive) : option A :=
    match pt with
    | None => None
    | Some pt' => fpt_get' pt' k
    end.

  (* --- singleton ----------------------------------------------------------- *)
  Fixpoint fpt_singleton (k : list positive) (v : A) : fpt' :=
    match k with
    | [] => fpt_leaf v
    | p :: k' => fpt_node (PTree.set0 p (fpt_singleton k' v))
    end.

  (* --- put ----------------------------------------------------------------- *)
  (* helper: update child at p of a PTree m with the put of (k',v) *)
  Definition fpt_child_put (m : PTree.tree' fpt') (p : positive)
                           (k' : list positive) (v : A)
                           (rec : fpt' -> fpt') : PTree.tree' fpt' :=
    match PTree.get' p m with
    | Some c => PTree.set' p (rec c) m
    | None => PTree.set' p (fpt_singleton k' v) m
    end.

  Fixpoint fpt_put' (pt : fpt') (k : list positive) (v : A) {struct k} : fpt' :=
    match k with
    | [] =>
        match pt with
        | fpt_leaf _ => fpt_leaf v
        | fpt_node m => fpt_both v m
        | fpt_both _ m => fpt_both v m
        end
    | p :: k' =>
        match pt with
        | fpt_leaf a =>
            (* leaf gains a child branch; keeps its own value *)
            fpt_both a (PTree.set0 p (fpt_singleton k' v))
        | fpt_node m =>
            fpt_node (fpt_child_put m p k' v (fun c => fpt_put' c k' v))
        | fpt_both a m =>
            fpt_both a (fpt_child_put m p k' v (fun c => fpt_put' c k' v))
        end
    end.

  Definition fpt_put (pt : fpt) (k : list positive) (v : A) : fpt :=
    match pt with
    | None => Some (fpt_singleton k v)
    | Some pt' => Some (fpt_put' pt' k v)
    end.

  (* --- remove -------------------------------------------------------------- *)
  (* collapse a PTree result of a child-removal back into an fpt' carrier:
     - when a [node] loses its last child, the whole subtrie is empty -> None
     - when a [both a] loses its last child, it collapses to [leaf a] *)
  Fixpoint fpt_remove' (pt : fpt') (k : list positive) {struct k} : option fpt' :=
    match k with
    | [] =>
        match pt with
        | fpt_leaf _ => None                 (* removed the only (empty-key) value *)
        | fpt_node m => Some (fpt_node m)    (* no value here; unchanged *)
        | fpt_both _ m => Some (fpt_node m)  (* drop the value, keep children *)
        end
    | p :: k' =>
        match pt with
        | fpt_leaf a => Some (fpt_leaf a)    (* key absent; unchanged *)
        | fpt_node m =>
            match PTree.get' p m with
            | Some c =>
                match fpt_remove' c k' with
                | Some c' => Some (fpt_node (PTree.set' p c' m))
                | None =>
                    match PTree.remove' p m with
                    | PTree.Empty => None              (* node lost all children *)
                    | PTree.Nodes m' => Some (fpt_node m')
                    end
                end
            | None => Some (fpt_node m)
            end
        | fpt_both a m =>
            match PTree.get' p m with
            | Some c =>
                match fpt_remove' c k' with
                | Some c' => Some (fpt_both a (PTree.set' p c' m))
                | None =>
                    match PTree.remove' p m with
                    | PTree.Empty => Some (fpt_leaf a) (* both lost children -> leaf *)
                    | PTree.Nodes m' => Some (fpt_both a m')
                    end
                end
            | None => Some (fpt_both a m)
            end
        end
    end.

  Definition fpt_remove (pt : fpt) (k : list positive) : fpt :=
    match pt with
    | None => None
    | Some pt' => fpt_remove' pt' k
    end.

  (* --- fold ---------------------------------------------------------------- *)
  Fixpoint fpt_fold' {R} (f : R -> list positive -> A -> R) (acc : R)
                     (pt : fpt') (stack : list positive) {struct pt} : R :=
    match pt with
    | fpt_leaf a => f acc (rev stack) a
    | fpt_node m =>
        TrieMap.trie_fold' (fun acc p c => fpt_fold' f acc c (p :: stack)) acc m 1
    | fpt_both a m =>
        let acc' := f acc (rev stack) a in
        TrieMap.trie_fold' (fun acc p c => fpt_fold' f acc c (p :: stack)) acc' m 1
    end.

  Definition fpt_fold {R} (f : R -> list positive -> A -> R) (acc : R) (pt : fpt) : R :=
    match pt with
    | None => acc
    | Some pt' => fpt_fold' f acc pt' []
    end.

  #[export] Instance full_pos_trie_map : map.map (list positive) A :=
    {
      rep := fpt;
      get := fpt_get;
      empty := None;
      put := fpt_put;
      remove := fpt_remove;
      fold _ := fpt_fold;
    }.

End __.

Arguments fpt' : clear implicits.
Arguments fpt : clear implicits.

(* ============================================================================
   Proof of map.ok for full_pos_trie_map
   ============================================================================ *)

Unset Implicit Arguments.

(* ---- PTree helpers (0-axiom, from PosListMapLaws.v) ---- *)

Lemma fpt_gss' : forall (B:Type) (i:positive) (x:B) (m: PTree.tree' B),
    PTree.get' i (PTree.set' i x m) = Some x.
Proof.
  induction i; destruct m; simpl; intros; auto using PTree.gss0.
Qed.

Lemma fpt_gso' : forall (B:Type) (i j:positive) (x:B) (m: PTree.tree' B),
    i <> j -> PTree.get' i (PTree.set' j x m) = PTree.get' i m.
Proof.
  intros B i j x m H.
  revert j H m; induction i; destruct j, m; simpl; intros; auto;
    solve [apply IHi; congruence | apply PTree.gso0; congruence | congruence].
Qed.

Lemma fpt_grs' : forall (B:Type) (p:positive) (m: PTree.tree' B),
    PTree.get p (PTree.remove' p m) = None.
Proof. intros B p m. exact (PTree.grs p (PTree.Nodes m)). Qed.

Lemma fpt_gro' : forall (B:Type) (j p:positive) (m: PTree.tree' B),
    j <> p -> PTree.get j (PTree.remove' p m) = PTree.get j (PTree.Nodes m).
Proof. intros B j p m H. exact (PTree.gro (PTree.Nodes m) H). Qed.

(* ---- fpt_singleton helpers ---- *)

Lemma fpt_get'_singleton_same : forall (A:Type) (k : list positive) (v : A),
    fpt_get' (fpt_singleton k v) k = Some v.
Proof.
  intros A.
  induction k as [|p k IH]; intros v; simpl; auto.
  rewrite PTree.gss0. apply IH.
Qed.

Lemma fpt_get'_singleton_diff : forall (A:Type) (k k' : list positive) (v : A),
    k <> k' -> fpt_get' (fpt_singleton k' v) k = None.
Proof.
  intros A.
  induction k as [|a k IH]; destruct k' as [|p k']; intros v Hne; simpl.
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (Pos.eq_dec a p) as [Heq | Hne'].
    + subst p. rewrite PTree.gss0.
      apply IH. intro Heq. apply Hne. rewrite Heq. reflexivity.
    + rewrite PTree.gso0 by auto. reflexivity.
Qed.

(* ---- get_put_same ---- *)

Lemma fpt_get'_put'_same : forall (A:Type) (k : list positive) (v : A) (pt : fpt' A),
    fpt_get' (fpt_put' pt k v) k = Some v.
Proof.
  intros A.
  induction k as [|p k' IH]; intros v pt.
  - destruct pt; reflexivity.
  - destruct pt as [a | m | a m]; simpl.
    + rewrite PTree.gss0. apply fpt_get'_singleton_same.
    + unfold fpt_child_put.
      destruct (PTree.get' p m) as [c|] eqn:Hgp.
      * rewrite fpt_gss'. apply IH.
      * rewrite fpt_gss'. apply fpt_get'_singleton_same.
    + unfold fpt_child_put.
      destruct (PTree.get' p m) as [c|] eqn:Hgp.
      * rewrite fpt_gss'. apply IH.
      * rewrite fpt_gss'. apply fpt_get'_singleton_same.
Qed.

Lemma fpt_get_put_same : forall (A:Type) (m : fpt A) (k : list positive) (v : A),
    fpt_get (fpt_put m k v) k = Some v.
Proof.
  intros A m k v.
  destruct m as [pt|].
  - cbn [fpt_put fpt_get]. apply fpt_get'_put'_same.
  - cbn [fpt_put fpt_get]. apply fpt_get'_singleton_same.
Qed.

(* ---- get_put_diff ---- *)

Lemma fpt_get'_put'_diff : forall (A:Type) (k k' : list positive) (v : A) (pt : fpt' A),
    k <> k' -> fpt_get' (fpt_put' pt k' v) k = fpt_get' pt k.
Proof.
  intros A k k' v pt Hne. revert k v pt Hne.
  induction k' as [|p k' IHk']; intros k v pt Hne.
  - destruct k as [|a k0].
    + exfalso. apply Hne. reflexivity.
    + destruct pt as [a0 | m | a0 m]; simpl; reflexivity.
  - destruct k as [|a k0].
    + destruct pt as [a0 | m | a0 m]; simpl; reflexivity.
    + destruct pt as [a0 | m | a0 m]; simpl.
      * destruct (Pos.eq_dec a p) as [Heq | Hne'].
        { subst p. rewrite PTree.gss0.
          apply fpt_get'_singleton_diff.
          intro Heq. apply Hne. rewrite Heq. reflexivity. }
        { rewrite PTree.gso0 by auto. reflexivity. }
      * unfold fpt_child_put.
        destruct (PTree.get' p m) as [c|] eqn:Hgp.
        { destruct (Pos.eq_dec a p) as [Heq | Hne'].
          - subst p. rewrite fpt_gss'. rewrite Hgp.
            apply IHk'. intro Heq. apply Hne. rewrite Heq. reflexivity.
          - rewrite fpt_gso' by auto. reflexivity. }
        { destruct (Pos.eq_dec a p) as [Heq | Hne'].
          - subst p. rewrite fpt_gss'. rewrite Hgp.
            apply fpt_get'_singleton_diff.
            intro Heq. apply Hne. rewrite Heq. reflexivity.
          - rewrite fpt_gso' by auto. reflexivity. }
      * unfold fpt_child_put.
        destruct (PTree.get' p m) as [c|] eqn:Hgp.
        { destruct (Pos.eq_dec a p) as [Heq | Hne'].
          - subst p. rewrite fpt_gss'. rewrite Hgp.
            apply IHk'. intro Heq. apply Hne. rewrite Heq. reflexivity.
          - rewrite fpt_gso' by auto. reflexivity. }
        { destruct (Pos.eq_dec a p) as [Heq | Hne'].
          - subst p. rewrite fpt_gss'. rewrite Hgp.
            apply fpt_get'_singleton_diff.
            intro Heq. apply Hne. rewrite Heq. reflexivity.
          - rewrite fpt_gso' by auto. reflexivity. }
Qed.

Lemma fpt_get_put_diff : forall (A:Type) (m : fpt A) (k k' : list positive) (v : A),
    k <> k' -> fpt_get (fpt_put m k' v) k = fpt_get m k.
Proof.
  intros A m k k' v Hne.
  destruct m as [pt|].
  - cbn [fpt_put fpt_get]. apply fpt_get'_put'_diff. exact Hne.
  - cbn [fpt_put fpt_get]. apply fpt_get'_singleton_diff. exact Hne.
Qed.

(* ---- get_remove_same ---- *)

Lemma fpt_get'_remove'_same : forall (A:Type) (k : list positive) (pt : fpt' A),
    fpt_get (fpt_remove' pt k) k = None.
Proof.
  intros A.
  induction k as [|p k' IH]; intro pt.
  - destruct pt as [a | m | a m]; simpl; reflexivity.
  - destruct pt as [a | m | a m]; simpl.
    + reflexivity.
    + destruct (PTree.get' p m) as [c|] eqn:Hgp.
      * destruct (fpt_remove' c k') as [c'|] eqn:Hrc.
        { cbn [fpt_get fpt_get']. rewrite fpt_gss'.
          pose proof (IH c) as Hih. rewrite Hrc in Hih. exact Hih. }
        { destruct (PTree.remove' p m) as [|m'] eqn:HR.
          - reflexivity.
          - cbn [fpt_get fpt_get'].
            pose proof (fpt_grs' (fpt' A) p m) as Hgrs. rewrite HR in Hgrs.
            cbn [PTree.get] in Hgrs. rewrite Hgrs. reflexivity. }
      * cbn [fpt_get fpt_get']. rewrite Hgp. reflexivity.
    + destruct (PTree.get' p m) as [c|] eqn:Hgp.
      * destruct (fpt_remove' c k') as [c'|] eqn:Hrc.
        { cbn [fpt_get fpt_get']. rewrite fpt_gss'.
          pose proof (IH c) as Hih. rewrite Hrc in Hih. exact Hih. }
        { destruct (PTree.remove' p m) as [|m'] eqn:HR.
          - cbn [fpt_get fpt_get']. reflexivity.
          - cbn [fpt_get fpt_get'].
            pose proof (fpt_grs' (fpt' A) p m) as Hgrs. rewrite HR in Hgrs.
            cbn [PTree.get] in Hgrs. rewrite Hgrs. reflexivity. }
      * cbn [fpt_get fpt_get']. rewrite Hgp. reflexivity.
Qed.

Lemma fpt_get_remove_same : forall (A:Type) (m : fpt A) (k : list positive),
    fpt_get (fpt_remove m k) k = None.
Proof.
  intros A m k.
  destruct m as [pt|].
  - cbn [fpt_remove]. apply fpt_get'_remove'_same.
  - reflexivity.
Qed.

(* ---- get_remove_diff ---- *)

Lemma fpt_get'_remove'_diff : forall (A:Type) (k k' : list positive) (pt : fpt' A),
    k <> k' -> fpt_get (fpt_remove' pt k') k = fpt_get' pt k.
Proof.
  intros A.
  induction k as [|a k0 IHk]; intros k' pt Hne.
  - destruct k' as [|p k''].
    + exfalso. apply Hne. reflexivity.
    + destruct pt as [a0 | m | a0 m]; simpl.
      * reflexivity.
      * destruct (PTree.get' p m) as [c|] eqn:Hgp.
        { destruct (fpt_remove' c k'') as [c'|] eqn:Hrc; simpl; try reflexivity.
          destruct (PTree.remove' p m) as [|m'] eqn:HR; simpl; reflexivity. }
        { simpl. reflexivity. }
      * destruct (PTree.get' p m) as [c|] eqn:Hgp.
        { destruct (fpt_remove' c k'') as [c'|] eqn:Hrc; simpl; try reflexivity.
          destruct (PTree.remove' p m) as [|m'] eqn:HR; simpl; reflexivity. }
        { simpl. reflexivity. }
  - destruct k' as [|p k''].
    + destruct pt as [a0 | m | a0 m]; simpl; reflexivity.
    + destruct pt as [a0 | m | a0 m]; simpl.
      * reflexivity.
      * destruct (PTree.get' p m) as [c|] eqn:Hgp.
        { destruct (fpt_remove' c k'') as [c'|] eqn:Hrc.
          - cbn [fpt_get fpt_get'].
            destruct (Pos.eq_dec a p) as [->|Hap].
            + rewrite fpt_gss', Hgp.
              assert (Hne' : k0 <> k'') by (intro H; apply Hne; rewrite H; auto).
              pose proof (IHk k'' c Hne') as Hih.
              rewrite Hrc in Hih. exact Hih.
            + rewrite fpt_gso' by auto. reflexivity.
          - destruct (PTree.remove' p m) as [|m'] eqn:HR.
            + cbn [fpt_get fpt_get'].
              destruct (Pos.eq_dec a p) as [->|Hap].
              * rewrite Hgp.
                assert (Hne' : k0 <> k'') by (intro H; apply Hne; rewrite H; auto).
                pose proof (IHk k'' c Hne') as Hih.
                rewrite Hrc in Hih. exact Hih.
              * pose proof (fpt_gro' (fpt' A) a p m Hap) as Hgro.
                rewrite HR in Hgro. cbn [PTree.get] in Hgro.
                rewrite <- Hgro. reflexivity.
            + cbn [fpt_get fpt_get'].
              destruct (Pos.eq_dec a p) as [->|Hap].
              * pose proof (fpt_grs' (fpt' A) p m) as Hgrs. rewrite HR in Hgrs.
                cbn [PTree.get] in Hgrs. rewrite Hgrs, Hgp.
                assert (Hne' : k0 <> k'') by (intro H; apply Hne; rewrite H; auto).
                pose proof (IHk k'' c Hne') as Hih.
                rewrite Hrc in Hih. exact Hih.
              * pose proof (fpt_gro' (fpt' A) a p m Hap) as Hgro.
                rewrite HR in Hgro. cbn [PTree.get] in Hgro. rewrite Hgro. reflexivity. }
        { cbn [fpt_get fpt_get']. reflexivity. }
      * destruct (PTree.get' p m) as [c|] eqn:Hgp.
        { destruct (fpt_remove' c k'') as [c'|] eqn:Hrc.
          - cbn [fpt_get fpt_get'].
            destruct (Pos.eq_dec a p) as [->|Hap].
            + rewrite fpt_gss', Hgp.
              assert (Hne' : k0 <> k'') by (intro H; apply Hne; rewrite H; auto).
              pose proof (IHk k'' c Hne') as Hih.
              rewrite Hrc in Hih. exact Hih.
            + rewrite fpt_gso' by auto. reflexivity.
          - destruct (PTree.remove' p m) as [|m'] eqn:HR.
            + cbn [fpt_get fpt_get'].
              destruct (Pos.eq_dec a p) as [->|Hap].
              * rewrite Hgp.
                assert (Hne' : k0 <> k'') by (intro H; apply Hne; rewrite H; auto).
                pose proof (IHk k'' c Hne') as Hih.
                rewrite Hrc in Hih. exact Hih.
              * pose proof (fpt_gro' (fpt' A) a p m Hap) as Hgro.
                rewrite HR in Hgro. cbn [PTree.get] in Hgro.
                rewrite <- Hgro. reflexivity.
            + cbn [fpt_get fpt_get'].
              destruct (Pos.eq_dec a p) as [->|Hap].
              * pose proof (fpt_grs' (fpt' A) p m) as Hgrs. rewrite HR in Hgrs.
                cbn [PTree.get] in Hgrs. rewrite Hgrs, Hgp.
                assert (Hne' : k0 <> k'') by (intro H; apply Hne; rewrite H; auto).
                pose proof (IHk k'' c Hne') as Hih.
                rewrite Hrc in Hih. exact Hih.
              * pose proof (fpt_gro' (fpt' A) a p m Hap) as Hgro.
                rewrite HR in Hgro. cbn [PTree.get] in Hgro. rewrite Hgro. reflexivity. }
        { cbn [fpt_get fpt_get']. reflexivity. }
Qed.

Lemma fpt_get_remove_diff : forall (A:Type) (m : fpt A) (k k' : list positive),
    k <> k' -> fpt_get (fpt_remove m k') k = fpt_get m k.
Proof.
  intros A m k k' Hne.
  destruct m as [pt|].
  - cbn [fpt_remove]. apply fpt_get'_remove'_diff. exact Hne.
  - reflexivity.
Qed.

(* ---- fold_parametricity ---- *)

(* Proved by fix IH_fpt 2 (structural on fpt') + inner fix IH_tree 1 on PTree.tree'.
   The inner fix has access to IH_fpt on the fpt' values stored in the tree's leaves,
   which are structural subterms of the outer fpt'. *)

Lemma fpt_fold'_parametric : forall (A:Type) (R1 R2 : Type) (Rel : R1 -> R2 -> Prop)
    (f1 : R1 -> list positive -> A -> R1) (f2 : R2 -> list positive -> A -> R2),
    (forall r1 r2 k v, Rel r1 r2 -> Rel (f1 r1 k v) (f2 r2 k v)) ->
    forall (pt : fpt' A) stack r1 r2,
      Rel r1 r2 ->
      Rel (fpt_fold' f1 r1 pt stack) (fpt_fold' f2 r2 pt stack).
Proof.
  intros A R1 R2 Rel f1 f2 Hstep.
  fix IH_fpt 1. (* structural on pt *)
  intros pt stack r1 r2 Hr.
  destruct pt as [a | m | a m]; simpl.
  - apply Hstep. exact Hr.
  - assert (Htree : forall (m' : PTree.tree' (fpt' A)) revnum r1' r2',
        Rel r1' r2' ->
        Rel (TrieMap.trie_fold' (fun acc p c => fpt_fold' f1 acc c (p::stack)) r1' m' revnum)
            (TrieMap.trie_fold' (fun acc p c => fpt_fold' f2 acc c (p::stack)) r2' m' revnum)).
    { fix IH_tree 1. intros m' revnum r1' r2' Hr'.
      destruct m' as [r | y | y r | l | l r | l y | l y r]; simpl.
      - apply IH_tree. exact Hr'.
      - apply IH_fpt. exact Hr'.
      - apply IH_tree. apply IH_fpt. exact Hr'.
      - apply IH_tree. exact Hr'.
      - apply IH_tree. apply IH_tree. exact Hr'.
      - apply IH_tree. apply IH_fpt. exact Hr'.
      - apply IH_tree. apply IH_tree. apply IH_fpt. exact Hr'. }
    apply Htree. exact Hr.
  - assert (Htree : forall (m' : PTree.tree' (fpt' A)) revnum r1' r2',
        Rel r1' r2' ->
        Rel (TrieMap.trie_fold' (fun acc p c => fpt_fold' f1 acc c (p::stack)) r1' m' revnum)
            (TrieMap.trie_fold' (fun acc p c => fpt_fold' f2 acc c (p::stack)) r2' m' revnum)).
    { fix IH_tree 1. intros m' revnum r1' r2' Hr'.
      destruct m' as [r | y | y r | l | l r | l y | l y r]; simpl.
      - apply IH_tree. exact Hr'.
      - apply IH_fpt. exact Hr'.
      - apply IH_tree. apply IH_fpt. exact Hr'.
      - apply IH_tree. exact Hr'.
      - apply IH_tree. apply IH_tree. exact Hr'.
      - apply IH_tree. apply IH_fpt. exact Hr'.
      - apply IH_tree. apply IH_tree. apply IH_fpt. exact Hr'. }
    apply Htree. apply Hstep. exact Hr.
Qed.

Lemma fpt_fold_parametric : forall (A:Type) (R1 R2 : Type) (Rel : R1 -> R2 -> Prop)
    (f1 : R1 -> list positive -> A -> R1) (f2 : R2 -> list positive -> A -> R2),
    (forall r1 r2 k v, Rel r1 r2 -> Rel (f1 r1 k v) (f2 r2 k v)) ->
    forall r1 r2, Rel r1 r2 ->
    forall (m : fpt A),
      Rel (fpt_fold f1 r1 m) (fpt_fold f2 r2 m).
Proof.
  intros A R1 R2 Rel f1 f2 Hstep r1 r2 Hr m.
  destruct m as [pt|].
  - cbn [fpt_fold]. apply fpt_fold'_parametric.
    + exact Hstep.
    + exact Hr.
  - simpl. exact Hr.
Qed.

(* ---- fpt' nonemptiness (for map_ext) ---- *)

(* fpt_fold'(fun n _ _ => S n) n pt stack > n for all pt, stack, n.
   Proved by fix IH_fpt 2 (structural on pt : fpt' A) + inner fix IH_tree 1
   for the PTree part. The inner fix can call IH_fpt on fpt' values from the
   tree's leaf constructors (which are structural subterms of pt). *)

Lemma fpt_fold'_S_pos : forall (A:Type) (pt : fpt' A) stack n,
    fpt_fold' (fun (n0:nat) _ _ => S n0) n pt stack > n.
Proof.
  fix IH_fpt 2.
  intros A pt.
  assert (Htree : forall (m : PTree.tree' (fpt' A)) stack n revnum,
      TrieMap.trie_fold' (fun acc p c => fpt_fold' (fun n0 _ _ => S n0) acc c (p::stack)) n m revnum > n).
  { fix IH_tree 1. intros m stack n revnum.
    destruct m as [r | y | y r | l | l r | l y | l y r]; simpl.
    - (* Node001 r *) apply IH_tree.
    - (* Node010 y *) apply IH_fpt.
    - (* Node011 y r *)
      pose proof (IH_fpt A y (pos_rev revnum :: stack) n) as Hy.
      pose proof (IH_tree r stack (fpt_fold' (fun n0 _ _ => S n0) n y (pos_rev revnum :: stack)) (xI revnum)) as Hr.
      lia.
    - (* Node100 l *) apply IH_tree.
    - (* Node101 l r *)
      pose proof (IH_tree r stack n (xI revnum)) as Hr.
      pose proof (IH_tree l stack (TrieMap.trie_fold' (fun acc p c => fpt_fold' (fun n0 _ _ => S n0) acc c (p::stack)) n r (xI revnum)) (xO revnum)) as Hl.
      lia.
    - (* Node110 l y *)
      pose proof (IH_fpt A y (pos_rev revnum :: stack) n) as Hy.
      pose proof (IH_tree l stack (fpt_fold' (fun n0 _ _ => S n0) n y (pos_rev revnum :: stack)) (xO revnum)) as Hl.
      lia.
    - (* Node111 l y r *)
      pose proof (IH_fpt A y (pos_rev revnum :: stack) n) as Hy.
      pose proof (IH_tree r stack (fpt_fold' (fun n0 _ _ => S n0) n y (pos_rev revnum :: stack)) (xI revnum)) as Hr.
      pose proof (IH_tree l stack (TrieMap.trie_fold' (fun acc p c => fpt_fold' (fun n0 _ _ => S n0) acc c (p::stack)) (fpt_fold' (fun n0 _ _ => S n0) n y (pos_rev revnum :: stack)) r (xI revnum)) (xO revnum)) as Hl.
      lia. }
  intros stack n.
  destruct pt as [a | m | a m]; simpl.
  - lia.
  - apply Htree.
  - pose proof (Htree m stack (S n) xH). lia.
Qed.

(* ---- Strong induction principle for fpt' ----
   The generated [fpt'_ind] gives NO induction hypothesis for the fpt' values
   stored inside a [PTree.tree'] child, so a plain [fix IH] that recurses into
   children via [PTree.get'] fails the guard checker.  This principle packages
   the nested-fix descent ONCE: in the node/both cases it hands an IH for every
   child reachable by [PTree.get'].  Proved by the same nested-fix technique as
   [fpt_fold'_parametric] (inner [fix IH_tree] structural on the tree', calling
   the outer [IH_fpt] on the values it extracts, which are structural subterms). *)
Lemma fpt'_strong_ind : forall (A:Type) (P : fpt' A -> Prop),
    (forall a, P (fpt_leaf a)) ->
    (forall m, (forall p c, PTree.get' p m = Some c -> P c) -> P (fpt_node m)) ->
    (forall a m, (forall p c, PTree.get' p m = Some c -> P c) -> P (fpt_both a m)) ->
    forall pt, P pt.
Proof.
  intros A P Hl Hn Hb.
  fix IH_fpt 1.
  intro pt. destruct pt as [a | m | a m].
  - apply Hl.
  - apply Hn.
    assert (Htree : forall (m' : PTree.tree' (fpt' A)) p c,
               PTree.get' p m' = Some c -> P c).
    { fix IH_tree 1. intros m' p c Hget.
      destruct m' as [r | y | y r | l | l r | l y | l y r];
        destruct p as [q | q | ]; simpl in Hget;
        solve [ discriminate
              | injection Hget as <-; apply IH_fpt
              | eapply IH_tree; exact Hget ]. }
    exact (Htree m).
  - apply Hb.
    assert (Htree : forall (m' : PTree.tree' (fpt' A)) p c,
               PTree.get' p m' = Some c -> P c).
    { fix IH_tree 1. intros m' p c Hget.
      destruct m' as [r | y | y r | l | l r | l y | l y r];
        destruct p as [q | q | ]; simpl in Hget;
        solve [ discriminate
              | injection Hget as <-; apply IH_fpt
              | eapply IH_tree; exact Hget ]. }
    exact (Htree m).
Qed.

(* ---- Section FptFold: elements list ---- *)
(* Defined here (not using map.ok-only lemmas) to support extensionality. *)

Section FptFold.
  Context {A : Type}.

  (* fpt_elements': guard-checker safe via trie_fold' *)
  Fixpoint fpt_elements' (pt : fpt' A) (stack : list positive)
      {struct pt} : list (list positive * A) :=
    match pt with
    | fpt_leaf a => [(rev stack, a)]
    | fpt_node m =>
        TrieMap.trie_fold' (fun acc p c => acc ++ fpt_elements' c (p :: stack)) [] m 1
    | fpt_both a m =>
        (rev stack, a) ::
        TrieMap.trie_fold' (fun acc p c => acc ++ fpt_elements' c (p :: stack)) [] m 1
    end.

  Definition fpt_elements (m : fpt A) : list (list positive * A) :=
    match m with
    | None => []
    | Some pt => fpt_elements' pt []
    end.

  (* fold_left g (flat_map h l) a0 = fold_left (fun a x => fold_left g (h x) a) l a0 *)
  Lemma fold_left_flat_map_het :
    forall (X Z Y : Type) (g : X -> Z -> X) (h : Y -> list Z) (l : list Y) (a0 : X),
      fold_left g (flat_map h l) a0 =
      fold_left (fun a x => fold_left g (h x) a) l a0.
  Proof.
    intros X Z Y g h l. induction l as [|x xs IH]; intro a0.
    - reflexivity.
    - cbn [flat_map fold_left]. rewrite fold_left_app. exact (IH _).
  Qed.

  Lemma fold_left_ext_in :
    forall (X Y : Type) (s1 s2 : X -> Y -> X) (l : list Y) (a0 : X),
      (forall a x, In x l -> s1 a x = s2 a x) ->
      fold_left s1 l a0 = fold_left s2 l a0.
  Proof.
    intros X Y s1 s2 l. induction l as [|x xs IH]; intros a0 Hext.
    - reflexivity.
    - cbn [fold_left]. rewrite (Hext a0 x (or_introl eq_refl)).
      apply IH. intros a y Hy. apply Hext. right. exact Hy.
  Qed.

  Lemma map_fst_flat_map_aux : forall (C D E : Type) (f : C -> list (D * E)) (l : list C),
      map fst (flat_map f l) = flat_map (fun x => map fst (f x)) l.
  Proof.
    intros. induction l as [|x l IH]; cbn; [reflexivity|].
    rewrite map_app. f_equal. exact IH.
  Qed.

  (* fpt_elements' = trie_fold'(++ elements' c) → flat_map over trie_elements.
     Only valid when revnum = xH (= 1 = the initial value used by fpt_elements'). *)
  Lemma fpt_elements'_fold_flat_map :
    forall (m : PTree.tree' (fpt' A)) stack,
      TrieMap.trie_fold' (fun acc p c => acc ++ fpt_elements' c (p :: stack)) [] m xH
      = flat_map (fun pc => fpt_elements' (snd pc) (fst pc :: stack))
                 (TrieMapFold.trie_elements (PTree.Nodes m)).
  Proof.
    intros m stack.
    change (TrieMap.trie_fold' (fun acc p c => acc ++ fpt_elements' c (p :: stack)) [] m xH)
      with (TrieMap.trie_fold (fun acc p c => acc ++ fpt_elements' c (p :: stack)) []
                              (PTree.Nodes m)).
    rewrite TrieMapFold.trie_fold_elements.
    generalize (TrieMapFold.trie_elements (PTree.Nodes m)) as L.
    (* fold_left with (fun acc y => acc ++ f y) satisfies:
       fold_left ... l acc = acc ++ fold_left ... l [] *)
    assert (Hacc : forall (X Y : Type) (f : Y -> list X) (l : list Y) (acc : list X),
        fold_left (fun a y => a ++ f y) l acc = acc ++ fold_left (fun a y => a ++ f y) l []).
    { intros X Y f l. induction l as [|y l IH]; intro acc.
      - rewrite app_nil_r. reflexivity.
      - simpl. rewrite IH. rewrite (IH (f y)). rewrite app_assoc. reflexivity. }
    intro L. induction L as [|[p c] L' IHL].
    - reflexivity.
    - simpl. rewrite Hacc. rewrite IHL. reflexivity.
  Qed.

  (* fpt_fold' and fpt_elements' relate via fold_left *)
  Lemma fpt_fold'_elements_step :
    forall (pt : fpt' A) (R : Type) (f : R -> list positive -> A -> R) acc stack,
      fpt_fold' f acc pt stack =
      fold_left (fun a p => f a (fst p) (snd p)) (fpt_elements' pt stack) acc.
  Proof.
    intro pt.
    induction pt as [a | m IHm | a m IHm] using fpt'_strong_ind;
      intros R f acc stack; simpl.
    - reflexivity.
    - (* Goal: trie_fold'(fun acc p c => fpt_fold' f acc c (p::stack)) acc m 1
             = fold_left(fun a p => f a (fst p) (snd p)) (fpt_elements' (fpt_node m) stack) acc *)
      change (TrieMap.trie_fold' (fun acc0 p c => fpt_fold' f acc0 c (p :: stack)) acc m 1)
        with (TrieMap.trie_fold (fun acc0 p c => fpt_fold' f acc0 c (p :: stack)) acc (PTree.Nodes m)).
      rewrite TrieMapFold.trie_fold_elements.
      rewrite fpt_elements'_fold_flat_map.
      rewrite fold_left_flat_map_het.
      apply fold_left_ext_in.
      intros acc0 [p c] Hpc.
      apply TrieMapFold.trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
      cbn [fst snd]. apply (IHm p c Hpc).
    - change (TrieMap.trie_fold' (fun acc0 p c => fpt_fold' f acc0 c (p :: stack)) (f acc (rev stack) a) m 1)
        with (TrieMap.trie_fold (fun acc0 p c => fpt_fold' f acc0 c (p :: stack)) (f acc (rev stack) a) (PTree.Nodes m)).
      rewrite TrieMapFold.trie_fold_elements.
      rewrite fpt_elements'_fold_flat_map.
      rewrite fold_left_flat_map_het.
      apply fold_left_ext_in.
      intros acc0 [p c] Hpc.
      apply TrieMapFold.trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
      cbn [fst snd]. apply (IHm p c Hpc).
  Qed.

  Lemma fpt_fold_elements : forall (R : Type) (f : R -> list positive -> A -> R) acc (m : fpt A),
      fpt_fold f acc m =
      fold_left (fun a p => f a (fst p) (snd p)) (fpt_elements m) acc.
  Proof.
    intros R f acc [pt|].
    - cbn [fpt_fold fpt_elements]. apply fpt_fold'_elements_step.
    - reflexivity.
  Qed.

  (* Spec: In (k,v) (fpt_elements' pt stack) <->
     exists suf, k = rev stack ++ suf /\ fpt_get' pt suf = Some v *)
  Lemma fpt_elements'_spec : forall (pt : fpt' A) stack k v,
      In (k, v) (fpt_elements' pt stack) <->
      exists suf, k = rev stack ++ suf /\ fpt_get' pt suf = Some v.
  Proof.
    intro pt.
    induction pt as [a | m IHm | a m IHm] using fpt'_strong_ind;
      intros stack k v; simpl.
    - split.
      + intros [Heq | []]. injection Heq as Hk Ha. subst.
        exists []. rewrite app_nil_r. split; reflexivity.
      + intros [suf [Hk Hget]].
        destruct suf as [|p suf]; simpl in Hget.
        * injection Hget as ->. rewrite app_nil_r in Hk. subst k. left. reflexivity.
        * discriminate.
    - rewrite fpt_elements'_fold_flat_map.
      rewrite in_flat_map. split.
      + intros [[p c] [Hpc Hin]].
        apply TrieMapFold.trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
        cbn [fst snd] in *.
        apply (IHm p c Hpc) in Hin. destruct Hin as [suf [Hk Hget]].
        exists (p :: suf). split.
        * rewrite Hk. cbn [rev]. rewrite <- app_assoc. reflexivity.
        * simpl. rewrite Hpc. exact Hget.
      + intros [suf [Hk Hget]].
        destruct suf as [|p suf]; simpl in Hget; [discriminate|].
        destruct (PTree.get' p m) as [c|] eqn:Hgp; [|discriminate].
        exists (p, c). split.
        { apply TrieMapFold.trie_tuples_spec. simpl. exact Hgp. }
        { cbn [fst snd]. apply (IHm p c Hgp).
          exists suf. split; [|exact Hget].
          rewrite Hk. cbn [rev]. rewrite <- app_assoc. reflexivity. }
    - rewrite fpt_elements'_fold_flat_map.
      rewrite in_flat_map. split.
      + intros [Hin | Hin].
        * injection Hin as Hk Ha. subst.
          exists []. rewrite app_nil_r. split; reflexivity.
        * destruct Hin as [[p c] [Hpc Hin]].
          apply TrieMapFold.trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
          cbn [fst snd] in *.
          apply (IHm p c Hpc) in Hin. destruct Hin as [suf [Hk Hget]].
          exists (p :: suf). split.
          { rewrite Hk. cbn [rev]. rewrite <- app_assoc. reflexivity. }
          { simpl. rewrite Hpc. exact Hget. }
      + intros [suf [Hk Hget]].
        destruct suf as [|p suf]; simpl in Hget.
        * injection Hget as ->. left. rewrite Hk, app_nil_r. reflexivity.
        * destruct (PTree.get' p m) as [c|] eqn:Hgp; [|discriminate].
          right. exists (p, c). split.
          { apply TrieMapFold.trie_tuples_spec. simpl. exact Hgp. }
          { cbn [fst snd]. apply (IHm p c Hgp).
            exists suf. split; [|exact Hget].
            rewrite Hk. cbn [rev]. rewrite <- app_assoc. reflexivity. }
  Qed.

  Lemma fpt_elements_spec : forall (m : fpt A) k v,
      In (k, v) (fpt_elements m) <-> fpt_get m k = Some v.
  Proof.
    intros m k v. destruct m as [pt|].
    - cbn [fpt_elements fpt_get].
      rewrite fpt_elements'_spec.
      split.
      + intros [suf [Hk Hget]]. rewrite Hk. simpl. exact Hget.
      + intros Hget. exists k. split; [reflexivity | exact Hget].
    - simpl. split; [contradiction | discriminate].
  Qed.

  (* fpt' is nonempty: derived from fpt_fold'_S_pos + fold_elements *)
  Lemma fpt'_elements_nonempty : forall (pt : fpt' A) stack,
      fpt_elements' pt stack <> [].
  Proof.
    intros pt stack Hempty.
    (* fpt_fold'(S) 0 pt stack > 0 by fpt_fold'_S_pos *)
    pose proof (fpt_fold'_S_pos A pt stack 0) as Hpos.
    (* fpt_fold'(S) 0 pt stack = length(fpt_elements' pt stack)
       (since S increments the counter per element) *)
    rewrite fpt_fold'_elements_step in Hpos.
    (* fold_left (fun a _ => S a) [] 0 = 0, but Hpos says > 0 *)
    rewrite Hempty in Hpos. simpl in Hpos. lia.
  Qed.

  Lemma fpt'_nonempty : forall (pt : fpt' A), exists k v, fpt_get' pt k = Some v.
  Proof.
    intros pt.
    destruct (fpt_elements' pt []) as [|[k v] rest] eqn:Helems.
    - exfalso. apply (fpt'_elements_nonempty pt []). exact Helems.
    - exists k, v.
      apply (proj1 (fpt_elements_spec (Some pt) k v)).
      cbn [fpt_elements]. rewrite Helems. left. reflexivity.
  Qed.

  (* NoDup of keys *)
  Lemma fpt_elements'_blocks_disjoint :
    forall (l : list (positive * fpt' A)) stack,
      NoDup (map fst l) ->
      ForallOrdPairs
        (fun bl1 bl2 =>
           forall k, In k (map fst bl1) -> ~ In k (map fst bl2))
        (map (fun pc => fpt_elements' (snd pc) (fst pc :: stack)) l).
  Proof.
    induction l as [|[p1 c1] l' IHl]; intros stack Hnd.
    - constructor.
    - simpl. apply FOP_cons.
      + rewrite Forall_forall.
        intros bl Hbl.
        rewrite in_map_iff in Hbl.
        destruct Hbl as [[p2 c2] [Hbl_eq Hpc2_in]]. subst bl. cbn [fst snd].
        assert (Hp1_ne_p2 : p1 <> p2).
        { intro Heq. subst.
          inversion Hnd as [|? ? Hnotin]. apply Hnotin.
          apply in_map_iff. exists (p2, c2). split; [reflexivity | exact Hpc2_in]. }
        intros k Hk1 Hk2.
        apply in_map_iff in Hk1. destruct Hk1 as [[k1 v1] [Hfst1 Hin1]].
        cbn [fst] in Hfst1. subst k.
        apply in_map_iff in Hk2. destruct Hk2 as [[k2 v2] [Hfst2 Hin2]].
        cbn [fst] in Hfst2.
        apply fpt_elements'_spec in Hin1. destruct Hin1 as [suf1 [Hk1 _]].
        apply fpt_elements'_spec in Hin2. destruct Hin2 as [suf2 [Hk2 _]].
        rewrite Hk1, Hk2 in Hfst2.
        cbn [rev] in Hfst2. rewrite <- !app_assoc in Hfst2.
        apply app_inv_head in Hfst2.
        injection Hfst2 as Hpeq _. exact (Hp1_ne_p2 (eq_sym Hpeq)).
      + apply IHl. inversion Hnd as [|? ? ? Hndl]. exact Hndl.
  Qed.

  Lemma fpt_elements'_nodup : forall (pt : fpt' A) stack,
      NoDup (map fst (fpt_elements' pt stack)).
  Proof.
    intro pt.
    induction pt as [a | m IHm | a m IHm] using fpt'_strong_ind;
      intros stack; simpl.
    - apply NoDup_cons; [simpl; tauto | constructor].
    - rewrite fpt_elements'_fold_flat_map.
      rewrite map_fst_flat_map_aux.
      rewrite flat_map_concat_map.
      apply NoDup_concat.
      + rewrite Forall_map. rewrite Forall_forall.
        intros [p c] Hpc. cbn [fst snd].
        apply TrieMapFold.trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
        apply (IHm p c Hpc).
      + rewrite <- map_map.
        pose proof (fpt_elements'_blocks_disjoint
                      (TrieMapFold.trie_elements (PTree.Nodes m)) stack
                      (TrieMapFold.trie_elements_nodup (PTree.Nodes m))) as Hdisj.
        induction Hdisj as [|bl bls Hbl Hdisj IH]; constructor.
        { rewrite Forall_forall in *. intros l Hl.
          apply in_map_iff in Hl. destruct Hl as [bl2 [<- Hbl2]].
          exact (Hbl bl2 Hbl2). }
        { exact IH. }
    - rewrite fpt_elements'_fold_flat_map.
      apply NoDup_cons.
      + rewrite in_map_iff. intros [[k' v'] [Hfst Hin]]. cbn [fst] in Hfst. subst k'.
        rewrite in_flat_map in Hin.
        destruct Hin as [[p c] [Hpc Hin']].
        apply TrieMapFold.trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
        cbn [fst snd] in Hin'.
        apply fpt_elements'_spec in Hin'.
        destruct Hin' as [suf [Hk _]].
        cbn [rev] in Hk. rewrite <- !app_assoc in Hk.
        apply (f_equal (fun l => length l)) in Hk.
        rewrite !length_app in Hk. simpl in Hk. lia.
      + rewrite map_fst_flat_map_aux. rewrite flat_map_concat_map.
        apply NoDup_concat.
        * rewrite Forall_map. rewrite Forall_forall.
          intros [p c] Hpc. cbn [fst snd].
          apply TrieMapFold.trie_tuples_spec in Hpc. cbn [PTree.get] in Hpc.
          apply (IHm p c Hpc).
        * rewrite <- map_map.
          pose proof (fpt_elements'_blocks_disjoint
                        (TrieMapFold.trie_elements (PTree.Nodes m)) stack
                        (TrieMapFold.trie_elements_nodup (PTree.Nodes m))) as Hdisj.
          induction Hdisj as [|bl bls Hbl Hdisj IH]; constructor.
          { rewrite Forall_forall in *. intros l Hl.
            apply in_map_iff in Hl. destruct Hl as [bl2 [<- Hbl2]].
            exact (Hbl bl2 Hbl2). }
          { exact IH. }
  Qed.

  Lemma fpt_elements_nodup : forall (m : fpt A),
      NoDup (map fst (fpt_elements m)).
  Proof.
    intros [pt|].
    - exact (fpt_elements'_nodup pt []).
    - simpl. constructor.
  Qed.

End FptFold.

(* ---- map extensionality ---- *)

(* fpt'_ext: two fpt' with the same get function are equal.
   The hard case is fpt_leaf vs fpt_both: uses fpt'_nonempty to derive contradiction. *)

Lemma fpt'_ext : forall (A:Type) (pt1 pt2 : fpt' A),
    (forall k, fpt_get' pt1 k = fpt_get' pt2 k) ->
    pt1 = pt2.
Proof.
  intros A.
  (* Strong induction on pt1: the child-IH [IHm] applies to c1 (a child of m1
     reached by PTree.get'), discharging the guard obstacle a plain fix would hit. *)
  intro pt1.
  induction pt1 as [a1 | m1 IHm | a1 m1 IHm] using fpt'_strong_ind;
    intros pt2 Hk; destruct pt2 as [a2 | m2 | a2 m2].
  - injection (Hk []) as ->. reflexivity.
  - exfalso. specialize (Hk []). simpl in Hk. discriminate.
  - (* leaf / both: fpt_get' (fpt_leaf a1) k = None for k<>[], but fpt_both has children *)
    injection (Hk []) as ->.
    exfalso.
    destruct (fpt'_nonempty (fpt_node m2)) as [k_node [v_node Hkv_node]].
    destruct k_node as [|p k'].
    + simpl in Hkv_node. discriminate.
    + specialize (Hk (p :: k')). simpl in Hk. simpl in Hkv_node.
      rewrite Hkv_node in Hk. discriminate.
  - exfalso. specialize (Hk []). simpl in Hk. discriminate.
  - (* node / node: show m1 = m2 via PTree.extensionality *)
    f_equal.
    assert (HN : PTree.Nodes m1 = PTree.Nodes m2).
    { apply PTree.extensionality. intro i. cbn [PTree.get].
      destruct (PTree.get' i m1) as [c1|] eqn:H1;
      destruct (PTree.get' i m2) as [c2|] eqn:H2.
      - f_equal.
        apply (IHm i c1 H1).
        intros k. specialize (Hk (i :: k)). simpl in Hk. rewrite H1, H2 in Hk. exact Hk.
      - exfalso.
        destruct (fpt'_nonempty c1) as [k [v Hkv]].
        specialize (Hk (i :: k)). simpl in Hk. rewrite H1, H2 in Hk.
        rewrite Hkv in Hk. discriminate.
      - exfalso.
        destruct (fpt'_nonempty c2) as [k [v Hkv]].
        specialize (Hk (i :: k)). simpl in Hk. rewrite H1, H2 in Hk.
        rewrite Hkv in Hk. discriminate.
      - reflexivity. }
    injection HN as ->. reflexivity.
  - exfalso. specialize (Hk []). simpl in Hk. discriminate.
  - (* both / leaf *)
    injection (Hk []) as ->.
    exfalso.
    destruct (fpt'_nonempty (fpt_node m1)) as [k_node [v_node Hkv_node]].
    destruct k_node as [|p k'].
    + simpl in Hkv_node. discriminate.
    + specialize (Hk (p :: k')). simpl in Hk. simpl in Hkv_node.
      rewrite Hkv_node in Hk. discriminate.
  - exfalso. specialize (Hk []). simpl in Hk. discriminate.
  - (* both / both *)
    injection (Hk []) as ->.
    f_equal.
    assert (HN : PTree.Nodes m1 = PTree.Nodes m2).
    { apply PTree.extensionality. intro i. cbn [PTree.get].
      destruct (PTree.get' i m1) as [c1|] eqn:H1;
      destruct (PTree.get' i m2) as [c2|] eqn:H2.
      - f_equal.
        apply (IHm i c1 H1).
        intros k. specialize (Hk (i :: k)). simpl in Hk. rewrite H1, H2 in Hk. exact Hk.
      - exfalso.
        destruct (fpt'_nonempty c1) as [k [v Hkv]].
        specialize (Hk (i :: k)). simpl in Hk. rewrite H1, H2 in Hk.
        rewrite Hkv in Hk. discriminate.
      - exfalso.
        destruct (fpt'_nonempty c2) as [k [v Hkv]].
        specialize (Hk (i :: k)). simpl in Hk. rewrite H1, H2 in Hk.
        rewrite Hkv in Hk. discriminate.
      - reflexivity. }
    injection HN as ->. reflexivity.
Qed.

Lemma fpt_map_ext : forall (A:Type) (m1 m2 : fpt A),
    (forall k, fpt_get m1 k = fpt_get m2 k) -> m1 = m2.
Proof.
  intros A m1 m2 Hk.
  destruct m1 as [pt1|]; destruct m2 as [pt2|].
  - f_equal. apply fpt'_ext. exact Hk.
  - exfalso.
    destruct (fpt'_nonempty pt1) as [k [v Hkv]].
    specialize (Hk k). simpl in Hk. rewrite Hkv in Hk. discriminate.
  - exfalso.
    destruct (fpt'_nonempty pt2) as [k [v Hkv]].
    specialize (Hk k). simpl in Hk. rewrite Hkv in Hk. discriminate.
  - reflexivity.
Qed.

(* ---- fold_spec ---- *)

Lemma fpt_fold_spec' : forall (A:Type) (R : Type) (P : fpt A -> R -> Prop)
    (f : R -> list positive -> A -> R) r0,
    P None r0 ->
    (forall k v (m : fpt A) r, fpt_get m k = None -> P m r -> P (fpt_put m k v) (f r k v)) ->
    forall m, P m (fpt_fold f r0 m).
Proof.
  intros A R P f r0 Hempty Hstep m.
  rewrite fpt_fold_elements.
  set (elems := fpt_elements m).
  set (g := fun (acc : fpt A) p => fpt_put acc (fst p) (snd p)).
  assert (get_notin : forall l (mm : fpt A) k,
      ~ In k (map fst l) ->
      fpt_get (fold_left g l mm) k = fpt_get mm k).
  { induction l as [|[k0 v0] l' IHl]; intros mm k Hnotin.
    - reflexivity.
    - simpl in *. rewrite IHl by (intro H; apply Hnotin; right; exact H).
      unfold g. simpl. apply fpt_get_put_diff.
      intro Heq. apply Hnotin. left. symmetry. exact Heq. }
  assert (get_in : forall l (mm : fpt A) k v,
      NoDup (map fst l) ->
      In (k, v) l ->
      fpt_get (fold_left g l mm) k = Some v).
  { induction l as [|[k0 v0] l' IHl]; intros mm k v Hnd Hin.
    - inversion Hin.
    - simpl in *. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
      destruct Hin as [Heq | Hin'].
      + injection Heq as Hkk Hvv. subst k0 v0.
        rewrite get_notin by exact Hnotin.
        unfold g. simpl. apply fpt_get_put_same.
      + apply IHl; [exact Hnd' | exact Hin']. }
  assert (Heq : fold_left g elems (None : fpt A) = m).
  { apply fpt_map_ext. intro k.
    unfold elems.
    destruct (fpt_get m k) as [v|] eqn:Hgetm.
    - apply get_in.
      + apply fpt_elements_nodup.
      + apply fpt_elements_spec. exact Hgetm.
    - rewrite get_notin.
      + reflexivity.
      + intro Hkin. rewrite in_map_iff in Hkin.
        destruct Hkin as [[k' v] [Hfst Hin]]. cbn [fst] in Hfst. subst k'.
        apply fpt_elements_spec in Hin. rewrite Hin in Hgetm. discriminate. }
  assert (gen : forall (l : list (list positive * A)),
      NoDup (map fst l) ->
      forall (mm : fpt A) (r : R),
        P mm r ->
        (forall k, In k (map fst l) -> fpt_get mm k = None) ->
        P (fold_left g l mm)
          (fold_left (fun a p => f a (fst p) (snd p)) l r)).
  { induction l as [|[k0 v0] l' IHl']; intros Hnd mm r HP Hfresh.
    - exact HP.
    - simpl. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
      apply IHl'.
      + exact Hnd'.
      + unfold g at 1. simpl.
        apply Hstep.
        * apply Hfresh. left. reflexivity.
        * exact HP.
      + intros k Hkin.
        unfold g at 1. simpl.
        destruct (list_eq_dec Pos.eq_dec k k0) as [Heqk | Hneq].
        * exfalso. apply Hnotin. rewrite <- Heqk. exact Hkin.
        * rewrite fpt_get_put_diff by exact Hneq.
          apply Hfresh. right. exact Hkin. }
  rewrite <- Heq.
  apply gen.
  - apply fpt_elements_nodup.
  - exact Hempty.
  - intros k _. reflexivity.
Qed.

(* ---- Assemble the map.ok instance ---- *)

#[export] Instance full_pos_trie_map_ok {A : Type}
  : @map.ok (list positive) A (@full_pos_trie_map A).
Proof.
  constructor.
  - intros m1 m2 H. apply fpt_map_ext. exact H.
  - intro k. reflexivity.
  - intros m k v. apply fpt_get_put_same.
  - intros m k v k' Hne. apply fpt_get_put_diff. exact Hne.
  - intros m k. apply fpt_get_remove_same.
  - intros m k k' Hne. apply fpt_get_remove_diff. exact Hne.
  - intros R P f r0 Hbase Hstep m.
    exact (@fpt_fold_spec' A R P f r0 Hbase Hstep m).
  - intros R1 R2 Rel fa fb Hpres r1 r2 Hr m.
    exact (@fpt_fold_parametric A R1 R2 Rel fa fb Hpres r1 r2 Hr m).
Qed.
