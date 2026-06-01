(* ============================================================================
   Depth-restricted fold_spec for pos_trie  (the last, hardest db-trie law).

   map.ok's fold_spec is the induction principle: P empty + (put-step) => P m
   (fold f r0 m), for all m.  We need it restricted to depth-n tries / length-n
   keys.  Architecture (mirrors src/Utils/TrieMapFold.v, reusing its single-level
   trie_elements / trie_fold_elements for the inner PTree at each level):

     A. pos_trie'_nonempty   : a depth-n trie has some length-n key (DONE here).
     B. extensionality        : depth-n tries agreeing on all length-n keys are
                                equal (needs A + Canonical PTree.extensionality).
     C. pt_elements + spec    : flatten a trie to its (key,value) list; In <-> get;
                                NoDup of keys; every key has length n.
     D. pt_fold = fold_left over pt_elements (via trie_fold_elements per level).
     E. of_list + fold_spec   : generic list induction; of_list(pt_elements m)=m
                                via B; assemble depth-restricted fold_spec.

   Unlike TrieMapFold, the db trie has NO unrestricted map_ext (it's false), so
   extensionality (B) is proven only for the depth-restricted case and used
   internally; it is NOT an interface field.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List Lia.
Import ListNotations.
From Tries Require Import Canonical.
From Utils Require Import PosListMap TrieMapFold.

Set Implicit Arguments.

Section FoldSpec.
  Context {A : Type}.

  (* ===== A. non-emptiness =================================================== *)
  Lemma pos_trie'_nonempty : forall n (t:@pos_trie' A),
      depth' t n -> exists k, length k = n /\ pt_get' t k <> None.
  Proof.
    induction n; intros t Hd.
    - inversion Hd; subst. exists []. split; [reflexivity| cbn; congruence].
    - inversion Hd as [| m n0 Hforall Hm Hn]; subst.
      destruct (PTree.tree'_not_empty m) as [p Hp].
      destruct (PTree.get' p m) as [c|] eqn:Hgp; [|congruence].
      destruct (IHn c (Hforall p c Hgp)) as [k' [Hlen Hget]].
      exists (p::k'). split; [cbn; lia|].
      cbn. rewrite Hgp. exact Hget.
  Qed.

  (* ===== B. extensionality (depth-restricted) ============================== *)
  Lemma pos_trie'_ext : forall n (t1 t2:@pos_trie' A),
      depth' t1 n -> depth' t2 n ->
      (forall k, length k = n -> pt_get' t1 k = pt_get' t2 k) ->
      t1 = t2.
  Proof.
  Admitted.

  Lemma pos_trie_ext : forall n (m1 m2:@pos_trie A),
      depth m1 n -> depth m2 n ->
      (forall k, length k = n -> pt_get m1 k = pt_get m2 k) ->
      m1 = m2.
  Proof.
  Admitted.

  (* ===== C. elements ======================================================= *)
  (* mirrors pt_fold' (leaf -> key = rev stack; node -> flatten over the inner
     PTree's trie_elements, descending with p::stack), so D holds by reusing
     trie_fold_elements at each level. *)
  Fixpoint pt_elements' (t:@pos_trie' A) (stack:list positive)
    : list (list positive * A) :=
    match t with
    | pos_trie_leaf a => [(rev stack, a)]
    | pos_trie_node m =>
        flat_map (fun pc => pt_elements' (snd pc) (fst pc :: stack))
                 (trie_elements (PTree.Nodes m))
    end.

  Definition pt_elements (m:@pos_trie A) : list (list positive * A) :=
    match m with None => [] | Some t => pt_elements' t [] end.

  (* In/get correspondence for the top level (depth-n m): keys all have length n. *)
  Lemma pt_elements_spec : forall n (m:@pos_trie A) k v,
      depth m n ->
      (In (k,v) (pt_elements m) <-> (pt_get m k = Some v /\ length k = n)).
  Proof.
  Admitted.

  Lemma pt_elements_nodup : forall (m:@pos_trie A),
      NoDup (map fst (pt_elements m)).
  Proof.
  Admitted.

  (* ===== D. fold = fold_left over elements ================================= *)
  Lemma pt_fold_elements : forall (R:Type) (f : R -> list positive -> A -> R) r0 (m:@pos_trie A),
      pt_fold f r0 m
      = fold_left (fun a p => f a (fst p) (snd p)) (pt_elements m) r0.
  Proof.
  Admitted.

  (* ===== E. fold_spec ====================================================== *)
  (* of_list builds the trie from a (key,value) list by repeated pt_put. *)
  Definition pt_of_list (l : list (list positive * A)) : @pos_trie A :=
    fold_right (fun p acc => pt_put acc (fst p) (snd p)) None l.

  (* of_list of m's elements reconstructs m (uses extensionality B). *)
  Lemma pt_of_list_elements : forall n (m:@pos_trie A),
      depth m n -> pt_of_list (pt_elements m) = m.
  Proof.
  Admitted.

  (* The depth-restricted fold_spec (matches map.fold_spec's shape, with the
     uniform-depth side conditions on the step and on m). *)
  Lemma pt_fold_spec : forall n (R:Type) (P : @pos_trie A -> R -> Prop)
                              (f : R -> list positive -> A -> R) r0,
      P None r0 ->
      (forall k v (m:@pos_trie A) r,
          length k = n -> depth m n -> pt_get m k = None -> P m r ->
          P (pt_put m k v) (f r k v)) ->
      forall m, depth m n -> P m (pt_fold f r0 m).
  Proof.
  Admitted.

End FoldSpec.
