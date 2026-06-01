(* ============================================================================
   Depth-restricted REMOVE laws + get_empty for pos_trie.

   Second batch of the depth-restricted db-trie interface (see
   WIP/PosTrieDepthLaws.v for get/put, WIP/PosTrieMapOk_false.v for why the
   unrestricted map.ok is false).  Scoping (session 50) showed the db trie needs
   exactly 6 map.ok fields: get_empty, get_put_same, get_put_diff (done),
   get_remove_same, get_remove_diff, fold_spec.  This file does get_empty and
   the two remove laws (+ pt_remove preserves depth, needed because map.remove
   is applied to db tries in db_remove / repair).  fold_spec is the remaining
   (hard) one, handled separately.

   get_remove_same is UNCONDITIONAL.  get_remove_diff needs the uniform-depth
   predicate + equal key length (the unrestricted form is false: m=Some(leaf a),
   k=[], k'=[1] gives None on the left but Some a on the right).

   All lemmas Qed, 0 axioms.  Destined for src/Utils/PosListMap.v.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List Lia.
Import ListNotations.
From Tries Require Import Canonical.
From Utils Require Import PosListMap.

Set Implicit Arguments.

(* ---- foundational PTree get'/set'/remove' interaction (helpers) ---------- *)

(* (re-proved here so this file is self-contained; same as in PosTrieDepthLaws.v) *)
Lemma gss' : forall (A:Type) (i:positive) (x:A) (m: PTree.tree' A),
    PTree.get' i (PTree.set' i x m) = Some x.
Proof.
  induction i; destruct m; simpl; intros; auto using PTree.gss0.
Qed.

Lemma gso' : forall (A:Type) (i j:positive) (x:A) (m: PTree.tree' A),
    i <> j -> PTree.get' i (PTree.set' j x m) = PTree.get' i m.
Proof.
  intros A i j x m H.
  revert j H m; induction i; destruct j, m; simpl; intros; auto;
    solve [apply IHi; congruence | apply PTree.gso0; congruence | congruence].
Qed.

(* remove' is option-level: PTree.remove' : positive -> tree' A -> tree A, and
   PTree.remove p (PTree.Nodes m) = PTree.remove' p m definitionally, so the
   option-level grs/gro instantiate to tree'-level facts. (PTree.grs/gro have A
   implicit and grs's index / gro's two indices are inferred.) *)
Lemma grs' : forall (A:Type) (p:positive) (m: PTree.tree' A),
    PTree.get p (PTree.remove' p m) = None.
Proof. intros A p m. exact (PTree.grs p (PTree.Nodes m)). Qed.

Lemma gro' : forall (A:Type) (j p:positive) (m: PTree.tree' A),
    j <> p -> PTree.get j (PTree.remove' p m) = PTree.get j (PTree.Nodes m).
Proof. intros A j p m H. exact (PTree.gro (PTree.Nodes m) H). Qed.

(* descending one level into [of_ptree T] *)
Lemma pt_get_of_ptree_cons : forall (A:Type) (T : PTree.tree (@pos_trie' A)) j rest,
    pt_get (of_ptree T) (j::rest)
    = match PTree.get j T with Some pt' => pt_get' pt' rest | None => None end.
Proof. intros. destruct T; reflexivity. Qed.

(* ---- get_empty (trivial) ------------------------------------------------- *)
Lemma pt_get_empty : forall (A:Type) (k:list positive), @pt_get A None k = None.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* M1: pt_remove preserves uniform depth.                                     *)
(*   No length constraint: removing any key keeps depth (or yields None,       *)
(*   which has every depth).                                                   *)
(* ========================================================================== *)
Lemma pt_remove'_depth' : forall (A:Type) (k:list positive) (t:@pos_trie' A) n,
    depth' t n -> depth (pt_remove' t k) n.
Proof.
  intros A.
  induction k as [|p k' IH]; intros t n Hd.
  - destruct t; simpl; exact I.
  - inversion Hd; subst.
    + simpl. exact I.
    + simpl. case_eq (PTree.get' p m); intros.
      * destruct (pt_remove' p0 k') eqn:E.
        -- simpl. apply node_depth. intros j w Hget.
           destruct (Pos.eq_dec j p) as [->|Hjp].
           ++ rewrite gss' in Hget. injection Hget as <-.
              pose proof (IH p0 n0 (H p p0 H0)) as Hd'.
              rewrite E in Hd'. simpl in Hd'. exact Hd'.
           ++ rewrite gso' in Hget by exact Hjp.
              exact (H j w Hget).
        -- destruct (PTree.remove' p m) eqn:ER; simpl.
           ++ exact I.
           ++ apply node_depth. intros j w Hget.
              destruct (Pos.eq_dec j p) as [->|Hjp].
              +++ pose proof (grs' p m) as Hg. rewrite ER in Hg. simpl in Hg.
                  rewrite Hget in Hg. discriminate.
              +++ pose proof (@gro' _ j p m Hjp) as Hg. rewrite ER in Hg. simpl in Hg.
                  rewrite Hget in Hg. symmetry in Hg. exact (H j w Hg).
      * simpl. apply node_depth. exact H.
Qed.

Lemma pt_remove_depth : forall (A:Type) (k:list positive) (m:@pos_trie A) n,
    depth m n -> depth (pt_remove m k) n.
Proof.
  intros A k m n H. destruct m; simpl.
  - apply pt_remove'_depth'. exact H.
  - exact I.
Qed.

(* ========================================================================== *)
(* M2: get_remove_same (UNCONDITIONAL).                                        *)
(* ========================================================================== *)
Lemma pt_get_remove'_same : forall (A:Type) (k:list positive) (t:@pos_trie' A),
    pt_get (pt_remove' t k) k = None.
Proof.
  intros A k. revert k. induction k as [|p k' IH]; intros t.
  { destruct t; reflexivity. }
  { destruct t as [a | m]; simpl.
    - reflexivity.
    - case_eq (PTree.get' p m); intros.
      + destruct (pt_remove' p0 k') eqn:E.
        * simpl. rewrite gss'.
          pose proof (IH p0) as Hih. rewrite E in Hih. simpl in Hih. exact Hih.
        * rewrite pt_get_of_ptree_cons. rewrite grs'. reflexivity.
      + simpl. rewrite H. reflexivity.
  }
Qed.

Lemma pt_get_remove_same : forall (A:Type) (k:list positive) (m:@pos_trie A),
    pt_get (pt_remove m k) k = None.
Proof.
  intros A k m. destruct m; simpl.
  - apply pt_get_remove'_same.
  - reflexivity.
Qed.

(* ========================================================================== *)
(* M3: get_remove_diff (depth-restricted, equal length).                       *)
(* ========================================================================== *)
Lemma pt_get_remove'_diff : forall (A:Type) (k k':list positive) (t:@pos_trie' A),
    length k = length k' -> k <> k' -> depth' t (length k') ->
    pt_get (pt_remove' t k') k = pt_get' t k.
Proof.
  intros A k. revert k. intro k. intros k' t Hlen Hne Hd. revert k' t Hlen Hne Hd.
  induction k as [|a k0 IH]; intros [|p k0'] t Hlen Hne Hd; simpl in Hlen.
  - congruence.
  - discriminate Hlen.
  - discriminate Hlen.
  - inversion Hd as [| m n0 Hforall Hm Hn]; subst.
    injection Hlen as Hlen0.
    destruct (Pos.eq_dec a p) as [Heq | Hap].
    + subst p.
      assert (Hk0 : k0 <> k0') by (intro Hc; apply Hne; subst; reflexivity).
      simpl.
      case_eq (PTree.get' a m); [intros pt' Ha | intros Ha].
      * destruct (pt_remove' pt' k0') eqn:E.
        -- simpl. rewrite gss'.
           pose proof (IH k0' pt' Hlen0 Hk0 (Hforall a pt' Ha)) as Hih.
           rewrite E in Hih; simpl in Hih. exact Hih.
        -- rewrite pt_get_of_ptree_cons.
           assert (H : PTree.get a (PTree.remove' a m) = None)
             by exact (PTree.grs a (PTree.Nodes m)).
           rewrite H.
           pose proof (IH k0' pt' Hlen0 Hk0 (Hforall a pt' Ha)) as Hih.
           rewrite E in Hih; simpl in Hih. exact Hih.
      * simpl. rewrite Ha. reflexivity.
    + simpl.
      case_eq (PTree.get' p m); [intros pt' Hp | intros Hp].
      * destruct (pt_remove' pt' k0') eqn:E.
        -- simpl. rewrite (gso' p0 m Hap). reflexivity.
        -- rewrite pt_get_of_ptree_cons.
           assert (H : PTree.get a (PTree.remove' p m) = PTree.get a (PTree.Nodes m))
             by exact (PTree.gro (PTree.Nodes m) Hap).
           rewrite H. cbn [PTree.get]. reflexivity.
      * simpl. reflexivity.
Qed.

Lemma pt_get_remove_diff : forall (A:Type) (k k':list positive) (m:@pos_trie A),
    length k = length k' -> k <> k' -> depth m (length k') ->
    pt_get (pt_remove m k') k = pt_get m k.
Proof.
  intros A k k' m Hlen Hne Hd. destruct m as [t|]; simpl in *.
  - apply pt_get_remove'_diff; assumption.
  - reflexivity.
Qed.
