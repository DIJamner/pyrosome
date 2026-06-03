(* ============================================================================
   Conversions between the two positive-list-keyed tries, and a conversion-
   wrapper generic-join.

   - [pos_trie] (PosListMap.v): the EFFICIENT query trie; carries
     [pt_spaced_intersect] (the generic join) and its 3352-line correctness
     proof, but [map.ok] is provably FALSE (mixed-depth tries break get_put).
   - [fpt]/[full_pos_trie_map] (FullPosTrie.v): a fattened (3-constructor)
     LAWFUL map ([map.ok] holds unconditionally), used as the e-graph carrier.

   To run the pos_trie-specialized generic join on the lawful [fpt] carrier we
   convert at the intersection boundary: [fpt_spaced_intersect] converts each
   input [fpt] to a [pos_trie], runs [compat_intersect], and converts back.
   This is a TEMPORARY wrapper (runtime conversion cost); a native [fpt]
   generic-join is a planned optimization that will reuse the get-preservation
   lemmas below.

   The conversions are fold-rebuild: fold the source map and re-[map.put] each
   binding into an empty target.  The two reps (option pos_trie' vs option fpt')
   are DISTINCT types, so the [map.put]/[map.empty]/[map.fold] instances are
   inferred unambiguously -- but [rep] is a Coercion and is NOT resolved back to
   its instance, so every projection must name its instance explicitly.
   ============================================================================ *)

From Stdlib Require Import NArith Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface Map.Properties.
From Tries Require Import Canonical.
From Utils Require Import Utils Monad Default FullPosTrie PosListMap PosListMapLaws
  PosListMapIntersectSpec TrieMap.

Set Implicit Arguments.

Section Conv.
  Context {B : Type}.

  Definition pt_to_fpt (t : @pos_trie B) : @FullPosTrie.fpt B :=
    @map.fold (list positive) B (@pos_trie_map B) (@FullPosTrie.fpt B)
      (fun acc k v => @map.put (list positive) B (@FullPosTrie.full_pos_trie_map B) acc k v)
      (@map.empty (list positive) B (@FullPosTrie.full_pos_trie_map B)) t.

  Definition fpt_to_pt (t : @FullPosTrie.fpt B) : @pos_trie B :=
    @map.fold (list positive) B (@FullPosTrie.full_pos_trie_map B) (@pos_trie B)
      (fun acc k v => @map.put (list positive) B (@pos_trie_map B) acc k v)
      (@map.empty (list positive) B (@pos_trie_map B)) t.

End Conv.

(* The proof-side specification: run the proven pos_trie generic join by
   converting each input [fpt] to a [pos_trie], joining, and converting back.
   This carries the runtime fold-rebuild conversion cost, so it is NO LONGER the
   function plugged into the running e-graph -- it is kept purely as the
   reference the native [fpt_spaced_intersect] (below) is proven equal to. *)
Definition fpt_spaced_intersect_via_conv {B} `{WithDefault B} (merge : B -> B -> B)
  (tries : (@FullPosTrie.fpt B * list bool)
           * list (@FullPosTrie.fpt B * list bool))
  : @FullPosTrie.fpt B :=
  let conv := fun p : @FullPosTrie.fpt B * list bool => (fpt_to_pt (fst p), snd p) in
  pt_to_fpt (compat_intersect merge (conv (fst tries), List.map conv (snd tries))).

(* The public name [fpt_spaced_intersect] (the function plugged into the running
   e-graph) is defined AFTER [fpt_spaced_intersect_native] (End FptNativeJoin),
   as the conversion-free native join.  It is proven equal (on keys, at the
   call-site depths) to [fpt_spaced_intersect_via_conv] via
   [fpt_spaced_intersect_native_keys_iff]. *)

Lemma pt_to_fpt_get {B} (t : @pos_trie B) (n : nat) :
  depth t n ->
  forall k, length k = n -> fpt_get (pt_to_fpt t) k = pt_get t k.
Proof.
  intros Hdepth.
  unfold pt_to_fpt.
  (* The pos_trie_map instance reduces its [map.fold] to [pt_fold] definitionally;
     leave the target-side [map.put]/[map.empty]/[map.get] in [map.*] form so the
     unconditional [full_pos_trie_map_ok] field rewrites apply syntactically. *)
  change (@map.fold (list positive) B (@pos_trie_map B) (@FullPosTrie.fpt B)
            (fun acc k v => @map.put (list positive) B (@FullPosTrie.full_pos_trie_map B) acc k v)
            (@map.empty (list positive) B (@FullPosTrie.full_pos_trie_map B)) t)
    with (pt_fold (fun (acc : @FullPosTrie.fpt B) k v =>
                     @map.put (list positive) B (@FullPosTrie.full_pos_trie_map B) acc k v)
                  (@map.empty (list positive) B (@FullPosTrie.full_pos_trie_map B)) t).
  apply (@pt_fold_spec' B n (@FullPosTrie.fpt B)
           (fun (src : @pos_trie B) (acc : @FullPosTrie.fpt B) =>
                   forall k, length k = n ->
                     @map.get (list positive) B (@FullPosTrie.full_pos_trie_map B) acc k
                     = pt_get src k)).
  - (* base: P None None *)
    intros k Hk.
    rewrite pt_get_empty.
    exact (@map.get_empty (list positive) B (@FullPosTrie.full_pos_trie_map B)
             (@FullPosTrie.full_pos_trie_map_ok B) k).
  - (* step *)
    intros k0 v0 m r Hk0 Hdm Hgetm IH k Hk.
    destruct (list_eq_dec Pos.eq_dec k k0) as [Heq | Hne].
    + subst k0.
      rewrite (@map.get_put_same (list positive) B (@FullPosTrie.full_pos_trie_map B)
                 (@FullPosTrie.full_pos_trie_map_ok B) r k v0).
      rewrite pt_get_put_same.
      * reflexivity.
      * rewrite Hk. exact Hdm.
    + rewrite (@map.get_put_diff (list positive) B (@FullPosTrie.full_pos_trie_map B)
                 (@FullPosTrie.full_pos_trie_map_ok B) r k v0 k0 Hne).
      rewrite pt_get_put_diff.
      * exact (IH k Hk).
      * rewrite Hk, Hk0. reflexivity.
      * exact Hne.
      * rewrite Hk0. exact Hdm.
  - exact Hdepth.
Qed.

(* ============================================================================
   fpt_to_pt_get : the conversion fpt -> pos_trie preserves get on length-n keys
   for uniform-depth fpt's.  (Companion to pt_to_fpt_get above.)
   ============================================================================ *)

(* Uniform-depth predicate on fpt' (the fpt_both constructor never arises under
   uniform depth, so it is intentionally absent here). *)
Inductive fpt_depth' {A} : @FullPosTrie.fpt' A -> nat -> Prop :=
| fpt_leaf_depth a : fpt_depth' (FullPosTrie.fpt_leaf a) 0
| fpt_node_depth m n :
    (forall p c, PTree.get' p m = Some c -> fpt_depth' c n) ->
    fpt_depth' (FullPosTrie.fpt_node m) (S n).

Definition fpt_depth {A} (t : @FullPosTrie.fpt A) (n : nat) : Prop :=
  match t with None => True | Some t' => fpt_depth' t' n end.

(* Depth of fpt_singleton matches key length. *)
Lemma fpt_singleton_depth' {A} (k : list positive) (v : A) :
  fpt_depth' (FullPosTrie.fpt_singleton k v) (length k).
Proof.
  induction k as [|p k' IH].
  - constructor.
  - cbn [FullPosTrie.fpt_singleton length].
    constructor.
    intros q c Hget.
    destruct (Pos.eq_dec q p) as [->|Hne].
    + rewrite PTree.gss0 in Hget. injection Hget as <-. exact IH.
    + rewrite PTree.gso0 in Hget by auto. discriminate.
Qed.

(* fpt_put' preserves fpt_depth' when the key has the correct length.
   Note: fpt_depth' has no fpt_both constructor, so fpt_both inputs are vacuously
   impossible at any S-depth (inversion closes those goals automatically). *)
Lemma fpt_put'_depth' {A} (k : list positive) (v : A) (t : FullPosTrie.fpt' A) (n : nat) :
  length k = n ->
  fpt_depth' t n ->
  fpt_depth' (FullPosTrie.fpt_put' t k v) n.
Proof.
  revert t n. induction k as [|p k' IH]; intros t n Hlen Hd.
  - subst n. destruct t as [a | m | a m]; cbn [FullPosTrie.fpt_put'].
    + constructor.
    + inversion Hd.
    + inversion Hd.
  - destruct n as [|n']; [discriminate|].
    injection Hlen as Hlen'.
    destruct t as [a | m | a m].
    + inversion Hd.
    + inversion Hd as [|m0 n0 Hchild Hm Hn]; subst.
      cbn [FullPosTrie.fpt_put'].
      constructor. intros q c Hget.
      unfold FullPosTrie.fpt_child_put in Hget.
      destruct (PTree.get' p m) as [c0|] eqn:Hgp;
        destruct (Pos.eq_dec q p) as [->|Hne].
      * rewrite FullPosTrie.fpt_gss' in Hget. injection Hget as <-.
        apply IH with (n := length k'); [reflexivity | exact (Hchild p c0 Hgp)].
      * rewrite FullPosTrie.fpt_gso' in Hget by auto.
        exact (Hchild q c Hget).
      * rewrite FullPosTrie.fpt_gss' in Hget. injection Hget as <-.
        exact (fpt_singleton_depth' k' v).
      * rewrite FullPosTrie.fpt_gso' in Hget by auto.
        exact (Hchild q c Hget).
    + inversion Hd as [|m0 n0 Hchild Hm Hn]; subst.
Qed.

(* fpt_put preserves fpt_depth when the key has the correct length. *)
Lemma fpt_put_depth {A} (k : list positive) (v : A) (m : FullPosTrie.fpt A) (n : nat) :
  length k = n ->
  fpt_depth m n ->
  fpt_depth (FullPosTrie.fpt_put m k v) n.
Proof.
  intros Hlen Hd.
  destruct m as [t|].
  - cbn [FullPosTrie.fpt_put fpt_depth] in *.
    apply fpt_put'_depth'; assumption.
  - cbn [FullPosTrie.fpt_put fpt_depth].
    rewrite <- Hlen. exact (fpt_singleton_depth' k v).
Qed.

(* pt_to_fpt preserves uniform depth: a depth-n pos_trie maps to a depth-n fpt. *)
Lemma pt_to_fpt_depth {B} (t : @pos_trie B) (n : nat) :
  depth t n -> fpt_depth (pt_to_fpt t) n.
Proof.
  intros Hdepth.
  unfold pt_to_fpt.
  change (@map.fold (list positive) B (@pos_trie_map B) (@FullPosTrie.fpt B)
            (fun acc k v => @map.put (list positive) B (@FullPosTrie.full_pos_trie_map B) acc k v)
            (@map.empty (list positive) B (@FullPosTrie.full_pos_trie_map B)) t)
    with (pt_fold (fun (acc : @FullPosTrie.fpt B) k v =>
                     @map.put (list positive) B (@FullPosTrie.full_pos_trie_map B) acc k v)
                  (@map.empty (list positive) B (@FullPosTrie.full_pos_trie_map B)) t).
  apply (@pt_fold_spec' B n (@FullPosTrie.fpt B)
           (fun (_ : @pos_trie B) (acc : @FullPosTrie.fpt B) => fpt_depth acc n)).
  - (* base: fpt_depth None n *)
    exact I.
  - (* step: fpt_depth acc n -> fpt_depth (fpt_put acc k v) n *)
    intros k v m r Hk Hdm Hgetm IH.
    change (@map.put (list positive) B (@FullPosTrie.full_pos_trie_map B) r k v)
      with (FullPosTrie.fpt_put r k v).
    apply fpt_put_depth; [exact Hk | exact IH].
  - exact Hdepth.
Qed.

(* Keys reachable in a uniform-depth fpt' have length n. *)
Lemma fpt_depth'_key_length {A} (t : FullPosTrie.fpt' A) (n : nat) :
  fpt_depth' t n -> forall k v, FullPosTrie.fpt_get' t k = Some v -> length k = n.
Proof.
  induction 1 as [a | m n Hchild IH].
  - intros k v Hget.
    destruct k as [|p k'].
    + reflexivity.
    + cbn [FullPosTrie.fpt_get'] in Hget. discriminate.
  - intros k v Hget.
    destruct k as [|p k'].
    + cbn [FullPosTrie.fpt_get'] in Hget. discriminate.
    + cbn [FullPosTrie.fpt_get'] in Hget.
      destruct (PTree.get' p m) as [c|] eqn:Hc.
      * cbn [Datatypes.length].
        f_equal.
        apply (IH p c Hc k' v Hget).
      * discriminate.
Qed.

Lemma fpt_depth_key_length {A} (t : FullPosTrie.fpt A) (n : nat) :
  fpt_depth t n -> forall k v, FullPosTrie.fpt_get t k = Some v -> length k = n.
Proof.
  destruct t as [t'|].
  - intros Hd k v Hget. cbn [fpt_depth] in Hd.
    cbn [FullPosTrie.fpt_get] in Hget.
    exact (fpt_depth'_key_length Hd k Hget).
  - intros Hd k v Hget. cbn [FullPosTrie.fpt_get] in Hget. discriminate.
Qed.

(* boolean key-equality with a spec, built from the decidable equality. *)
Definition lkeqb (k1 k2 : list positive) : bool :=
  if list_eq_dec Pos.eq_dec k1 k2 then true else false.

Lemma lkeqb_true_iff k1 k2 : lkeqb k1 k2 = true <-> k1 = k2.
Proof.
  unfold lkeqb. destruct (list_eq_dec Pos.eq_dec k1 k2) as [He|Hne].
  - split; intro; [exact He | reflexivity].
  - split; intro H; [discriminate | contradiction].
Qed.

Lemma lkeqb_refl k : lkeqb k k = true.
Proof. apply lkeqb_true_iff. reflexivity. Qed.

Lemma find_none_of_not_in {B} (k : list positive) (l : list (list positive * B)) :
  ~ In k (map fst l) ->
  find (fun p => lkeqb (fst p) k) l = None.
Proof.
  induction l as [|a l' IH].
  - intros _. reflexivity.
  - intros Hnin. cbn [find].
    destruct (lkeqb (fst a) k) eqn:Hb.
    + apply lkeqb_true_iff in Hb. exfalso. apply Hnin.
      cbn [map]. left. exact Hb.
    + apply IH. intro Hin. apply Hnin. cbn [map]. right. exact Hin.
Qed.

(* The meat: building a pos_trie by fold_left of pt_put over a NoDup, length-n
   list of bindings preserves get (relative to acc and a find over the list). *)
Lemma fold_left_pt_put_get {B} (l : list (list positive * B)) :
  forall (acc : @pos_trie B) (n : nat),
  depth acc n ->
  NoDup (map fst l) ->
  (forall p, In p l -> length (fst p) = n) ->
  forall k, length k = n ->
    pt_get (fold_left (fun (a : @pos_trie B) p => pt_put a (fst p) (snd p)) l acc) k
    = match find (fun p => lkeqb (fst p) k) l with
      | Some p => Some (snd p)
      | None    => pt_get acc k
      end.
Proof.
  induction l as [|a l' IH].
  - intros acc n Hd _ _ k Hk. cbn [fold_left find]. reflexivity.
  - intros acc n Hd Hnd Hlen k Hk.
    cbn [fold_left].
    set (acc' := pt_put acc (fst a) (snd a)).
    assert (Hla : length (fst a) = n) by (apply Hlen; left; reflexivity).
    assert (Hd' : depth acc' n).
    { unfold acc'. rewrite <- Hla. apply pt_put_depth. rewrite Hla. exact Hd. }
    cbn [map] in Hnd. rewrite NoDup_cons_iff in Hnd.
    destruct Hnd as [Hnin Hnd'].
    assert (Hlen' : forall p, In p l' -> length (fst p) = n).
    { intros p Hp. apply Hlen. right. exact Hp. }
    specialize (IH acc' n Hd' Hnd' Hlen' k Hk).
    cbn [find].
    destruct (lkeqb (fst a) k) eqn:Hb.
    + (* fst a = k *)
      apply lkeqb_true_iff in Hb.
      rewrite IH.
      assert (Hfn : find (fun p => lkeqb (fst p) k) l' = None).
      { apply find_none_of_not_in. rewrite Hb in Hnin. exact Hnin. }
      rewrite Hfn.
      unfold acc'. rewrite Hb.
      rewrite pt_get_put_same.
      * reflexivity.
      * rewrite Hk. exact Hd.
    + (* fst a <> k *)
      rewrite IH.
      assert (Hne : k <> fst a).
      { intro He. assert (lkeqb (fst a) k = true) as Hcon.
        { apply lkeqb_true_iff. symmetry. exact He. }
        rewrite Hcon in Hb. discriminate. }
      destruct (find (fun p => lkeqb (fst p) k) l') as [p|] eqn:Hf.
      * reflexivity.
      * unfold acc'.
        rewrite pt_get_put_diff.
        -- reflexivity.
        -- rewrite Hk, Hla. reflexivity.
        -- exact Hne.
        -- rewrite Hla. exact Hd.
Qed.

Lemma fpt_to_pt_get {B} (t : @FullPosTrie.fpt B) (n : nat) :
  fpt_depth t n ->
  forall k, length k = n -> pt_get (fpt_to_pt t) k = FullPosTrie.fpt_get t k.
Proof.
  intros Hdepth k Hk.
  unfold fpt_to_pt.
  (* The full_pos_trie_map instance reduces its [map.fold] to [fpt_fold]
     definitionally; expose it, leaving target-side put/empty as pos_trie ops. *)
  change (@map.fold (list positive) B (@FullPosTrie.full_pos_trie_map B) (@pos_trie B)
            (fun acc k v => @map.put (list positive) B (@pos_trie_map B) acc k v)
            (@map.empty (list positive) B (@pos_trie_map B)) t)
    with (FullPosTrie.fpt_fold
            (fun (acc : @pos_trie B) k v => pt_put acc k v)
            (@None (@pos_trie' B)) t).
  rewrite FullPosTrie.fpt_fold_elements.
  cbv beta.
  set (elems := FullPosTrie.fpt_elements t).
  (* per-element length: each element's get holds, so its key has length n *)
  assert (Hlen : forall p, In p elems -> length (fst p) = n).
  { intros [k0 v0] Hin. cbn [fst].
    assert (Hgk0 : FullPosTrie.fpt_get t k0 = Some v0).
    { apply FullPosTrie.fpt_elements_spec.
      change (In (k0, v0) elems) in Hin. exact Hin. }
    eapply fpt_depth_key_length; eassumption. }
  rewrite (fold_left_pt_put_get elems (@None (@pos_trie' B)) (n:=n)
             I (FullPosTrie.fpt_elements_nodup t) Hlen k Hk).
  rewrite pt_get_empty.
  (* relate find over elems to fpt_get t k *)
  destruct (find (fun p => lkeqb (fst p) k) elems) as [p|] eqn:Hf.
  - (* found: In p elems and fst p = k, so fpt_get t k = Some (snd p) *)
    apply find_some in Hf. destruct Hf as [Hin Hb].
    apply lkeqb_true_iff in Hb.
    symmetry.
    apply FullPosTrie.fpt_elements_spec.
    rewrite <- Hb.
    destruct p as [k0 v0]. cbn [fst snd] in *. subst k0.
    change (In (k, v0) elems) in Hin. exact Hin.
  - (* not found: fpt_get t k = None *)
    symmetry.
    destruct (FullPosTrie.fpt_get t k) as [v|] eqn:Hg.
    + exfalso.
      assert (In (k, v) elems) as Hin.
      { apply FullPosTrie.fpt_elements_spec. exact Hg. }
      pose proof (find_none _ _ Hf (k, v) Hin) as Hnn.
      cbn [fst] in Hnn. rewrite lkeqb_refl in Hnn. discriminate.
    + reflexivity.
Qed.

(* fold_left of pt_put over a list of length-n keys into a depth-n acc
   preserves depth n. *)
Lemma fold_left_pt_put_depth {B} (l : list (list positive * B)) (n : nat) :
  (forall p, In p l -> length (fst p) = n) ->
  forall acc, depth acc n ->
  depth (fold_left (fun (a : @pos_trie B) p => pt_put a (fst p) (snd p)) l acc) n.
Proof.
  induction l as [|[k v] l' IH]; intros Hlen acc Hacc.
  - exact Hacc.
  - cbn [fold_left fst snd].
    apply IH.
    + intros p Hp. apply Hlen. right. exact Hp.
    + assert (Hk : length k = n) by (apply (Hlen (k, v)); left; reflexivity).
      rewrite <- Hk. apply pt_put_depth. rewrite Hk. exact Hacc.
Qed.

(* fpt_to_pt preserves uniform depth: a depth-n fpt maps to a depth-n pos_trie. *)
Lemma fpt_to_pt_has_depth' {B} (t : @FullPosTrie.fpt B) (n : nat) :
  fpt_depth t n -> depth (fpt_to_pt t) n.
Proof.
  intros Hdepth.
  unfold fpt_to_pt.
  change (@map.fold (list positive) B (@FullPosTrie.full_pos_trie_map B) (@pos_trie B)
            (fun acc k v => @map.put (list positive) B (@pos_trie_map B) acc k v)
            (@map.empty (list positive) B (@pos_trie_map B)) t)
    with (FullPosTrie.fpt_fold
            (fun (acc : @pos_trie B) k v => pt_put acc k v)
            (@None (@pos_trie' B)) t).
  rewrite FullPosTrie.fpt_fold_elements.
  cbv beta.
  set (elems := FullPosTrie.fpt_elements t).
  assert (Hlen : forall p, In p elems -> length (fst p) = n).
  { intros [k0 v0] Hin. cbn [fst].
    assert (Hgk0 : FullPosTrie.fpt_get t k0 = Some v0).
    { apply FullPosTrie.fpt_elements_spec. exact Hin. }
    eapply fpt_depth_key_length; eassumption. }
  apply fold_left_pt_put_depth.
  - exact Hlen.
  - exact I.
Qed.

(* Builder (converse of [trie_fold'_andb_get_inv]): if every entry's value
   satisfies [f], the [andb]-fold over the trie is true. *)
Lemma trie_fold'_andb_get_build {B : Type} (f : B -> bool)
  (m : PTree.tree' B) (revnum : positive) :
  (forall p v, PTree.get' p m = Some v -> Is_true (f v)) ->
  Is_true (TrieMap.trie_fold' (fun res (_:positive) (v:B) => andb res (f v))
                              true m revnum).
Proof.
  revert revnum.
  induction m as [m IH | a | a m IH | m IH | m1 IH1 m2 IH2 | m IH a | m1 IH1 a m2 IH2];
    intros revnum Hall; cbn.
  - apply IH. intros p v Hget. apply (Hall (xI p)). cbn. exact Hget.
  - apply Hall with (p := xH). reflexivity.
  - rewrite (trie_fold'_andb_factor f m (xI revnum) (f a)).
    apply Is_true_eq_left. apply Bool.andb_true_iff. split.
    + apply Is_true_eq_true. apply (Hall xH). reflexivity.
    + apply Is_true_eq_true. apply IH. intros p v Hget. apply (Hall (xI p)). cbn. exact Hget.
  - apply IH. intros p v Hget. apply (Hall (xO p)). cbn. exact Hget.
  - rewrite (trie_fold'_andb_factor f m1 (xO revnum) _).
    apply Is_true_eq_left. apply Bool.andb_true_iff. split.
    + apply Is_true_eq_true. apply IH2. intros p v Hget. apply (Hall (xI p)). cbn. exact Hget.
    + apply Is_true_eq_true. apply IH1. intros p v Hget. apply (Hall (xO p)). cbn. exact Hget.
  - rewrite (trie_fold'_andb_factor f m (xO revnum) (f a)).
    apply Is_true_eq_left. apply Bool.andb_true_iff. split.
    + apply Is_true_eq_true. apply (Hall xH). reflexivity.
    + apply Is_true_eq_true. apply IH. intros p v Hget. apply (Hall (xO p)). cbn. exact Hget.
  - rewrite (trie_fold'_andb_factor f m1 (xO revnum) _).
    apply Is_true_eq_left. apply Bool.andb_true_iff. split.
    + apply Is_true_eq_true. rewrite (trie_fold'_andb_factor f m2 (xI revnum) (f a)).
      apply Is_true_eq_left. apply Bool.andb_true_iff. split.
      * apply Is_true_eq_true. apply (Hall xH). reflexivity.
      * apply Is_true_eq_true. apply IH2. intros p v Hget. apply (Hall (xI p)). cbn. exact Hget.
    + apply Is_true_eq_true. apply IH1. intros p v Hget. apply (Hall (xO p)). cbn. exact Hget.
Qed.

(* Reverse bridge: the [depth'] Prop entails the [has_depth'] boolean.
   [P3] needs [Is_true (has_depth' ...)] for [wf_input], but [fpt_to_pt_has_depth']
   and [pt_spaced_intersect_depth] produce the [depth'] Prop. *)
Lemma depth'_to_has_depth' {B} (n : nat) (pt : @pos_trie' B) :
  depth' pt n -> Is_true (has_depth' n pt).
Proof.
  revert pt. induction n; intros pt Hd.
  - inversion Hd; subst. cbn. exact I.
  - inversion Hd; subst. cbn [has_depth'].
    change (Is_true (TrieMap.trie_fold'
                       (fun res (_:positive) (w:@pos_trie' B) =>
                          res && has_depth' n w)
                       true m xH)).
    apply trie_fold'_andb_get_build.
    intros p v Hget. apply IHn. apply (H1 p v Hget).
Qed.

(* ============================================================================
   M1 — NATIVE FPT' SPACED JOIN

   Definitions that operate directly on [FullPosTrie.fpt'] with no
   fold-rebuild conversion.  Mirrors the [pos_trie'] join in PosListMap.v
   (pt_spaced_intersect' / pt_spaced_intersect).
   ============================================================================ *)

Section FptNativeJoin.
  Context {B : Type} `{Hdef : WithDefault B}.
  Context (merge : B -> B -> B).

  Local Notation fpt' := (@FullPosTrie.fpt' B).
  Local Notation fpt  := (@FullPosTrie.fpt  B).

  (* M1-1: proj_node_map — mirror proj_node_map_unchecked (PosListMap.v:412).
     leaf a  => PTree.Node010 (fpt_leaf default)   [dead sentinel]
     node m  => m
     both _m => m                                   [fpt_both dead under fpt_depth'] *)
  Definition fpt_proj_node_unchecked (p : fpt') : PTree.tree' fpt' :=
    match p with
    | FullPosTrie.fpt_leaf _ => PTree.Node010 (FullPosTrie.fpt_leaf default)
    | FullPosTrie.fpt_node m => m
    | FullPosTrie.fpt_both _ m => m
    end.

  (* M1-2: leaf_intersect — mirror leaf_intersect (PosListMap.v:424).
     Structural on the list; dead cases (node/both) pass through unchanged. *)
  Fixpoint fpt_leaf_intersect (a : B) (ptl : list fpt') : B :=
    match ptl with
    | [] => a
    | (FullPosTrie.fpt_leaf a') :: ptl' => fpt_leaf_intersect (merge a a') ptl'
    | (FullPosTrie.fpt_node _)  :: ptl' => fpt_leaf_intersect a ptl'   (* dead *)
    | (FullPosTrie.fpt_both _ _) :: ptl' => fpt_leaf_intersect a ptl'  (* dead *)
    end.

  (* M1-3: partition_result / partition_tries — clone of PosListMap.v:468-502
     with carrier fpt' instead of pos_trie'. *)
  Variant fpt_partition_result :=
    | fpt_just_false_part
        (ci0 : list bool) (pt0 : fpt')
        (cil : list (list bool)) (ptl : list fpt')
    | fpt_have_true_part
        (f_cil : list (list bool)) (f_ptl : list fpt')
        (t_ci0 : list bool) (t_pt0 : fpt')
        (t_cil : list (list bool)) (t_ptl : list fpt').

  Fixpoint fpt_partition_tries
      (cil : list (list bool)) (ptl : list fpt')
      (acc : fpt_partition_result) : fpt_partition_result :=
    match cil, ptl, acc with
    | [], [], _ => acc
    | (false :: l1) :: cil', pt :: ptl',
      fpt_just_false_part ci0 pt0 other_cil other_tries =>
        fpt_partition_tries cil' ptl'
          (fpt_just_false_part l1 pt (ci0 :: other_cil) (pt0 :: other_tries))
    | (false :: l1) :: cil', pt :: ptl',
      fpt_have_true_part other_cil other_tries t_ci0 t_pt0 true_cil true_tries =>
        fpt_partition_tries cil' ptl'
          (fpt_have_true_part (l1 :: other_cil) (pt :: other_tries)
             t_ci0 t_pt0 true_cil true_tries)
    | (true :: l1) :: cil', pt :: ptl',
      fpt_just_false_part ci0 pt0 other_cil other_tries =>
        fpt_partition_tries cil' ptl'
          (fpt_have_true_part (ci0 :: other_cil) (pt0 :: other_tries)
             l1 pt [] [])
    | (true :: l1) :: cil', pt :: ptl',
      fpt_have_true_part other_cil other_tries t_ci0 t_pt0 true_cil true_tries =>
        fpt_partition_tries cil' ptl'
          (fpt_have_true_part other_cil other_tries
             l1 pt (t_ci0 :: true_cil) (t_pt0 :: true_tries))
    | [] :: _, _, _  (* should never happen *)
    | _, _, _ => acc
    end.

  (* M1-4: fpt_spaced_intersect'' — mirror pt_spaced_intersect' (PosListMap.v:852).
     Structural on [fuel]; no nested-fix guard issue.
     Uses TrieMap.list_intersect instantiated at B:=fpt', C:=fpt'. *)
  Fixpoint fpt_spaced_intersect''
      (fuel : nat)
      (cil : list (list bool)) (ptl : list fpt')
      (ci0 : list bool) (cil' : list (list bool)) (pt0 : fpt') (ptl' : list fpt')
      : option fpt' :=
    match fuel, ci0, pt0 with
    | S _, [], FullPosTrie.fpt_node _
    | S _, [], FullPosTrie.fpt_both _ _ (* dead under fpt_depth' *)
    | O,   _,  _ => None   (* should never happen *)
    | S _, [], FullPosTrie.fpt_leaf a =>
        Some (FullPosTrie.fpt_leaf
                (fpt_leaf_intersect (fpt_leaf_intersect a ptl) ptl'))
    | S fuel', ci0_hd :: ci0_tl, _ =>
        let initial_part :=
          if ci0_hd
          then fpt_have_true_part [] [] ci0_tl pt0 [] []
          else fpt_just_false_part ci0_tl pt0 [] []
        in
        let part :=
          fpt_partition_tries cil' ptl'
            (fpt_partition_tries cil ptl initial_part)
        in
        match part with
        | fpt_just_false_part ci0' pt0' oc ot =>
            fpt_spaced_intersect'' fuel' oc ot ci0' [] pt0' []
        | fpt_have_true_part oc ot t_ci0 t_pt0 t_cil t_ptl =>
            let true_cil_rev := rev t_cil in
            let pt_intersect :=
              TrieMap.list_intersect
                (fun is_forward =>
                   fpt_spaced_intersect'' fuel' oc ot t_ci0
                     (if is_forward then t_cil else true_cil_rev))
                (fpt_proj_node_unchecked t_pt0)
                (map fpt_proj_node_unchecked t_ptl)
            in
            option_map FullPosTrie.fpt_node pt_intersect
        end
    end.

  (* M1-5: fpt_spaced_intersect_native — mirror pt_spaced_intersect (PosListMap.v:891).
     Input type matches fpt_spaced_intersect_via_conv for drop-in use.
     Note: [list_Mmap id ptl] with [ptl : list fpt = list (option fpt')] uses the
     option monad (M = option, A = B = fpt') — we pin the monad explicitly to avoid
     Rocq inferring the list monad. *)
  Definition fpt_spaced_intersect_native
      (tries : (fpt * list bool) * list (fpt * list bool))
      : fpt :=
    let '(ptl, cil) := split (snd tries) in
    let '(pt0, ci0) := fst tries in
    let fuel := S (length ci0) in
    match pt0, @list_Mmap option _ _ option_monad id ptl with
    | Some pt0', Some ptl' =>
        fpt_spaced_intersect'' fuel cil ptl' ci0 [] pt0' []
    | _, _ => None
    end.

End FptNativeJoin.

(* The public generic-join the running e-graph uses: the conversion-free native
   [fpt'] join.  Downstream code and soundness statements reference only this
   name; it is proven equivalent (on keys) to [fpt_spaced_intersect_via_conv]
   via [fpt_spaced_intersect_native_keys_iff]. *)
Definition fpt_spaced_intersect {B} `{WithDefault B} (merge : B -> B -> B)
  (tries : (@FullPosTrie.fpt B * list bool)
           * list (@FullPosTrie.fpt B * list bool))
  : @FullPosTrie.fpt B :=
  fpt_spaced_intersect_native merge tries.

(* ============================================================================
   M1b — STRUCTURAL INJECTION fpt' -> pos_trie'
   (proof-convenience only; no performance requirement)
   ============================================================================ *)

(* M1b-6: tree'_map' — structural map on PTree.tree' (plain Fixpoint, no guard issue). *)
Fixpoint tree'_map' {X Y : Type} (f : X -> Y) (m : PTree.tree' X) : PTree.tree' Y :=
  match m with
  | PTree.Node001 r        => PTree.Node001 (tree'_map' f r)
  | PTree.Node010 y        => PTree.Node010 (f y)
  | PTree.Node011 y r      => PTree.Node011 (f y) (tree'_map' f r)
  | PTree.Node100 l        => PTree.Node100 (tree'_map' f l)
  | PTree.Node101 l r      => PTree.Node101 (tree'_map' f l) (tree'_map' f r)
  | PTree.Node110 l y      => PTree.Node110 (tree'_map' f l) (f y)
  | PTree.Node111 l y r    => PTree.Node111 (tree'_map' f l) (f y) (tree'_map' f r)
  end.

(* Key lemma: get' on tree'_map' f m equals option_map f (get' on m). *)
Lemma tree'_map'_get {X Y : Type} (f : X -> Y) (m : PTree.tree' X) (p : positive) :
  PTree.get' p (tree'_map' f m) = option_map f (PTree.get' p m).
Proof.
  revert p.
  induction m as [r IHr | y | y r IHr | l IHl | l IHl r IHr | l IHl y | l IHl y r IHr];
    intros p; destruct p; cbn;
    try reflexivity;
    try (apply IHr);
    try (apply IHl).
Qed.

(* M1b-7: pt'_of_fpt' — structural injection fpt' B -> pos_trie' B.
   [fpt_both] is dead under [fpt_depth'] so we treat it like [fpt_node].
   Guard: the recursion goes through tree'_map', which is opaque to the guard
   checker — we use the same nested-fix technique as fpt'_strong_ind
   (FullPosTrie.v:586). *)
Fixpoint pt'_of_fpt' {B : Type} (t : @FullPosTrie.fpt' B) : @pos_trie' B :=
  match t with
  | FullPosTrie.fpt_leaf a => pos_trie_leaf a
  | FullPosTrie.fpt_node m =>
      pos_trie_node
        (let fix IH_tree (m' : PTree.tree' (@FullPosTrie.fpt' B))
               : PTree.tree' (@pos_trie' B) :=
           match m' with
           | PTree.Node001 r     => PTree.Node001 (IH_tree r)
           | PTree.Node010 y     => PTree.Node010 (pt'_of_fpt' y)
           | PTree.Node011 y r   => PTree.Node011 (pt'_of_fpt' y) (IH_tree r)
           | PTree.Node100 l     => PTree.Node100 (IH_tree l)
           | PTree.Node101 l r   => PTree.Node101 (IH_tree l) (IH_tree r)
           | PTree.Node110 l y   => PTree.Node110 (IH_tree l) (pt'_of_fpt' y)
           | PTree.Node111 l y r => PTree.Node111 (IH_tree l) (pt'_of_fpt' y) (IH_tree r)
           end
         in IH_tree m)
  | FullPosTrie.fpt_both _ m =>
      pos_trie_node
        (let fix IH_tree (m' : PTree.tree' (@FullPosTrie.fpt' B))
               : PTree.tree' (@pos_trie' B) :=
           match m' with
           | PTree.Node001 r     => PTree.Node001 (IH_tree r)
           | PTree.Node010 y     => PTree.Node010 (pt'_of_fpt' y)
           | PTree.Node011 y r   => PTree.Node011 (pt'_of_fpt' y) (IH_tree r)
           | PTree.Node100 l     => PTree.Node100 (IH_tree l)
           | PTree.Node101 l r   => PTree.Node101 (IH_tree l) (IH_tree r)
           | PTree.Node110 l y   => PTree.Node110 (IH_tree l) (pt'_of_fpt' y)
           | PTree.Node111 l y r => PTree.Node111 (IH_tree l) (pt'_of_fpt' y) (IH_tree r)
           end
         in IH_tree m)
  end.

(* The inner [let fix IH_tree] in pt'_of_fpt' equals tree'_map' pt'_of_fpt'. *)
Lemma pt'_of_fpt'_fpt_node {B : Type} (m : PTree.tree' (@FullPosTrie.fpt' B)) :
  pt'_of_fpt' (FullPosTrie.fpt_node m) = pos_trie_node (tree'_map' pt'_of_fpt' m).
Proof.
  cbn [pt'_of_fpt'].
  f_equal.
  induction m as [r IHr | y | y r IHr | l IHl | l IHl r IHr | l IHl y | l IHl y r IHr];
    cbn; try (rewrite <- IHr); try (rewrite <- IHl); reflexivity.
Qed.

(* M1b-8: get-lemma — fpt_get' agrees with pt_get' through pt'_of_fpt'.
   Proved by fpt'_strong_ind; the fpt_both case is vacuous under fpt_depth'. *)
Lemma pt'_of_fpt'_get {B : Type} (t : @FullPosTrie.fpt' B) (n : nat) :
  fpt_depth' t n ->
  forall k, length k = n ->
    FullPosTrie.fpt_get' t k = pt_get' (pt'_of_fpt' t) k.
Proof.
  revert n.
  apply (FullPosTrie.fpt'_strong_ind B
    (fun t => forall n, fpt_depth' t n ->
                forall k, length k = n ->
                  FullPosTrie.fpt_get' t k = pt_get' (pt'_of_fpt' t) k)).
  - (* fpt_leaf a *)
    intros a n Hd k Hk.
    inversion Hd; subst. destruct k; [reflexivity | discriminate].
  - (* fpt_node m — use tree'_map'_get + pt'_of_fpt'_fpt_node *)
    intros m IHm n Hd k Hk.
    inversion Hd as [| m0 n0 Hchild Hm0 Hn0]; subst.
    destruct k as [| p k'].
    + discriminate.
    + rewrite pt'_of_fpt'_fpt_node.
      cbn [FullPosTrie.fpt_get' pt_get'].
      rewrite tree'_map'_get.
      destruct (PTree.get' p m) as [c |] eqn:Hgp; cbn [option_map].
      * apply (IHm p c Hgp n0 (Hchild p c Hgp) k').
        cbn [length] in Hn0. injection Hn0 as Hn0'. exact (eq_sym Hn0').
      * reflexivity.
  - (* fpt_both — vacuous under fpt_depth' (no fpt_both constructor) *)
    intros a m _IHm n Hd k _Hk.
    inversion Hd.
Qed.

(* ============================================================================
   INTERSECT INHERITANCE.

   [fpt_spaced_intersect] is a conversion wrapper:
     [fpt_spaced_intersect merge (tries, rest)
        = pt_to_fpt (compat_intersect merge (cvt tries, map cvt rest))]
   where [cvt p := (fpt_to_pt (fst p), snd p)].

   The e-graph saturation machinery consumes the intersection keys via the
   [Hsli] obligation (the last conjunct of [run1iter_rule_hyps], SemanticsSaturate.v):
   for every [sigma] enumerated by [map.keys (fpt_spaced_intersect (fun _ _ => tt) tries)],
   EVERY input trie's projected lookup must hit ([= Some tt]).

   [fpt_spaced_intersect_inputs_hit] establishes exactly this, by inheriting the
   already-proven [pt_spaced_intersect_correct] (3352-line proof) through the two
   get-preserving conversion lemmas [pt_to_fpt_get] / [fpt_to_pt_get].  The one
   structural fact it cannot derive locally -- that [compat_intersect]'s result is
   uniform-depth -- is taken as a hypothesis and discharged separately
   (pt_spaced_intersect result-depth preservation, ingredient (b)).
   ============================================================================ *)

Section Inherit.
  Context {B : Type} `{WithDefault B}.
  Context (merge : B -> B -> B).
  Context (merge_comm : forall a b, merge a b = merge b a).
  Context (merge_assoc : forall a b c, merge a (merge b c) = merge (merge a b) c).

  Local Notation cvt :=
    (fun p : @FullPosTrie.fpt B * list bool => (fpt_to_pt (fst p), snd p)).

  (* ---- helper 1: an all-true bool pattern projects a length-N key to itself. *)
  Lemma project_repeat_true (sigma : list positive) (N : nat) :
    length sigma = N ->
    map fst (filter snd (combine sigma (repeat true N))) = sigma.
  Proof.
    intros Hlen. subst N.
    induction sigma as [|p sigma' IH]; cbn [repeat combine filter map].
    - reflexivity.
    - cbn [length repeat combine filter map snd]. rewrite IH. reflexivity.
  Qed.

  (* ---- helper 2: a projected key's length = the number of selected (true) flags. *)
  Lemma project_length (sigma : list positive) (bs : list bool) :
    length sigma = length bs ->
    length (map fst (filter snd (combine sigma bs))) = length (filter id bs).
  Proof.
    intros Hlen. rewrite length_map. revert sigma Hlen.
    induction bs as [|b bs' IH]; intros sigma Hlen.
    - destruct sigma; cbn [combine filter]; reflexivity.
    - destruct sigma as [|p sigma']; cbn [length] in Hlen; [discriminate|].
      cbn [combine filter id]. destruct b; cbn [length filter snd].
      + rewrite IH; [reflexivity| congruence].
      + rewrite IH; [reflexivity| congruence].
  Qed.

  (* ---- helper 3: a successful [list_Mmap] means every element maps to [Some]. *)
  Lemma list_Mmap_in_some {T1 T2} (f : T1 -> option T2) (l : list T1) (r : list T2) :
    list_Mmap f l = Some r -> forall p, In p l -> exists v, f p = Some v.
  Proof.
    revert r. induction l as [|a l' IH]; intros r Hmm q Hin.
    - cbn in Hin. contradiction.
    - cbn [list_Mmap] in Hmm. unfold Mbind, Mret, option_monad in Hmm.
      destruct (f a) as [va|] eqn:Hfa; [|discriminate].
      destruct (list_Mmap f l') as [vs|] eqn:Hml; [|discriminate].
      destruct Hin as [Heq|Hin].
      + subst q. exists va. exact Hfa.
      + apply (IH vs eq_refl q Hin).
  Qed.

  (* [fpt_spaced_intersect_inputs_hit] is now proved later, inside BridgeSection,
     because its re-routing through the native join needs
     [fpt_spaced_intersect_native_keys_iff]. *)

End Inherit.

(* ============================================================================
   M2 — SIMULATION LEMMAS
   Prove that [fpt_spaced_intersect_native] agrees with [pt_spaced_intersect]
   through the structural injection [pt'_of_fpt'].

   Organization (all inside a single section for B, Hdef, merge):
   - helper: [fpt_both_pt'_node]    (pt'_of_fpt' on fpt_both)
   - EASY 1: [fpt_leaf_intersect_sim]    (Qed)
   - EASY 2: [fpt_proj_sim]              (Qed)
   - helper: [pr_map]                     (mapping fpt_partition_result -> partition_result)
   - EASY 3: [fpt_partition_tries_sim]   (Qed)
   - HARD A: [list_intersect_natural]    (Qed — TrieMap.list_intersect naturality)
   - EASY 4: [fpt_spaced_intersect''_sim] (Qed, uses list_intersect_natural)
   - helper: [list_Mmap_option_map_pt]    (Qed)
   - helper: [split_cvt'_comm]           (Qed)
   - EASY 5: [fpt_spaced_intersect_native_sim] (Qed)
   ============================================================================ *)

Section FptSim.
  Context {B : Type} `{Hdef : WithDefault B}.
  Context (merge : B -> B -> B).

  (* ---- Helper: pt'_of_fpt' on fpt_both reduces like fpt_node (drops the value). ---- *)
  Lemma fpt_both_pt'_node (a : B) (m : PTree.tree' (@FullPosTrie.fpt' B)) :
    pt'_of_fpt' (FullPosTrie.fpt_both a m) = pos_trie_node (tree'_map' pt'_of_fpt' m).
  Proof.
    cbn [pt'_of_fpt']. f_equal.
    induction m as [r IHr | y | y r IHr | l IHl | l IHl r IHr | l IHl y | l IHl y r IHr];
      cbn; try (rewrite <- IHr); try (rewrite <- IHl); reflexivity.
  Qed.

  (* ---- EASY 1: leaf_intersect simulation. ---- *)
  Lemma fpt_leaf_intersect_sim :
    forall (ptl : list (@FullPosTrie.fpt' B)) (a : B),
    fpt_leaf_intersect merge a ptl = leaf_intersect merge a (map pt'_of_fpt' ptl).
  Proof.
    induction ptl as [| t ptl' IH]; intros a.
    - reflexivity.
    - destruct t as [a' | m | a' m];
        cbn [fpt_leaf_intersect map pt'_of_fpt' leaf_intersect]; apply IH.
  Qed.

  (* ---- EASY 2: proj_node_map simulation. ---- *)
  Lemma fpt_proj_sim :
    forall (t : @FullPosTrie.fpt' B),
    tree'_map' pt'_of_fpt' (fpt_proj_node_unchecked t)
    = proj_node_map_unchecked (pt'_of_fpt' t).
  Proof.
    intros [a | m | a m].
    - cbn [fpt_proj_node_unchecked pt'_of_fpt' proj_node_map_unchecked tree'_map'].
      reflexivity.
    - rewrite pt'_of_fpt'_fpt_node.
      cbn [fpt_proj_node_unchecked proj_node_map_unchecked]. reflexivity.
    - rewrite fpt_both_pt'_node.
      cbn [fpt_proj_node_unchecked proj_node_map_unchecked]. reflexivity.
  Qed.

  (* ---- Helper: mapping fpt_partition_result to partition_result. ---- *)
  Definition pr_map (pr : @fpt_partition_result B) : @partition_result B :=
    match pr with
    | fpt_just_false_part ci0 pt0 cil ptl =>
        just_false_part ci0 (pt'_of_fpt' pt0) cil (map pt'_of_fpt' ptl)
    | fpt_have_true_part f_cil f_ptl t_ci0 t_pt0 t_cil t_ptl =>
        have_true_part f_cil (map pt'_of_fpt' f_ptl) t_ci0 (pt'_of_fpt' t_pt0)
                       t_cil (map pt'_of_fpt' t_ptl)
    end.

  (* ---- EASY 3: partition_tries simulation. ---- *)
  Lemma fpt_partition_tries_sim :
    forall (cil : list (list bool)) (ptl : list (@FullPosTrie.fpt' B))
           (acc : @fpt_partition_result B),
    pr_map (fpt_partition_tries cil ptl acc)
    = partition_tries cil (map pt'_of_fpt' ptl) (pr_map acc).
  Proof.
    induction cil as [| ci cil' IH]; intros ptl acc.
    - destruct ptl; reflexivity.
    - destruct ptl as [| pt ptl']; [destruct ci as [|[|] ?]; reflexivity |].
      destruct ci as [| b ci_tl]; [reflexivity|].
      destruct b; destruct acc;
        cbn [fpt_partition_tries partition_tries map pr_map]; apply IH.
  Qed.

  (* ---- Helper B: both-free predicate + element preservation for list_intersect'. ---- *)

  (* Both-free fpt': no fpt_both constructors appear. *)
  Inductive fpt_both_free' : @FullPosTrie.fpt' B -> Prop :=
  | fpt_bf_leaf (a : B) : fpt_both_free' (FullPosTrie.fpt_leaf a)
  | fpt_bf_node (m : PTree.tree' (@FullPosTrie.fpt' B)) :
      (forall p c, PTree.get' p m = Some c -> fpt_both_free' c) ->
      fpt_both_free' (FullPosTrie.fpt_node m).

  (* All elements of a PTree.tree' fpt' are both-free. *)
  Local Definition bf_tree' (m : PTree.tree' (@FullPosTrie.fpt' B)) : Prop :=
    forall p c, PTree.get' p m = Some c -> fpt_both_free' c.

  (* Helper: bf_tree' of a result built by tree'_of_tuple_k.
     If l_opt/r_opt hold bf subtrees and c_opt holds a bf element,
     then any element of the result tree is bf. *)
  Local Lemma bf_of_result
      (l_opt : option (PTree.tree' (@FullPosTrie.fpt' B)))
      (c_opt : option (@FullPosTrie.fpt' B))
      (r_opt : option (PTree.tree' (@FullPosTrie.fpt' B)))
      (m : PTree.tree' (@FullPosTrie.fpt' B)) :
    TrieMap.tree'_of_tuple_k (l_opt, c_opt, r_opt) Some None = Some m ->
    (forall vl, l_opt = Some vl -> bf_tree' vl) ->
    (forall vc, c_opt = Some vc -> fpt_both_free' vc) ->
    (forall vr, r_opt = Some vr -> bf_tree' vr) ->
    bf_tree' m.
  Proof.
    destruct l_opt as [vl|], c_opt as [vc|], r_opt as [vr|];
      cbn [TrieMap.tree'_of_tuple_k]; try discriminate;
      intros Hm Hl Hc Hr; injection Hm as <-;
      unfold bf_tree'; intros p ct Hpct; destruct p; cbn [PTree.get'] in Hpct;
      try discriminate Hpct.
    all: try (injection Hpct as <-; exact (Hc vc eq_refl)).
    all: try (exact (Hl vl eq_refl p ct Hpct)).
    all: try (exact (Hr vr eq_refl p ct Hpct)).
  Qed.

  (* Element preservation for list_intersect'_pre_cbv. *)
  Local Lemma lin_list_intersect'_bf
      (ef : bool -> @FullPosTrie.fpt' B -> list (@FullPosTrie.fpt' B) -> option (@FullPosTrie.fpt' B))
      (Hef : forall b x xs r, ef b x xs = Some r -> fpt_both_free' r) :
    forall (is_rev : bool) (hd : PTree.tree' (@FullPosTrie.fpt' B))
           (args : list (PTree.tree' (@FullPosTrie.fpt' B))),
    forall m, TrieMap.list_intersect'_pre_cbv ef hd is_rev args = Some m ->
    bf_tree' m.
  Proof.
    intros is_rev hd. revert is_rev.
    induction hd as [r IHr | y | y r IHr | l IHl | l IHl r IHr | l IHl y | l IHl y r IHr];
      intros is_rev args m Hm p c Hpc.
    all: cbn [TrieMap.list_intersect'_pre_cbv TrieMap.list_intersect'F
              TrieMap.tree'_tuple_k TrieMap.tree'_tuple fst snd] in Hm.
    all: rewrite TrieMap.hfin3_to_tuple_un_k in Hm.
    (* Node001 r *)
    - destruct (TrieMap.hfin3_to_tuple (TrieMap.gather_tries args
         (@TrieMap.initial_acc (PTree.tree' _) _ (PTree.tree' _) (None, None, Some r))))
         as [[acc_l acc_c] acc_r] eqn:Hacc.
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2
           Mbind Mret option_monad] in Hm.
      destruct acc_r as [rs|]; [|discriminate Hm].
      destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr;
        [|discriminate Hm]. injection Hm as <-.
      destruct p; cbn [PTree.get'] in Hpc.
      + exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
      + discriminate Hpc.
      + discriminate Hpc.
    (* Node010 y *)
    - destruct (TrieMap.hfin3_to_tuple (TrieMap.gather_tries args
         (@TrieMap.initial_acc (PTree.tree' _) _ (PTree.tree' _) (None, Some y, None))))
         as [[acc_l acc_c] acc_r] eqn:Hacc.
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2
           Mbind Mret option_monad] in Hm.
      destruct acc_c as [cs|]; [|discriminate Hm].
      destruct (ef is_rev y cs) as [vc|] eqn:Hvc; [|discriminate Hm].
      injection Hm as <-.
      destruct p; cbn [PTree.get'] in Hpc.
      + discriminate Hpc.
      + discriminate Hpc.
      + injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
    (* Node011 y r *)
    - destruct (TrieMap.hfin3_to_tuple (TrieMap.gather_tries args
         (@TrieMap.initial_acc (PTree.tree' _) _ (PTree.tree' _) (None, Some y, Some r))))
         as [[acc_l acc_c] acc_r] eqn:Hacc.
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2
           Mbind Mret option_monad] in Hm.
      destruct acc_c as [cs|]; destruct acc_r as [rs|].
      + (* acc_c = Some cs, acc_r = Some rs *)
        destruct (ef is_rev y cs) as [vc|] eqn:Hvc;
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr.
        * (* vc = Some, vr = Some: result = Node011 vc vr *)
          injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * (* vc = Some, vr = None: result = Node010 vc *)
          injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * (* vc = None, vr = Some: result = Node001 vr *)
          injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- discriminate Hpc.
        * (* vc = None, vr = None: result = None *)
          discriminate Hm.
      + (* acc_c = Some cs, acc_r = None: center only *)
        destruct (ef is_rev y cs) as [vc|] eqn:Hvc; [|discriminate Hm].
        injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * discriminate Hpc.
        * discriminate Hpc.
        * injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
      + (* acc_c = None, acc_r = Some rs: right only *)
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr;
          [|discriminate Hm]. injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
        * discriminate Hpc.
        * discriminate Hpc.
      + (* acc_c = None, acc_r = None: result = None *)
        discriminate Hm.
    (* Node100 l *)
    - destruct (TrieMap.hfin3_to_tuple (TrieMap.gather_tries args
         (@TrieMap.initial_acc (PTree.tree' _) _ (PTree.tree' _) (Some l, None, None))))
         as [[acc_l acc_c] acc_r] eqn:Hacc.
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2
           Mbind Mret option_monad] in Hm.
      destruct acc_l as [ls|]; [|discriminate Hm].
      destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
        [|discriminate Hm]. injection Hm as <-.
      destruct p; cbn [PTree.get'] in Hpc.
      + discriminate Hpc.
      + exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
      + discriminate Hpc.
    (* Node101 l r *)
    - destruct (TrieMap.hfin3_to_tuple (TrieMap.gather_tries args
         (@TrieMap.initial_acc (PTree.tree' _) _ (PTree.tree' _) (Some l, None, Some r))))
         as [[acc_l acc_c] acc_r] eqn:Hacc.
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2
           Mbind Mret option_monad] in Hm.
      destruct acc_l as [ls|]; destruct acc_r as [rs|].
      + (* ls=Some, rs=Some *)
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr.
        * injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- discriminate Hpc.
        * discriminate Hm.
      + destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
          [|discriminate Hm]. injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * discriminate Hpc.
        * exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
        * discriminate Hpc.
      + destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr;
          [|discriminate Hm]. injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
        * discriminate Hpc.
        * discriminate Hpc.
      + discriminate Hm.
    (* Node110 l y *)
    - destruct (TrieMap.hfin3_to_tuple (TrieMap.gather_tries args
         (@TrieMap.initial_acc (PTree.tree' _) _ (PTree.tree' _) (Some l, Some y, None))))
         as [[acc_l acc_c] acc_r] eqn:Hacc.
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2
           Mbind Mret option_monad] in Hm.
      destruct acc_l as [ls|]; destruct acc_c as [cs|].
      + (* ls=Some, cs=Some *)
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
        destruct (ef is_rev y cs) as [vc|] eqn:Hvc.
        * injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-.
          destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * discriminate Hm.
      + destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
          [|discriminate Hm]. injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * discriminate Hpc.
        * exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
        * discriminate Hpc.
      + destruct (ef is_rev y cs) as [vc|] eqn:Hvc; [|discriminate Hm].
        injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * discriminate Hpc.
        * discriminate Hpc.
        * injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
      + discriminate Hm.
    (* Node111 l y r *)
    - destruct (TrieMap.hfin3_to_tuple (TrieMap.gather_tries args
         (@TrieMap.initial_acc (PTree.tree' _) _ (PTree.tree' _) (Some l, Some y, Some r))))
         as [[acc_l acc_c] acc_r] eqn:Hacc.
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2
           Mbind Mret option_monad] in Hm.
      destruct acc_l as [ls|]; destruct acc_c as [cs|]; destruct acc_r as [rs|].
      + (* ls=Some, cs=Some, rs=Some: 8 subcases *)
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
        destruct (ef is_rev y cs) as [vc|] eqn:Hvc;
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- discriminate Hpc.
        * discriminate Hm.
      + (* ls=Some, cs=Some, rs=None: 4 subcases *)
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
        destruct (ef is_rev y cs) as [vc|] eqn:Hvc.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * discriminate Hm.
      + (* ls=Some, cs=None, rs=Some: 4 subcases *)
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
          -- discriminate Hpc.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- discriminate Hpc.
        * discriminate Hm.
      + (* ls=Some, cs=None, rs=None *)
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|] eqn:Hvl;
          [|discriminate Hm]. injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * discriminate Hpc.
        * exact (IHl (negb is_rev) ls vl Hvl p c Hpc).
        * discriminate Hpc.
      + (* ls=None, cs=Some, rs=Some: 4 subcases *)
        destruct (ef is_rev y cs) as [vc|] eqn:Hvc;
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr.
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- discriminate Hpc.
          -- discriminate Hpc.
          -- injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
        * injection Hm as <-. destruct p; cbn [PTree.get'] in Hpc.
          -- exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
          -- discriminate Hpc.
          -- discriminate Hpc.
        * discriminate Hm.
      + (* ls=None, cs=Some, rs=None *)
        destruct (ef is_rev y cs) as [vc|] eqn:Hvc; [|discriminate Hm].
        injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * discriminate Hpc.
        * discriminate Hpc.
        * injection Hpc as <-. exact (Hef is_rev y cs vc Hvc).
      + (* ls=None, cs=None, rs=Some *)
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|] eqn:Hvr;
          [|discriminate Hm]. injection Hm as <-.
        destruct p; cbn [PTree.get'] in Hpc.
        * exact (IHr (negb is_rev) rs vr Hvr p c Hpc).
        * discriminate Hpc.
        * discriminate Hpc.
      + (* ls=None, cs=None, rs=None *)
        discriminate Hm.
  Qed.

  (* Wrapper: list_intersect (the public function) preserves both-free. *)
  Lemma list_intersect_bf
      (ef : bool -> @FullPosTrie.fpt' B -> list (@FullPosTrie.fpt' B) -> option (@FullPosTrie.fpt' B))
      (Hef : forall b x xs r, ef b x xs = Some r -> fpt_both_free' r)
      (hd : PTree.tree' (@FullPosTrie.fpt' B))
      (args : list (PTree.tree' (@FullPosTrie.fpt' B)))
      (m : PTree.tree' (@FullPosTrie.fpt' B)) :
    TrieMap.list_intersect ef hd args = Some m ->
    bf_tree' m.
  Proof.
    intro Hm.
    change (TrieMap.list_intersect'_pre_cbv ef hd false args = Some m) in Hm.
    exact (lin_list_intersect'_bf ef Hef false hd args Hm).
  Qed.

  (* ---- HARD A: list_intersect naturality. ---- *)
  (* Helper: option_all over Datatypes.option_map'd list *)
  Local Lemma lin_option_all_Dmap {A1 A2 : Type} (f : A1 -> A2) (l : list (Datatypes.option A1)) :
    option_all (map (Datatypes.option_map f) l) = Datatypes.option_map (map f) (option_all l).
  Proof.
    induction l as [| [x|] rest IH]; cbn [map option_all Datatypes.option_map]; try reflexivity.
    rewrite IH. destruct (option_all rest); reflexivity.
  Qed.

  (* Helper: split3 of tree'_tuples commutes with tree'_map' *)
  Local Lemma lin_split3_map_tree'_tuple {Bf Bp : Type} (g : Bf -> Bp) (tl : list (PTree.tree' Bf)) :
    split3 (map tree'_tuple (map (tree'_map' g) tl)) =
    (map (Datatypes.option_map (tree'_map' g)) (fst (fst (split3 (map tree'_tuple tl)))),
     map (Datatypes.option_map g) (snd (fst (split3 (map tree'_tuple tl)))),
     map (Datatypes.option_map (tree'_map' g)) (snd (split3 (map tree'_tuple tl)))).
  Proof.
    rewrite !map_map. unfold split3, pair_map, id. rewrite !split_map; cbn [fst snd].
    f_equal; [f_equal|]; rewrite !map_map; apply map_ext; intro t;
    destruct t; cbn [tree'_tuple tree'_map' fst snd]; reflexivity.
  Qed.

  (* Helper: gather_tries_simple commutes with tree'_map' *)
  Local Lemma lin_gather_tries_simple_natural {Bf Bp : Type} (g : Bf -> Bp) (tl : list (PTree.tree' Bf))
      (al : Datatypes.option (list (PTree.tree' Bf))) (ac : Datatypes.option (list Bf)) (ar : Datatypes.option (list (PTree.tree' Bf))) :
    gather_tries_simple (map (tree'_map' g) tl)
      (hfin3_of_tuple (Datatypes.option_map (map (tree'_map' g)) al, Datatypes.option_map (map g) ac, Datatypes.option_map (map (tree'_map' g)) ar))
    = (Datatypes.option_map (map (tree'_map' g)) (fst (fst (gather_tries_simple tl (hfin3_of_tuple (al, ac, ar))))),
       Datatypes.option_map (map g) (snd (fst (gather_tries_simple tl (hfin3_of_tuple (al, ac, ar))))),
       Datatypes.option_map (map (tree'_map' g)) (snd (gather_tries_simple tl (hfin3_of_tuple (al, ac, ar))))).
  Proof.
    unfold gather_tries_simple. rewrite !hfin3_tuple_inverse'.
    rewrite (lin_split3_map_tree'_tuple g tl). unfold pair_map, pair_map2, id. cbn [fst snd].
    rewrite <- !map_rev, !lin_option_all_Dmap.
    unfold option_map2, Mbind, Mret, option_monad.
    destruct (option_all (rev (fst (fst (split3 (map tree'_tuple tl)))))) as [ls1|];
    destruct (option_all (rev (snd (fst (split3 (map tree'_tuple tl)))))) as [ls2|];
    destruct (option_all (rev (snd (split3 (map tree'_tuple tl))))) as [ls3|];
    destruct al as [al_v|]; destruct ac as [ac_v|]; destruct ar as [ar_v|];
    cbn [Datatypes.option_map]; try (rewrite <- !map_app; reflexivity); reflexivity.
  Qed.

  (* Helper: gather_tries naturality — general form *)
  Local Lemma lin_gather_tries_natural_general {Bf Bp : Type} (g : Bf -> Bp)
      (tl : list (PTree.tree' Bf))
      (acc_Bf : hfin3 (list (PTree.tree' Bf)) (list Bf) (list (PTree.tree' Bf)))
      (acc_Bp : hfin3 (list (PTree.tree' Bp)) (list Bp) (list (PTree.tree' Bp)))
      (Hacc : hfin3_to_tuple acc_Bp =
              (Datatypes.option_map (map (tree'_map' g)) (fst (fst (hfin3_to_tuple acc_Bf))),
               Datatypes.option_map (map g) (snd (fst (hfin3_to_tuple acc_Bf))),
               Datatypes.option_map (map (tree'_map' g)) (snd (hfin3_to_tuple acc_Bf)))) :
    hfin3_to_tuple (gather_tries (map (tree'_map' g) tl) acc_Bp) =
    (Datatypes.option_map (map (tree'_map' g)) (fst (fst (hfin3_to_tuple (gather_tries tl acc_Bf)))),
     Datatypes.option_map (map g) (snd (fst (hfin3_to_tuple (gather_tries tl acc_Bf)))),
     Datatypes.option_map (map (tree'_map' g)) (snd (hfin3_to_tuple (gather_tries tl acc_Bf)))).
  Proof.
    rewrite !gather_no_short.
    revert acc_Bf acc_Bp Hacc.
    induction tl as [| t tl' IH]; intros acc_Bf acc_Bp Hacc.
    - cbn [map gather_tries_no_short gather_tries'F]. exact Hacc.
    - cbn [map gather_tries_no_short gather_tries'F].
      destruct t as [r1 | y1 | y1 r1 | l1 | l1 r1 | l1 y1 | l1 y1 r1].
      all: rewrite !tree'_tuple_un_k, !hfin3_to_tuple_un_k.
      all: cbn [tree'_tuple tree'_map' fst snd].
      all: rewrite Hacc.
      all: destruct (hfin3_to_tuple acc_Bf) as [[al ac] ar].
      all: cbn [fst snd pair_map2 Datatypes.option_map].
      all: apply IH.
      all: cbn [hfin3_to_tuple fst snd Datatypes.option_map map hfin3_of_tuple].
      all: rewrite hfin3_tuple_inverse'.
      all: destruct al as [al_v|], ac as [ac_v|], ar as [ar_v|];
           cbn [Datatypes.option_map map mcons hfin3_to_tuple hfin3_of_tuple];
           try reflexivity.
  Qed.

  (* Helper: gather_tries naturality for initial_acc values *)
  Local Lemma lin_gather_tries_natural_init {Bf Bp : Type} (g : Bf -> Bp)
      (tl : list (PTree.tree' Bf))
      (pl_f : Datatypes.option (PTree.tree' Bf)) (pc_f : Datatypes.option Bf) (pr_f : Datatypes.option (PTree.tree' Bf))
      (pl_g : Datatypes.option (PTree.tree' Bp)) (pc_g : Datatypes.option Bp) (pr_g : Datatypes.option (PTree.tree' Bp))
      (Hpl : pl_g = Datatypes.option_map (tree'_map' g) pl_f)
      (Hpc : pc_g = Datatypes.option_map g pc_f)
      (Hpr : pr_g = Datatypes.option_map (tree'_map' g) pr_f) :
    hfin3_to_tuple (gather_tries (map (tree'_map' g) tl)
                      (@initial_acc (PTree.tree' Bp) Bp (PTree.tree' Bp) (pl_g, pc_g, pr_g)))
    = (Datatypes.option_map (map (tree'_map' g))
           (fst (fst (hfin3_to_tuple (gather_tries tl (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (pl_f, pc_f, pr_f)))))),
       Datatypes.option_map (map g)
           (snd (fst (hfin3_to_tuple (gather_tries tl (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (pl_f, pc_f, pr_f)))))),
       Datatypes.option_map (map (tree'_map' g))
           (snd (hfin3_to_tuple (gather_tries tl (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (pl_f, pc_f, pr_f)))))).
  Proof.
    apply lin_gather_tries_natural_general.
    subst.
    unfold initial_acc, pair_map, Mbind, Mret, option_monad.
    destruct pl_f, pc_f, pr_f;
      cbn [hfin3_to_tuple hfin3_of_tuple fst snd Datatypes.option_map];
      reflexivity.
  Qed.

  (* Helper: generalized list_intersect' naturality (with is_rev parameter) *)
  Local Lemma lin_list_intersect'_natural {Bf Bp : Type} (g : Bf -> Bp)
      (ef : bool -> Bf -> list Bf -> Datatypes.option Bf)
      (eg : bool -> Bp -> list Bp -> Datatypes.option Bp)
      (Helts : forall b x xs, Datatypes.option_map g (ef b x xs) = eg b (g x) (map g xs)) :
    forall (is_rev : bool) (hd : PTree.tree' Bf) (args : list (PTree.tree' Bf)),
    Datatypes.option_map (tree'_map' g) (TrieMap.list_intersect'_pre_cbv ef hd is_rev args)
    = TrieMap.list_intersect'_pre_cbv eg (tree'_map' g hd) is_rev (map (tree'_map' g) args).
  Proof.
    intros is_rev hd. revert is_rev.
    induction hd as [r IHr | y | y r IHr | l IHl | l IHl r IHr | l IHl y | l IHl y r IHr];
      intros is_rev args.
    all: cbn [tree'_map' TrieMap.list_intersect'_pre_cbv TrieMap.list_intersect'F
              TrieMap.tree'_tuple_k TrieMap.tree'_tuple fst snd].
    all: rewrite !TrieMap.hfin3_to_tuple_un_k.
    (* Node001 r *)
    - pose proof (@lin_gather_tries_natural_init Bf Bp g args None None (Some r)
          None None (Some (tree'_map' g r)) eq_refl eq_refl eq_refl) as Hgt.
      rewrite Hgt; clear Hgt.
      destruct (hfin3_to_tuple (gather_tries args (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (None, None, Some r)))) as [[acc_l acc_c] acc_r].
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2 Mbind Mret option_monad Datatypes.option_map].
      destruct acc_r as [rs|]; cbn [Datatypes.option_map]; try reflexivity.
      specialize (IHr (negb is_rev) rs).
      destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [v|];
        cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHr); reflexivity.
    (* Node010 y *)
    - pose proof (@lin_gather_tries_natural_init Bf Bp g args None (Some y) None
          None (Some (g y)) None eq_refl eq_refl eq_refl) as Hgt.
      rewrite Hgt; clear Hgt.
      destruct (hfin3_to_tuple (gather_tries args (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (None, Some y, None)))) as [[acc_l acc_c] acc_r].
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2 Mbind Mret option_monad Datatypes.option_map].
      destruct acc_c as [cs|]; cbn [Datatypes.option_map]; try reflexivity.
      specialize (Helts is_rev y cs).
      destruct (ef is_rev y cs) as [v|];
        cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- Helts); reflexivity.
    (* Node011 y r *)
    - pose proof (@lin_gather_tries_natural_init Bf Bp g args None (Some y) (Some r)
          None (Some (g y)) (Some (tree'_map' g r)) eq_refl eq_refl eq_refl) as Hgt.
      rewrite Hgt; clear Hgt.
      destruct (hfin3_to_tuple (gather_tries args (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (None, Some y, Some r)))) as [[acc_l acc_c] acc_r].
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2 Mbind Mret option_monad Datatypes.option_map].
      destruct acc_c as [cs|]; destruct acc_r as [rs|]; cbn [Datatypes.option_map].
      + specialize (IHr (negb is_rev) rs). specialize (Helts is_rev y cs).
        destruct (ef is_rev y cs) as [vc|];
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *;
          try (rewrite <- IHr); try (rewrite <- Helts); reflexivity.
      + specialize (Helts is_rev y cs).
        destruct (ef is_rev y cs) as [vc|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- Helts); reflexivity.
      + specialize (IHr (negb is_rev) rs).
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHr); reflexivity.
      + reflexivity.
    (* Node100 l *)
    - pose proof (@lin_gather_tries_natural_init Bf Bp g args (Some l) None None
          (Some (tree'_map' g l)) None None eq_refl eq_refl eq_refl) as Hgt.
      rewrite Hgt; clear Hgt.
      destruct (hfin3_to_tuple (gather_tries args (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (Some l, None, None)))) as [[acc_l acc_c] acc_r].
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2 Mbind Mret option_monad Datatypes.option_map].
      destruct acc_l as [ls|]; cbn [Datatypes.option_map]; try reflexivity.
      specialize (IHl (negb is_rev) ls).
      destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [v|];
        cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHl); reflexivity.
    (* Node101 l r *)
    - pose proof (@lin_gather_tries_natural_init Bf Bp g args (Some l) None (Some r)
          (Some (tree'_map' g l)) None (Some (tree'_map' g r)) eq_refl eq_refl eq_refl) as Hgt.
      rewrite Hgt; clear Hgt.
      destruct (hfin3_to_tuple (gather_tries args (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (Some l, None, Some r)))) as [[acc_l acc_c] acc_r].
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2 Mbind Mret option_monad Datatypes.option_map].
      destruct acc_l as [ls|]; destruct acc_r as [rs|]; cbn [Datatypes.option_map].
      + specialize (IHl (negb is_rev) ls). specialize (IHr (negb is_rev) rs).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *;
          try (rewrite <- IHl); try (rewrite <- IHr); reflexivity.
      + specialize (IHl (negb is_rev) ls).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHl); reflexivity.
      + specialize (IHr (negb is_rev) rs).
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHr); reflexivity.
      + reflexivity.
    (* Node110 l y *)
    - pose proof (@lin_gather_tries_natural_init Bf Bp g args (Some l) (Some y) None
          (Some (tree'_map' g l)) (Some (g y)) None eq_refl eq_refl eq_refl) as Hgt.
      rewrite Hgt; clear Hgt.
      destruct (hfin3_to_tuple (gather_tries args (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (Some l, Some y, None)))) as [[acc_l acc_c] acc_r].
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2 Mbind Mret option_monad Datatypes.option_map].
      destruct acc_l as [ls|]; destruct acc_c as [cs|]; cbn [Datatypes.option_map].
      + specialize (IHl (negb is_rev) ls). specialize (Helts is_rev y cs).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
        destruct (ef is_rev y cs) as [vc|];
          cbn [Datatypes.option_map tree'_map'] in * |- *;
          try (rewrite <- IHl); try (rewrite <- Helts); reflexivity.
      + specialize (IHl (negb is_rev) ls).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHl); reflexivity.
      + specialize (Helts is_rev y cs).
        destruct (ef is_rev y cs) as [vc|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- Helts); reflexivity.
      + reflexivity.
    (* Node111 l y r *)
    - pose proof (@lin_gather_tries_natural_init Bf Bp g args (Some l) (Some y) (Some r)
          (Some (tree'_map' g l)) (Some (g y)) (Some (tree'_map' g r)) eq_refl eq_refl eq_refl) as Hgt.
      rewrite Hgt; clear Hgt.
      destruct (hfin3_to_tuple (gather_tries args (@initial_acc (PTree.tree' Bf) Bf (PTree.tree' Bf) (Some l, Some y, Some r)))) as [[acc_l acc_c] acc_r].
      cbn [fst snd TrieMap.tree'_of_tuple_k TrieMap.pair_map2 Mbind Mret option_monad Datatypes.option_map].
      destruct acc_l as [ls|]; destruct acc_c as [cs|]; destruct acc_r as [rs|]; cbn [Datatypes.option_map].
      + specialize (IHl (negb is_rev) ls). specialize (IHr (negb is_rev) rs). specialize (Helts is_rev y cs).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
        destruct (ef is_rev y cs) as [vc|];
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *;
          try (rewrite <- IHl); try (rewrite <- Helts); try (rewrite <- IHr); reflexivity.
      + specialize (IHl (negb is_rev) ls). specialize (Helts is_rev y cs).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
        destruct (ef is_rev y cs) as [vc|];
          cbn [Datatypes.option_map tree'_map'] in * |- *;
          try (rewrite <- IHl); try (rewrite <- Helts); reflexivity.
      + specialize (IHl (negb is_rev) ls). specialize (IHr (negb is_rev) rs).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *;
          try (rewrite <- IHl); try (rewrite <- IHr); reflexivity.
      + specialize (IHl (negb is_rev) ls).
        destruct (TrieMap.list_intersect'_pre_cbv ef l (negb is_rev) ls) as [vl|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHl); reflexivity.
      + specialize (Helts is_rev y cs). specialize (IHr (negb is_rev) rs).
        destruct (ef is_rev y cs) as [vc|];
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *;
          try (rewrite <- Helts); try (rewrite <- IHr); reflexivity.
      + specialize (Helts is_rev y cs).
        destruct (ef is_rev y cs) as [vc|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- Helts); reflexivity.
      + specialize (IHr (negb is_rev) rs).
        destruct (TrieMap.list_intersect'_pre_cbv ef r (negb is_rev) rs) as [vr|];
          cbn [Datatypes.option_map tree'_map'] in * |- *; try (rewrite <- IHr); reflexivity.
      + reflexivity.
  Qed.

  Lemma list_intersect_natural :
    forall {Bf Bp : Type} (g : Bf -> Bp)
           (ef : bool -> Bf -> list Bf -> option Bf)
           (eg : bool -> Bp -> list Bp -> option Bp),
    (forall b x xs, option_map g (ef b x xs) = eg b (g x) (map g xs)) ->
    forall (hd : PTree.tree' Bf) (args : list (PTree.tree' Bf)),
    option_map (tree'_map' g) (TrieMap.list_intersect ef hd args)
    = TrieMap.list_intersect eg (tree'_map' g hd) (map (tree'_map' g) args).
  Proof.
    intros Bf Bp g ef eg Helts hd args.
    unfold TrieMap.list_intersect, TrieMap.list_intersect'.
    fold (TrieMap.list_intersect'_pre_cbv ef) (TrieMap.list_intersect'_pre_cbv eg).
    apply (lin_list_intersect'_natural g ef eg Helts false).
  Qed.

  (* ---- EASY 4: the main fixpoint simulation. ---- *)
  Lemma fpt_spaced_intersect''_sim :
    forall (fuel : nat) (cil : list (list bool)) (ptl : list (@FullPosTrie.fpt' B))
           (ci0 : list bool) (cil' : list (list bool))
           (pt0 : @FullPosTrie.fpt' B) (ptl' : list (@FullPosTrie.fpt' B)),
    option_map pt'_of_fpt'
      (fpt_spaced_intersect'' merge fuel cil ptl ci0 cil' pt0 ptl')
    = pt_spaced_intersect' merge fuel cil (map pt'_of_fpt' ptl) ci0 cil'
                           (pt'_of_fpt' pt0) (map pt'_of_fpt' ptl').
  Proof.
    induction fuel as [| fuel' IH]; intros cil ptl ci0 cil' pt0 ptl'.
    - reflexivity.
    - destruct ci0 as [| ci0_hd ci0_tl].
      + (* ci0 = [] : leaf/node cases *)
        destruct pt0 as [a | m | a m].
        * cbn [fpt_spaced_intersect'' pt_spaced_intersect' option_map pt'_of_fpt'].
          f_equal.
          rewrite fpt_leaf_intersect_sim. rewrite fpt_leaf_intersect_sim. reflexivity.
        * cbn [fpt_spaced_intersect'' pt_spaced_intersect'].
          rewrite pt'_of_fpt'_fpt_node. reflexivity.
        * cbn [fpt_spaced_intersect'' pt_spaced_intersect'].
          rewrite fpt_both_pt'_node. reflexivity.
      + (* ci0 = ci0_hd :: ci0_tl : recursive step *)
        cbn [fpt_spaced_intersect'' pt_spaced_intersect'].
        (* Show the combined partition map commutes *)
        assert (Hcombined :
          pr_map (fpt_partition_tries cil' ptl'
                    (fpt_partition_tries cil ptl
                       (if ci0_hd then fpt_have_true_part [] [] ci0_tl pt0 [] []
                        else fpt_just_false_part ci0_tl pt0 [] [])))
          = partition_tries cil' (map pt'_of_fpt' ptl')
              (partition_tries cil (map pt'_of_fpt' ptl)
                 (if ci0_hd then have_true_part [] [] ci0_tl (pt'_of_fpt' pt0) [] []
                  else just_false_part ci0_tl (pt'_of_fpt' pt0) [] []))).
        { rewrite fpt_partition_tries_sim.
          rewrite fpt_partition_tries_sim.
          destruct ci0_hd; reflexivity. }
        destruct (fpt_partition_tries cil' ptl'
                    (fpt_partition_tries cil ptl
                       (if ci0_hd then fpt_have_true_part [] [] ci0_tl pt0 [] []
                        else fpt_just_false_part ci0_tl pt0 [] [])))
          as [ci0' pt0' oc ot | oc ot t_ci0 t_pt0 t_cil t_ptl].
        * (* just_false_part branch *)
          cbn [pr_map] in Hcombined.
          rewrite <- Hcombined. cbn [option_map]. apply IH.
        * (* have_true_part branch *)
          cbn [pr_map] in Hcombined.
          rewrite <- Hcombined. cbn [option_map].
          (* option_map pt'_of_fpt' (option_map fpt_node X)
             = option_map pos_trie_node (option_map (tree'_map' pt'_of_fpt') X) *)
          rewrite TrieMap.option_map_option_map.
          rewrite (TrieMap.option_map_ext
            (fun x => pt'_of_fpt' (FullPosTrie.fpt_node x))
            (fun x => pos_trie_node (tree'_map' pt'_of_fpt' x))
            _
            (fun x _ => pt'_of_fpt'_fpt_node x)).
          rewrite <- TrieMap.option_map_option_map.
          f_equal.
          erewrite (list_intersect_natural pt'_of_fpt'
            (fun is_forward (x : @FullPosTrie.fpt' B) (xs : list (@FullPosTrie.fpt' B)) =>
               fpt_spaced_intersect'' merge fuel' oc ot t_ci0
                 (if is_forward then t_cil else rev t_cil) x xs)
            (fun is_forward (x : @pos_trie' B) (xs : list (@pos_trie' B)) =>
               pt_spaced_intersect' merge fuel' oc (map pt'_of_fpt' ot) t_ci0
                 (if is_forward then t_cil else rev t_cil) x xs)).
          2: { intros b x xs. cbn beta. apply IH. }
          f_equal.
          { apply fpt_proj_sim. }
          { rewrite !map_map. apply map_ext. intros x. apply fpt_proj_sim. }
  Qed.

  (* ---- Helper B2: fpt_spaced_intersect'' only produces both-free fpt' values. ---- *)
  Lemma fpt_spaced_intersect''_both_free :
    forall (fuel : nat)
           (cil : list (list bool)) (ptl : list (@FullPosTrie.fpt' B))
           (ci0 : list bool) (cil' : list (list bool))
           (pt0 : @FullPosTrie.fpt' B) (ptl' : list (@FullPosTrie.fpt' B))
           (r : @FullPosTrie.fpt' B),
    fpt_spaced_intersect'' merge fuel cil ptl ci0 cil' pt0 ptl' = Some r ->
    fpt_both_free' r.
  Proof.
    induction fuel as [|fuel' IH]; intros cil ptl ci0 cil' pt0 ptl' r Hr.
    - discriminate Hr.
    - destruct ci0 as [|ci0_hd ci0_tl].
      + (* ci0 = [] *)
        destruct pt0 as [a|m|a m]; cbn [fpt_spaced_intersect''] in Hr.
        * injection Hr as <-. constructor.
        * discriminate Hr.
        * discriminate Hr.
      + (* ci0 = ci0_hd :: ci0_tl *)
        cbn [fpt_spaced_intersect''] in Hr.
        set (initial_part :=
          if ci0_hd then fpt_have_true_part [] [] ci0_tl pt0 [] []
          else fpt_just_false_part ci0_tl pt0 [] []) in *.
        set (part :=
          fpt_partition_tries cil' ptl'
            (fpt_partition_tries cil ptl initial_part)) in *.
        destruct part as [ci0' pt0' oc ot | oc ot t_ci0 t_pt0 t_cil t_ptl] eqn:Hpart.
        * (* just_false_part: recurse *)
          exact (IH oc ot ci0' [] pt0' [] r Hr).
        * (* have_true_part: list_intersect *)
          cbn [fpt_spaced_intersect''] in Hr.
          set (true_cil_rev := rev t_cil) in *.
          set (pt_intersect :=
            TrieMap.list_intersect
              (fun is_forward =>
                 fpt_spaced_intersect'' merge fuel' oc ot t_ci0
                   (if is_forward then t_cil else true_cil_rev))
              (fpt_proj_node_unchecked t_pt0)
              (map fpt_proj_node_unchecked t_ptl)) in *.
          destruct pt_intersect as [m_res|] eqn:Hli; [|discriminate Hr].
          cbn [option_map] in Hr. injection Hr as <-.
          constructor.
          unfold pt_intersect in Hli.
          apply list_intersect_bf with
            (ef := (fun is_forward : bool =>
               fpt_spaced_intersect'' merge fuel' oc ot t_ci0
                 (if is_forward then t_cil else true_cil_rev) :
               @FullPosTrie.fpt' B -> list (@FullPosTrie.fpt' B) -> option (@FullPosTrie.fpt' B)))
            (hd := fpt_proj_node_unchecked t_pt0)
            (args := map fpt_proj_node_unchecked t_ptl)
            (m := m_res);
            [intros b x xs r' Hr';
             exact (IH oc ot t_ci0 (if b then t_cil else true_cil_rev) x xs r' Hr')
            | exact Hli].
  Qed.

  (* ---- Helper B3: both-free + depth'-after-injection = fpt_depth'. ---- *)
  Lemma both_free_depth_reflect :
    forall (t : @FullPosTrie.fpt' B),
    fpt_both_free' t ->
    forall n, depth' (pt'_of_fpt' t) n -> fpt_depth' t n.
  Proof.
    apply (FullPosTrie.fpt'_strong_ind B
      (fun t => fpt_both_free' t -> forall n, depth' (pt'_of_fpt' t) n -> fpt_depth' t n)).
    - (* fpt_leaf a *)
      intros a _Hbf n Hd. inversion Hd; subst. constructor.
    - (* fpt_node m *)
      intros m IHm Hbf n Hd.
      inversion Hbf as [|m0 Hchildren Hm0]; subst.
      rewrite pt'_of_fpt'_fpt_node in Hd.
      inversion Hd as [|m1 n0 Hchildren_d Hm1 Hn1]; subst.
      constructor. intros p c Hgp.
      apply (IHm p c Hgp (Hchildren p c Hgp) n0).
      apply (Hchildren_d p).
      rewrite tree'_map'_get, Hgp. reflexivity.
    - (* fpt_both a m -- excluded by fpt_both_free' *)
      intros a m _IHm Hbf. inversion Hbf.
  Qed.

  (* ---- Helper: list_Mmap id commutes with option_map pt'_of_fpt'. ---- *)
  Lemma list_Mmap_option_map_pt :
    forall (l : list (@FullPosTrie.fpt B)),
    @list_Mmap option _ _ option_monad id (map (option_map pt'_of_fpt') l)
    = option_map (map pt'_of_fpt') (@list_Mmap option _ _ option_monad id l).
  Proof.
    induction l as [| [x'|] l' IH].
    - reflexivity.
    - cbn [map list_Mmap option_map id].
      unfold Mbind, Mret. cbn [option_monad].
      cbn [id]. rewrite IH.
      destruct (@list_Mmap option _ _ option_monad id l'); cbn [option_map]; reflexivity.
    - cbn [map list_Mmap option_map id].
      unfold Mbind, Mret. cbn [option_monad]. reflexivity.
  Qed.

  (* ---- Helper: split commutes with cvt' element-wise. ---- *)
  Local Notation cvt' :=
    (fun p : @FullPosTrie.fpt B * list bool => (option_map pt'_of_fpt' (fst p), snd p)).

  Lemma split_cvt'_comm :
    forall (rest : list (@FullPosTrie.fpt B * list bool)),
    split (map cvt' rest)
    = (map (option_map pt'_of_fpt') (fst (split rest)), snd (split rest)).
  Proof.
    induction rest as [| [p q] rest' IH].
    - reflexivity.
    - cbn [map split fst snd].
      destruct (split rest') as [ptl'' cil''] eqn:Hsp.
      cbn [fst snd] in *. rewrite IH. reflexivity.
  Qed.

  (* ---- EASY 5: wrapper-level simulation. ---- *)
  Lemma fpt_spaced_intersect_native_sim :
    forall (tries : (@FullPosTrie.fpt B * list bool) * list (@FullPosTrie.fpt B * list bool)),
    option_map pt'_of_fpt' (fpt_spaced_intersect_native merge tries)
    = pt_spaced_intersect merge (cvt' (fst tries), map cvt' (snd tries)).
  Proof.
    intros [[pt0 ci0] rest].
    unfold fpt_spaced_intersect_native, pt_spaced_intersect.
    cbn [fst snd].
    rewrite split_cvt'_comm. cbn [fst snd].
    rewrite list_Mmap_option_map_pt.
    destruct (split rest) as [ptl cil] eqn:Hsp. cbn [fst snd].
    unfold Mbind, Mret, option_monad.
    destruct pt0 as [pt0'|]; cbn [option_map].
    - destruct (@list_Mmap option _ _ option_monad id ptl) as [ptl2|] eqn:Hmm;
        cbn [option_map].
      + setoid_rewrite Hmm. cbn [option_map]. apply fpt_spaced_intersect''_sim.
      + setoid_rewrite Hmm. cbn [option_map]. reflexivity.
    - reflexivity.
  Qed.

End FptSim.

(* ============================================================================
   M3 — BRIDGE LEMMAS
   Prove that [fpt_spaced_intersect_native] agrees get-for-get with
   [fpt_spaced_intersect_via_conv], and derive the keys corollary consumed by
   the e-graph assembly (QcAlignment.v trie_join_H9/H10).
   ============================================================================ *)

(* Lemma 1a: the structural injection pt'_of_fpt' preserves the depth predicate. *)
Lemma pt'_of_fpt'_has_depth' {B : Type} :
  forall (t : @FullPosTrie.fpt' B) (n : nat),
    fpt_depth' t n -> depth' (pt'_of_fpt' t) n.
Proof.
  induction 1 as [a | m n Hchild IH].
  - constructor.
  - rewrite pt'_of_fpt'_fpt_node. constructor.
    intros k v Hget. rewrite tree'_map'_get in Hget.
    destruct (PTree.get' k m) as [c|] eqn:Hc; [|discriminate].
    cbn [option_map] in Hget. injection Hget as <-.
    exact (IH k c Hc).
Qed.

Section BridgeSection.
  Context {B : Type} `{WithDefault B}.
  Context (merge : B -> B -> B).
  Context (merge_comm : forall a b, merge a b = merge b a).
  Context (merge_assoc : forall a b c, merge a (merge b c) = merge (merge a b) c).

  (* cvt  : fpt → pos_trie via fold-rebuild (= fpt_to_pt)   *)
  Local Notation cvt :=
    (fun p : @FullPosTrie.fpt B * list bool => (fpt_to_pt (fst p), snd p)).
  (* cvt' : fpt → pos_trie via structural injection pt'_of_fpt' *)
  Local Notation cvt' :=
    (fun p : @FullPosTrie.fpt B * list bool => (option_map pt'_of_fpt' (fst p), snd p)).

  (* combined_bools only uses snd (bool list), equal for cvt and cvt'. *)
  Lemma combined_bools_cvt_cvt'
    (tries : @FullPosTrie.fpt B * list bool)
    (rest : list (@FullPosTrie.fpt B * list bool)) :
    @combined_bools B (cvt tries, map cvt rest) = @combined_bools B (cvt' tries, map cvt' rest).
  Proof.
    unfold combined_bools. cbn [fst snd].
    generalize (snd tries).
    induction rest as [| [pt bs] rest' IH].
    - intros init. reflexivity.
    - intros init. cbn [map fold_left fst snd]. apply IH.
  Qed.

  Lemma wf_input_cvt'
    (sigma : list positive) (p : @FullPosTrie.fpt B * list bool) :
    length (snd p) = length sigma ->
    fpt_depth (fst p) (length (filter id (snd p))) ->
    @wf_input B sigma (cvt' p).
  Proof.
    intros Hlen Hd. unfold wf_input. cbn [fst snd]. split.
    - exact Hlen.
    - destruct (fst p) as [t'|] eqn:Hfst; cbn [option_map].
      + apply depth'_to_has_depth'. apply pt'_of_fpt'_has_depth'.
        cbn [fpt_depth] in Hd. exact Hd.
      + exact I.
  Qed.

  Lemma wf_tries_cvt'_at
    (sigma : list positive) (N : nat)
    (tries : @FullPosTrie.fpt B * list bool)
    (rest : list (@FullPosTrie.fpt B * list bool)) :
    length sigma = N ->
    (forall p, In p (tries :: rest) -> fpt_depth (fst p) (length (filter id (snd p)))) ->
    (forall p, In p (tries :: rest) -> length (snd p) = N) ->
    @wf_tries B sigma (cvt' tries, map cvt' rest).
  Proof.
    intros HN Hfd Hlen. unfold wf_tries. cbn [fst snd]. split.
    - apply wf_input_cvt'.
      + rewrite HN. apply (Hlen tries). left. reflexivity.
      + apply (Hfd tries). left. reflexivity.
    - apply Forall_map. apply Forall_forall.
      intros q Hq. apply wf_input_cvt'.
      + rewrite HN. apply (Hlen q). right. exact Hq.
      + apply (Hfd q). right. exact Hq.
  Qed.

  (* lookup_one sigma (cvt p) = lookup_one sigma (cvt' p) when depths+lengths match *)
  Lemma lookup_one_cvt_cvt'
    (sigma : list positive) (N : nat)
    (p : @FullPosTrie.fpt B * list bool) :
    length sigma = N ->
    fpt_depth (fst p) (length (filter id (snd p))) ->
    length (snd p) = N ->
    @lookup_one B sigma (cvt p) = @lookup_one B sigma (cvt' p).
  Proof.
    intros HN Hfd Hlensnd.
    unfold lookup_one, spaced_get. cbn [fst snd].
    set (proj := map fst (filter snd (combine sigma (snd p)))).
    assert (Hprojlen : length proj = length (filter id (snd p))).
    { subst proj. rewrite <- (project_length sigma (snd p)).
      - reflexivity. - rewrite HN, Hlensnd. reflexivity. }
    rewrite (@fpt_to_pt_get B (fst p) _ Hfd proj Hprojlen).
    destruct (fst p) as [t'|] eqn:Hfst; cbn [option_map FullPosTrie.fpt_get pt_get].
    - eapply pt'_of_fpt'_get.
      all: [> (cbn [fpt_depth] in Hfd; exact Hfd) | exact Hprojlen].
    - reflexivity.
  Qed.

  (* list_Mmap lookup_one is equal on cvt' and cvt lists *)
  (* Helper: list_Mmap equality for a list *)
  Lemma list_Mmap_lookup_list
    (sigma : list positive) (N : nat)
    (l : list (@FullPosTrie.fpt B * list bool)) :
    length sigma = N ->
    (forall p, In p l -> fpt_depth (fst p) (length (filter id (snd p)))) ->
    (forall p, In p l -> length (snd p) = N) ->
    list_Mmap (lookup_one sigma) (map cvt' l) =
    list_Mmap (lookup_one sigma) (map cvt l).
  Proof.
    intros HN Hfd Hlen.
    induction l as [|q l' IH].
    - reflexivity.
    - cbn [map list_Mmap]. unfold Mbind, Mret. cbn [option_monad].
      rewrite <- (lookup_one_cvt_cvt' sigma q HN
                 (Hfd q (or_introl eq_refl)) (Hlen q (or_introl eq_refl))).
      pose proof (IH (fun p Hp => Hfd p (or_intror Hp))
                     (fun p Hp => Hlen p (or_intror Hp))) as IH'.
      rewrite IH'. reflexivity.
  Qed.

  Lemma list_Mmap_lookup_cvt_cvt'
    (sigma : list positive) (N : nat)
    (tries : @FullPosTrie.fpt B * list bool)
    (rest : list (@FullPosTrie.fpt B * list bool)) :
    length sigma = N ->
    (forall p, In p (tries :: rest) -> fpt_depth (fst p) (length (filter id (snd p)))) ->
    (forall p, In p (tries :: rest) -> length (snd p) = N) ->
    list_Mmap (lookup_one sigma) (cvt' tries :: map cvt' rest) =
    list_Mmap (lookup_one sigma) (cvt tries :: map cvt rest).
  Proof.
    intros HN Hfd Hlen.
    cbn [list_Mmap]. unfold Mbind, Mret. cbn [option_monad].
    rewrite <- (lookup_one_cvt_cvt' sigma tries HN
               (Hfd tries (or_introl eq_refl)) (Hlen tries (or_introl eq_refl))).
    destruct (lookup_one sigma (cvt tries)) as [lv|] eqn:Hlv.
    - rewrite (list_Mmap_lookup_list sigma rest HN
                (fun p Hp => Hfd p (or_intror Hp))
                (fun p Hp => Hlen p (or_intror Hp))).
      reflexivity.
    - reflexivity.
  Qed.

  (** Lemma 3: [fpt_spaced_intersect_native] has uniform depth N. *)
  Lemma fpt_spaced_intersect_native_depth
    (tries : @FullPosTrie.fpt B * list bool)
    (rest  : list (@FullPosTrie.fpt B * list bool))
    (N : nat) :
    depth (@compat_intersect B _ merge (cvt tries, map cvt rest)) N ->
    @combined_bools B (cvt tries, map cvt rest) = repeat true N ->
    (forall p, In p (tries :: rest) -> fpt_depth (fst p) (length (filter id (snd p)))) ->
    (forall p, In p (tries :: rest) -> length (snd p) = N) ->
    fpt_depth (@fpt_spaced_intersect_native B _ merge (tries, rest)) N.
  Proof.
    intros _Hdepth Hbools Hfd Hlen.
    (* Build wf_tries for cvt' using repeat xH N as witness. *)
    assert (Hwf' : @wf_tries B (repeat xH N) (cvt' tries, map cvt' rest)).
    { eapply (wf_tries_cvt'_at (repeat xH N)).
      - rewrite repeat_length. reflexivity.
      - exact Hfd.
      - exact Hlen. }
    (* Apply pt_spaced_intersect_depth to get depth of the cvt' join. *)
    (* combined_bools of cvt' = combined_bools of cvt = repeat true N *)
    assert (Hcbools' : @combined_bools B (cvt' tries, map cvt' rest) = repeat true N).
    { exact (eq_trans (eq_sym (combined_bools_cvt_cvt' tries rest)) Hbools). }
    assert (HfilterN : length (filter id (repeat true N)) = N).
    { clear. induction N as [|n IHn]; cbn [filter id repeat length]; [reflexivity | congruence]. }
    (* pt_spaced_intersect_depth gives depth N for the cvt' join. *)
    pose proof (@pt_spaced_intersect_depth B _ merge merge_comm merge_assoc
                 (cvt' tries, map cvt' rest) (repeat xH N) Hwf') as Hdepth'.
    set (cb := @combined_bools B (cvt' tries, map cvt' rest)) in *.
    rewrite Hcbools', HfilterN in Hdepth'.
    (* Hdepth' : depth (pt_spaced_intersect merge (cvt' tries, map cvt' rest)) N *)
    (* Use simulation lemma. *)
    (* Case-split on the native result. *)
    destruct (fpt_spaced_intersect_native merge (tries, rest)) as [t'|] eqn:Hnat.
    - (* Some t': derive fpt_depth' t' N *)
      cbn [fpt_depth].
      (* Use the sim lemma to get pt'_of_fpt' t' = inner of pt_spaced_intersect *)
      pose proof (@fpt_spaced_intersect_native_sim B _ merge (tries, rest)) as Hsim.
      cbn [fst snd] in Hsim.
      rewrite Hnat in Hsim. cbn [option_map] in Hsim.
      (* Hdepth' says depth (pt_spaced_intersect merge (cvt' ...)) N *)
      (* Hsim says Some (pt'_of_fpt' t') = pt_spaced_intersect merge (cvt' ...) *)
      (* Combine: depth' (pt'_of_fpt' t') N *)
      assert (Hdepth'' : depth' (pt'_of_fpt' t') N).
      { rewrite <- Hsim in Hdepth'. exact Hdepth'. }
      (* Get both-free for t' by tracing fpt_spaced_intersect_native's internal call. *)
      assert (Hbf : fpt_both_free' t').
      { unfold fpt_spaced_intersect_native in Hnat.
        change (fst (tries, rest)) with tries in Hnat.
        change (snd (tries, rest)) with rest in Hnat.
        destruct (split rest) as [ptl cil] eqn:Hsplit.
        destruct tries as [pt0_opt ci0].
        cbn [fst snd] in Hnat.
        destruct pt0_opt as [pt0'|]; [|discriminate Hnat].
        destruct (@list_Mmap option _ _ option_monad id ptl) as [ptl'|] eqn:Hmm;
          [|discriminate Hnat].
        exact (fpt_spaced_intersect''_both_free merge
                 (S (length ci0)) cil ptl' ci0 [] pt0' [] Hnat). }
      (* Reflect: both-free + depth' (pt'_of_fpt' t') N → fpt_depth' t' N *)
      exact (both_free_depth_reflect Hbf Hdepth'').
    - (* None: fpt_depth None N = True *)
      exact I.
  Qed.

  (** Lemma 2: get-level bridge.
      fpt_get native sigma = fpt_get via_conv sigma when sigma has length N. *)
  Lemma fpt_spaced_intersect_native_eq_via_conv
    (tries : @FullPosTrie.fpt B * list bool)
    (rest  : list (@FullPosTrie.fpt B * list bool))
    (sigma : list positive) (N : nat) :
    length sigma = N ->
    depth (@compat_intersect B _ merge (cvt tries, map cvt rest)) N ->
    @combined_bools B (cvt tries, map cvt rest) = repeat true N ->
    @wf_tries B sigma (cvt tries, map cvt rest) ->
    (forall p, In p (tries :: rest) -> fpt_depth (fst p) (length (filter id (snd p)))) ->
    (forall p, In p (tries :: rest) -> length (snd p) = N) ->
    fpt_get (@fpt_spaced_intersect_native B _ merge (tries, rest)) sigma
    = fpt_get (fpt_spaced_intersect_via_conv merge (tries, rest)) sigma.
  Proof.
    intros HN Hdepth Hbools Hwf Hfd Hlen.
    unfold fpt_spaced_intersect_via_conv. cbn [fst snd].
    set (R := @compat_intersect B _ merge (cvt tries, map cvt rest)) in *.
    rewrite (@pt_to_fpt_get B R N Hdepth sigma HN).
    pose proof (fpt_spaced_intersect_native_depth Hdepth Hbools Hfd Hlen) as Hnativedepth.
    pose proof (@fpt_spaced_intersect_native_sim B _ merge (tries, rest)) as Hsim.
    cbn [fst snd] in Hsim.
    pose proof (wf_tries_cvt'_at sigma HN Hfd Hlen) as Hwf'.
    pose proof (pt_spaced_intersect_correct merge merge_comm merge_assoc
                  (cvt' tries, map cvt' rest) sigma Hwf') as Hspec'.
    pose proof (pt_spaced_intersect_correct merge merge_comm merge_assoc
                  (cvt tries, map cvt rest) sigma Hwf) as Hspec.
    unfold pt_spaced_intersect_spec, spaced_get in *.
    cbn [fst snd] in *.
    rewrite <- combined_bools_cvt_cvt' in Hspec'.
    rewrite Hbools in Hspec, Hspec'.
    rewrite (project_repeat_true sigma HN) in Hspec, Hspec'.
    unfold compat_intersect in Hspec. fold R in Hspec.
    pose proof (list_Mmap_lookup_cvt_cvt' sigma HN Hfd Hlen) as Hlookupeq.
    (* Destruct on the cvt' list_Mmap; use [change] to align with [HCvt'] syntactically,
       then [rewrite HCvt'] to simplify both specs; align Hspec via Hlookupeq. *)
    destruct (list_Mmap (lookup_one sigma)
        ((option_map pt'_of_fpt' (fst tries), snd tries) :: map cvt' rest))
      as [[|e es]|] eqn:HCvt'.
    all: (
      change (match list_Mmap (lookup_one sigma)
        ((option_map pt'_of_fpt' (fst tries), snd tries) :: map cvt' rest) with
      | Some (e0 :: es0) =>
          pt_get (pt_spaced_intersect merge
            (option_map pt'_of_fpt' (fst tries), snd tries, map cvt' rest)) sigma
          = Some (fold_left merge es0 e0)
      | _ =>
          pt_get (pt_spaced_intersect merge
            (option_map pt'_of_fpt' (fst tries), snd tries, map cvt' rest)) sigma
          = None
      end) in Hspec';
      rewrite HCvt' in Hspec';
      rewrite <- HCvt' in Hlookupeq;
      rewrite <- Hlookupeq in Hspec;
      rewrite HCvt' in Hspec
      ).
    all: destruct (@fpt_spaced_intersect_native B _ merge (tries, rest)) as [t'|] eqn:Hnat.
    all: [>
      (* native = Some t', HCvt' = Some [] *)
      (cbn [fpt_depth] in Hnativedepth; cbn [FullPosTrie.fpt_get];
       erewrite pt'_of_fpt'_get; [|exact Hnativedepth|exact HN];
       change (pt_get (option_map pt'_of_fpt' (Some t')) sigma = pt_get R sigma);
       apply (f_equal (fun x => pt_get x sigma)) in Hsim;
       rewrite Hsim; rewrite Hspec'; unfold R; unfold compat_intersect; symmetry; exact Hspec)
      |
      (* native = None, HCvt' = Some [] *)
      (cbn [FullPosTrie.fpt_get]; unfold R; unfold compat_intersect; symmetry; exact Hspec)
      |
      (* native = Some t', HCvt' = Some (e::es) *)
      (cbn [fpt_depth] in Hnativedepth; cbn [FullPosTrie.fpt_get];
       erewrite pt'_of_fpt'_get; [|exact Hnativedepth|exact HN];
       change (pt_get (option_map pt'_of_fpt' (Some t')) sigma = pt_get R sigma);
       apply (f_equal (fun x => pt_get x sigma)) in Hsim;
       rewrite Hsim; rewrite Hspec'; unfold R; unfold compat_intersect; symmetry; exact Hspec)
      |
      (* native = None, HCvt' = Some (e::es): contradiction via Hsim *)
      (cbn [option_map] in Hsim;
       rewrite <- Hsim in Hspec'; cbn [pt_get] in Hspec'; discriminate)
      |
      (* native = Some t', HCvt' = None *)
      (cbn [fpt_depth] in Hnativedepth; cbn [FullPosTrie.fpt_get];
       erewrite pt'_of_fpt'_get; [|exact Hnativedepth|exact HN];
       change (pt_get (option_map pt'_of_fpt' (Some t')) sigma = pt_get R sigma);
       apply (f_equal (fun x => pt_get x sigma)) in Hsim;
       rewrite Hsim; rewrite Hspec'; unfold R; unfold compat_intersect; symmetry; exact Hspec)
      |
      (* native = None, HCvt' = None *)
      (cbn [FullPosTrie.fpt_get]; unfold R; unfold compat_intersect; symmetry; exact Hspec)
    ].
  Qed.

  (** Lemma 4: Keys corollary.
      sigma ∈ keys(native) ↔ sigma ∈ keys(via_conv).
      Derived from the get-equality and fpt_depth_key_length for both sides. *)
  Lemma fpt_spaced_intersect_native_keys_iff
    (tries : @FullPosTrie.fpt B * list bool)
    (rest  : list (@FullPosTrie.fpt B * list bool))
    (N : nat)
    (sigma : list positive) :
    depth (@compat_intersect B _ merge (cvt tries, map cvt rest)) N ->
    @combined_bools B (cvt tries, map cvt rest) = repeat true N ->
    @wf_tries B sigma (cvt tries, map cvt rest) ->
    (forall p, In p (tries :: rest) -> fpt_depth (fst p) (length (filter id (snd p)))) ->
    (forall p, In p (tries :: rest) -> length (snd p) = N) ->
    In sigma (@map.keys (list positive) B (@FullPosTrie.full_pos_trie_map B)
                (@fpt_spaced_intersect_native B _ merge (tries, rest)))
    <->
    In sigma (@map.keys (list positive) B (@FullPosTrie.full_pos_trie_map B)
                (fpt_spaced_intersect_via_conv merge (tries, rest))).
  Proof.
    intros Hdepth Hbools Hwf Hfd Hlen.
    assert (Hbs : forall x y : list positive,
      BoolSpec (x = y) (x <> y) (if list_eq_dec Pos.eq_dec x y then true else false)).
    { intros x y. destruct (list_eq_dec Pos.eq_dec x y); constructor; assumption. }
    (* Depth facts for both sides *)
    pose proof (fpt_spaced_intersect_native_depth Hdepth Hbools Hfd Hlen) as Hnativedepth.
    pose proof (pt_to_fpt_depth _ _ Hdepth) as Hvialdepth.
    (* Forward direction: sigma ∈ keys native → sigma ∈ keys via_conv *)
    split; intros Hin.
    - (* sigma ∈ keys native → fpt_get native sigma ≠ None *)
      pose proof (@Properties.map.in_keys_inv (list positive) B
                    (@FullPosTrie.full_pos_trie_map B) (@FullPosTrie.full_pos_trie_map_ok B)
                    _ Hbs sigma _ Hin) as Hget.
      change (@map.get (list positive) B (@FullPosTrie.full_pos_trie_map B)
                (@fpt_spaced_intersect_native B _ merge (tries, rest)) sigma)
        with (fpt_get (@fpt_spaced_intersect_native B _ merge (tries, rest)) sigma) in Hget.
      destruct (fpt_get (@fpt_spaced_intersect_native B _ merge (tries, rest)) sigma)
        as [v|] eqn:Hfget; [|contradiction].
      (* sigma has length N from native depth *)
      assert (HsigmaN : length sigma = N).
      { exact (fpt_depth_key_length _ _ Hnativedepth sigma Hfget). }
      assert (Hwf2 : @wf_tries B sigma (cvt tries, map cvt rest)).
      { exact Hwf. }
      (* get-equality at sigma *)
      pose proof (fpt_spaced_intersect_native_eq_via_conv HsigmaN Hdepth Hbools Hwf2 Hfd Hlen) as Heq.
      rewrite Hfget in Heq. symmetry in Heq.
      (* Now Heq : fpt_get via_conv sigma = Some v ≠ None *)
      (* sigma ∈ keys via_conv *)
      unfold fpt_spaced_intersect_via_conv in Heq. cbn [fst snd] in Heq.
      set (R := @compat_intersect B _ merge (cvt tries, map cvt rest)) in *.
      (* fpt_get (pt_to_fpt R) sigma = Some v *)
      change (fpt_get (pt_to_fpt R) sigma = Some v) in Heq.
      apply (@Properties.map.in_keys (list positive) B
               (@FullPosTrie.full_pos_trie_map B) (@FullPosTrie.full_pos_trie_map_ok B)
               _ Hbs (pt_to_fpt R) sigma v).
      change (@map.get (list positive) B (@FullPosTrie.full_pos_trie_map B) (pt_to_fpt R) sigma)
        with (fpt_get (pt_to_fpt R) sigma).
      exact Heq.
    - (* via_conv → native: symmetric *)
      pose proof (@Properties.map.in_keys_inv (list positive) B
                    (@FullPosTrie.full_pos_trie_map B) (@FullPosTrie.full_pos_trie_map_ok B)
                    _ Hbs sigma _ Hin) as Hget.
      unfold fpt_spaced_intersect_via_conv in Hget. cbn [fst snd] in Hget.
      set (R := @compat_intersect B _ merge (cvt tries, map cvt rest)) in *.
      change (@map.get (list positive) B (@FullPosTrie.full_pos_trie_map B) (pt_to_fpt R) sigma)
        with (fpt_get (pt_to_fpt R) sigma) in Hget.
      destruct (fpt_get (pt_to_fpt R) sigma) as [v|] eqn:Hfget; [|contradiction].
      (* sigma has length N from via_conv depth *)
      assert (HsigmaN : length sigma = N).
      { exact (fpt_depth_key_length _ _ Hvialdepth sigma Hfget). }
      pose proof (fpt_spaced_intersect_native_eq_via_conv HsigmaN Hdepth Hbools Hwf Hfd Hlen) as Heq.
      change (fpt_get (pt_to_fpt R) sigma = Some v) in Hfget.
      change (fpt_get (fpt_spaced_intersect_via_conv merge (tries, rest)) sigma = Some v)
        in Hfget.
      rewrite <- Heq in Hfget.
      apply (@Properties.map.in_keys (list positive) B
               (@FullPosTrie.full_pos_trie_map B) (@FullPosTrie.full_pos_trie_map_ok B)
               _ Hbs (@fpt_spaced_intersect_native B _ merge (tries, rest)) sigma v).
      change (@map.get (list positive) B (@FullPosTrie.full_pos_trie_map B)
                (@fpt_spaced_intersect_native B _ merge (tries, rest)) sigma)
        with (fpt_get (@fpt_spaced_intersect_native B _ merge (tries, rest)) sigma).
      exact Hfget.
  Qed.

  (* The inheritance bridge (relocated here from Section Inherit so it can use
     [fpt_spaced_intersect_native_keys_iff]).  [tries]/[rest] are the ORIGINAL fpt
     query tries.  Hypotheses: [Hdepth] result uniform depth N; [Hbools] OR-combined
     bool pattern all-true; [Hwf] converted tries wf at [sigma]; [Hfd] each fpt input
     uniform depth = #true flags.  Now that the public join is the native one, the
     opening converts [In sigma (keys native)] to [In sigma (keys via_conv)] via the
     keys corollary; the remaining inheritance through [pt_spaced_intersect_correct]
     is unchanged. *)
  Lemma fpt_spaced_intersect_inputs_hit
    (tries : @FullPosTrie.fpt B * list bool)
    (rest : list (@FullPosTrie.fpt B * list bool))
    (sigma : list positive) (N : nat) :
    In sigma (@map.keys (list positive) B (@FullPosTrie.full_pos_trie_map B)
                (fpt_spaced_intersect merge (tries, rest))) ->
    length sigma = N ->
    depth (compat_intersect merge (cvt tries, List.map cvt rest)) N ->
    combined_bools (cvt tries, List.map cvt rest) = repeat true N ->
    wf_tries sigma (cvt tries, List.map cvt rest) ->
    (forall p, In p (tries :: rest) ->
       fpt_depth (fst p) (length (filter id (snd p)))) ->
    forall p, In p (tries :: rest) ->
      exists v, fpt_get (fst p) (map fst (filter snd (combine sigma (snd p)))) = Some v.
  Proof.
    intros Hin Hlen Hdepth Hbools Hwf Hfd.
    (* per-input bool-list length (= N), from Hwf, needed by the keys corollary *)
    assert (Hlenp : forall p, In p (tries :: rest) -> length (snd p) = N).
    { intros p Hp. destruct Hwf as [Hwfh Hwft]. cbn [fst snd] in Hwfh, Hwft.
      destruct Hp as [Heqp | Hinp].
      - subst p. destruct Hwfh as [Hl _]. cbn [snd] in Hl. rewrite Hl. exact Hlen.
      - rewrite Forall_forall in Hwft.
        specialize (Hwft (cvt p) (in_map cvt rest p Hinp)).
        destruct Hwft as [Hl _]. cbn [snd] in Hl. rewrite Hl. exact Hlen. }
    (* re-route: native-keys membership -> via_conv-keys membership.
       (tries/rest/N/sigma are implicit, inferred from Hdepth/Hwf before [set].) *)
    unfold fpt_spaced_intersect in Hin.
    apply (proj1 (fpt_spaced_intersect_native_keys_iff
                    Hdepth Hbools Hwf Hfd Hlenp)) in Hin.
    set (R := compat_intersect merge (cvt tries, List.map cvt rest)) in *.
    assert (Heq : fpt_spaced_intersect_via_conv merge (tries, rest) = pt_to_fpt R).
    { unfold fpt_spaced_intersect_via_conv, R. cbn [fst snd]. reflexivity. }
    rewrite Heq in Hin.
    assert (Hbs : forall x y : list positive,
               BoolSpec (x = y) (x <> y) (if list_eq_dec Pos.eq_dec x y then true else false)).
    { intros x y. destruct (list_eq_dec Pos.eq_dec x y); constructor; assumption. }
    pose proof (@Properties.map.in_keys_inv (list positive) B
                  (@FullPosTrie.full_pos_trie_map B) (@FullPosTrie.full_pos_trie_map_ok B)
                  _ Hbs sigma (pt_to_fpt R) Hin) as Hget.
    change (@map.get (list positive) B (@FullPosTrie.full_pos_trie_map B) (pt_to_fpt R) sigma)
      with (fpt_get (pt_to_fpt R) sigma) in Hget.
    destruct (fpt_get (pt_to_fpt R) sigma) as [v|] eqn:Hfget; [|congruence].
    clear Hget Hbs Hin.
    rewrite (pt_to_fpt_get R Hdepth sigma Hlen) in Hfget.
    pose proof (pt_spaced_intersect_correct (A:=B) merge merge_comm merge_assoc
                  (cvt tries, List.map cvt rest) sigma Hwf) as Hspec.
    unfold pt_spaced_intersect_spec in Hspec.
    unfold spaced_get in Hspec. cbn [fst snd] in Hspec.
    rewrite Hbools in Hspec.
    rewrite (project_repeat_true sigma Hlen) in Hspec.
    change (pt_spaced_intersect merge (fpt_to_pt (fst tries), snd tries, map cvt rest))
      with R in Hspec.
    rewrite Hfget in Hspec.
    destruct (list_Mmap (lookup_one sigma)
                ((fpt_to_pt (fst tries), snd tries) :: map cvt rest))
      as [[|e es]|] eqn:Hmm; [discriminate Hspec | | discriminate Hspec].
    intros p Hp.
    assert (Hincvt : In (cvt p) ((fpt_to_pt (fst tries), snd tries) :: map cvt rest)).
    { change ((fpt_to_pt (fst tries), snd tries) :: map cvt rest)
        with (map cvt (tries :: rest)).
      exact (in_map cvt (tries :: rest) p Hp). }
    pose proof (list_Mmap_in_some _ _ Hmm (cvt p) Hincvt) as [w Hw].
    unfold lookup_one, spaced_get in Hw. cbn [fst snd] in Hw.
    assert (Hlen_eq : length sigma = length (snd p)).
    { destruct Hwf as [Hwfh Hwft]. cbn [fst snd] in Hwfh.
      destruct Hp as [Heqp | Hinp].
      - subst p. destruct Hwfh as [Hl _]. cbn [snd] in Hl. symmetry. exact Hl.
      - rewrite Forall_forall in Hwft.
        specialize (Hwft (cvt p) (in_map cvt rest p Hinp)).
        destruct Hwft as [Hl _]. cbn [snd] in Hl. symmetry. exact Hl. }
    pose proof (project_length sigma (snd p) Hlen_eq) as Hkey.
    rewrite (fpt_to_pt_get (fst p) (Hfd p Hp) _ Hkey) in Hw.
    exists w. exact Hw.
  Qed.

End BridgeSection.
