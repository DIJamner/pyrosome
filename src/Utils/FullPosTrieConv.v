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
  PosListMapIntersectSpec.

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

(* TEMPORARY alias during the native-join migration (M0): definitionally equal to
   [fpt_spaced_intersect_via_conv].  Its body is replaced by the conversion-free
   native [fpt'] join once the simulation/bridge lemmas are in place; downstream
   code and soundness statements reference only this name. *)
Definition fpt_spaced_intersect {B} `{WithDefault B} (merge : B -> B -> B)
  (tries : (@FullPosTrie.fpt B * list bool)
           * list (@FullPosTrie.fpt B * list bool))
  : @FullPosTrie.fpt B :=
  fpt_spaced_intersect_via_conv merge tries.

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

  (* The inheritance bridge.  [tries]/[rest] are the ORIGINAL fpt query tries.
     Hypotheses (downstream obligations):
       - [Hdepth]: the converted pos_trie intersection result is uniform depth N
         (ingredient (b): pt_spaced_intersect result-depth preservation);
       - [Hbools]: the OR-combined bool pattern is all-true of length N
         (the build_rule_set invariant: variable_flags cover every query var);
       - [Hwf]: the converted tries are well-formed at key [sigma]
         (lengths + per-trie has_depth', from build_tries output);
       - [Hfd]: each ORIGINAL fpt input has uniform depth = its number of true
         flags (so [fpt_to_pt_get] fires on the projected key). *)
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
    (* PLAN (the inheritance chain):
       Let R := compat_intersect merge (cvt tries, map cvt rest).
       Note fpt_spaced_intersect merge (tries,rest) = pt_to_fpt R (unfold; reflexivity).

       1. From [In sigma (map.keys (pt_to_fpt R))]:
            map.in_keys_inv (@full_pos_trie_map_ok) -> map.get (pt_to_fpt R) sigma <> None.
          map.get on full_pos_trie_map is defeq fpt_get, so get [v] with
            fpt_get (pt_to_fpt R) sigma = Some v.
       2. pt_to_fpt_get R N Hdepth sigma Hlen : fpt_get (pt_to_fpt R) sigma = pt_get R sigma.
          So pt_get R sigma = Some v.
       3. pt_spaced_intersect_correct merge merge_comm merge_assoc
            (cvt tries, map cvt rest) sigma Hwf : pt_spaced_intersect_spec ... sigma.
          Unfold the spec: result := spaced_get sigma (combined_bools, R').
          R' = pt_spaced_intersect merge (...) = compat_intersect ... = R (defeq).
          spaced_get sigma (combined_bools, R) = pt_get R (project sigma combined_bools).
          Rewrite Hbools (combined_bools = repeat true N) + project_repeat_true Hlen
            => spaced_get sigma (...) = pt_get R sigma = Some v (from step 2).
          So the spec's [match ... with Some (e::es) => result = Some _ | _ => result = None]
            forces list_Mmap (lookup_one sigma) (fst::snd) = Some (_::_) (else result=None,
            contradicting Some v). Name it [Hmm].
       4. For p in tries::rest: cvt p in (cvt tries :: map cvt rest) = the spec's all_tries.
          list_Mmap_in_some Hmm (cvt p) (In) : exists w, lookup_one sigma (cvt p) = Some w.
          lookup_one sigma (cvt p) = spaced_get sigma (snd p, fpt_to_pt (fst p))
            = pt_get (fpt_to_pt (fst p)) (map fst (filter snd (combine sigma (snd p)))).
       5. fpt_to_pt_get (fst p) (length (filter id (snd p))) (Hfd p)
            (key := project sigma (snd p)):
          need |project| = length (filter id (snd p)): project_length with
            length sigma = length (snd p) (= N, from Hwf's wf_input length fields).
          => pt_get (fpt_to_pt (fst p)) (project) = fpt_get (fst p) (project) = Some w.
          exists w; exact. *)
    intros Hin Hlen Hdepth Hbools Hwf Hfd.
    set (R := compat_intersect merge (cvt tries, List.map cvt rest)) in *.
    assert (Heq : fpt_spaced_intersect merge (tries, rest) = pt_to_fpt R).
    { unfold fpt_spaced_intersect, fpt_spaced_intersect_via_conv, R. cbn [fst snd]. reflexivity. }
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

End Inherit.
