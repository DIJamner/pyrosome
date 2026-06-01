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

Definition fpt_spaced_intersect {B} `{WithDefault B} (merge : B -> B -> B)
  (tries : (@FullPosTrie.fpt B * list bool)
           * list (@FullPosTrie.fpt B * list bool))
  : @FullPosTrie.fpt B :=
  let conv := fun p : @FullPosTrie.fpt B * list bool => (fpt_to_pt (fst p), snd p) in
  pt_to_fpt (compat_intersect merge (conv (fst tries), List.map conv (snd tries))).

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
    { unfold fpt_spaced_intersect, R. cbn [fst snd]. reflexivity. }
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
