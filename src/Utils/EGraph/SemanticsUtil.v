(* Small of_list / assignment / list utility lemmas, split out of Semantics.v
   (Section WithMap) to keep that file smaller.  Re-declared in a local Section
   whose Context matches the relevant WithMap variables (explicit, same order),
   so the closed constants are type-identical to the section-closed originals
   consumed by SemanticsProcessErule / QueryOptSound. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.

Section Util.
  Context (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
          (symbol : Type)
          (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
          (m : model symbol).

  (* For a [named_list] with [NoDup] keys, the coqutil [of_list] map and the
     Pyrosome [named_list_lookup] agree on present keys. *)
  Lemma named_list_lookup_of_list (B : Type) (dflt : B) (l : list (idx * B)) (k : idx) :
    List.NoDup (List.map fst l) ->
    In k (List.map fst l) ->
    map.get (map.of_list l) k = Some (named_list_lookup dflt l k).
  Proof.
    induction l as [|[a b] l' IH]; cbn [List.map fst map.of_list named_list_lookup];
      intros Hnd Hin.
    - contradiction.
    - inversion Hnd as [|? ? Ha_notin Hnd']; subst.
      pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok k a) as Hbs.
      destruct (eqb k a) eqn:Hka.
      + subst k. rewrite map.get_put_same. reflexivity.
      + rewrite (map.get_put_diff _ _ _ _ Hbs).
        apply IH; [exact Hnd'|].
        destruct Hin as [Haeq|Hin']; [ exfalso; apply Hbs; symmetry; exact Haeq | exact Hin' ].
  Qed.

  (* Specialisation to [combine]: looking up a key present in [qs] in the
     [of_list] of [combine qs vs] yields the [named_list_lookup] value. *)
  Lemma get_of_list_combine (B : Type) (dflt : B) (qs : list idx) (vs : list B) (k : idx) :
    List.NoDup qs ->
    List.length qs = List.length vs ->
    In k qs ->
    map.get (map.of_list (combine qs vs)) k = Some (named_list_lookup dflt (combine qs vs) k).
  Proof.
    intros Hnd Hlen Hin.
    apply named_list_lookup_of_list.
    - rewrite (map_combine_fst qs vs Hlen). exact Hnd.
    - rewrite (map_combine_fst qs vs Hlen). exact Hin.
  Qed.

  (* of_list lookups for absent / present keys. *)
  Lemma get_of_list_none (B : Type) (l : list (idx * B)) (x : idx) :
    ~ In x (map fst l) -> map.get (map.of_list l) x = None.
  Proof.
    induction l as [|[a b] l' IH]; cbn [map fst map.of_list]; intros Hni.
    - apply map.get_empty.
    - pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok x a) as Hbs.
      destruct (eqb x a) eqn:Hxa.
      + subst a. exfalso. apply Hni. left. reflexivity.
      + rewrite (map.get_put_diff _ _ _ _ Hbs). apply IH. intro Hin. apply Hni. right. exact Hin.
  Qed.

  Lemma get_of_list_in_keys (B : Type) (l : list (idx * B)) (x : idx) (v : B) :
    map.get (map.of_list l) x = Some v -> In x (map fst l).
  Proof.
    induction l as [|[a b] l' IH]; cbn [map fst map.of_list]; intros Hg.
    - rewrite map.get_empty in Hg. discriminate.
    - pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok x a) as Hbs.
      destruct (eqb x a) eqn:Hxa.
      + subst a. left. reflexivity.
      + rewrite (map.get_put_diff _ _ _ _ Hbs) in Hg. right. exact (IH Hg).
  Qed.

  (* Every element of a successfully-mapped list has a defined image. *)
  Lemma list_Mmap_get_some (B : Type) (f : idx -> option B) (l : list idx) (l' : list B) :
    list_Mmap f l = Some l' -> forall x, In x l -> exists b, f x = Some b.
  Proof.
    revert l'; induction l as [|a l IHl]; cbn [list_Mmap]; intros l' Hl x Hx.
    - contradiction.
    - destruct (f a) as [b0|] eqn:Hfa; cbn [Mbind option_monad] in Hl; [|discriminate].
      destruct (list_Mmap f l) as [bl|] eqn:Hfl; cbn [Mbind option_monad] in Hl; [|discriminate].
      destruct Hx as [->|Hx]; [exists b0; exact Hfa | exact (IHl _ eq_refl x Hx)].
  Qed.

  (* The model assignment [a_q] for a query assignment: compose the
     interpretation [i] after the query-variable->idx map [env0], dropping
     keys whose idx is not in [i]. Realises the bind spec that
     query_clause_ptr_sound / query_atoms_sound consume. *)
  Definition compose_assignment (i : idx_map (domain symbol m)) (env0 : idx_map idx)
    : idx_map (domain symbol m) :=
    map.fold (fun acc x v => match map.get i v with
                             | Some d => map.put acc x d
                             | None => acc
                             end) map.empty env0.

  Lemma get_compose_assignment (i : idx_map (domain symbol m)) (env0 : idx_map idx) (x : idx) :
    map.get (compose_assignment i env0) x
    = match map.get env0 x with
      | Some v => map.get i v
      | None => None
      end.
  Proof.
    unfold compose_assignment.
    revert x.
    apply (map.fold_spec
      (fun env0' acc => forall x, map.get acc x
         = match map.get env0' x with Some v => map.get i v | None => None end)).
    - intros y. rewrite !map.get_empty. reflexivity.
    - intros k v m0 r Hnone IH y.
      destruct (map.get i v) as [d|] eqn:Hiv.
      + pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok k y) as Hbs.
        destruct (eqb k y) eqn:Hky.
        * subst y. rewrite !map.get_put_same. rewrite Hiv. reflexivity.
        * rewrite !(map.get_put_diff _ _ _ _ (not_eq_sym Hbs)). apply IH.
      + pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok k y) as Hbs.
        destruct (eqb k y) eqn:Hky.
        * subst y. rewrite map.get_put_same. rewrite Hiv. rewrite IH, Hnone; reflexivity.
        * rewrite (map.get_put_diff _ _ _ _ (not_eq_sym Hbs)). apply IH.
  Qed.

  (* [all] over a mapped list reduces to a per-element obligation. *)
  Lemma all_map_in {A B} (g : A -> B) (Pr : B -> Prop) (l : list A) :
    (forall x, In x l -> Pr (g x)) -> all Pr (map g l).
  Proof.
    induction l as [|a l' IH]; cbn [map]; intros Hl; [exact I|].
    cbn [all]; split.
    - apply Hl; left; reflexivity.
    - apply IH; intros y Hy; apply Hl; right; exact Hy.
  Qed.
End Util.
