(* parents_keys_in_equiv: the structural invariant + its add_ctx building-block
   preservation lemmas, split out of Semantics.v (Section WithMap) to keep that
   file smaller.  Stated at top level with the egraph context as explicit
   arguments; [parents_keys_in_equiv] keeps the exact section-closed signature
   that Theorems.v consumes. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.

(* EXTERNAL (Theorems.v): keep section-closed signature exactly (all explicit ctx). *)
Definition parents_keys_in_equiv
  (idx symbol : Type) (symbol_map : forall A, map.map symbol A)
  (idx_map : forall A, map.map idx A) (idx_trie : forall A, map.map (list idx) A)
  (analysis_result : Type)
  (e : instance idx symbol symbol_map idx_map idx_trie analysis_result) : Prop :=
  forall y, (exists s, map.get e.(parents) y = Some s) ->
            Sep.has_key y e.(equiv).(parent).

(* INTERNAL helpers/lemmas: ctx args IMPLICIT so proof bodies are verbatim. *)
Lemma in_dedup_in_orig {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  (y : idx) (l : list idx)
  : In y (dedup (eqb (A:=idx)) l) -> In y l.
Proof.
  intro Hdedup.
  exact (proj2 (dedup_preserves_In (aeqb_dec := @eqb_boolspec idx _ Eqb_idx_ok) l y) Hdedup).
Qed.

Lemma fold_left_new_key {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {symbol : Type} {idx_map : forall A, map.map idx A} {idx_map_ok : forall A, map.ok (idx_map A)}
  (ks : list idx) (a0 : atom idx symbol)
  (mp : idx_map (list (atom idx symbol))) (y : idx) (s : list (atom idx symbol))
  : map.get (fold_left (fun m k => map_update m k (cons a0)) ks mp) y = Some s ->
    map.get mp y = None ->
    In y ks.
Proof.
  revert mp.
  induction ks as [|k ks IH]; intros mp Hfold Hnone.
  - cbn [fold_left] in Hfold. congruence.
  - cbn [fold_left In].
    pose proof (@eqb_spec _ _ Eqb_idx_ok y k) as Hspec_yk.
    destruct (eqb y k); cbn beta iota in Hspec_yk.
    + subst k. left. reflexivity.
    + right.
      apply IH with (mp := map_update mp k (cons a0)).
      * cbn [fold_left] in Hfold. exact Hfold.
      * assert (Hget_eq : map.get (map_update mp k (cons a0)) y = map.get mp y).
        { apply get_update_diff.
          - exact (idx_map_ok _).
          - intro Heq. exact (Hspec_yk (eq_sym Heq)). }
        rewrite Hget_eq. exact Hnone.
Qed.

Lemma db_set'_parents_keys_in_equiv {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {symbol : Type} {symbol_map : forall A, map.map symbol A}
  {idx_map : forall A, map.map idx A} {idx_map_ok : forall A, map.ok (idx_map A)}
  {idx_trie : forall A, map.map (list idx) A} {analysis_result : Type}
  (atom_0 : atom idx symbol) (out_0 : analysis_result)
  : vc (db_set' idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result atom_0 out_0)
      (fun e res =>
         Sep.has_key atom_0.(atom_ret) e.(equiv).(parent) ->
         all (fun x => Sep.has_key x e.(equiv).(parent)) atom_0.(atom_args) ->
         (forall y, Sep.has_key y e.(equiv).(parent) ->
                    Sep.has_key y (snd res).(equiv).(parent)) ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result (snd res)).
Proof.
  unfold vc, db_set', parents_keys_in_equiv. intros e.
  cbn [fst snd].
  intros Hret_in Hargs_in Hequiv_mono Hstruc y (s & Hg).
  apply Hequiv_mono.
  set (dkeys := dedup (eqb (A:=idx)) (atom_0.(atom_ret) :: atom_0.(atom_args))).
  destruct (map.get e.(parents) y) as [s_old|] eqn:Hg_old.
  - apply Hstruc. exists s_old. exact Hg_old.
  - assert (Hin_dkeys : In y dkeys).
    { eapply fold_left_new_key; [exact Hg | exact Hg_old]. }
    apply in_dedup_in_orig in Hin_dkeys.
    cbn [In] in Hin_dkeys.
    destruct Hin_dkeys as [Heq | Hin].
    + subst y. exact Hret_in.
    + exact (in_all _ _ _ Hargs_in Hin).
Qed.

Lemma alloc_opaque_parents_keys_in_equiv {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {lt : idx -> idx -> Prop} {idx_succ : idx -> idx}
  {symbol : Type} {symbol_map : forall A, map.map symbol A}
  {idx_map : forall A, map.map idx A} {idx_map_ok : forall A, map.ok (idx_map A)}
  {idx_trie : forall A, map.map (list idx) A} {analysis_result : Type}
  {HA : analysis idx symbol analysis_result}
  (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
  : vc (alloc_opaque idx idx_succ symbol symbol_map idx_map idx_trie analysis_result)
      (fun e res =>
         egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result (snd res)).
Proof.
  unfold vc.
  intros e.
  destruct (alloc_opaque idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e)
    as [x' e'] eqn:Heq.
  cbn [fst snd].
  pose proof (@alloc_opaque_egraph_ok idx Eqb_idx Eqb_idx_ok lt idx_succ symbol symbol_map idx_map idx_map_ok idx_trie analysis_result HA Hlti Hlts Hltt) as Hao.
  unfold vc in Hao. specialize (Hao e).
  rewrite Heq in Hao. cbn [fst snd] in Hao.
  intros Hok Hpke.
  destruct (Hao Hok) as (_ & _ & _ & Hmono & _ & Hpar_eq & _).
  unfold parents_keys_in_equiv in *.
  intros y (s & Hg).
  apply Hmono.
  apply Hpke.
  exists s.
  rewrite Hpar_eq.
  exact Hg.
Qed.

Lemma union_parents_keys_in_equiv {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {lt : idx -> idx -> Prop} {idx_succ : idx -> idx} {idx_zero : WithDefault idx}
  {symbol : Type} {symbol_map : forall A, map.map symbol A}
  {idx_map : forall A, map.map idx A} {idx_map_ok : forall A, map.ok (idx_map A)}
  {idx_trie : forall A, map.map (list idx) A}
  {analysis_result : Type} {HA : analysis idx symbol analysis_result}
  (v v1 : idx)
  : vc (Defs.union v v1)
      (fun e res =>
         (exists roots, union_find_ok lt (equiv e) roots) ->
         Sep.has_key v e.(equiv).(parent) ->
         Sep.has_key v1 e.(equiv).(parent) ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result (snd res)).
Proof.
  unfold vc.
  intros e.
  destruct (Defs.union v v1 e) as [u e'] eqn:Heq.
  cbn [fst snd].
  intros Hroots Hkv Hkv1 Hpke.
  pose proof (@union_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result HA v v1) as Hus.
  unfold vc in Hus. specialize (Hus e).
  rewrite Heq in Hus. cbn [snd] in Hus.
  destruct (Hus Hroots Hkv Hkv1) as (_ & Hroots' & Hper & Hpar_eq & _).
  destruct Hroots' as [roots' Hroots'].
  unfold parents_keys_in_equiv in *.
  intros y (s & Hg).
  assert (Hyk_e : Sep.has_key y (parent (equiv e))).
  { apply Hpke. exists s. rewrite Hpar_eq. exact Hg. }
  unfold Sep.has_key in Hyk_e.
  destruct (map.get (parent (equiv e)) y) as [vy|] eqn:Hgy; [|tauto].
  assert (Hyy_in : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e) y y).
  { unfold uf_rel_PER.
    eapply PER_clo_trans;
      [ apply PER_clo_base; exact Hgy
      | apply PER_clo_sym; apply PER_clo_base; exact Hgy ]. }
  assert (Hyy_clo : union_closure_PER (uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e)) (singleton_rel v v1) y y).
  { unfold union_closure_PER. apply PER_clo_base. left. exact Hyy_in. }
  assert (Hyy_u : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e') y y) by (apply Hper; exact Hyy_clo).
  exact (proj1 (@uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map idx_map_ok _ roots' _ _ Hroots' Hyy_u)).
Qed.

Lemma hash_entry_parents_keys_in_equiv {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {lt : idx -> idx -> Prop} {idx_succ : idx -> idx} {idx_zero : WithDefault idx}
  {symbol : Type} {symbol_map : forall A, map.map symbol A}
  {idx_map : forall A, map.map idx A} {idx_map_ok : forall A, map.ok (idx_map A)}
  {idx_trie : forall A, map.map (list idx) A}
  {analysis_result : Type} {HA : analysis idx symbol analysis_result}
  (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
  (f : symbol) (args : list idx)
  : vc (hash_entry idx_succ f args)
      (fun e res =>
         (exists roots, union_find_ok lt (equiv e) roots) ->
         all (fun x => Sep.has_key x (parent (equiv e))) args ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e ->
         parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result (snd res)).
Proof.
  unfold vc, hash_entry. intro e. cbn [Mbind StateMonad.state_monad].
  intros Hroots Hargs Hpke.
  pose proof (@list_Mmap_find_preserves_fields_strong idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result args) as Hmmap.
  unfold vc in Hmmap. specialize (Hmmap e).
  destruct (list_Mmap find args e) as [args' e1] eqn:Heq_mmap.
  cbn [fst snd] in *.
  destruct (Hmmap Hroots Hargs) as (Hroots1 & Hfp & _).
  destruct Hfp as (_ & Hpar_eq & _ & _ & _ & Hhk_iff & _).
  assert (Hpke1 : parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e1) by
    (unfold parents_keys_in_equiv in *; intros y (s & Hg);
     apply (proj1 (Hhk_iff y)); apply Hpke; exists s; rewrite <- Hpar_eq; exact Hg).
  pose proof (@db_lookup_pure idx symbol symbol_map idx_map idx_trie analysis_result f args') as Hdbl.
  unfold vc in Hdbl. specialize (Hdbl e1).
  destruct (db_lookup idx symbol symbol_map idx_map idx_trie analysis_result f args' e1) as [mout e2] eqn:Heq_dbl.
  cbn [fst snd] in Hdbl.
  destruct Hdbl as (He2_eq & _).
  subst e2.
  destruct mout as [r|].
  - cbn [Mret StateMonad.state_monad snd]. exact Hpke1.
  - pose proof (@alloc_struct idx Eqb_idx Eqb_idx_ok lt idx_succ symbol symbol_map idx_map idx_map_ok idx_trie analysis_result Hlti Hlts Hltt) as Halloc.
    unfold vc in Halloc. specialize (Halloc e1).
    destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e1) as [r e3] eqn:Heq_alloc.
    cbn [fst snd] in Halloc.
    destruct Hroots1 as [roots1 Hroots1].
    destruct (Halloc roots1 Hroots1) as (Hroots3 & _ & Hr_hk3 & Hmono3 & _ & Hpar_eq3 & _).
    assert (Hpke3 : parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e3) by
      (unfold parents_keys_in_equiv in *; intros y (s & Hg);
       apply Hmono3; apply Hpke1; exists s; rewrite <- Hpar_eq3 in Hg; exact Hg).
    cbn [db_set Mbind StateMonad.state_monad snd] in *.
    cbn [atom_args atom_fn atom_ret] in *.
    pose proof (@get_analyses_preserves_fields idx lt idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result HA args') as Hga.
    unfold vc in Hga. specialize (Hga e3).
    destruct (get_analyses idx symbol symbol_map idx_map idx_trie analysis_result args' e3) as [out_a e4] eqn:Heq_ga.
    cbn [fst snd] in Hga.
    destruct Hga as (_ & Hequiv_eq4 & Hpar_eq4).
    assert (Hpke4 : parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e4) by
      (unfold parents_keys_in_equiv in *; intros y (s & Hg);
       rewrite Hequiv_eq4;
       apply Hpke3; exists s; rewrite <- Hpar_eq4; exact Hg).
    set (out_val := analyze idx symbol analysis_result {| atom_fn := f; atom_args := args'; atom_ret := r |} out_a).
    unfold update_analyses.
    cbn [atom_ret fst snd].
    set (e5 := {|
      db := db e4;
      equiv := equiv e4;
      parents := parents e4;
      epoch := epoch e4;
      worklist := worklist e4;
      analyses := map.put (analyses e4) r
        match map.get (analyses e4) r with
        | Some oa => analysis_meet idx symbol analysis_result out_val oa
        | None => out_val
        end;
      log := log idx symbol symbol_map idx_map idx_trie analysis_result e4
    |} : instance idx symbol symbol_map idx_map idx_trie analysis_result).
    assert (Hpke5 : parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result e5) by
      (unfold parents_keys_in_equiv in *; exact Hpke4).
    assert (Hr_hk5 : Sep.has_key r (parent (equiv e5))) by
      (cbn [equiv e5]; rewrite Hequiv_eq4; exact Hr_hk3).
    pose proof (@Hmmap Hroots Hargs) as Hmmap'.
    destruct Hmmap' as (Hroots1' & _ & Hall2).
    assert (Hargs'_hk1 : all (fun x => Sep.has_key x (parent (equiv e1))) args') by
      (apply all2_const_to_all_l with (l2 := args);
       apply all2_impl with (R := uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e1));
       [ intros a b Hab; exact (proj1 (@uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map idx_map_ok (equiv e1) roots1 a b Hroots1 Hab))
       | exact Hall2 ]).
    assert (Hargs'_hk5 : all (fun x => Sep.has_key x (parent (equiv e5))) args') by
      (apply all_wkn with (P := fun x => Sep.has_key x (parent (equiv e1)));
       [ intros a _ Ha; cbn [equiv e5]; rewrite Hequiv_eq4; apply Hmono3; exact Ha
       | exact Hargs'_hk1 ]).
    pose proof (@db_set'_parents_keys_in_equiv idx Eqb_idx Eqb_idx_ok symbol symbol_map idx_map idx_map_ok idx_trie analysis_result {| atom_fn := f; atom_args := args'; atom_ret := r |} out_val) as Hds'.
    unfold vc in Hds'. specialize (Hds' e5).
    cbn [atom_ret atom_args] in *.
    set (ds_result := db_set' idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result {| atom_fn := f; atom_args := args'; atom_ret := r |} out_val e5).
    change (parents_keys_in_equiv idx symbol symbol_map idx_map idx_trie analysis_result (snd (let (_, y) := ds_result in (@! ret r) y))).
    exact (Hds' Hr_hk5 Hargs'_hk5 (fun y Hy => Hy) Hpke5).
Qed.
