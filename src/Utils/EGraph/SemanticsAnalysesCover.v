(* analyses_cover: every node that is a key in the union-find has an analysis.
   The per-op (alloc_opaque / union) preservation+extension lemmas are threaded
   through add_ctx's good_worklist assembly so that add_ctx's internal hashes
   never push an [analysis_repair] worklist entry (the worklist stays pure
   [union_repair]).  Stated generically and split out of Semantics.v so the
   add_ctx invariant proof need not re-derive them.  The [hash_entry] case is
   already covered by [hash_entry_wl_frame] (Theorems.v) and the [add_open_sort]
   case by [add_open_sort_worklist_frame] (Theorems.v); these two close the
   remaining primitives. *)
From Stdlib Require Import Lists.List Classes.RelationClasses.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.

(* EXTERNAL: same body as Theorems.v's section-local [analyses_cover], stated at
   top level with the egraph context explicit (mirrors [parents_keys_in_equiv]
   in SemanticsParents.v). *)
Definition analyses_cover
  (idx symbol : Type) (symbol_map : forall A, map.map symbol A)
  (idx_map : forall A, map.map idx A) (idx_trie : forall A, map.map (list idx) A)
  (analysis_result : Type)
  (e : instance idx symbol symbol_map idx_map idx_trie analysis_result) : Prop :=
  forall z, Sep.has_key z e.(equiv).(parent) ->
            exists a, map.get e.(analyses) z = Some a.

(* alloc_opaque writes a default analysis for the fresh id and adds it as the
   only new key, so it preserves [analyses_cover] and covers the new id. *)
Lemma alloc_opaque_analyses_cover
  {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {lt : idx -> idx -> Prop} {idx_succ : idx -> idx}
  {symbol : Type} {symbol_map : forall A, map.map symbol A}
  {idx_map : forall A, map.map idx A} {idx_map_ok : forall A, map.ok (idx_map A)}
  {idx_trie : forall A, map.map (list idx) A} {analysis_result : Type}
  {HA : analysis idx symbol analysis_result}
  : vc (alloc_opaque idx idx_succ symbol symbol_map idx_map idx_trie analysis_result)
      (fun e res =>
         egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
         analyses_cover idx symbol symbol_map idx_map idx_trie analysis_result e ->
         analyses_cover idx symbol symbol_map idx_map idx_trie analysis_result (snd res)
         /\ exists a, map.get (snd res).(analyses) (fst res) = Some a).
Proof.
  unfold vc. intros e. unfold alloc_opaque.
  destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e))
    as [equiv' x_fresh] eqn:Halloc.
  cbn [fst snd]. intros Hok Hcov.
  assert (Hpar : parent equiv' = map.put (parent (equiv e)) x_fresh x_fresh)
    by (unfold UnionFind.alloc in Halloc; destruct (equiv e) as [ra pa mr l0];
        injection Halloc as <- <-; reflexivity).
  split.
  - unfold analyses_cover. cbn [analyses equiv]. intros z Hz. rewrite Hpar in Hz.
    eqb_case z x_fresh.
    + rewrite map.get_put_same. exists default. reflexivity.
    + rewrite map.get_put_diff by assumption.
      apply Hcov. unfold Sep.has_key in *.
      rewrite map.get_put_diff in Hz by assumption. exact Hz.
  - cbn [analyses]. rewrite map.get_put_same. exists default. reflexivity.
Qed.

(* Both endpoints of a PER-closure pair lie in the field of the base relation. *)
Lemma PER_closure_field {A : Type} (R : A -> A -> Prop) (a b : A)
  : PER_closure R a b ->
    (exists w, R a w \/ R w a) /\ (exists w, R b w \/ R w b).
Proof.
  induction 1.
  - split; [exists b; left | exists a; right]; assumption.
  - split; [exact (proj1 IHPER_closure1) | exact (proj2 IHPER_closure2)].
  - split; [exact (proj2 IHPER_closure) | exact (proj1 IHPER_closure)].
Qed.

(* union changes only [analyses] (by [map.put] at the two representatives) and
   adds no new union-find key, so it preserves [analyses_cover]. *)
Lemma union_analyses_cover
  {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
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
         analyses_cover idx symbol symbol_map idx_map idx_trie analysis_result e ->
         analyses_cover idx symbol symbol_map idx_map idx_trie analysis_result (snd res)).
Proof.
  unfold vc. intros e.
  pose proof (@union_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol
                symbol_map idx_map idx_map_ok idx_trie analysis_result HA v v1) as Hus.
  unfold vc in Hus. specialize (Hus e).
  destruct (Defs.union v v1 e) as [u e'] eqn:Heq. cbn [snd] in Hus |- *.
  intros Hroots Hkv Hkv1 Hcov.
  destruct (Hus Hroots Hkv Hkv1) as (Hdb & [roots' Hroots'] & Hper & Hpar_eq & _).
  unfold analyses_cover. intros z Hz.
  destruct Hroots as [roots_e Hroots_e].
  (* Step A: union adds no new key, so z is a key in e. *)
  assert (Hz_e : Sep.has_key z (parent (equiv e))).
  { unfold Sep.has_key in Hz.
    destruct (map.get (parent (equiv e')) z) as [vy|] eqn:Hgz; [|tauto].
    assert (Hzz' : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e') z z).
    { eapply PER_clo_trans;
        [ apply PER_clo_base; exact Hgz | apply PER_clo_sym; apply PER_clo_base; exact Hgz ]. }
    pose proof (proj2 (Hper z z) Hzz') as Hclo.
    unfold union_closure_PER in Hclo.
    destruct (PER_closure_field _ _ _ Hclo) as [ [w Hw] _ ].
    destruct Hw as [Hzw | Hwz].
    - destruct Hzw as [Huf | Hsing].
      + exact (proj1 (@uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map
                        idx_map_ok (equiv e) roots_e z w Hroots_e Huf)).
      + destruct Hsing as [Hzv _]. subst z. exact Hkv.
    - destruct Hwz as [Huf | Hsing].
      + exact (proj2 (@uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map
                        idx_map_ok (equiv e) roots_e w z Hroots_e Huf)).
      + destruct Hsing as [_ Hzv1]. subst z. exact Hkv1. }
  (* Step B: z therefore has an analysis in e. *)
  destruct (Hcov z Hz_e) as [a Ha].
  (* Step C: union only [map.put]s onto [analyses e], preserving Some-ness. *)
  unfold Defs.union in Heq. cbn [Mbind StateMonad.state_monad] in Heq.
  destruct (Defs.find v e) as [cx e1] eqn:Hf1. cbn [fst snd] in Heq.
  destruct (Defs.find v1 e1) as [cy e2] eqn:Hf2. cbn [fst snd] in Heq.
  assert (Hane1 : analyses e1 = analyses e)
    by (unfold Defs.find in Hf1; destruct (UnionFind.find (equiv e) v);
        injection Hf1 as <- <-; reflexivity).
  assert (Hane2 : analyses e2 = analyses e1)
    by (unfold Defs.find in Hf2; destruct (UnionFind.find (equiv e1) v1);
        injection Hf2 as <- <-; reflexivity).
  destruct (eqb cx cy) eqn:Hcxcy.
  - cbn [Mret StateMonad.state_monad] in Heq. injection Heq as <- <-.
    exists a. rewrite Hane2, Hane1. exact Ha.
  - destruct (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) (equiv e2) cx cy)
      as [uf' v'] eqn:Hufu.
    destruct (eqb cx v') eqn:Hcxv'; injection Heq as <- <-; cbn [analyses].
    + set (NEW := analysis_meet idx symbol analysis_result
                    (unwrap_with_default (map.get (analyses e2) cx))
                    (unwrap_with_default (map.get (analyses e2) cy))).
      eqb_case z v'.
      * rewrite map.get_put_same. exists NEW. reflexivity.
      * rewrite map.get_put_diff by assumption. eqb_case z cx.
        -- rewrite map.get_put_same. exists NEW. reflexivity.
        -- rewrite map.get_put_diff by assumption. rewrite Hane2, Hane1. exists a. exact Ha.
    + set (NEW := analysis_meet idx symbol analysis_result
                    (unwrap_with_default (map.get (analyses e2) cx))
                    (unwrap_with_default (map.get (analyses e2) cy))).
      eqb_case z v'.
      * rewrite map.get_put_same. exists NEW. reflexivity.
      * rewrite map.get_put_diff by assumption. eqb_case z cx.
        -- rewrite map.get_put_same. exists NEW. reflexivity.
        -- rewrite map.get_put_diff by assumption. rewrite Hane2, Hane1. exists a. exact Ha.
Qed.
